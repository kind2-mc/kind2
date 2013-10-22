(*
This file is part of the Kind verifier

* Copyright (c) 2007-2009 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

open Types
open OldFlags
open Exceptions
open Globals

  
let idcounter = new Counter.counter

(*
let list_print ids = List.iter (fun x-> Printf.printf "%d " x) ids; Printf.printf "\n"
let list_print2 ids = List.iter (fun (x,y)-> Printf.printf "%d,%d " x y) ids; Printf.printf "\n"
*)



let max_depth = ref 0 (* number of nested pres *)
let max_adepth = ref 0 (* number of nested pres *)


(* makes a copy of the specified hashtbl *)
let store_hash a b = Hashtbl.iter (fun x y -> Hashtbl.replace b x y) a

(* current line number and position of the last newline *)
let linenum = ref 1
let linepos = ref 0


(*

(* assertion formula collection *)
(* starts out with TRUE/ONE, and adds *)
let assertion_formula = ref []
(* returns a il_expression option *)
let add_assertion_term t =
    assertion_formula := t::(!assertion_formula)
  
let get_assertion_term () =
  let rec build_term af =
    match af with
       [] -> ONE
     | [x] -> x
     | x::y -> B_AND(x,build_term y)
  in
  match build_term !assertion_formula with
      ONE -> None
    | x -> Some x

let assertions_present () = 
  not (!assertion_formula = [])

*)

let property_formula = ref []

let get_property_term () =
  let rec build_term af =
    match af with
       [] -> ONE
     | [x] -> x
     | x::y -> B_AND(x,build_term y)
  in
  match build_term !property_formula with
      ONE -> None
    | x -> Some x



let rec simplify_position_depth p = 
  match p with
     POSITION_VAR _ -> 0
   | NUM(x) -> x
   | PLUS (e1,e2) -> (simplify_position_depth e1)+(simplify_position_depth e2)
   | MINUS (e1,e2) -> (simplify_position_depth e1)-(simplify_position_depth e2)
   | UMINUS (e1) -> -(simplify_position_depth e1)
   | _ -> raise SimplifyPositionException





(* simplifies formulas with true/false *)
(* il_formula -> il_formula -> il_formula *)
let f_and f1 f2 = 
  match f1,f2 with
      F_TRUE,x -> x
    | x,F_TRUE -> x
    | F_FALSE,_ -> F_FALSE
    | _,F_FALSE -> F_FALSE
    | _ -> F_AND(f1,f2)

(* il_formula -> il_formula -> il_formula -> il_formula *)
let f_and3 f1 f2 f3 =
  match f_and f2 f3 with
     F_TRUE -> f1
   | F_FALSE -> F_FALSE
   | x -> F_AND(f1,x)



(* the transtable goes from the original varid to this instance's varid *)

(* inst_ref should be a string of form "_num_" *)
(* inst_ref is the reference string for this call instance *)
(* tt is the table *)
(* sourcelist is the list of (varid,_) to be processed *)
let augment_transtable inst_ref tt sourcelist =
  try
    List.iter (fun (x,_) ->
      (* generate a new variable instance *)
      let (n,v,t,c) = Tables.safe_find_varinfo x ("augment_transtable:"^(string_of_int x)) in
      let inst_id = idcounter#next in
      let s = Tables.rename_sym (inst_ref^"_"^(Tables.resolve_var_name v)) in
      let new_class = if c=ABSTRACT then c else LOCAL in
      Tables.update_varinfo inst_id (n,s,t,new_class);
      Tables.varid_name_add s inst_id;
      (* links the original id to the new id in tt *)
      Hashtbl.replace tt x inst_id
    ) sourcelist
  with Not_found -> ()

(* similar to the augment, but we do not create new vars or sdefs *)
(* do we just substitute the external id for the inst_id *)
let substitute_transtable tt orig_ids external_ids =
  List.iter2 (fun (x,_) (y,_) -> 
      Hashtbl.replace tt x y
    ) orig_ids external_ids

(* returns substitution expr, list of new sdefs *)
(* this builds a table of *)
let build_transtable nid ir transtable inputs outputs =
  let name = Tables.get_nodename nid in
  let locals = 
    try Tables.get_node_locals nid
    with Not_found -> []
  in
  (* build a translation table of original ids -> new ids *)
  let num = idcounter#next in
  let inst_ref = name^"_"^(string_of_int num) in
  augment_transtable inst_ref transtable inputs;
  augment_transtable inst_ref transtable outputs;
  augment_transtable inst_ref transtable locals;
  transtable

(* tt is Some(string,tt) *) 
let subs_var tt v_id =
  match tt with 
      None -> v_id
    | Some (_,tbl) ->
        try
          Hashtbl.find tbl v_id
        with Not_found -> v_id
 

(* takes a node call and expands it into a list of S_DEFS *)
(* node A (x,y) returns (z);
   var w;
   let 
     z = x+y;
   tel;
   
   A(a,b) becomes:
   z'
   and we add
   x' = a;
   y' = b;
   z' = x'+y';
*)
(* additional S_DEFs list from parameters *)
let expand_node nid params tt inputs =
  (* get existing defs *)
  let defs = Tables.get_node_defs nid in
  (* add parameter assignments *)
  List.fold_left2 (fun acc rhs (id,lt) ->
    let sid = subs_var tt id in
    let lhs = (S_VAR("_",sid),lt) in
    (S_DEF(nid,lhs,rhs),L_BOOL)::acc
  ) defs params inputs


(* as above, but make sure everything is guarded by the condact's clock *)
let expand_condact_node nid params tt clk =
  let inputs = Tables.get_node_inputs nid in
  (* base definitions *)
  let defs = Tables.get_node_defs nid in
  let defs' = List.map (fun w ->
                let x,y,zt,z =
                  match w with 
                    (S_DEF(x,y,((_,zt) as z)),L_BOOL) -> x,y,zt,z
                    | _ -> raise (ConversionError "expand_condact_node")
                in
                let z' = (S_ITE(clk,z,(S_PRE(y),zt)),zt) in
                (S_DEF(x,y,z'),L_BOOL)
              ) defs 
  in
  List.fold_left2 (fun acc p (id,lt) ->
      let sid = subs_var tt id in
      let lhs = (S_VAR("_",sid),lt) in
      let rhs = (S_ITE(clk,p,(S_PRE(lhs),lt)),lt) in
      (S_DEF(nid,lhs,rhs),L_BOOL)::acc
  ) defs' params inputs


(* returns the output S_VAR *)
let expand_node_output nid tt =
  let outputs = Tables.get_node_outputs nid in
  if List.length outputs = 1 then
    let (out,ty) = List.hd outputs in
    S_VAR("_",out),ty
  else
    S_TUPLELIT(List.map (fun (x,t) -> S_VAR("_",x),t) outputs), (* term *)
    L_TUPLE(List.map (fun (_,t) -> t) outputs) (* type *)

(* typed_stream -> il_expression -> il_expression -> il_expression * il_formula *)
(*is a cvc expression that represents the "beginning"of stream *)
(*  position is the n-value we are checking (a cvcl expression) *)
(* depth is the current number of pres we have encountered *)
(* adepth is the current number of ->s we have encountered *)
(* subs is a Hashtbl.t option -- None indicates no substitution to take place*)
(* cclk is a typedstream option, with Some clk indicating we are within a condact *)
let rec convert_term (s,t) position depth adepth subs cclk =
assert (depth >= 0);
  match s with 
      S_TRUE -> (ONE,F_TRUE)
    | S_FALSE -> (ZERO,F_TRUE)
    | S_INT(x) -> (INT_CONST(NUM(x)),F_TRUE)
    | S_REAL(i,n,d) -> (* cvcl doesn't accept floats, per se *)
        (* so convert to a rational expression *)
        if i != 0 && n != 0 then
          let cvctmp = PLUS(NUM(i),DIV(NUM(n),NUM(d))) in
          let ftmp = (float_of_int i)+.(float_of_int n)/.(float_of_int d) in
          (REAL_CONST(cvctmp,ftmp),F_TRUE)
        else if i = 0 then
          let cvctmp = DIV(NUM(n),NUM(d)) in
          let ftmp = (float_of_int n)/.(float_of_int d) in
          (REAL_CONST(cvctmp,ftmp),F_TRUE)
        else if n = 0 then
          (REAL_CONST(NUM(i),(float_of_int i)),F_TRUE)
        else (* prevent div by zero *)
          (REAL_CONST(NUM(0),0.0),F_TRUE)
    | S_VAR(sym,id) -> 
        begin
assert(id >= 0);
          Tables.add_var_count (Tables.resolve_substitution id) 1; (* number of occurrences *)
          match t with
              L_BOOL 
            | L_INT
            | L_INT_RANGE(_)
            | L_REAL 
            | L_RECORD(_)
            | L_TUPLE(_) -> (VAR_GET({s=sym},depth,NUM(subs_var subs id),position),F_TRUE)
            | _ -> raise (IncorrectTypedConversion "S_VAR")
        end
    | S_AND(s1,s2) ->
        begin
          match s1,s2 with
              (S_TRUE,_),_ ->
                   convert_term s2 position depth adepth subs cclk
            | _,(S_TRUE,_) ->
                   convert_term s1 position depth adepth subs cclk
            | _ ->
                   let b1,f1 = convert_term s1 position depth adepth subs cclk in
                   let b2,f2 = convert_term s2 position depth adepth subs cclk in
                   B_AND(b1,b2), (f_and f1 f2)
        end
    | S_OR(s1,s2) ->
        begin
          match s1,s2 with
              (S_FALSE,_),_ ->
                  convert_term s2 position depth adepth subs cclk
            | _,(S_FALSE,_) ->
                  convert_term s1 position depth adepth subs cclk
            | _ ->
                  let b1,f1 = convert_term s1 position depth adepth subs cclk in
                  let b2,f2 = convert_term s2 position depth adepth subs cclk in
                  B_OR(b1,b2), (f_and f1 f2)
        end
    | S_IMPL(s1,s2) ->
              let b1,f1 = convert_term s1 position depth adepth subs cclk in
              let b2,f2 = convert_term s2 position depth adepth subs cclk in
              B_IMPL(b1,b2), (f_and f1 f2)
    | S_XOR(s1,s2) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        let b2,f2 = convert_term s2 position depth adepth subs cclk in
        B_NOT(B_IFF(b1,b2)), (f_and f1 f2)
    | S_NOT(s1) -> 
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        B_NOT(b1),f1
    | S_PRE(s1) ->
        if depth >= !max_depth then
          max_depth := depth+1;
        convert_term s1 (MINUS (position,NUM(1))) (depth+1) adepth subs cclk
    | S_FBY(s1,i,s2) ->
        if depth+i > !max_depth then
          max_depth := depth+i;
        if adepth+i > !max_adepth then
          max_adepth := adepth+i;
        let b1,f1 = 
          convert_term s1 (MINUS (position,NUM(i))) (depth+i) (adepth+i) subs cclk 
        in
        let b2,f2 = convert_term s2 position depth adepth subs cclk in
        STREAM_ITE(REL(GTE,position,NUM(i)), b1, b2), (f_and f1 f2)
    | S_FOLLOWEDBY(s1,s2) ->
        (* ARROW *)
        (* note that x->z->y = xyyyyyyyy..., not xzyyyyyy... *)
        if adepth >= !max_adepth then
          max_adepth := adepth+1;
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        let b2,f2 = convert_term s2 position depth (adepth+1) subs cclk in
        STREAM_ITE(REL(EQ,position,STEP_BASE), b1, b2), (f_and f1 f2)
(*
    | S_CONDACT(s1,s2,s3,s4) ->
        (* s2 is only _evaluated_ when s1 is true *)
        (* s4 = if s1 then s2 else (s3->pre(s4)) *)
        (* s4 = S_FOLLOWEDBY(s3,S_ITE(s1,s2,S_PRE(s4))) *)
        (* not correct if s2 contains a node *)
        let ck =
          match cclk with
              None -> s1
            | Some clk -> S_AND(clk,s1),L_BOOL
        in
        (* X -> *)
        let b1,f1 = convert_term s3 position depth adepth subs cclk in
        (* -> ITE *)
        let b2,f2 = convert_term ck position depth adepth subs cclk in
        let b3,f3 = convert_term s2 position depth adepth subs (Some ck) in
        let b4,f4 = convert_term (S_PRE(s4),t) position depth adepth subs cclk in
        let fbterm = STREAM_ITE(REL(EQ,position,STEP_BASE), b1, b4) in
        let iteterm = STREAM_ITE(b2,b3,fbterm) in
        iteterm,(f_and f1 (f_and f2 (f_and f3 f4)))
        
(*        convert_term (S_FOLLOWEDBY(s3,(S_ITE(ck,s2,(S_PRE(s4),t)),t)),t) position depth adepth subs cclk
*)
(*
        let iteterm = ITE(b2,b3,b4) in
        ITE(REL(EQ,position,NUM(0)), b1, iteterm),(f_and f1 (f_and f2 (f_and f3 f4)))
*)
*)
    | S_ITE(s1,s2,s3) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        let b2,f2 = convert_term s2 position depth adepth subs cclk in
        let b3,f3 = convert_term s3 position depth adepth subs cclk in
        ITE(b1,b2,b3), (f_and f1 (f_and f2 f3))
    | S_EQ(((_,L_BOOL) as s1),((_,L_BOOL) as s2)) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        let b2,f2 = convert_term s2 position depth adepth subs cclk in
        B_IFF(b1,b2), (f_and f1 f2)
    | S_EQ(s1,s2) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        let b2,f2 = convert_term s2 position depth adepth subs cclk in
        REL(EQ,b1,b2), (f_and f1 f2)
    | S_LT(s1,s2) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        let b2,f2 = convert_term s2 position depth adepth subs cclk in
        REL(LT,b1,b2), (f_and f1 f2)
    | S_GT(s1,s2) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        let b2,f2 = convert_term s2 position depth adepth subs cclk in
        REL(GT,b1,b2), (f_and f1 f2)
    | S_LTE(s1,s2) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        let b2,f2 = convert_term s2 position depth adepth subs cclk in
        REL(LTE,b1,b2), (f_and f1 f2)
    | S_GTE(s1,s2) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        let b2,f2 = convert_term s2 position depth adepth subs cclk in
        REL(GTE,b1,b2), (f_and f1 f2)
    | S_PLUS(s1,s2) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        let b2,f2 = convert_term s2 position depth adepth subs cclk in
        PLUS(b1,b2), (f_and f1 f2)
    | S_MINUS(s1,s2) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        let b2,f2 = convert_term s2 position depth adepth subs cclk in
        MINUS(b1,b2), (f_and f1 f2)
    | S_MULT(s1,s2) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        let b2,f2 = convert_term s2 position depth adepth subs cclk in
        MULT(b1,b2), (f_and f1 f2)
    | S_DIV(s1,s2) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        let b2,f2 = convert_term s2 position depth adepth subs cclk in
        DIV(b1,b2), (f_and f1 f2)
    | S_INTDIV(s1,s2) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        let b2,f2 = convert_term s2 position depth adepth subs cclk in
        INTDIV(b1,b2), (f_and f1 f2)
    | S_MOD(s1,s2) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        let b2,f2 = convert_term s2 position depth adepth subs cclk in
        MOD(b1,b2), (f_and f1 f2)
    | S_UMINUS(s1) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        UMINUS(b1), f1
    | S_COERCE_TO_INT(s1) -> (* not applicable to cvcl? *)
        convert_term s1 position depth adepth subs cclk
    | S_COERCE_TO_REAL(s1) -> (* not applicable to cvcl? *)
        convert_term s1 position depth adepth subs cclk
(*    | S_CURRENT(S_WHEN(s1,s2),t1) -> (* different clock *)
        (* is this correct?  no!  not if s1 contains a node! *)
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        let b2,f2 = convert_term s2 position depth adepth subs cclk in
        let b3,f3 = convert_term (S_PRE s1,t1) position depth adepth subs cclk in
        ITE(b2,b1,b3), (f_and f1 (f_and f2 f3))
*)
    | S_RECORDLIT(s1) ->
        let r,f =
          List.fold_left (fun (rs,fs) (field,e) -> 
              let b1,f1 = convert_term e position depth adepth subs cclk in
              (((field,b1)::rs),(f_and f1 fs))
          ) ([],F_TRUE) s1 
        in
        RECORD_LIT(r),f
    | S_TUPLELIT(s1) ->
        let t,f =
          List.fold_left (fun (ts,fs) (e) -> 
              let b1,f1 = convert_term e position depth adepth subs cclk in
              (((b1)::ts),(f_and f1 fs))
          ) ([],F_TRUE) s1 
        in
        TUPLE_LIT(List.rev t),f
    | S_RECORDREF(s1,fieldname) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        RECORDREF(b1,fieldname),f1
    | S_TUPLEREF(s1,index) ->
        let b1,f1 = convert_term s1 position depth adepth subs cclk in
        TUPLEREF(b1,index),f1
    | S_CURRENT(s1) -> (* if no clock change, does nothing *)
        convert_term s1 position depth adepth subs cclk
    | S_DEF(nid,s1,s2) -> (* this includes a "dummy" ONE expr *)
          if !inlining_mode then
            begin
              match s1,s2 with
                  (S_VAR(_,x),_),(S_VAR(_,y),_) -> 
                     (* strips out redundant sdefs *)
                     let b1,f1 = 
                       convert_term s1 position depth adepth subs cclk 
                     in
                     let b2,f2 = 
                       convert_term s2 position depth adepth subs cclk 
                     in
                     Tables.add_substitution (subs_var subs x) (subs_var subs y); 
                     ONE, f_and3 F_TRUE f1 f2
                | (S_TUPLELIT(tup1),_),(S_TUPLELIT(tup2),_) ->
                     (* breaks tuples into individual sdefs *)
                     let f_final = List.fold_left2 (fun f x y ->
                        let b1,f1 =
                          convert_term (S_DEF(nid,x,y),L_BOOL) position depth 
                            adepth subs cclk
                        in
                        f_and f f1
                      ) F_TRUE tup1 tup2
                     in
                     ONE,f_final
                | lhs_vars,(S_NODE(nid,lnum,pnum,params),_) -> 
		    (* Yeting. To ensure that only one node allowd *)
		    (* For implication invariants only *)
		    (*failwith "More than one node found";*)
                     (* breaks node calls into individual sdefs *)
                    let name = Tables.get_nodename nid in
                    let s1,tt1 = match subs with
                        None -> "",Hashtbl.create 1
                      | Some (s2,tt2) -> s2^"_",tt2
                    in
                    let s = 
                      s1^name^"_"^(string_of_int lnum)^"_"^(string_of_int pnum)
                    in
                    let inputs=Tables.get_node_inputs nid in
                    let outputs=Tables.get_node_outputs nid in
                    let tt = 
                      Some (s,build_transtable nid s tt1 inputs outputs) 
                    in
                    let sdeflist = 
                      match cclk with
                          None -> expand_node nid params tt inputs
                        | Some clk -> expand_condact_node nid params tt clk
                    in
                    let out = expand_node_output nid tt in
                    let b1,f1 = 
                      convert_term (S_DEF(nid,lhs_vars,out),L_BOOL) position 
                        depth adepth tt cclk 
                    in
                    let f = List.fold_left (fun acc sd ->
                        let _,f2 = convert_term sd position depth adepth tt cclk in
                        f_and f2 acc 
                      ) f1 sdeflist
                    in
                    ONE,f
                | _,_ -> 
                  let b1,f1 = convert_term s1 position depth adepth subs cclk in
                  let b2,f2 = convert_term s2 position depth adepth subs cclk in
                  ONE, f_and3 (F_EQ(b1,b2,L_INT)) f1 f2
            end
          else
            let b1,f1 = convert_term s1 position depth adepth subs cclk in
            let b2,f2 = convert_term s2 position depth adepth subs cclk in
            ONE, f_and3 (F_EQ(b1,b2,L_INT)) f1 f2
    | S_ASSERT(nid,s1) -> 
        (* we make sure this is linked by also including the "true_var" *)
        let b2,f2 = convert_term s1 position depth adepth subs cclk in
          (* add_assertion_term b2;  (*Yeting*) *)
        Lus_assertions.add_assertion_term b2;  (*Yeting*)
        ONE, f_and (F_EQ(ONE,b2,L_INT)) f2
    | S_PROPERTY(nid,s1) -> 
        (* we make sure this is linked by also including the "true_var" *)
        let b2,f2 = convert_term s1 position depth adepth subs cclk in
          
	  (*add_assertion_term b2; Yeting *)
	  failwith "This should never happen S_PROPERTY"; (*Yeting*)
        ONE, f_and (F_EQ(ONE,b2,L_INT)) f2
    | S_NODE(nid,lnum,pnum,params) -> (* flatten the node call *)
       (* this may fail on recursive node calls *)
      (* this does not work for condact'd nodes!!! *)
      (* in this case we need to expand the condact to all instance S_DEFS *)
      let name = Tables.get_nodename nid in
      let s1,tt1 = match subs with
          None -> "",Hashtbl.create 1
        | Some (s2,tt2) -> s2^"_",tt2
      in
      let s = s1^name^"_"^(string_of_int lnum)^"_"^(string_of_int pnum) in
      let inputs = Tables.get_node_inputs nid in
      let outputs = Tables.get_node_outputs nid in
      let tt = Some (s,build_transtable nid s tt1 inputs outputs) in
      let sdeflist = 
        match cclk with
            None -> expand_node nid params tt inputs
          | Some clk -> expand_condact_node nid params tt clk
      in
      let out = expand_node_output nid tt in
      let b1,f1 = convert_term out position depth adepth tt cclk in
      let f = List.fold_left (fun acc sd ->
                let _,f2 = convert_term sd position depth adepth tt cclk in
                f_and f2 acc 
              ) f1 sdeflist
      in
      b1,f
(*    | S_ATMOSTONE(),_ -> *)
    | _ -> raise (IncorrectTypedConversion "convert_term")

let get_max_depth () = !max_depth
let get_max_adepth () = !max_depth
let reset_max_depth () = max_depth := 0;  max_adepth := 0



let state_vars_list () = 
    Hashtbl.fold (fun i e acc ->
       match e with
           None -> acc
         | Some r -> i::acc
    ) (Tables.get_used_vars()) []

(* typed_stream -> il_formula *)
let convert_equation s position =
  let _,x = convert_term s position 0 0 None None in
  x

let convert_def_list position target_node =
  (* set position name *)
  let ds = Tables.get_node_defs target_node in
  reset_max_depth();
  List.fold_left (fun acc s ->
               f_and acc (convert_equation s position)) F_TRUE ds


