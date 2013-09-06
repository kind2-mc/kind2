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


(* cone of influence *)
open Types
open Lus_convert
open Exceptions

let solver = Globals.my_solver

type var_id = int

(* id, pos *)
type var_id_pos = 
    int*int

(* stores the earliest (closest to 0) depth at which a variable is used *)
let general_coi_table = (Hashtbl.create 10: (idtype,int)Hashtbl.t)

let general_coi_table_inactive = ref true (* set to false when coi generated *)
(* this is done so that we only figure in coi modifications if they have
   been calculated -- otherwise check_coi is always true *)
  
(* returns true if something changed *)
(* depth starts at zero and increases *)
(* stores the minimal depth at which a var is referenced *)
let add_general_coi var depth =
assert (depth >=0); 
  general_coi_table_inactive := false;
  try
    let d = Hashtbl.find general_coi_table var in
    if d < depth then
      begin
        Hashtbl.replace general_coi_table var depth;
        true
      end
    else
      false
  with Not_found ->
    Hashtbl.replace general_coi_table var depth;
    true
        
(* returns true if the variable should be defined at this depth *)
(* defaults to true if the table was never initialized *)
(* depth should be >= 0 *)
(* simplify this to not deal with depth for the time being *)
let check_general_coi var curr_depth =
  !general_coi_table_inactive ||
  (Hashtbl.mem general_coi_table var)


let rec print_pairlist ls =
  match ls with
      [] -> Printf.printf "\n"
    | (x,y)::t -> Printf.printf "(%d,%d)" x y;print_pairlist t


let rec combine_lists l1 l2 =
    begin
      match l1 with
          [] -> l2
        | h::t -> if List.mem h l2 then 
                    combine_lists t l2
                  else
                    combine_lists t (h::l2)
    end


(* il_expression -> idtype*int list *)
(* returns the id(s) & depth for a il_expression *)
let rec get_coi_signatures c1 = 
  match c1 with
      | VAR_GET(_,d,(NUM nk),_) -> [(nk,d)]
      | TUPLE_LIT(el) ->  (* get a lowest-d example *)
         let rec do_elist ls = match ls with
             [] -> []
           | [e1] -> get_coi_signatures e1
           | e1::es -> (get_coi_signatures e1) @ (do_elist es)
         in
         do_elist el
      | ONE -> (* assertion *) [(1,0)]
      | _ -> raise COIException

(* returns true if any id in the coi sig should be present *)
(* meaning if the LHS was tagged in the COI initialization *)
(* depth should be >= 0 *)
let check_coi c1 depth =  
assert (depth >= 0);
  let ids = get_coi_signatures c1 in
  List.fold_left (fun acc (id,d) ->
                   (check_general_coi id (d+depth)) || acc
                 ) false ids

(* listing dependencies for recursive lookup, static once set *)
(* the bool option if for the recursive definition check, currently unused *)
let dependencies_table = 
  (Hashtbl.create 10:(idtype,(bool option * var_id_pos list))Hashtbl.t)

(* each assignment should be unique on LHS *)
let add_dependencies (x,_) y = 
  Hashtbl.replace dependencies_table x (None,y)

let get_dependencies v = 
  let (_,deps) = Hashtbl.find dependencies_table v in
  deps

(* takes a cvclexpression *)
(* returns an id,depth pair list *)
let rec extract_ids ce inlist = 
  begin
    match ce with
      (* we need to define constant arrays because, eg. pre(false) = nil *)
      (* special case for true/false, they return the special valies 1 or 0 *)
        ZERO -> inlist
      | ONE -> inlist
      | INT_CONST(e1) -> 
          extract_ids e1 inlist
      | REAL_CONST(e1,_) -> 
          extract_ids e1 inlist
      | FLOAT _ -> inlist
      | STRING _ -> inlist
      | STEP_BASE -> inlist
      | POSITION_VAR _ -> inlist
      | NUM _ -> inlist
      | PLUS(e1,e2) -> 
          combine_lists (extract_ids e1 []) (extract_ids e2 inlist)
      | MINUS(e1,e2) -> 
          combine_lists (extract_ids e1 []) (extract_ids e2 inlist)
      | UMINUS(e1) -> 
          extract_ids e1 inlist
      | MULT(e1,e2) -> 
          combine_lists (extract_ids e1 []) (extract_ids e2 inlist)
      | DIV(e1,e2) -> 
          combine_lists (extract_ids e1 []) (extract_ids e2 inlist)
      | INTDIV(e1,e2) -> 
          combine_lists (extract_ids e1 []) (extract_ids e2 inlist)
      | MOD(e1,e2) -> 
          combine_lists (extract_ids e1 []) (extract_ids e2 inlist)
      | REL(_,e1,e2) ->
          combine_lists (extract_ids e1 []) (extract_ids e2 inlist)
      | ITE(e1,e2,e3) -> 
          let l1 = combine_lists (extract_ids e2 []) 
                    (extract_ids e3 inlist)
          in
          combine_lists (extract_ids e1 []) l1
      | STREAM_ITE(e1,e2,e3) -> 
(* deal with special case here? *)
          let l1 = combine_lists (extract_ids e2 []) 
                    (extract_ids e3 inlist)
          in
          combine_lists (extract_ids e1 []) l1
      | B_AND(e1,e2) -> 
          combine_lists (extract_ids e1 []) (extract_ids e2 inlist)
      | B_OR(e1,e2) -> 
          combine_lists (extract_ids e1 []) (extract_ids e2 inlist)
      | B_IMPL(e1,e2) -> 
          combine_lists (extract_ids e1 []) (extract_ids e2 inlist)
      | B_NOT(e1) -> 
          extract_ids e1 inlist
      | B_IFF(e1,e2) -> 
          combine_lists (extract_ids e1 []) (extract_ids e2 inlist)
      | VAR_GET(s,d,(NUM nk'),i) -> 
          let nk = Tables.resolve_substitution nk' in
          let id = nk in
          combine_lists [(id,d)] inlist
      | RECORD_LIT(el) -> 
         let rec do_elist ls outl = match ls with
             [] -> outl
           | (_,h)::t -> do_elist t (extract_ids h outl)
         in
         do_elist el inlist
      | RECORDREF(e1,field) ->
(* not supported yet *)
raise Expr_not_supported
        (* extract_ids e1 inlist*)
      | TUPLE_LIT(el) -> 
         let rec do_elist ls outl = match ls with
             [] -> outl
           | h::t -> do_elist t (extract_ids h outl)
         in
         do_elist el inlist
      | TUPLEREF(e1,index) -> 
(* not supported yet *)
raise Expr_not_supported
        (* extract_ids e1 inlist*)
      | _ -> raise (ConversionError "Coi.extract_ids")
  end

(* takes a il_formula *)
(* note: dealing with tuple LHS can be troublesome -- currently only
 indexing against the first element, which may be a mistake *)
let rec examine_assignments f =
    match f with
      | F_NOT(f1) -> examine_assignments f1
      | F_AND(f1,f2) -> 
          examine_assignments f1;
          examine_assignments f2
      | F_EQ(a,b,t) ->
          let lhs = extract_ids a [] in
          let rhs = extract_ids b [] in
          begin
            match lhs with
             | [] ->
                 if a = ONE then
                   begin (* assertion, can happen multiple times *)
                     try
                       let olddep = get_dependencies 1 in
                       add_dependencies (1,0) (combine_lists rhs olddep)
                     with Not_found ->
                       add_dependencies (1,0) rhs
                   end
                 else
                   raise EmptyLHS
             | h::t -> 
                 add_dependencies h rhs;
                 List.iter (fun x -> 
                              add_dependencies x rhs
                 ) t
          end
      | _ -> ()

let property_id_list p =
  let term,_ = convert_term p (POSITION_VAR (solver#get#position_var1)) 0 0 None None in
  List.map (fun (i,d) -> i) (extract_ids term [])


(* given an id list & depth, calculates a list of vars at this level *)
(* assumes examine_assignments has already been called *)
(* vrefs is a list of var ids (at curr_depth) *)
(* curr depth starts at zero and increases *)
(* need to re-think the depth offsets *)
let rec calculate_dependencies vrefs curr_depth max_depth =
  if curr_depth <= max_depth then
    begin
      match vrefs with
          [] -> ()
        | id::t -> 
            if (add_general_coi id curr_depth) then
              begin
                try
                  List.iter (fun (i,d) -> 
                          calculate_dependencies [i] (curr_depth(*+d*)) max_depth
                        ) (get_dependencies id)
                with Not_found -> ()
              end;
            calculate_dependencies t curr_depth max_depth
    end

let rec calculate_all_dependencies vrefs curr_depth max_depth =
  if curr_depth <= max_depth then
    begin
      calculate_dependencies vrefs curr_depth max_depth;
      calculate_all_dependencies vrefs (curr_depth+1) max_depth
    end

(* assumed used_vars has been populated *)
(* assumed examine_assingments has been called *)
(* removes redundant nodes from used_vars *)
(* we know there are no cyclic definitions, so we can remove any references
   that themselves are only dependent on other variables that are already present *)
let clean_used_vars max_depth =
  Hashtbl.iter (fun x y ->
    match y with
        None -> ()
      | Some r ->
          if Tables.is_input_var x then ()
          else
            begin
              (* get a list of dependencies wrt depth 0 *)
              (* only include inputs vars & pres *)
              let newrefs = List.fold_left (fun acc d ->
                (* now check all the references for this var against its deps *)
                (* if all dependencies are already in the used_vars table, 
                   we can safely remove this reference *)
                  try
                    List.iter (fun (u,d2) ->
                      let l1 = match Tables.find_used_var u with
                        | None -> raise Not_found
                        | Some r2 -> r2.depths
                      in
                      if not (List.mem (d2+d) l1) then raise Not_found
                    ) (get_dependencies x);
                    acc
                  with Not_found ->
                    d::acc
                ) [] r.depths
              in
              r.depths <- newrefs
            end
  ) (Tables.get_used_vars())
