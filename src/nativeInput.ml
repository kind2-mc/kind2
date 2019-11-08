(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)

open Lib

module Ids = Lib.ReservedIds

module HH = HString.HStringHashtbl
module HS = HStringSExpr
module D = GenericSMTLIBDriver

module I = Ident

let s_prime = HString.mk_hstring "prime"

module Conv = SMTExpr.Converter(D)
let conv = { D.smtlib_string_sexpr_conv with
             D.prime_symbol = Some s_prime }
let conv_type_of_sexpr = conv.D.type_of_sexpr
let conv_term_of_sexpr = conv.D.expr_of_string_sexpr conv

  
let s_define_node = HString.mk_hstring "define-node"
let s_init = HString.mk_hstring "init"
let s_trans = HString.mk_hstring "trans"
let s_callers = HString.mk_hstring "callers"
let s_subsystems = HString.mk_hstring "subsystems"
let s_lambda = HString.mk_hstring "lambda"
let s_opt_const = HString.mk_hstring ":const"
let s_opt_input = HString.mk_hstring ":input"
let s_opt_for_inv_gen = HString.mk_hstring ":for-inv-gen"
let s_opt_init_flag =  HString.mk_hstring ":init-flag"
let s_annot = HString.mk_hstring ":user"
let s_contract = HString.mk_hstring ":contract"
let s_gen = HString.mk_hstring ":generated"
let s_inst = HString.mk_hstring ":subsystem"
let s_cand = HString.mk_hstring ":candidate"
let s_assumption =  HString.mk_hstring ":assumption"
let s_guarantee =  HString.mk_hstring ":guarantee"
let s_guaranteeonemodeactive = HString.mk_hstring ":one_mode_active"
let s_guaranteemodeimplication = HString.mk_hstring ":mode_implication"
let s_props = HString.mk_hstring "props"
let s_intrange = HString.mk_hstring "IntRange"


let seen_systems = HH.create 17

(*********************************************)
(* Parsing of systems in native input format *)
(*********************************************)

(* Return the name of the initial state constraint predicate *)
let init_pred_hname pred =
  Format.sprintf "%s_%s_0" Ids.init_uf_string
    (HString.string_of_hstring pred)

(* Return the name of the transition relation predicate *)
let trans_pred_hname pred =
  Format.sprintf "%s_%s_0" Ids.trans_uf_string
    (HString.string_of_hstring pred)


(* Return a type of an S-expression *)
let type_of_sexpr = function 

  (* Integer range type *)
  | HS.List [HS.Atom c;
             HS.Atom l;
             HS.Atom u] when c == s_intrange -> 

    (* Numeral of lower bound *)
    let nl =
      try Numeral.of_string (HString.string_of_hstring l) with 
        | Invalid_argument _ -> 
          failwith "Invalid argument for integer range type"
    in
    
    (* Numeral of lower upper bound *)
    let nu = 
      try Numeral.of_string (HString.string_of_hstring u) with 
        | Invalid_argument _ -> 
          failwith "Invalid argument for integer range type"
    in
    
    (* Create integer range type *)
    Type.mk_int_range nl nu

  | s ->
    (* Otherwise get SMTLIB type *)
    conv_type_of_sexpr s



(* Create a state variable with the given scope from the S-expression *)
let state_var_of_sexpr = function 

  (* State variable definition is the name, its type and options *)
  | HS.List (HS.Atom v :: t :: opts) -> 

    (* Name of the variable *)
    let var_name, scope =
      Lib.extract_scope_name (HString.string_of_hstring v) in

    (* Type of the variable *)
    let var_type = type_of_sexpr t in

    (* Options of the variable *)
    let is_const, is_input, for_inv_gen, is_init_flag = 
      List.fold_left 

        (* Parse input and modify options *)
        (fun (is_const, is_input, for_inv_gen, is_init_flag) -> function 
           | HS.Atom c when c == s_opt_const ->
             (true, is_input, for_inv_gen, is_init_flag)
           | HS.Atom c when c == s_opt_input ->
             (is_const, true, for_inv_gen,is_init_flag)
           | HS.Atom c when c == s_opt_for_inv_gen ->
             (is_const, is_input, true, is_init_flag)
           | HS.Atom c when c == s_opt_init_flag ->
             (is_const, is_input, for_inv_gen, true)
           | _ -> failwith "Invalid option for state variable")

        (* Defaults for the options *)
        (false, false, false, false)

        opts
    in

    (* Create state variable and return *)
    StateVar.mk_state_var ~is_input ~is_const ~for_inv_gen
      var_name scope var_type,
    is_init_flag

  | _ -> failwith "Invalid state variable declaration"



(* Convert an s-expression to a term *)
let term_of_sexpr s = conv_term_of_sexpr [] s

(* Convert an s-expression to a term with bound free varaibles *)
let term_of_sexpr_bound_vars bvars s = conv_term_of_sexpr bvars s



(* Arguments of initial state predicate *)
let init_args_of_state_vars state_vars =
  List.map
    (fun sv -> Var.mk_state_var_instance sv Numeral.zero)
    state_vars

(* Arguments of transition relation predicate *)
let trans_args_of_state_vars state_vars =
  let at0 = init_args_of_state_vars state_vars in
  let at1 =
    List.map (fun v -> Var.bump_offset_of_state_var_instance v Numeral.one) at0 in
  let at0 = List.filter (fun v -> not (Var.is_const_state_var v)) at0 in
  at1 @ at0



let sbind_of_sexpr = function
  | HS.List [HS.Atom v1; HS.Atom v2] ->
    HString.string_of_hstring v1, HString.string_of_hstring v2
  | s ->
    Format.eprintf "CALL MAP %a@." HS.pp_print_sexpr s;
    failwith "Invalid state variable map in caller"

let state_var_map_of_smap m =
  List.fold_left (fun acc (v1, v2) ->
      try
        let sv1, sv2 = StateVar.state_var_of_long_string v1,
                       StateVar.state_var_of_long_string v2 in
        StateVar.StateVarMap.add sv1 sv2 acc
      with Not_found -> failwith "Invalid state variable map in caller"
    ) StateVar.StateVarMap.empty m


let state_var_of_atom = function
  | HS.Atom v ->
    StateVar.state_var_of_long_string (HString.string_of_hstring v)
  | _ -> failwith "Not a state var"

let subsystems_of_sexpr = function
  | HS.List 
      [HS.Atom c;
       HS.List m;
       HS.List [HS.Atom f;
                HS.List [HS.List [HS.Atom v; ty]];
                HS.List [g]]] 
    when f == s_lambda ->
    (* Get name of caller *)
    let name = c in
    (* Get variable map *)
    let m =  List.map sbind_of_sexpr m in
    let map_down = state_var_map_of_smap m in
    let map_up = state_var_map_of_smap (List.map (fun (x,y) -> y,x) m) in

    (* Get guard of boolean function *)
    (* Get list of variables of fun *)
    let tyv = type_of_sexpr ty in

    let v = Var.mk_free_var v tyv in
    let bvars = [Var.hstring_of_free_var v, v] in
    let body = term_of_sexpr_bound_vars bvars g in
    let guard_lambda = Term.mk_lambda [v] body in
    let guard_clock =
      if Term.is_lambda_identity guard_lambda then
        (* Simply return the identity (on terms) function if the guard
           is lambda x.x *)
        (fun _ t -> t)
      else (fun i t ->
          Term.bump_state i (* KLUDGE we should just bump the clock *)
            (Term.eval_lambda guard_lambda [t]))
    in

    let subsys =
      try HH.find seen_systems name
      with Not_found ->
        failwith (Format.sprintf "Undefined subsystem %s"
                    (HString.string_of_hstring name))
    in

    let inst = { TransSys.pos = Lib.dummy_pos; map_down; map_up; guard_clock} in

    (* assemble subsystem *)
    subsys, inst
    
  | s ->
    Format.eprintf "SUBSYSTEM %a@." HS.pp_print_sexpr s;
    failwith "Invalid subsystem description"
    


let file_row_col_of_string s =
  Scanf.sscanf s "%s@:%d-%d" (fun x1 x2 x3-> x1, x2, x3)

let prop_source_of_sexpr prop_term = function
  | [] -> Property.PropAnnot Lib.dummy_pos

  | [HS.Atom c; HS.Atom pos]
    when c == s_annot || c == s_contract ->
    let frc_pos = file_row_col_of_string (HString.string_of_hstring pos) in
    let ppos = Lib.pos_of_file_row_col frc_pos in
    if c == s_annot then Property.PropAnnot ppos
    else assert false

  | [HS.Atom c; HS.List svs] when c == s_gen ->
    let vars = List.map state_var_of_atom svs in
    Property.Generated vars

  | [HS.Atom c; HS.Atom scopedprop] ->
    let p, scope =
      Lib.extract_scope_name (HString.string_of_hstring scopedprop) in
    if c == s_inst then
      let rec prop = {Property.prop_name = p; prop_source = source;
                  prop_term; prop_status = Property.PropUnknown }
      and source = Property.Instantiated (scope, prop) in
      source
    else assert false

  | [HS.Atom c; HS.Atom pos; HS.Atom scopedprop] ->

    let frc_pos = file_row_col_of_string (HString.string_of_hstring pos) in
    let ppos = Lib.pos_of_file_row_col frc_pos in
    let p, scope =
      Lib.extract_scope_name (HString.string_of_hstring scopedprop) in
    if c == s_assumption then Property.Assumption (ppos, scope)
    else if c == s_guarantee then Property.Guarantee (ppos, scope)
    else if c = s_guaranteeonemodeactive then
      Property.GuaranteeOneModeActive (ppos, scope)
    else if c == s_guaranteemodeimplication then
      Property.GuaranteeModeImplication (ppos, scope)
    else assert false

  | [HS.Atom c] when c == s_cand -> Property.Candidate None

  | _ -> failwith "Invalid property source"


let prop_of_sexpr = function
  | HS.List (HS.Atom n :: p :: source) ->
    let prop_term = term_of_sexpr p in
    { Property.prop_name = HString.string_of_hstring n;
      prop_source = prop_source_of_sexpr prop_term source;
      prop_term;
      prop_status = Property.PropUnknown }
  | _ -> failwith "Invalid property"


module TM = Map.Make(struct
    type t = TransSys.t
    let compare = TransSys.compare_scope
  end)

let merge_subsystem_insts subs =
  List.fold_left (fun acc (s, inst) ->
      let other_insts = try TM.find s acc with Not_found -> [] in
      TM.add s (inst :: other_insts) acc
    ) TM.empty subs
  |> TM.bindings

let rec optional_fields_of_sexprs (subsystems, props) = function
  (* Subsystems *)
  | HS.List (HS.Atom s :: subs_l) :: rs
    when s == s_subsystems ->
    let subsystems = List.map subsystems_of_sexpr subs_l
                     |> merge_subsystem_insts in
    optional_fields_of_sexprs (subsystems, props) rs

  (* Propeties *)
  | HS.List [HS.Atom p; HS.List ps] :: rs
    when p == s_props ->
    let props = List.map prop_of_sexpr ps in 
    optional_fields_of_sexprs (subsystems, props) rs

  | [] -> (subsystems, props)

  | _ -> failwith "Invalid field in node"




(* Convert a predicate definition *)
let node_def_of_sexpr = function

  (* (define-node NAME (VARS) (init INIT) (trans TRANS) (callers CALLERS))?
     (props PROPS)? *)
  | HS.List 
      (HS.Atom c :: 
       HS.Atom n ::
       HS.List v ::
       HS.List [HS.Atom ci; i] ::
       HS.List [HS.Atom ct; t] ::
       others
      ) 
    when c == s_define_node &&
         ci == s_init &&
         ct = s_trans ->

    (* Get name of defined predicate *)
    let node_name = n in

    (* Create state variables *)
    let state_vars_b = List.map state_var_of_sexpr v in
    let state_vars = List.map fst state_vars_b in
    let init_flag = match List.filter snd state_vars_b with
      | [init_flag, _] -> init_flag
      | _ ->
        (* there may be no init flag (for jkind systems), we make one up *)
        StateVar.mk_init_flag [HString.string_of_hstring node_name]
        (* failwith "No init flag in native definition" *)
    in

    (* Arguments of initial state predicate *)
    let init_args = init_args_of_state_vars state_vars in
    
    (* Arguments of transition relation predicate *)
    let trans_args = trans_args_of_state_vars state_vars in
    
    (* Types of initial state predicate arguments *)
    let init_args_types = List.map Var.type_of_var init_args in

    (* Types of transition relation predicate arguments *)
    let trans_args_types = List.map Var.type_of_var trans_args in

    (* Predicate symbol for initial state predicate *)
    let init_uf_symbol = 
      UfSymbol.mk_uf_symbol
        (init_pred_hname node_name) 
        init_args_types
        Type.t_bool 
    in

    (* Predicate symbol for transition relation predicate *)
    let trans_uf_symbol = 
      UfSymbol.mk_uf_symbol
        (trans_pred_hname node_name) 
        trans_args_types
        Type.t_bool 
    in
    
    (* Initial state constraint *)
    let init_term = term_of_sexpr i in

    (* Transition relation *)
    let trans_term = term_of_sexpr t in

    (* Optional callers and properties *)
    let subsystems, props = optional_fields_of_sexprs ([], []) others in
    
    (* Intermediate representation of node/system *)
    (
      node_name,
      init_flag,
      state_vars,
      (init_uf_symbol, (init_args, init_term)), 
      (trans_uf_symbol, (trans_args, trans_term)),
      subsystems,
      props
    )

  | HS.Atom _ 
  | HS.List _ -> failwith "Invalid format of node definition"




let rec mk_subsys_structure sys =
  { SubSystem.scope = TransSys.scope_of_trans_sys sys;
    source = sys;
    has_contract = false;
    has_impl = true;
    has_modes = false;
    subsystems =
      TransSys.get_subsystems sys
      |> List.map mk_subsys_structure;
  }


(* Parse from input channel *)
let of_channel in_ch = 

  let lexbuf = Lexing.from_channel in_ch in
  let sexps = SExprParser.sexps SExprLexer.main lexbuf in

  (* Callers mapping to transition system *)
  (* let calling_table = HH.create (List.length sexps) in *)

  (* Parse sexps *)
  let systems =
    List.map (fun sexp ->

        let node_name, init_flag, state_vars,
            (init_uf_symbol, (init_args, init_term)), 
            (trans_uf_symbol, (trans_args, trans_term)),
            subsystems, props =
          node_def_of_sexpr sexp in

        (* Scope from name *)
        let node_scope =
          let n, s =
            Lib.extract_scope_name (HString.string_of_hstring node_name) in
          s @ [n] in

        (* find who I call *)
        (* let i_call = *)
        (*   try *)
        (*     HH.find calling_table node_name *)
        (*     |> snd *)
        (*     |> List.map (fun (a,_,_) -> a) *)
        (*   with Not_found -> [] *)
        (* in *)

        
        (* Create transition system *)
        let sys, _ = TransSys.mk_trans_sys
            node_scope
            None
            init_flag
            []
            state_vars
            (StateVar.StateVarHashtbl.create 7)
            []
            [] (* ufs *)
            init_uf_symbol
            init_args
            init_term
            trans_uf_symbol
            trans_args
            trans_term
            subsystems
            props
            (None, []) (Invs.empty ()) Term.TermMap.empty in

        (* Add calling information *)
        (* List.iter (fun (c, m, g) -> *)
        (*     let n, calling_c = *)
        (*       try HH.find calling_table c *)
        (*       with Not_found -> None, [] *)
        (*     in *)
        (*     HH.replace calling_table c (n, (sys, m, g) :: calling_c); *)
        (*   ) callers; *)

        (* (\* Register new system *\) *)
        (* let calling_me = *)
        (*   try snd (HH.find calling_table node_name) *)
        (*   with Not_found -> [] in *)
        (* HH.replace calling_table node_name (Some sys, calling_me);         *)

        HH.add seen_systems node_name sys;
        
        (* Return constructed system  *)
        sys (* , callers *)

      ) sexps
  in


  (* Format.eprintf "CALLING TABLE:@."; *)
  (* HH.iter (fun c (n, calls) -> *)
  (*     Format.eprintf "%s " (HString.string_of_hstring c); *)
  (*     (match n with *)
  (*      | None -> Format.eprintf "(None)" *)
  (*      | Some s -> Format.eprintf "(%s)" *)
  (*                    (String.concat "." (TransSys.get_scope s))); *)
  (*     Format.eprintf  " -> ["; *)
  (*     List.iter (fun (sys, _, _) -> *)
  (*         Format.eprintf "%s," *)
  (*           (String.concat "." (TransSys.get_scope sys)) *)
  (*       ) calls; *)
  (*     Format.eprintf  "]@."; *)
  (*   ) calling_table; *)

  
  (* Add callers *)
  (* let all_sys = *)
  (*   List.fold_left (fun acc (sys, callers) -> *)
  (*       (\* Add callers *\) *)
  (*       List.fold_left (fun (c, m, (vars, g)) -> *)
  (*           let c_sys = match fst (HH.find calling_table c) with *)
  (*             | None -> assert false *)
  (*             | Some s -> s in *)

  (*           (\* Construct state var map *\) *)
  (*           let map = state_var_map_of_smap m in *)

  (*           (\* Construct lambda for guard now that all symbols are declared *\) *)
  (*           let bvars = List.map (fun v -> Var.hstring_of_free_var v, v) vars in *)
  (*           let guard_lambda = *)
  (*             Term.mk_lambda vars (term_of_sexpr_bound_vars bvars g) in *)
  (*           let guard_fun = *)
  (*             if Term.is_lambda_identity guard_lambda then *)
  (*               (\* Simply return the identity (on terms) function if the guard *)
  (*                  is lambda x.x *\) *)
  (*               (fun t -> t) *)
  (*             else (fun t -> Term.eval_lambda guard_lambda [t]) *)
  (*           in *)

  (*           TransSys.add_caller sys c_sys (map, guard_fun) *)
  (*         ) callers; *)
  (*       sys :: acc *)
  (*     ) [] sys_and_calls *)
  (* in *)

  (* Return top level system *)
  match List.rev systems with
  | top_sys :: _ ->

    Debug.native "%a" TransSys.pp_print_trans_sys top_sys ;

    mk_subsys_structure top_sys
      
  | _ -> failwith "No systems"



(* Open and parse from file *)
let of_file filename = 

    (* Open the given file for reading *)
    let use_file = open_in filename in
    let in_ch = use_file in

    of_channel in_ch



(************************************************************************)
(* Printing of transition systems to the compatible native input format *)
(************************************************************************)


let pp_print_var ppf v =
  if Var.is_state_var_instance v then
    let sv = Var.state_var_of_state_var_instance v in
    let n = Var.offset_of_state_var_instance v |> Numeral.to_int in

    let rec add_primes ppf = function
      | 0 -> StateVar.pp_print_state_var ppf sv
      | n when n > 0 ->
        Format.fprintf ppf "(prime %a)" add_primes (n-1)
      | _ -> assert false
    in

    add_primes ppf n
  else Var.pp_print_var ppf v

let pp_print_term ppf =
  Term.T.pp_print_term_w (fun ?arity -> Symbol.pp_print_symbol)
    pp_print_var Type.pp_print_type ppf

let pp_print_lambda ppf =
  Term.T.pp_print_lambda_w (fun ?arity -> Symbol.pp_print_symbol)
    pp_print_var Type.pp_print_type ppf


let pp_print_state_var sys ppf state_var = 
  Format.fprintf ppf
    "@[<hv 1>(%a@ %a%t%t%t%t)@]" 
    StateVar.pp_print_state_var state_var
    Type.pp_print_type (StateVar.type_of_state_var state_var)
    (fun ppf -> 
       if StateVar.is_const state_var
       then Format.fprintf ppf "@ :const")
    (fun ppf -> 
       if StateVar.is_input state_var
       then Format.fprintf ppf "@ :input")
    (fun ppf -> 
       if StateVar.for_inv_gen state_var
       then Format.fprintf ppf "@ :for-inv-gen")
    (fun ppf -> 
       if StateVar.equal_state_vars state_var (TransSys.init_flag_state_var sys)
       then Format.fprintf ppf "@ :init-flag")

let pp_pos ppf pos =
  let f,r,c = file_row_col_of_pos pos in
  Format.fprintf ppf "%s:%d-%d" f r c
  

let pp_print_prop_source sys ppf = function 
  | Property.PropAnnot pos -> Format.fprintf ppf ":user@ %a" pp_pos pos
  | Property.Generated state_vars ->
    Format.fprintf ppf ":generated@ (@[<v>%a@])"
    (pp_print_list (pp_print_state_var sys) "@ ") state_vars  
  | Property.Instantiated (scope, prop) ->
    let name = prop.Property.prop_name in
    Format.fprintf ppf ":subsystem@ %s" (String.concat "." (scope @ [name]))
  | Property.Candidate _ ->
    Format.fprintf ppf ":candidate"
  | _ -> () (* TODO *)


let pp_print_property sys ppf {Property.prop_name; prop_source; prop_term} = 
  Format.fprintf 
    ppf
    "@[<hv 1>(%s@ %a@ %a)@]"
    prop_name
    pp_print_term prop_term
    (pp_print_prop_source sys) prop_source


let fresh_statevar =
  let cpt = ref 0 in
  fun ty ->
    let s = "__v"^(string_of_int !cpt) in
    incr cpt;
    StateVar.mk_state_var s [] ty
      

let pp_print_subsystem name_c ppf {TransSys.map_down; guard_clock} =
  Format.fprintf ppf 
    "(%s@ @[<hv 1>(%a)@,@[<v>%a@]@])"
    name_c
    (pp_print_list 
       (fun ppf (s, t) ->
          Format.fprintf ppf
            "@[<hv 1>(@[<hv>%a@]@ @[<hv>%a@])@]"
            StateVar.pp_print_state_var s
            StateVar.pp_print_state_var t)
       "@ ")
    (StateVar.StateVarMap.bindings map_down)
    pp_print_lambda
    (let sv = fresh_statevar Type.t_bool in
     let v = Var.mk_state_var_instance sv Numeral.zero in
     let tv = Term.mk_var v in
     Term.mk_lambda [v] (guard_clock Numeral.zero tv))


let pp_print_subsystems ppf (t, inst) =
  let name_s = String.concat "." (TransSys.scope_of_trans_sys t) in
  Format.fprintf ppf
    "@[<hv 1>%a@]"
    (pp_print_list (pp_print_subsystem name_s) "@ ") inst


let pp_print_props ppf sys =
  let props = (* TransSys.get_real_properties *)
    (TransSys.get_properties sys) @ (TransSys.get_candidate_properties sys)
  in
  if props <> [] then
  Format.fprintf ppf
     "@[<hv 2>(props@ (@[<v>%a@]))@]\n@,"
     (pp_print_list (pp_print_property sys) "@ ") props
     

let pp_print_subsystems ppf sys =
  let subs = TransSys.get_subsystem_instances sys in
  if subs <> [] then
  Format.fprintf ppf
     "@[<hv 2>(subsystems@ @[<v>%a@])@]\n@,"
     (pp_print_list pp_print_subsystems "@ ") subs
     

let eq_sys s1 s2 =
  TransSys.equal_scope s1 s2 &&
  List.for_all2 StateVar.equal_state_vars
    (TransSys.state_vars s1) (TransSys.state_vars s2) &&
  Term.equal
    (TransSys.init_of_bound None s1 Numeral.zero)
    (TransSys.init_of_bound None s2 Numeral.zero) &&
  Term.equal
    (TransSys.trans_of_bound None s1 Numeral.zero)
    (TransSys.trans_of_bound None s2 Numeral.zero)

let all_systems sys =
  let rec all_systems_rec acc sys =
    let acc = List.fold_left all_systems_rec acc (TransSys.get_subsystems sys) in
    let acc = if List.exists (eq_sys sys) acc then acc
      else sys :: acc in
    acc
  in
  all_systems_rec [] sys |> List.rev

let pp_print_one_native ppf sys = 
  
  Format.fprintf 
    ppf
    "@[<v>(define-node %s@,\
     @[<v 2>@[<hv 2>(@[<v>%a@])@]\n@,\
     @[<hv 2>(init@ @[<v>%a@])@]\n@,\
     @[<hv 2>(trans@ @[<v>%a@])@]\n@,\
     %a\
     %a\
     @]\
     )@]\
     \n@."
    (String.concat "." (TransSys.scope_of_trans_sys sys))
    (pp_print_list (pp_print_state_var sys) "@ ") (TransSys.state_vars sys)
    pp_print_term (TransSys.init_of_bound None sys TransSys.init_base)
    pp_print_term (TransSys.trans_of_bound None sys TransSys.trans_base)
    pp_print_subsystems sys
    pp_print_props sys


let pp_print_native ppf sys = 
  List.iter (pp_print_one_native ppf) (all_systems sys)

let dump_native_to sys filename =
  let dump_oc = open_out filename in
  let fmt = Format.formatter_of_out_channel dump_oc in
  pp_print_native fmt sys

  

let dump_native sys =
  let dirname = Flags.output_dir () in
  create_dir dirname;
  let filename =
    Filename.concat
      dirname
      (Format.sprintf "%s.kind2" 
         (Filename.basename (Flags.input_file ()))
      )
  in
  dump_native_to sys filename


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
