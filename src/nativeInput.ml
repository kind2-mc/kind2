(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

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

module HH = HString.HStringHashtbl
module HS = HStringSExpr
module D = GenericSMTLIBDriver

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
let s_lambda = HString.mk_hstring "lambda"
let s_opt_const = HString.mk_hstring ":const"
let s_opt_input = HString.mk_hstring ":input"
let s_opt_for_inv_gen = HString.mk_hstring ":for-inv-gen"
let s_annot = HString.mk_hstring ":user"
let s_contract = HString.mk_hstring ":contract"
let s_gen = HString.mk_hstring ":generated"
let s_inst = HString.mk_hstring ":subsystem"
let s_cand = HString.mk_hstring ":candidate"
let s_props = HString.mk_hstring "props"
let s_intrange = HString.mk_hstring "IntRange"


(*********************************************)
(* Parsing of systems in native input format *)
(*********************************************)

(* Return the name of the initial state constraint predicate *)
let init_pred_hname pred =
  Format.sprintf "%s_%s" LustreIdent.init_uf_string
    (HString.string_of_hstring pred)

(* Return the name of the transition relation predicate *)
let trans_pred_hname pred =
  Format.sprintf "%s_%s" LustreIdent.trans_uf_string
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
    let is_const, is_input, for_inv_gen  = 
      List.fold_left 

        (* Parse input and modify options *)
        (fun (is_const, is_input, for_inv_gen) -> function 
           | HS.Atom c when c == s_opt_const ->
             (true, is_input, for_inv_gen)
           | HS.Atom c when c == s_opt_input ->
             (is_const, true, for_inv_gen)
           | HS.Atom c when c == s_opt_for_inv_gen ->
             (is_const, is_input, true)
           | _ -> failwith "Invalid option for state variable")

        (* Defaults for the options *)
        (false, false, false)

        opts
    in

    (* Create state variable and return *)
    StateVar.mk_state_var ~is_input ~is_const ~for_inv_gen
      var_name scope var_type

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
  let at1 = List.map (Var.bump_offset_of_state_var_instance Numeral.one) at0 in
  let at0 = List.filter (fun v -> not (Var.is_const_state_var v)) at0 in
  at1 @ at0



let sbind_of_sexpr = function
  | HS.List [HS.Atom v1; HS.Atom v2] ->
    HString.string_of_hstring v1, HString.string_of_hstring v2
  | s ->
    Format.eprintf "CALL MAP %a@." HS.pp_print_sexpr s;
    failwith "Invalid state variable map in caller"

let state_var_map_of_smap =
  List.map (fun (v1, v2) ->
      try
        StateVar.state_var_of_long_string v1,
        StateVar.state_var_of_long_string v2
      with Not_found -> failwith "Invalid state variable map in caller"
    )


let state_var_of_atom = function
  | HS.Atom v ->
    StateVar.state_var_of_long_string (HString.string_of_hstring v)
  | _ -> failwith "Not a state var"

let caller_of_sexpr = function
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
    let map = List.map sbind_of_sexpr m in
    (* Get guard of boolean function *)
    (* Get list of variables of fun *)
    let tyv = type_of_sexpr ty in
    let vars = [Var.mk_free_var v tyv] in
    (* Assemble caller *)
    name, map, (vars, g)

  | s ->
    Format.eprintf "CALLER %a@." HS.pp_print_sexpr s;
    failwith "Invalid caller description"
    



let file_row_col_of_string s =
  Scanf.sscanf s "%s@:%d-%d" (fun x1 x2 x3-> x1, x2, x3)

let prop_source_of_sexpr = function
  | [] -> TermLib.PropAnnot Lib.dummy_pos

  | [HS.Atom c; HS.Atom pos]
    when c == s_annot || c == s_contract ->
    let frc_pos = file_row_col_of_string (HString.string_of_hstring pos) in
    let ppos = Lib.pos_of_file_row_col frc_pos in
    if c == s_annot then TermLib.PropAnnot ppos
    else if c == s_contract then TermLib.Contract ppos
    else assert false

  | [HS.Atom c; HS.List svs] when c == s_gen ->
    let vars = List.map state_var_of_atom svs in
    TermLib.Generated vars

  | [HS.Atom c; HS.Atom scopedprop] when c == s_inst ->
    let p, scope =
      Lib.extract_scope_name (HString.string_of_hstring scopedprop) in
    TermLib.Instantiated (scope, p)

  | [HS.Atom c] when c == s_cand -> TermLib.Candidate

  | _ -> failwith "Invalid property source"


let prop_of_sexpr = function
  | HS.List (HS.Atom n :: p :: source) ->
    (HString.string_of_hstring n,
     prop_source_of_sexpr source,
     term_of_sexpr p)
  | _ -> failwith "Invalid property"


let rec optional_fields_of_sexprs (callers, props) = function
  (* Callers *)
  | HS.List (HS.Atom ca :: ca_l) :: rs
    when ca = s_callers ->
    let callers = List.map caller_of_sexpr ca_l in
    optional_fields_of_sexprs (callers, props) rs

  (* Propeties *)
  | HS.List [HS.Atom p; HS.List ps] :: rs
    when p = s_props ->
    let props = List.map prop_of_sexpr ps in 
    optional_fields_of_sexprs (callers, props) rs

  | [] -> (callers, props)

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
    let state_vars = List.map state_var_of_sexpr v in

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
    let callers, props = optional_fields_of_sexprs ([], []) others in
    
    (* Intermediate representation of node/system *)
    (
      node_name,
      state_vars,
      (init_uf_symbol, (init_args, init_term)), 
      (trans_uf_symbol, (trans_args, trans_term)),
      callers,
      props
    )

  | HS.Atom _ 
  | HS.List _ -> failwith "Invalid format of node definition"






(* Parse from input channel *)
let of_channel in_ch = 

  let lexbuf = Lexing.from_channel in_ch in
  let sexps = SExprParser.sexps SExprLexer.main lexbuf in

  (* Callers mapping to transition system *)
  let calling_table = HH.create (List.length sexps) in

  (* Parse sexps and register callers *)
  let sys_and_calls =
    List.map (fun sexp ->

        let node_name, state_vars, init_pred, trans_pred, callers, props =
          node_def_of_sexpr sexp in

        (* Scope from name *)
        let node_scope =
          let n, s =
            Lib.extract_scope_name (HString.string_of_hstring node_name) in
          s @ [n] in

        (* find who I call *)
        let i_call =
          try
            HH.find calling_table node_name
            |> snd
            |> List.map (fun (a,_,_) -> a)
          with Not_found -> []
        in

        (* Create transition system *)
        let sys = TransSys.mk_trans_sys
            node_scope state_vars init_pred trans_pred i_call props
            TransSys.Native in

        (* Add calling information *)
        List.iter (fun (c, m, g) ->
            let n, calling_c =
              try HH.find calling_table c
              with Not_found -> None, []
            in
            HH.replace calling_table c (n, (sys, m, g) :: calling_c);
          ) callers;

        (* Register new system *)
        let calling_me =
          try snd (HH.find calling_table node_name)
          with Not_found -> [] in
        HH.replace calling_table node_name (Some sys, calling_me);        
        
        (* Return constructed system and callers *)
        sys, callers

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
  let all_sys =
    List.fold_left (fun acc (sys, callers) ->
        (* Add callers *)
        List.iter (fun (c, m, (vars, g)) ->
            let c_sys = match fst (HH.find calling_table c) with
              | None -> assert false
              | Some s -> s in

            (* Construct state var map *)
            let map = state_var_map_of_smap m in

            (* Construct lambda for guard now that all symbols are declared *)
            let bvars = List.map (fun v -> Var.hstring_of_free_var v, v) vars in
            let guard_lambda =
              Term.mk_lambda vars (term_of_sexpr_bound_vars bvars g) in
            let guard_fun =
              if Term.is_lambda_identity guard_lambda then
                (* Simply return the identity (on terms) function if the guard
                   is lambda x.x *)
                (fun t -> t)
              else (fun t -> Term.eval_lambda guard_lambda [t])
            in

            TransSys.add_caller sys c_sys (map, guard_fun)
          ) callers;
        sys :: acc
      ) [] sys_and_calls
  in

  (* Return top level system *)
  match all_sys with
  | top_sys :: _ ->

    debug nativeInput
      "%a"
      TransSys.pp_print_trans_sys top_sys
    in

    top_sys
      
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
    pp_print_var ppf

let pp_print_lambda ppf =
  Term.T.pp_print_lambda_w (fun ?arity -> Symbol.pp_print_symbol)
    pp_print_var ppf


let pp_print_state_var ppf state_var = 
  Format.fprintf ppf
    "@[<hv 1>(%a@ %a%t%t%t)@]" 
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

let pp_pos ppf pos =
  let f,r,c = file_row_col_of_pos pos in
  Format.fprintf ppf "%s:%d-%d" f r c
  

let pp_print_prop_source ppf = function 
  | TermLib.PropAnnot pos -> Format.fprintf ppf ":user@ %a" pp_pos pos
  | TermLib.Contract pos -> Format.fprintf ppf ":contract@ %a" pp_pos pos
  | TermLib.Generated state_vars ->
    Format.fprintf ppf ":generated@ (@[<v>%a@])"
    (pp_print_list pp_print_state_var "@ ") state_vars  
  | TermLib.Instantiated (scope, name) ->
    Format.fprintf ppf ":subsystem@ %s" (String.concat "." (scope @ [name]))
  | TermLib.Candidate ->
    Format.fprintf ppf ":candidate"


let pp_print_property ppf (prop_name, prop_source, prop_term, _) = 
  Format.fprintf 
    ppf
    "@[<hv 1>(%s@ %a@ %a)@]"
    prop_name
    pp_print_term prop_term
    pp_print_prop_source prop_source


let pp_print_caller name_c ppf (m, ft) =
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
    m
    pp_print_lambda
    (let v = Var.mk_fresh_var Type.t_bool in
     let tv = Term.mk_var v in
     Term.mk_lambda [v] (ft tv))


let pp_print_callers ppf (t, c) =
  let name_c = String.concat "." (TransSys.get_scope t) in
  Format.fprintf ppf
    "@[<hv 1>%a@]"
    (pp_print_list (pp_print_caller name_c) "@ ") c


let pp_print_props ppf sys =
  let props = TransSys.get_properties sys in
  if props <> [] then
  Format.fprintf ppf
     "@[<hv 2>(props@ (@[<v>%a@]))@]\n@,"
     (pp_print_list pp_print_property "@ ") props
     

let pp_print_callers ppf sys =
  let callers = TransSys.get_callers sys in
  if callers <> [] then
  Format.fprintf ppf
     "@[<hv 2>(callers@ @[<v>%a@])@]\n@,"
     (pp_print_list pp_print_callers "@ ") callers
     

let eq_sys s1 s2 =
  TransSys.get_name s1 = TransSys.get_name s2 &&
  TransSys.get_scope s1 = TransSys.get_scope s2 &&
  List.for_all2 StateVar.equal_state_vars
    (TransSys.state_vars s1) (TransSys.state_vars s2) &&
  Term.equal (TransSys.init_term s1) (TransSys.init_term s2) &&
  Term.equal (TransSys.trans_term s1) (TransSys.trans_term s2)

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
    (String.concat "." (TransSys.get_scope sys))
    (pp_print_list pp_print_state_var "@ ") (TransSys.state_vars sys)
    pp_print_term (TransSys.init_term sys)
    pp_print_term (TransSys.trans_term sys)
    pp_print_callers sys
    pp_print_props sys


let pp_print_native ppf sys = 
  List.iter (pp_print_one_native ppf) (all_systems sys)

let dump_native_to sys filename =
  let dump_oc = open_out filename in
  let fmt = Format.formatter_of_out_channel dump_oc in
  pp_print_native fmt sys

  

let dump_native sys =
  let dirname = Flags.dump_dir () in
  create_dir dirname;
  let filename =
    Filename.concat
      dirname
      (Format.sprintf "%s.kind2" 
         (Filename.basename (Flags.input_file ()))
      )
  in
  dump_native_to sys filename

  
(* ************************************************************ *)
(* Counterexample output in plain text                          *)
(* ************************************************************ *)


let print_term_or_lambda fmt = function
  | Model.Term t -> Term.pp_print_term fmt t
  | Model.Lambda l -> Term.pp_print_lambda fmt l

(* Return width of widest identifier and widest value *)
let rec widths_of_model max_ident_width max_val_width = function 
  
  | [] -> (max_ident_width, max_val_width)

  | (state_var, values) :: tl -> 

    (* Maximal print width of state variable *)
    let max_ident_width' = 
      max
        max_ident_width
        (String.length 
           (string_of_t StateVar.pp_print_state_var state_var))
    in
    
    (* Maximal print width of values *)
    let max_val_width' =
      List.fold_left 
        (fun m v -> 
           max
             m
             (String.length
                (string_of_t print_term_or_lambda v)))
        max_val_width
        values
    in

    (* Return new maximum widths *)
    widths_of_model max_ident_width' max_val_width' tl

(* Pretty-print a value in a model *)
let pp_print_value_pt val_width ppf value = 

  Format.fprintf
    ppf
    "%-*s"
    val_width
    (string_of_t print_term_or_lambda value)

(* Pretty-print a state variable and its values *)
let pp_print_state_var_pt state_var_width val_width ppf (state_var, values) =

  Format.fprintf 
    ppf
    "@[<h>%-*s: %a@]"
    state_var_width
    (string_of_t StateVar.pp_print_state_var state_var)
    (pp_print_list
       (pp_print_value_pt val_width)
       " ")
    values

(* Pretty-print a model without the values for the Skolem variables. Because
   they are not original state variables, their values are generally not
   useful. *)
let pp_print_path_pt ppf model = 
  let state_var_width, val_width = widths_of_model 0 0 model in

  Format.fprintf
    ppf
    "@[<v>%a@]"
    (pp_print_list
       (pp_print_state_var_pt state_var_width val_width)
       "@,")
    model
       
(* ************************************************************ *)
(* Counterexample output in XML                                 *)
(* ************************************************************ *)

let pp_print_path_xml ppf model = () (* TODO *)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
