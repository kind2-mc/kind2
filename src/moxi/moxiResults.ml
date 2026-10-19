(* This file is part of the Kind 2 model checker.

   Copyright (c) 2025 by the Board of Trustees of the University of Iowa

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

module TS = TransSys
module SVM = StateVar.StateVarMap

(* A symbol in SMT-LIB syntax, quoted if needed *)
let quote = Lib.smtlib_symbol

let name_of_state_var sv = quote (StateVar.name_of_state_var sv)

(* The name of the model, trace, trail or certificate of a query *)
let derived prop_name suffix = quote (prop_name ^ suffix)


(* A sort in MoXI syntax *)
let rec pp_print_sort ppf ty =
  match Type.node_of_type ty with
  | Type.Enum _ -> Format.pp_print_string ppf (quote (Type.name_of_enum ty))
  | Type.Array (e, i) ->
    Format.fprintf ppf "(Array %a %a)" pp_print_sort i pp_print_sort e
  | _ -> Type.pp_print_type ppf ty

(* A value of a state variable of the given type, in MoXI syntax: the value
   of an enumeration sort, rather than the integer that stands for it, and
   the value of an array, a constant array with stores, in SMT-LIB syntax *)
let rec string_of_value ty value =
  if Type.is_enum ty then
    quote (Type.get_constr_of_num (Term.numeral_of_term value))
  else if Type.is_array ty then
    let index_ty = Type.index_type_of_array ty in
    let elem_ty = Type.elem_type_of_array ty in
    match Term.destruct value with
    | Term.T.App (sym, [a; i; v])
      when Symbol.node_of_symbol sym = `STORE ->
      Format.sprintf "(store %s %s %s)" (string_of_value ty a)
        (string_of_value index_ty i) (string_of_value elem_ty v)
    | Term.T.App (sym, [d]) when (match Symbol.node_of_symbol sym with
        | `CONST_ARRAY _ -> true | _ -> false) ->
      Format.asprintf "((as const %a) %s)" pp_print_sort ty
        (string_of_value elem_ty d)
    | _ -> Term.string_of_term value
  else Term.string_of_term value

(* A value of an array sort in MoXI syntax, given the elements at each list
   of indices, outermost first: a constant array of the most frequent
   element, with a store of each other one. MoXI arrays are indexed by
   bit-vectors. *)
let rec string_of_array ty elements =
  let elem_ty = Type.elem_type_of_array ty in
  let width = Type.bitvectorsize (Type.index_type_of_array ty) in
  (* The model reads the indices as signed integers *)
  let unsigned i = let n = 1 lsl width in ((i mod n) + n) mod n in
  let index i =
    Bitvector.num_to_ubv (Numeral.of_int width) (Numeral.of_int i)
    |> Term.mk_ubv |> Term.string_of_term
  in
  (* The value at each index of the outer array, in order *)
  let values =
    List.fold_left (fun acc (indices, t) ->
      match indices with
      | i :: inner ->
        let i = unsigned i in
        let others = try List.assoc i acc with Not_found -> [] in
        (i, (inner, t) :: others) :: List.remove_assoc i acc
      | [] -> assert false
    ) [] elements
    |> List.sort compare
    |> List.map (fun (i, inner) ->
      i,
      if Type.is_array elem_ty then string_of_array elem_ty (List.rev inner)
      else match inner with
        | [([], t)] -> string_of_value elem_ty t
        | _ -> assert false)
  in
  let count v = List.length (List.filter (fun (_, v') -> v' = v) values) in
  match values with
  | [] -> "_"
  | (_, first) :: _ ->
    let default =
      List.fold_left (fun best (_, v) -> if count v > count best then v else best)
        first values
    in
    List.fold_left (fun acc (i, v) ->
      if v = default then acc
      else Format.sprintf "(store %s %s %s)" acc (index i) v
    ) (Format.asprintf "((as const %a) %s)" pp_print_sort ty default) values

let join_maps (top_to_sys: StateVar.t SVM.t) (sys_to_subsys: StateVar.t SVM.t) = 
  List.fold_left (fun map (subsys_val, sys_val)  ->
    let top_val = StateVar.StateVarMap.find_opt sys_val top_to_sys in
    match top_val with 
    | None ->       StateVar.StateVarMap.add subsys_val sys_val map
    | Some value ->  StateVar.StateVarMap.add subsys_val value map 
) StateVar.StateVarMap.empty (SVM.bindings sys_to_subsys)

let get_state_var_vals_at_k ?(prefix="") trans_sys model_assoc_list k map = 
  let sys_vars = TransSys.state_vars trans_sys in
  (TransSys.state_vars trans_sys) |> List.filter_map (fun state_var -> 
    let state_var_opt = List.find_opt (fun v -> v == state_var) sys_vars in
    match state_var_opt with 
    | None -> None
    | Some sys_state_var when not (StateVar.for_inv_gen sys_state_var) -> None (* Filter out init flags *)
    (* The declared constants, which every system has, are in the model *)
    | Some sys_state_var when StateVar.is_const sys_state_var -> None
    (* May want to find a more robust way to filter out invar_props*)
    (* | _ when String.starts_with ~prefix: "invar_prop." (StateVar.name_of_state_var state_var) -> None Filter out invar_props *)
    | Some sys_state_var -> (
      let var_name = prefix ^ name_of_state_var sys_state_var in
      let translated_svar = StateVar.StateVarMap.find sys_state_var map in
      let svar_state_values = List.assoc translated_svar model_assoc_list in
      let svar_kth_state_value = List.nth svar_state_values (Numeral.to_int k) in 
      let state_value_changed = 
        (Numeral.to_int k) == 0 || 
        not (Model.equal_value (List.nth svar_state_values ((Numeral.to_int k) - 1)) 
                               svar_kth_state_value) 
      in
      match svar_kth_state_value with
      | Model.Term value ->
        let ty = StateVar.type_of_state_var sys_state_var in
        Some (var_name, string_of_value ty value, state_value_changed)
      | Model.Map _ ->
        Some (var_name, "[...]", true)
      | _ -> 
        failwith (Format.asprintf "Received unexpected model value. Unable to construct counterexample.")
    )
  )

let rec get_state_var_vals_at_k_all ?(map=None) ?(prefix="") trans_sys (model_assoc_list: (StateVar.t * Model.value list) list) k = 
  let sys_map = match map with 
    | None -> (* Create the identity map for the top trans system *)
      List.fold_left (fun map sys_state_var  ->
          StateVar.StateVarMap.add sys_state_var sys_state_var map
      ) StateVar.StateVarMap.empty (TransSys.state_vars trans_sys)
    | Some map -> 
      map
  in 
  
  let help k subsystems =
    List.map (fun (subsys_transys, TransSys.({ map_up; })) ->
      let map = Some (join_maps sys_map map_up) in
      let subsys_name = TransSys.scope_of_trans_sys subsys_transys |> Lib.string_of_t Scope.pp_print_scope_internal |> quote in
      let prefix = prefix ^ subsys_name ^ "::" in
      (get_state_var_vals_at_k_all ~map ~prefix subsys_transys model_assoc_list k)
    ) subsystems in

  let instances = 
    (TransSys.get_subsystem_instances trans_sys) |> 
    List.map (fun (subsys, subsys_instances) -> 
      (List.map (fun instance -> (subsys, instance)) subsys_instances)
    ) |> 
    List.flatten 
  in 

  (* For now, we remove the (non-reachability) variables in the check-system renamings. 
     This could reasonably change in the future.
  *)
  let trans_sys_state_vars = 
    if prefix = "" then [] else get_state_var_vals_at_k ~prefix trans_sys model_assoc_list k sys_map 
  in
  let subsys_state_vars = (help k instances) in
  List.flatten (trans_sys_state_vars :: subsys_state_vars)

let pp_print_str_var_val ppf (state_var, value, changed) =
  if changed then 
    Format.fprintf ppf "(%s %s) " state_var value   
  else 
    if false then (* TODO: Get flag for condensed output *)
      ()
    else
      Format.fprintf ppf "@{<black>(%s %s)@} " state_var value 



let pp_print_last_step_of_trace (trans_sys : TransSys.t) path ppf k =
  let reachability_prop = TransSys.get_properties trans_sys in
  let reachability_svars =
    List.map (fun Property.({prop_term}) ->
      StateVar.StateVarSet.elements (Term.state_vars_of_term prop_term)
    ) reachability_prop |> List.flatten in

  let model_list = Model.path_to_list path in
  let formatted_svar_names = get_state_var_vals_at_k_all trans_sys model_list k in
  let any_change =
    List.fold_left (fun change_detected (_, _, svar_changed) ->
      change_detected || svar_changed
    ) false formatted_svar_names
  in

  let reachability_var_names =
    List.map name_of_state_var reachability_svars
  in
  let formatted_svar_names = List.filter (fun (var, _, _) ->
    not (List.exists (String.equal var) reachability_var_names)
  ) formatted_svar_names in

  if any_change then
    Format.fprintf ppf "(%a %a)"
      Numeral.pp_print_numeral k
      (Lib.pp_print_list pp_print_str_var_val "") formatted_svar_names
  else
    if false then (* TODO: Get flag for condensed output *)
      ()
    else
      Format.fprintf ppf "@{<black>(%a %a)@}"
        Numeral.pp_print_numeral k
        (Lib.pp_print_list pp_print_str_var_val " ") formatted_svar_names

let pp_print_step_of_trace (trans_sys : TransSys.t) path ppf k = 
  let reachability_prop = TransSys.get_properties trans_sys in
  let reachability_svars = 
    List.map (fun Property.({prop_term}) -> 
      StateVar.StateVarSet.elements (Term.state_vars_of_term prop_term)
    ) reachability_prop |> List.flatten in
  
  (* Reachable svars may have duplicates if referenced in multiple queries. Filter them out.  *)
  let reachability_svars = 
    List.fold_left (fun rvars rvar -> 
      if (List.exists (StateVar.equal_state_vars rvar) rvars) 
      then rvars 
      else rvar :: rvars
    ) [] reachability_svars |> List.rev in

  let model_list = Model.path_to_list path in
  let values = List.map (fun reachability_svar -> 
    List.nth (List.assoc reachability_svar model_list) (Numeral.to_int k + 1)
  ) reachability_svars  in
  let reachability_values = List.map2 (fun value reachability_svar -> 
    if (Numeral.to_int k) == 0 then 
      (reachability_svar, value, true)
    else 
      reachability_svar, 
      value, 
      not (Model.equal_value value (List.nth (List.assoc reachability_svar model_list) ((Numeral.to_int k)) ))
    ) values reachability_svars
   in
  let reachability_change = List.fold_left (fun changed (_, _, change) -> 
    changed || change
  ) false reachability_values in
  let formatted_svar_names = get_state_var_vals_at_k_all trans_sys model_list k in
  let any_change = 
    reachability_change 
    ||
    List.fold_left (fun change_detected (_, _, svar_changed) -> 
      change_detected || svar_changed
    ) false formatted_svar_names
  in

  (* To check reachability, we were checking invariance of the negation of the reachability query. 
     When displaying the value of the reachability condition, we need to un-negate it. *)
  let reachability_values = List.map (fun (svar, value, changed) -> match value with 
    | Model.Term value -> 
      let negated_value = not (Term.bool_of_term value) in
      name_of_state_var svar, string_of_bool negated_value, changed
    | _ -> assert false 
  ) reachability_values in
  let reachability_var_names = List.map (fun (name, _, _) -> name) reachability_values in
  let formatted_svar_names = List.filter (fun (var, _, _) ->
    not (List.exists (String.equal var) reachability_var_names) 
  ) formatted_svar_names in

  if any_change then
    Format.fprintf ppf "(%a %a %a)" 
      Numeral.pp_print_numeral k 
      (Lib.pp_print_list pp_print_str_var_val "") formatted_svar_names
      (Lib.pp_print_list pp_print_str_var_val "") reachability_values
  else
    if false then (* TODO: Get flag for condensed output *)
      ()
    else
      Format.fprintf ppf "@{<black>(%a %a %a)@}" 
        Numeral.pp_print_numeral k 
        (Lib.pp_print_list pp_print_str_var_val " ") formatted_svar_names
        (Lib.pp_print_list pp_print_str_var_val "") reachability_values
    
let (--) i j = 
  let rec aux n acc =
    if n < i then acc else aux (n-1) ((Numeral.of_int n) :: acc)
  in aux j [] 

let pp_print_trail is_current_state trans_sys ppf path =
  let range = 0 -- (Model.path_length path - 2) in

  (match range with
  | [] -> ()
  | _ ->
    Format.fprintf ppf "%a@,"
      (Lib.pp_print_list (pp_print_step_of_trace trans_sys path) "@,") range );

  (* Only show the last state if it is not a property of the current state. *)
  if not is_current_state then
    (* In the last state, do not print value of reachability variables *)
    Format.fprintf ppf "%a@,"
      (pp_print_last_step_of_trace trans_sys path)
      (Numeral.of_int (Model.path_length path - 1))

let pp_print_cex_trail trans_sys prop_name prefix is_current_state ppf cex = 
  Format.fprintf ppf "@[<hv 2>:trail@ (%s (@[<v>@,%a@])@,) @]@,"
    (derived prop_name (if prefix then "_prefix" else "_lasso"))
    (pp_print_trail is_current_state trans_sys) (Model.path_of_list cex)

let pp_print_prop_trail trans_sys current_state_props ppf prop =
  let prop_name = prop.Property.prop_name in
  let is_current_state =
    List.mem prop_name current_state_props
  in
  match Property.get_prop_status prop with 
  | PropFalse cex -> 
    (pp_print_cex_trail trans_sys prop_name true is_current_state ppf cex)
  | PropInvariant _
  | PropKTrue _ 
  | PropUnknown -> () 

let pp_print_prop_trace _ prop = 
  let prop_name = prop.Property.prop_name in
  match Property.get_prop_status prop with
  | PropFalse _ -> 
    Format.printf "@[<hv 2>:trace@ (@[<v>%s :prefix %s@])@]@,"
      (derived prop_name "_trace")
      (derived prop_name "_prefix")
  | PropInvariant _
  | PropKTrue _ 
  | PropUnknown -> () 

(* The interpretation of the free symbols: the declared constants *)
let has_model trans_sys svar_path =
  List.exists (fun svar -> List.mem_assoc svar svar_path)
    (TransSys.global_const_state_vars trans_sys)

let pp_print_const_decl _ppf (svar, svar_value_path) =
  let svar_type = StateVar.type_of_state_var svar in
  (* These should be constant; assume that all values are the same *)
  let const_value = List.hd svar_value_path in

  match List.find_all (fun value -> 
    not (Model.equal_value value const_value)
  ) (List.tl svar_value_path) with
  | [] -> 
    let pp_print_value ppf = function
      | Model.Term t -> Format.pp_print_string ppf (string_of_value svar_type t)
      | Model.Map m ->
        Format.pp_print_string ppf
          (string_of_array svar_type (Model.MIL.bindings m))
      | v -> Model.pp_print_value ~as_type:svar_type ppf v
    in
    Format.printf "(define-fun %s () %a %a)"
      (name_of_state_var svar)
      pp_print_sort svar_type
      pp_print_value const_value
  
  | _ -> 
    failwith (Format.asprintf 
      "Recieved unexpected model value. Unable to construct counterexample.\n
       Variable %a should be constant but was assigned multiple values. %a"
      StateVar.pp_print_state_var svar 
      (Lib.pp_print_list Model.pp_print_value ", ") svar_value_path) 

let pp_print_const_decls: TransSys.t -> Format.formatter -> (StateVar.t * Model.value list) list -> unit 
= fun trans_sys _ppf svar_path -> 
  let const_svars = List.map (fun svar -> 
    svar, List.assoc svar svar_path
  ) (TransSys.global_const_state_vars trans_sys) in
  Format.printf "%a" (Lib.pp_print_list pp_print_const_decl "@,") const_svars

let pp_print_model trans_sys prop_name _ppf path =
  if has_model trans_sys path then 
    Format.printf "%s@,%a@," (derived prop_name "_model") (pp_print_const_decls trans_sys) path
  else 
    Format.printf "%s ()" (derived prop_name "_model")

let pp_print_prop_model: TransSys.t -> Format.formatter -> Property.t -> unit 
= fun trans_sys _ppf prop ->
  let prop_name = prop.Property.prop_name in
  match Property.get_prop_status prop with
  | PropFalse cex -> 
    Format.printf "@[<hv 2>:model@ (@[<v>%a@]@])@,"
      (pp_print_model trans_sys prop_name) cex
  | PropInvariant _
  | PropKTrue _ 
  | PropUnknown -> ()

(* The name of a variable of the system of a check in a certificate, as an
   SMT-LIB symbol, quoted if needed:
   - a variable of the check, by its name in the check;
   - a variable of a subsystem instance, by the path of the instances down
     to it, as in [C1::C::l]: the first instance, the call of the system of
     the check, is the check itself;
   - a declared constant, by its name;
   - a variable of kmoxi's own, such as the one a reachability condition is
     encoded by, by its name after an [@], with which SMT-LIB reserves
     symbols for solvers, so that it is the name of no variable of the
     model. *)
let cert_name_of_state_var sv =
  let name = StateVar.name_of_state_var sv in
  (* The scope of the variables of a system, rather than kmoxi's own *)
  let usr = List.hd LustreIdent.user_scope in
  match StateVar.scope_of_state_var sv with
  | _ when StateVar.is_const sv -> quote name
  | [ _ ; s ] when s = usr -> quote name
  | _ :: "ins" :: _ :: rest ->
    (* The instances, each after an "ins", and the scope of the variable in
       the last one *)
    let rec instances acc = function
      | "ins" :: instance :: rest -> instances (instance :: acc) rest
      | [ s ] when s = usr -> Some (List.rev acc)
      | _ -> None
    in
    (match instances [] rest with
     | Some path -> quote (String.concat "::" (path @ [ name ]))
     | None -> quote ("@" ^ String.concat "::" (List.tl rest @ [ name ])))
  | _ -> quote ("@" ^ name)

(* Print a term of an invariant in SMT-LIB syntax, over the names of
   [cert_name_of_state_var]: the value of an enumeration sort by its name,
   rather than the integer that stands for it, wherever it is compared with
   a term of the sort; a function defined with define-fun by its MoXI name;
   a divisibility constraint as [(_ divisible n)] *)
let rec pp_print_cert_term ?enum ppf t =
  match Term.destruct t with
  | Term.T.Var v ->
    Format.pp_print_string ppf
      (cert_name_of_state_var (Var.state_var_of_state_var_instance v))
  | Term.T.Const s -> (
    match Symbol.node_of_symbol s, enum with
    | `NUMERAL n, Some _ ->
      Format.pp_print_string ppf (quote (Type.get_constr_of_num n))
    | _ -> GenericSMTLIBDriver.pp_print_symbol ppf s )
  | Term.T.App (s, args) ->
    (* The enumeration sort of the arguments of an equation, or of the
       branches of an if-then-else, if one is of such a sort *)
    let enum_of args =
      List.find_map (fun a ->
        let ty = Term.type_of_term a in
        if Type.is_enum ty then Some ty else None) args
    in
    let pp_args ?enum ppf args =
      List.iter (fun a ->
        Format.fprintf ppf "@ %a" (pp_print_cert_term ?enum) a) args
    in
    (match Symbol.node_of_symbol s, args with
     | (`EQ | `DISTINCT), _ ->
       Format.fprintf ppf "@[<hv 1>(%a%a)@]"
         (GenericSMTLIBDriver.pp_print_symbol ~arity:(List.length args)) s
         (pp_args ?enum:(enum_of args)) args
     | `ITE, [c; t; e] ->
       let enum = match enum_of [t; e] with Some _ as e -> e | None -> enum in
       Format.fprintf ppf "@[<hv 1>(ite@ %a%a)@]"
         (pp_print_cert_term ?enum:None) c (pp_args ?enum) [t; e]
     | `DIVISIBLE n, _ ->
       Format.fprintf ppf "@[<hv 1>((_ divisible %a)%a)@]"
         Numeral.pp_print_numeral n (pp_args ?enum:None) args
     | `UF u, _ ->
       let name =
         match MoxiInput.moxi_name_of_uf u with
         | Some name -> quote name
         | None -> UfSymbol.smtlib_string_of_uf_symbol u
       in
       if args = [] then Format.pp_print_string ppf name
       else
         Format.fprintf ppf "@[<hv 1>(%s%a)@]" name (pp_args ?enum:None) args
     | _ ->
       Format.fprintf ppf "@[<hv 1>(%a%a)@]"
         (GenericSMTLIBDriver.pp_print_symbol ~arity:(List.length args)) s
         (pp_args ?enum:None) args)

(* The most cases an atom over variables of enumeration sorts is split into
   (see [split_enum_atoms]) *)
let max_enum_cases = 64

(* The invariant with every atom that uses a variable of an enumeration sort
   other than in an equation with its values written as a case split over
   the values of these variables. The engines take a value of an
   enumeration sort for the integer that encodes it, and an atom such as
   [2 - c >= 0] has no sort in MoXI: it is the disjunction of [(= c v)] for
   the values [v] it holds for, each with what the atom is for that value
   if it has other variables. An atom with more than [max_enum_cases] cases
   is left as it is. *)
let rec split_enum_atoms t =
  let enum_vars t =
    Term.vars_of_term t |> Var.VarSet.elements
    |> List.filter (fun v -> Type.is_enum (Var.type_of_var v))
  in
  (* A value, or a variable, of an enumeration sort *)
  let is_enum_value t =
    Term.is_numeral t ||
    match Term.destruct t with
    | Term.T.Var v -> Type.is_enum (Var.type_of_var v)
    | _ -> false
  in
  match Term.destruct t with
  (* Boolean structure *)
  | Term.T.App (s, args) when (match Symbol.node_of_symbol s with
      | `AND | `OR | `NOT | `IMPLIES | `XOR -> true
      | `ITE -> Type.is_bool (Term.type_of_term t)
      | `EQ -> List.for_all (fun a -> Type.is_bool (Term.type_of_term a)) args
      | _ -> false) ->
    Term.mk_app s (List.map split_enum_atoms args)
  (* An equation between values of an enumeration sort, printed as it is *)
  | Term.T.App (s, args)
    when (match Symbol.node_of_symbol s with
        | `EQ | `DISTINCT -> true | _ -> false)
      && List.for_all is_enum_value args
      && List.exists (fun a -> Type.is_enum (Term.type_of_term a)) args -> t
  | _ ->
    match enum_vars t with
    | [] -> t
    | vars ->
      let domains =
        List.map (fun v ->
          let l, u = Type.bounds_of_enum (Var.type_of_var v) in
          v, List.init (Numeral.to_int Numeral.(u - l) + 1)
               (fun i -> Numeral.(l + of_int i))) vars
      in
      let cases =
        List.fold_left (fun n (_, d) -> n * List.length d) 1 domains
      in
      if cases > max_enum_cases then t
      else
        (* Every assignment of values to the variables *)
        let rec assignments = function
          | [] -> [ [] ]
          | (v, d) :: rest ->
            let tails = assignments rest in
            List.concat_map (fun n -> List.map (fun a -> (v, n) :: a) tails) d
        in
        assignments domains
        |> List.filter_map (fun a ->
          let model =
            Model.of_list
              (List.map (fun (v, n) -> v, Model.Term (Term.mk_num n)) a)
          in
          let equations =
            List.map (fun (v, n) -> Term.mk_eq [ Term.mk_var v; Term.mk_num n ]) a
          in
          (* The atom for these values, with its other variables left as
             they are rather than given the defaults of their types *)
          let value =
            Simplify.simplify_term_model ~default_of_var:Term.mk_var [] model t
          in
          if Term.equal value Term.t_false then None
          else if Term.equal value Term.t_true then Some (Term.mk_and equations)
          else Some (Term.mk_and (equations @ [ value ])))
        |> (function [] -> Term.t_false | [ c ] -> c | cs -> Term.mk_or cs)

(* An invariant of a certificate. The invariants of certificates are of the
   current state, with no variable at another offset. *)
let pp_print_inv ppf inv = pp_print_cert_term ppf (split_enum_atoms inv)

let pp_print_prop_cert _ppf prop =
  let prop_name = prop.Property.prop_name in
  match Property.get_prop_status prop with
  | PropInvariant (k, inv) ->
    Format.printf "@[<hv 2>:certificate@ (@[<v>%s :inv %a :k %i@])@]@,"
      (derived prop_name "_cert")
      pp_print_inv
      inv
      k
  | PropFalse _ 
  | PropKTrue _
  | PropUnknown -> ()

let prop_result_info prop_name prop_result = match prop_result with 
| Property.PropFalse _ ->
  Format.sprintf ":model %s :trace %s"
    (derived prop_name "_model") (derived prop_name "_trace")
| PropInvariant _ ->
  Format.sprintf ":certificate %s" (derived prop_name "_cert")
| PropKTrue _
| PropUnknown -> ""

let pp_print_prop_result _ppf prop =
  let prop_name = prop.Property.prop_name in
  let prop_result = Property.get_prop_status prop in
  let result = match prop_result with
  | PropFalse _ -> "sat"
  | PropInvariant _ -> "unsat"
  | PropKTrue _ 
  | PropUnknown -> "unknown"
  in
  (* As in the format of responses of the MoXI paper (SPIN 2024, Fig. 2):
     [:query (q :result sat :model m :trace t)], and [:query (q :result
     unknown)] for an answer with no other attribute *)
  let info =
    match prop_result_info prop_name prop_result with
    | "" -> ""
    | info -> " " ^ info
  in
  Format.printf "@[<hv 2>:query@ @[<v>@[<hv 1>(%s@ :result %s%s)@]@]@]@,"
    (quote prop_name) result info

let pp_print_results: TransSys.t -> _ InputSystem.t -> Property.t list -> unit 
= fun trans_sys in_sys props ->
  let current_state_props =
    InputSystem.current_state_props in_sys (TS.scope_of_trans_sys trans_sys)
  in
  Format.printf
  "@[<v 1>(check-system-response @,\
   @[<hv 2>:verbosity@ %s@]@,\
    %a\
    %a\
    %a\
    %a\
    %a\
    )@]@.@."
  (if false then "condensed" else "full") (* TODO: Get flag for condensed output *)
  (Lib.pp_print_list pp_print_prop_result "") props
  (Lib.pp_print_list pp_print_prop_trace "") props
  (Lib.pp_print_list (pp_print_prop_model trans_sys) "") props
  (Lib.pp_print_list (pp_print_prop_trail trans_sys current_state_props) "") props
  (Lib.pp_print_list pp_print_prop_cert "") props
