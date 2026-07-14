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

module I = LustreIdent
module D = LustreIndex
module E = LustreExpr
module C = LustreContract
module N = LustreNode
module S = LustreSlicing
module G = LustreGlobals
module NI = NodeId

module A = Analysis
module P = Property

module SVS = StateVar.StateVarSet
module SVM = StateVar.StateVarMap
module TM = Type.TypeMap


type settings = {
  preserve_sig: bool;
  slice_nodes: Flags.slice_nodes;
  add_functional_constraints: bool;
  slice_to_prop: P.t option
}

let default_settings = {
  preserve_sig = false ;
  slice_nodes = Flags.slice_nodes () ;
  add_functional_constraints = true ;
  slice_to_prop = None
}

module NodeInstance = struct
  
  type t = NI.t * int NI.Map.t

  let equal (node_id1, num_unrollings1) (node_id2, num_unrollings2) =
    (NodeId.equal node_id1 node_id2) &&
    (NI.Map.equal Int.equal num_unrollings1 num_unrollings2)

  let compare (node_id1, num_unrollings1) (node_id2, num_unrollings2) =
    let cmp_id = NodeId.compare node_id1 node_id2 in
    if cmp_id <> 0 then cmp_id
    else NI.Map.compare Int.compare num_unrollings1 num_unrollings2

end

module NodeInstanceMap = Map.Make(NodeInstance)

(*
(* Hash map from node scopes to their index for fresh state variables.
   Used to make sure fresh state variables are indeed fresh after a restart,
   without risking to reach [MAXINT]. *)
let scope_index_map = ref Scope.Map.empty
(* Returns a fresh index for a scope. *)
let index_of_scope s =
  let curr =
    try !scope_index_map |> Scope.Map.find s with Not_found -> 0
  in
  scope_index_map := !scope_index_map |> Scope.Map.add s (curr + 1) ;
  curr
*)

let node_num_id = ref 0
let get_node_num_id () =
  let res = ! node_num_id in
  node_num_id := 1 + !node_num_id ;
  res

let get_rec_tag id = Format.asprintf "rec_%d" id

(* Transition system and information needed when calling it *)
type node_def = {

  (* Node the transition system was created from *)
  node : LustreNode.t;

  (* Initial state predicate *)
  init_uf_symbol : UfSymbol.t;

  (* Transition relation predicate *)
  trans_uf_symbol : UfSymbol.t;

  (* Transition system for node *)
  trans_sys : TransSys.t;

  (* Stateful local variables to be instantiated by the caller 

     Local variables of the callees of the node *)
  stateful_locals : StateVar.t list;

  (* Init flags to be set to true *)
  init_flags : StateVar.t list;

  (* Properties to be instantiated by the caller 

     Properties of the callees of the node *)
  properties : P.t list;

  history_svars: (StateVar.t list) SVM.t TM.t;

  ctr_svars: StateVar.t list ;

  definition_set : Term.TermSet.t;
  (* Terms which occur as part of a definition *)
}


(* ********************************************************************** *)
(* Instantiate in calling node                                            *)
(* ********************************************************************** *)

(* Instantiate state variable to the scope of a different node *)
let lift_state_var state_var_map state_var = 

  try 

    (* Find state variable in map *)
    SVM.find state_var state_var_map

  (* Fail, because we don't want a term with state variables of mixed
     scopes *)
  with Not_found -> 

    Format.printf "state_var_map: @[<v>%a@]@."
      (pp_print_list (fun fmt (k,b) ->
        Format.fprintf fmt "%a -> %a"
          StateVar.pp_print_state_var k
          StateVar.pp_print_state_var b)
        "@ "
      ) (SVM.bindings state_var_map) ;

    raise
      (Invalid_argument
         (Format.asprintf 
            "lift_term: state variable %a not found in map"
            StateVar.pp_print_state_var state_var))


(* Instantiate the variables of the term to the scope of a different
   node *)
let lift_term state_var_map term =

  Term.map

    (function _ -> function 

       (* Need to instantiate free variables *)
       | term when Term.is_free_var term -> 

         (* Get variable of term, this will not fail *)
         let var = Term.free_var_of_term term in

         (* Only if variable is an instance of a state variable *)
         if Var.is_state_var_instance var then 

           (* Get state variable of free variable *)
           let state_var = Var.state_var_of_state_var_instance var in

           (* Get offset of variable instance *) 
           let offset = Var.offset_of_state_var_instance var in

           (* Lift state variable to scope of calling node *)
           let state_var' = lift_state_var state_var_map state_var in


           (* Return state variable instance of the lifted state
              variable at the same offset *)
           Term.mk_var (Var.mk_state_var_instance state_var' offset)

         else

           (* No change if free variable is not an instance of a state
              variable *)
           term

       (* No change term that are not free variables *)
       | term -> term)

    term


(* Lift the name of a property in a subnode by adding the position of
   the node call *)
let lift_prop_name node_name pos prop_name =

  (* Pretty-print a position as attributes *)
  let pp_print_pos ppf pos = 

    (* Do not print anything for a dummy position *)
    if is_dummy_pos pos then () else 

      Lib.pp_print_line_and_column ppf pos

  in

  let node_name = string_of_t (LustreIdent.pp_print_ident true) node_name in

  string_of_t
    (fun ppf prop_name ->
       Format.fprintf
         ppf
         "%s%a%t%s"
         node_name
         pp_print_pos pos
         Lib.StringValues.pp_print_scope_sep
         prop_name)
    prop_name



(* ********************************************************************** *)
(* Properties of contracts                                                *)
(* ********************************************************************** *)

(* Create a property from Lustre expression *)
let property_of_expr
  ?(prop_kind=P.Invariant)
  candidate
  prop_name
  prop_status
  prop_source
  src_expr
  { E.expr_step; E.expr_init }
=

  (* Terms for initial state and step state must be equal. Otherwise
     we would need to abstract to a fresh variable. *)
  assert (E.equal_expr expr_step expr_init);

  (* Term of expresssion *)
  let prop_term = E.cur_term_of_expr TransSys.prop_base expr_step in

  let prop_source =
    if candidate then P.Candidate (Some prop_source) else prop_source
  in

  (* Return property *)
  { P.prop_name ; P.prop_source ; P.prop_term ; P.prop_status ; prop_kind ; P.prop_expr = src_expr}

(* Creates the conjunction of a list of contract svar. *)
let conj_of l = List.map (fun { C.svar } -> E.mk_var svar) l |> E.mk_and_n

(* Creates the term conjunction of a list of contract svar. *)
let term_conj_of l = List.map (
  fun { C.svar } ->
    Var.mk_state_var_instance svar Numeral.zero |> Term.mk_var
) l |> Term.mk_and

(* The assumption of the contract. *)
let assumption_of_contract { C.assumes } = conj_of assumes

(* The mode requirements of a contract, for test generation. *)
let ass_and_mode_requires_of_contract = function
| Some { C.assumes ; C.modes } -> (
    match assumes with
      | [] -> None
      | _ -> Some (term_conj_of assumes)
  ), modes |> List.map (
    fun { C.path ; C.requires } -> path, term_conj_of requires
  )
| None -> None, []


let non_vacuity_check scope name pos requires props =
  match requires with
  | { C.scope = s } :: _ ->
    let name =
      Format.asprintf "%a%s%a" (
        pp_print_list (
          fun fmt (pos, call) ->
            Format.fprintf fmt "%s%a%t"
              call Lib.pp_print_line_and_column pos Lib.StringValues.pp_print_scope_sep
        ) ""
      ) s name Lib.pp_print_line_and_column pos 
    in
    let guard = conj_of requires in
    let sexprs = (List.map (fun { C.src_expr } -> (src_expr)) requires) in
    property_of_expr
      ~prop_kind:(P.Reachable None) 
      false
      name
      P.PropUnknown
      (P.NonVacuityCheck (pos, scope))
      (Some (sexprs |> String.concat " and "))
      (E.mk_not guard)
    :: props
  | _ ->
    props

let mode_non_vacuity_checks scope { C.modes } =
  if Flags.check_nonvacuity () then (
    List.fold_left
      (fun props { C.name ; C.pos; C.requires } ->
        let name = Format.asprintf "%a" (I.pp_print_ident true) name in
        non_vacuity_check scope name pos requires props
      )
      []
      modes
  )
  else []

(* The guarantees of a contract, including mode implications, as properties. *)
let guarantees_of_contract scope { C.guarantees ; C.modes } =
  (* Originally properties are unknown. *)
  let prop_status = P.PropUnknown in
  (* Creates a property for a guarantee. *)
  let guarantee_of_svar ({ C.svar ; C.pos } as sv, is_cand) =
    property_of_expr
      is_cand
      (C.prop_name_of_svar sv "guarantee" "")
      prop_status
      (P.Guarantee (pos, scope))
      (Some sv.src_expr)
      (E.mk_var svar)
  in
  (* Creates properties for mode implications of a mode. *)
  let implications_of_modes modes acc =
    modes |> List.fold_left (
      fun acc { C.name ; C.pos; C.requires ; C.ensures ; C.candidate } ->
        let name = Format.asprintf "%a" (I.pp_print_ident true) name in
        (* LHS of the implication. *)
        let guard = conj_of requires in
        (* Generating one property per ensure. *)
        let ensure_props =
          ensures |> List.fold_left (
            fun acc ({ C.pos ; C.svar } as sv) -> (
              E.mk_var svar |> E.mk_impl guard
              |> property_of_expr
                candidate
                (C.prop_name_of_svar sv name (Format.asprintf "%tensure" Lib.StringValues.pp_print_scope_sep))
                prop_status
                (P.GuaranteeModeImplication (pos, scope))
                (Some sv.src_expr)
            ) :: acc
          ) acc
        in
        if Flags.check_nonvacuity () then (
          (* Generating one non-vacuity check per mode *)
          non_vacuity_check scope name pos requires ensure_props
        )
        else ensure_props
    ) acc
  in

  guarantees |> List.map guarantee_of_svar |> implications_of_modes modes

(* The assumptions of a contract as properties. *)
let subrequirements_of_contract call_pos scope node_id svar_map { C.assumes } =
  assumes |> List.map (
    fun { C.pos ; C.name ; C.svar ; C.src_expr} ->
      let prop_term =
        Var.mk_state_var_instance svar TransSys.prop_base
        |> Term.mk_var
        |> lift_term svar_map
      in
      let prop_name =
        match name with
        | None -> (
          Format.asprintf "%a%a%tassume%a"
            NI.pp_print_node_id_user_name node_id
            pp_print_line_and_column call_pos
            Lib.StringValues.pp_print_scope_sep
            pp_print_line_and_column pos
        )
        | Some n -> (
          Format.asprintf "%a%a%t%s"
            NI.pp_print_node_id_user_name node_id
            pp_print_line_and_column call_pos 
            Lib.StringValues.pp_print_scope_sep n
        )
      in
      let prop_status = P.PropUnknown in
      let prop_source = P.Assumption (pos, (scope, call_pos)) in
      { P.prop_name ;
        P.prop_source ;
        P.prop_term ;
        P.prop_status ;
        prop_kind = Invariant ; 
        P.prop_expr = Some src_expr}
  )

let bounded_check call_pos caller_rf =
  let prop_name =
    Format.asprintf "bounded_check%a" pp_print_line_and_column call_pos
  in
  (* Lexicographic termination requires the measure to be bounded below, i.e.
     each component is non-negative. *)
  let prop_term =
    List.map (fun e ->
      Term.mk_leq [Term.mk_num Numeral.zero; E.base_term_of_expr TransSys.prop_base e])
      caller_rf
    |> Term.mk_and
  in
  let prop_expr =
    List.map (fun e -> Format.asprintf "(0 <= %a)" (E.pp_print_expr false) e) caller_rf
    |> String.concat " and "
  in
  let prop_status = P.PropUnknown in
  let prop_source = P.TerminationCheck call_pos in
  { P.prop_name ;
    P.prop_source ;
    P.prop_term ;
    P.prop_status ;
    P.prop_kind = Invariant;
    P.prop_expr = Some prop_expr
  }

let decrease_check call_pos svar_map src_expr caller_rf callee_rf =
  let prop_name =
    Format.asprintf "decrease_check%a" pp_print_line_and_column call_pos
  in
  let callee_rf_terms =
    List.map (fun e ->
      E.base_term_of_expr TransSys.prop_base e |> lift_term svar_map) callee_rf
  in
  let caller_rf_terms =
    List.map (E.base_term_of_expr TransSys.prop_base) caller_rf
  in
  (* The measure strictly decreases in the lexicographic order: some component
     decreases while all earlier components stay equal. For a single component
     this reduces to the ordinary "callee < caller". When the two measures have
     different arities (possible for mutually recursive functions), their common
     prefix is compared. *)
  let prop_term =
    let rec lex cs ds =
      match cs, ds with
      | [c], [d] -> Term.mk_lt [c; d]
      | c :: cs', d :: ds' ->
        Term.mk_or [
          Term.mk_lt [c; d];
          Term.mk_and [Term.mk_eq [c; d]; lex cs' ds']
        ]
      | _ -> assert false
    in
    let n = min (List.length callee_rf_terms) (List.length caller_rf_terms) in
    let take l = List.filteri (fun i _ -> i < n) l in
    lex (take callee_rf_terms) (take caller_rf_terms)
  in
  (* Prefer the source-level rendering reconstructed during node generation
     (e.g. "n - 1 < n"); fall back to the normalized term otherwise. *)
  let prop_expr =
    match src_expr with
    | Some e -> e
    | None ->
      Format.asprintf "%a" (E.pp_print_term_as_expr false) prop_term
  in
  let prop_status = P.PropUnknown in
  let prop_source = P.TerminationCheck call_pos in
  { P.prop_name ;
    P.prop_source ;
    P.prop_term ;
    P.prop_status ;
    P.prop_kind = Invariant;
    P.prop_expr = Some prop_expr
  }

(* The termination checks of a contract as properties. *)

let termination_checks call_pos svar_map src_expr caller_rf callee_rf =
  [bounded_check call_pos caller_rf;
   decrease_check call_pos svar_map src_expr caller_rf callee_rf]

(* Builds the abstraction of a node given its contract.
If the contract is [(a, g, {r_i, e_i})], then the abstraction is
[ a => ( g and /\ {r_i => e_i} ) ]. *)
let abstraction_of_contract assumption_assumed
  { C.assumes ; C.sofar_assump ; C.guarantees ; C.modes } =
  (* LHS of the implication. *)
  let lhs =
    if (assumes <> [] && not assumption_assumed) then
      match sofar_assump with
      | None -> conj_of assumes
      | Some v -> E.mk_var v
    else
      E.t_true
  in
  (* Guarantee. *)
  let gua = guarantees |> List.map (fun ({ C.svar }, _) -> E.mk_var svar) in
  (* Adding mode implications to guarantees. *)
  modes |> List.fold_left (
    fun acc { C.requires ; C.ensures } ->
      (E.mk_impl (conj_of requires) (conj_of ensures)) :: acc
  ) gua
  |> E.mk_and_n
  (* Building actual abstraction. *)
  |> E.mk_impl lhs

(* A one element list with the property corresponding to
   at least one mode of a contract being active, or
   the empty list if no mode is present *)
let one_mode_active scope { C.modes } =
  if modes = [] then
    [] (* failwith "one_mode_active asked on mode-less contract" ; *)
  else (
    let first_mode = List.hd modes in
    let pos = first_mode.C.pos in
    let rev_path = first_mode.C.path |> List.rev |> List.tl in
    let name =
      let l = ("_one_mode_active" :: rev_path) |> List.rev in
      Format.asprintf "%a"
        (pp_print_list Format.pp_print_string ".") l
    in
    (* Disjunction of mode requirements. *)
    let prop =
      modes |> List.map (fun { C.requires } -> conj_of requires) |> E.mk_or_n
      (* Building property. *)
      |> property_of_expr false name
          P.PropUnknown (P.GuaranteeOneModeActive (pos, scope)) None
    in
    [prop]
  )




(* ********************************************************************** *)
(* Constraints from types                                                 *)
(* ********************************************************************** *)

(* Add constraint for subrange/enumeration *)
let add_constraints_of_type init terms state_var =
  (* Get type of state variable *)
  let state_var_type = StateVar.type_of_state_var state_var in

  if Type.is_array state_var_type then (

    let base_type = Type.last_elem_type_of_array state_var_type in

    let indices =
      Type.all_index_types_of_array state_var_type 
      |> List.map (fun ty -> ty, Var.mk_fresh_var ty)
    in

    let array_var =
      Var.mk_state_var_instance state_var
        (if init then TransSys.init_base else TransSys.trans_base)
      |> Term.mk_var
    in

    let select_term =
      List.fold_left
        (fun acc (_, iv) -> Term.mk_select acc (Term.mk_var iv))
        array_var
        indices
    in

    let ct = 
      if Type.is_enum base_type then 
        let l, u = Type.bounds_of_enum base_type in 
        Term.mk_leq [ Term.mk_num l; select_term; Term.mk_num u]
      else 
        match Type.bounds_of_int_range base_type with 
          | Some l, Some u -> Term.mk_leq [ Term.mk_num l; select_term; Term.mk_num u]
          | None, Some u -> Term.mk_leq [ select_term; Term.mk_num u]
          | Some l, None -> Term.mk_leq [ Term.mk_num l; select_term]
          | None, None -> Term.mk_bool true
    in

    let qct =
      List.fold_left
        (fun acc (ty, iv) ->
           match Type.node_of_type ty with
           | (Type.IntRange (Some i, Some j) | Type.Enum (i, j)) when Flags.Arrays.inline () -> (
             let cj = ref [] in
             for x = (Numeral.to_int j) downto (Numeral.to_int i) do
               cj := Term.mk_let [iv, Term.mk_num_of_int x] acc :: !cj
             done;
             Term.mk_and !cj
           )
           | (Type.IntRange (Some i, Some j) | Type.Enum (i, j)) -> (
             let bounds =
               Term.mk_leq
                 [ Term.mk_num i; Term.mk_var iv; Term.mk_num Numeral.(j - one)]
             in
             Term.mk_forall [iv] (Term.mk_implies [bounds; acc])
           )
           | Type.IntRange (None, Some j) -> (
             let bounds =
               Term.mk_leq
                 [ Term.mk_var iv; Term.mk_num Numeral.(j - one)]
             in
             Term.mk_forall [iv] (Term.mk_implies [bounds; acc])
           )
           | Type.IntRange (Some i, None) -> (
             let bounds =
               Term.mk_leq
                 [ Term.mk_num i; Term.mk_var iv; ]
             in
             Term.mk_forall [iv] (Term.mk_implies [bounds; acc])
           )
           | _ ->
             Term.mk_forall [iv] acc)
        ct
        indices
      |> Term.convert_select
    in

    qct :: terms

  )

  else (
    (* Get bounds of integer range *)
    let l, u = 
      (if Type.is_int_range state_var_type
      then None, None
      else Type.bounds_of_enum state_var_type |> (fun (a, b) -> Some a, Some b))
    in
    let 
    var = Var.mk_state_var_instance state_var 
                    (if init then TransSys.init_base else TransSys.trans_base) |> Term.mk_var
    in

    (* Constrain values of variable between bounds *)
    match l, u with 
      | Some l, Some u ->
        Term.mk_leq
          [ Term.mk_num l; var; Term.mk_num u ]
        (* Add to terms *)
        :: terms 
      | Some l, None ->
        Term.mk_leq
          [ Term.mk_num l; var; ]
      (* Add to terms *)
      :: terms 
    | None, Some u -> 
      Term.mk_leq
        [ var; Term.mk_num u ]
      (* Add to terms *)
      :: terms 
    | None, None -> Term.mk_bool true :: terms
  )
                 


(* ********************************************************************** *)
(* Node calls                                                             *)
(* ********************************************************************** *)

(* Add instance of called node to list of subsystems

   Group instances of the same node together, each has a different
   state variable map and guarding function. *)
let rec add_subsystem' trans_sys instance accum =

  function 

    (* No other instance of this node found: add as a singleton list  *) 
    | [] -> 

      (trans_sys, [instance]) :: accum

    (* Check if there is another instance of this node  *)
    | (trans_sys', inst) as h :: tl -> 

      (* Compare transition systems by name *)
      if TransSys.equal_scope trans_sys trans_sys' then 

        (* Add node instance to previous instances, append remainder of
           list of subsystems and return *)
        List.rev_append
          ((trans_sys, (instance :: inst)) :: accum)
          tl

      else

        (* Keep searching for transition system in tail of list *)
        add_subsystem' 
          trans_sys
          instance
          (h :: accum)
          tl
      
(* Add instance of called node to list of subsystems *)
let add_subsystem
    trans_sys
    uid
    pos
    map_up
    map_down
    guard_clock
    assumes
    subsystems =

  let instance =
    { TransSys.uid;
      TransSys.pos; 
      TransSys.map_up; 
      TransSys.map_down; 
      TransSys.guard_clock;
      TransSys.assumes }
  in

  (* Use recursive function with empty accumulator *)
  add_subsystem'
    trans_sys
    instance
    []
    subsystems


(* Change the bounds of state variables to the ones corresponding to actual
   parameters of the node call *)
let register_call_bound globals map_up sv =
  let bounds =
    try StateVar.StateVarHashtbl.find globals.G.state_var_bounds sv
    with Not_found -> [] in

  let bounds = List.map (fun b -> match b with
      | E.Fixed _ | E.Unbound _ -> b
      | E.Bound e ->
        let t = E.unsafe_term_of_expr e in
        let svs = Term.state_vars_of_term t |> SVS.elements in
        let sigma =
          List.fold_left (fun acc s ->
              (*assert (StateVar.is_const s);
              let v = Var.mk_const_state_var s in*)
              let v = Var.mk_state_var_instance s Numeral.zero in
              try
                let sv' = SVM.find s map_up in
                (*assert (StateVar.is_const sv');
                let tv' = Var.mk_const_state_var sv' |> Term.mk_var in*)
                let tv' = Var.mk_state_var_instance sv' Numeral.zero |> Term.mk_var in
                (v, tv') :: acc
              with Not_found -> acc) [] svs
          |> List.rev in
        if sigma = [] then b
        else
          E.Bound (Term.apply_subst sigma t |> E.unsafe_expr_of_term)
    ) bounds in
  StateVar.StateVarHashtbl.add globals.G.state_var_bounds sv bounds

let add_call_context_to_prop call_context prop =
  match call_context with
  | None -> prop
  | Some sv -> (
    let v = Var.mk_state_var_instance sv TransSys.prop_base in
    { prop with P.prop_term = Term.mk_implies [Term.mk_var v; prop.P.prop_term] }
  )

(* Return term and lifted property for node call 

   This factors out node calls with or without an activation
   condition *)
let call_terms_of_node_call mk_fresh_state_var globals caller_comp_type
    { N.call_node_id ;
      N.call_id        ;
      N.call_pos       ;
      N.call_context   ;
      N.call_inputs    ;
      N.call_oracles   ;
      N.call_outputs   ;
      N.call_rec_decrease_expr ;}
    node_locals
    node_props
    node_hist_svars
    node_crt_svars
    { init_uf_symbol  ;
      trans_uf_symbol ;
      node = {
        N.comp_type;
        N.inputs    ;
        N.oracles   ;
        N.outputs   ;
        N.contract  ;
      }               ;
      stateful_locals ;
      properties      ;
      history_svars   ;
      ctr_svars ;
    } =

  (* Initialize map of state variable in callee to instantiated state
     variable in caller *)
  let state_var_map_up, state_var_map_down = 

    (SVM.empty, SVM.empty)

    (* Map actual to formal inputs *)
    |> D.fold2 (
      fun _ state_var inst_state_var (state_var_map_up, state_var_map_down) -> 
         (SVM.add state_var inst_state_var state_var_map_up,
          SVM.add inst_state_var state_var state_var_map_down)
     ) inputs call_inputs

    (* Map actual to formal outputs *)
    |> D.fold2 (
      fun _ state_var inst_state_var (state_var_map_up, state_var_map_down) -> 
         (SVM.add state_var inst_state_var state_var_map_up,
          SVM.add inst_state_var state_var state_var_map_down)
    ) outputs call_outputs

    |> fun (state_var_map_up, state_var_map_down) ->

        (* Map actual to formal oracles *)
        List.fold_left2 (
          fun (state_var_map_up, state_var_map_down) state_var inst_state_var -> 
             (SVM.add state_var inst_state_var state_var_map_up,
              SVM.add inst_state_var state_var state_var_map_down)
        ) (state_var_map_up, state_var_map_down)
          oracles
          call_oracles

  in

  (* Create fresh state variable for each state variable local
     to the called node and add to the respective data
     structures *)
  let node_locals, call_locals, (state_var_map_up, state_var_map_down) = 

    (* Need to preserve the order of the stateful_locals in call_locals *)
    List.fold_right

      (fun state_var (locals, call_locals, (state_var_map_up, state_var_map_down)) -> 

         (* Create a fresh state variable in the caller *)
         let inst_state_var =
           let name =
             let row, col = row_col_of_pos call_pos in
             Format.asprintf "inst_%a_l%dc%d_%a_%d"
               NI.pp_print_node_id_internal_name call_node_id
               row col
               StateVar.pp_print_state_var state_var
               call_id
           in
           mk_fresh_state_var
             ?is_const:(Some (StateVar.is_const state_var))
             ?for_inv_gen:(Some true)
             ?inst_for_sv:(Some state_var)
             name
             (StateVar.type_of_state_var state_var)
         in

         N.set_state_var_instance
           inst_state_var call_pos (NI.get_internal_name call_node_id |> I.of_hstring) state_var;
          (* No need to call N.add_state_var_def for local instances
             because they have no definition in this node *)
         
         (* Add fresh state variable to locals of this node, to actual
            input parameters of node call and to map of state variable
            instances *)
         (inst_state_var :: locals,
          inst_state_var :: call_locals,
          (SVM.add state_var inst_state_var state_var_map_up,
           SVM.add inst_state_var state_var state_var_map_down)))

      (* All stateful local variables of the called node

         This includes the init flag and the instance variable. *)
      stateful_locals

      (* Add to local variables of the node, start with empty list of
         variables instantiated at the call, and extend the state
         variable map *)
      (node_locals, [], (state_var_map_up, state_var_map_down))

  in

  let node_hist_svars =
    let lifted_hist_svars =
      history_svars |> TM.map (fun m ->
        SVM.fold (fun sv l acc ->
          let sv' = lift_state_var state_var_map_up sv in
          let l' =
            List.map (fun h_sv -> lift_state_var state_var_map_up h_sv) l
          in
          SVM.add sv' l' acc
        )
        m
        SVM.empty
      )
    in
    TM.union
      (fun _ m1 m2 -> Some (SVM.union (fun _ l1 l2 ->
        Some (l1 @ l2)
      ) m1 m2))
      lifted_hist_svars
      node_hist_svars
  in

  let node_crt_svars =
    (List.map (lift_state_var state_var_map_up) ctr_svars)
    @ node_crt_svars
  in

  (* Instantiate properties of the called node in this node *)
  let node_props =
    properties
    |> List.filter (fun p ->
      match P.get_prop_original_source p with
      | P.Assumption _ -> true
      (* Candidate invariants are lifted so that, once proven, they can
         strengthen the analysis of the calling node *)
      | P.Candidate _ -> not (Flags.modular ())
      | _ -> Flags.check_subproperties () && not (Flags.modular ())
    )
    |> List.fold_left (
      fun a ({ P.prop_name = n; P.prop_term = t; P.prop_kind ; P.prop_expr } as p) ->

        (* Lift name of property *)
        let prop_name =
          lift_prop_name (NI.get_name call_node_id |> I.of_hstring) call_pos n
        in

        (* Lift state variable of property

          Property is a local variable, thus it has been
          instantiated and is in the map *)
        let prop_term = lift_term state_var_map_up t in

        (* Property is instantiated *)
        let prop_source =
          let called_scope =
            I.to_scope (NI.get_internal_name call_node_id |> I.of_hstring)
          in
          P.Instantiated ((called_scope, call_pos), p)
        in

        (* Property status is unknown *)
        let prop_status = P.PropUnknown in

        (* Create and append property *)
        let prop =
          { P.prop_name ;
            P.prop_source ;
            P.prop_term ;
            P.prop_status ;
            P.prop_kind ; 
            P.prop_expr }
        in
        (add_call_context_to_prop call_context prop) :: a

    ) node_props
  in

  (* Instantiate assumptions from contracts in this node. *)
  let node_assume_props =
    match contract with
    | None -> []
    | Some contract -> (
      subrequirements_of_contract
        call_pos
        (I.to_scope (NI.get_internal_name call_node_id |> I.of_hstring))
        call_node_id
        state_var_map_up
        contract
      |> List.map (add_call_context_to_prop call_context)
    )
  in

  let func_termination_props =
    match caller_comp_type, comp_type with
    | N.Function { rec_info = Some (caller_id, caller_rf) },
      N.Function { rec_info = Some (callee_id, callee_rf) } when caller_id = callee_id -> (
      termination_checks
        call_pos state_var_map_up call_rec_decrease_expr caller_rf callee_rf
      |> List.map (add_call_context_to_prop call_context)
    )
    | _ -> []
  in

  let node_props = node_assume_props @ func_termination_props @ node_props in

  let node_assumes =
    if node_assume_props = [] then None
    else (
      match contract with
      | None -> assert false
      | Some {C.sofar_assump} -> (
        match sofar_assump with
        | None -> None
        | Some sofar_assump ->
          let assume_terms =
            List.map (fun { P.prop_term } -> prop_term) node_assume_props
          in
          let sofar_term =
            Var.mk_state_var_instance sofar_assump TransSys.prop_base
            |> Term.mk_var
            |> lift_term state_var_map_up
          in
          Some (assume_terms, sofar_term)
      )
    )
  in

  (* Return actual parameters of initial state constraint at bound in
     the correct order *)
  let init_params_of_bound term_of_state_var =
    List.map 
      term_of_state_var
      ((D.values call_inputs) @ 
       call_oracles @ 
       (D.values call_outputs) @
       call_locals)
  in

  let non_constant_inputs =
    (* Filter out inputs that are constants FOR THE CALLEE. *)
    D.fold2
      (fun formal_idx formal_sv actual_sv acc ->
        if StateVar.is_const formal_sv then acc
        else D.add formal_idx actual_sv acc
      )
      inputs
      call_inputs
      D.empty
    |> D.values
  in

  let call_locals =
    (* Filter out instance vars that are arguments of a constant parameter in a subnode call *)
    List.filter (fun sv -> StateVar.is_const sv |> not) call_locals
  in

  (* Return actual parameters of transition relation at bound in the
     correct order *)
  let trans_params_of_bound term_of_state_var pre_term_of_state_var =
    init_params_of_bound term_of_state_var @ (
      ( non_constant_inputs @ D.values call_outputs @ call_locals )
      |> List.map pre_term_of_state_var
    )
  in

  (* Term for initial state constraint at initial state *)
  let init_call_term =
    init_params_of_bound
      (E.base_term_of_state_var TransSys.init_base)

    |> Term.mk_uf init_uf_symbol

  in

  (* Term for initial state constraint at current state *)
  let init_call_term_trans = 
    init_params_of_bound
      (E.cur_term_of_state_var TransSys.trans_base)

    |> Term.mk_uf init_uf_symbol

  in

  (* Term for transition relation at current state *)
  let trans_call_term =
    trans_params_of_bound
      (E.cur_term_of_state_var TransSys.trans_base)
      (E.pre_term_of_state_var TransSys.trans_base)
    |> Term.mk_uf trans_uf_symbol
  in

  (* apply subsitutions on bounds also *)
  LustreIndex.iter (fun _ ->
      register_call_bound globals state_var_map_up) call_inputs;
  LustreIndex.iter (fun _ ->
      register_call_bound globals state_var_map_up) call_outputs;
  List.iter (register_call_bound globals state_var_map_up) call_oracles;
  List.iter (register_call_bound globals state_var_map_up) call_locals;
  
  (* Return information to build constraint for node call with or
     without activation condition *)
  state_var_map_up, 
  state_var_map_down, 
  node_locals, 
  node_props, 
  node_hist_svars,
  node_crt_svars,
  node_assumes,
  call_locals,
  init_call_term, 
  init_call_term_trans,
  trans_call_term
  

let add_call_context call_context init_term trans_term =
  match call_context with
  | None -> init_term, trans_term
  | Some sv -> (
    let v_i = Var.mk_state_var_instance sv TransSys.init_base in
    let v_t = Var.mk_state_var_instance sv TransSys.trans_base in
    Term.mk_implies [Term.mk_var v_i; init_term],
    Term.mk_implies [Term.mk_var v_t; trans_term]
  )

(* Add constraints from node calls to initial state constraint and
   transition relation *)
let rec constraints_of_node_calls 
  mk_fresh_state_var
  globals
  comp_type
  num_unrollings_map
  trans_sys_defs
  node_locals
  node_init_flags
  node_props 
  node_hist_svars
  node_crt_svars
  subsystems
  init_terms
  trans_terms
= function

  (* Definitions for all node calls created, return *)
  | [] -> (
    subsystems, 
    node_locals, 
    node_init_flags, 
    node_props, 
    node_hist_svars,
    node_crt_svars,
    init_terms, 
    trans_terms
  )

  (* Node call without an activation condition or restart *)
  | { N.call_id; N.call_pos; N.call_context; N.call_node_id; N.call_cond = [] }
    as node_call :: tl ->

    (* Get generated transition system of callee *)
    let { trans_sys } as node_def =
      let num_unrollings =
        match NI.Map.find_opt call_node_id num_unrollings_map with
        | Some nu -> nu
        | None -> assert false
      in
      try NodeInstanceMap.find (call_node_id, num_unrollings) trans_sys_defs
      (* Fail if transition system for node not found *)
      with Not_found -> assert false
    in

    let 
      state_var_map_up,
      state_var_map_down,
      node_locals,
      node_props,
      node_hist_svars,
      node_crt_svars,
      node_assumes,
      _,
      init_term,
      _,
      trans_term
    =
      (* Create node call *)
      call_terms_of_node_call
        mk_fresh_state_var
        globals
        comp_type
        node_call
        node_locals
        node_props
        node_hist_svars
        node_crt_svars
        node_def
    in

    (* Add node instance to list of subsystems *)
    let subsystems =
      add_subsystem
        trans_sys
        call_id
        call_pos
        state_var_map_up
        state_var_map_down
        (* No guarding necessary when instantiating term, because
           this node instance does not have an activation
           condition *)
        (fun _ t -> t)
        node_assumes
        subsystems
    in

    let init_term, trans_term =
      add_call_context call_context init_term trans_term
    in

    (* Continue with next node calls *)
    constraints_of_node_calls 
      mk_fresh_state_var
      globals
      comp_type
      num_unrollings_map
      trans_sys_defs
      node_locals
      node_init_flags
      node_props
      node_hist_svars
      node_crt_svars
      subsystems
      (init_term :: init_terms)
      (trans_term :: trans_terms)
      tl

  (* Node call with restart condition *)
  | { N.call_id; N.call_pos; N.call_context; N.call_node_id;
      N.call_cond = [N.CRestart restart] } as node_call :: tl ->

    assert (call_context = None);

    (* Get generated transition system of callee *)
    let { trans_sys } as node_def =
      let num_unrollings =
        match NI.Map.find_opt call_node_id num_unrollings_map with
        | Some nu -> nu
        | None -> assert false
      in
      try NodeInstanceMap.find (call_node_id, num_unrollings) trans_sys_defs
      (* Fail if transition system for node not found *)
      with Not_found -> assert false
    in

    let state_var_map_up, state_var_map_down, node_locals, node_props, node_hist_svars,
        node_crt_svars, node_assumes, _, init_term, _, trans_term =
      (* Create node call *)
      call_terms_of_node_call
        mk_fresh_state_var globals comp_type node_call node_locals
        node_props node_hist_svars node_crt_svars node_def
    in

    (* Guard lifted property with restart conditions of node *)
    let restart_prop = E.cur_term_of_state_var TransSys.prop_base restart in
    
    let node_props = 
      List.map
        (fun ({ P.prop_term } as p) ->
           let is_one_state =
             match Term.var_offsets_of_term prop_term with
             | Some lo, Some up -> Numeral.(equal lo up)
             | _ -> true
           in
           if is_one_state then p else
             { p with
               P.prop_term =
                 Term.mk_implies [Term.negate restart_prop; prop_term] })
        node_props
    in

    
    (* Add node instance to list of subsystems and guard with not restart *)
    let subsystems =
      add_subsystem trans_sys call_id call_pos state_var_map_up state_var_map_down
        (fun i t ->  
           Term.mk_implies
             [Var.mk_state_var_instance restart i |> Term.mk_var
              |> Term.mk_not;
              t])
        node_assumes
        subsystems
    in

    let restart_trans = E.cur_term_of_state_var TransSys.trans_base restart in
    (* Reset state of node to initial state when restart condition is true *)
    let trans_term =
      Term.mk_ite restart_trans
        (Term.bump_state
           Numeral.(TransSys.trans_base - E.cur_offset) init_term)
        trans_term
    in
    
    (* Continue with next node calls *)
    constraints_of_node_calls 
      mk_fresh_state_var
      globals
      comp_type
      num_unrollings_map
      trans_sys_defs
      node_locals
      node_init_flags
      node_props
      node_hist_svars
      node_crt_svars
      subsystems
      (init_term :: init_terms)
      (trans_term :: trans_terms)
      tl


  (* Node call with activation condition *)
  | { N.call_id;
      N.call_pos;
      N.call_context;
      N.call_node_id; 
      N.call_cond = N.CActivate clock :: other_conds;
      N.call_inputs;
      N.call_outputs; 
      N.call_defaults } as node_call :: tl -> 

    assert (call_context = None);

    (* Get generated transition system of callee *)
    let { node = { N.inputs; }; trans_sys; init_flags } as node_def =

      let num_unrollings =
        match NI.Map.find_opt call_node_id num_unrollings_map with
        | Some nu -> nu
        | None -> assert false
      in

      try 

      NodeInstanceMap.find (call_node_id, num_unrollings) trans_sys_defs

      (* Fail if transition system for node not found *)
      with Not_found -> assert false

    in


    (* Create shadow variable for each non-constant input *)
    let 
      
      (* Add shadow state variable to local variables, return term
         at previous instant, equation with corresponding inputs,
         and equation with previous state value *)
      (shadow_inputs,
       node_locals,
       propagate_inputs_init, 
       propagate_inputs_trans, 
       interpolate_inputs) =

      D.fold2
        (fun
          formal_idx 
          formal_sv 
          actual_sv
          (shadow_inputs, 
           node_locals,
           propagate_inputs_init, 
           propagate_inputs_trans, 
           interpolate_inputs) ->

          (* Skip over constant formal inputs *)
          if StateVar.is_const formal_sv then 

            (D.add formal_idx formal_sv shadow_inputs, 
             node_locals,
             propagate_inputs_init, 
             propagate_inputs_trans, 
             interpolate_inputs )

          else

            (* Create fresh shadow variable for input *)
            let shadow_sv =
              let name =
                let row, col = row_col_of_pos call_pos in
                Format.asprintf "shw_%a_l%dc%d_%a"
                  (I.pp_print_ident true) (NI.get_internal_name call_node_id |> I.of_hstring)
                  row col
                  StateVar.pp_print_state_var formal_sv
              in
              mk_fresh_state_var
                ?is_const:None
                ?for_inv_gen:(Some false)
                ?inst_for_sv:(Some formal_sv)
                name
                (StateVar.type_of_state_var formal_sv) 
            in

            (* Shadow variable takes value of input *)
            let p_i = 
              Term.mk_eq
                [E.base_term_of_state_var TransSys.init_base actual_sv; 
                 E.base_term_of_state_var TransSys.init_base shadow_sv]
            in

            (* Shadow variable takes value of input *)
            let p_t = 
              Term.mk_eq
                [E.cur_term_of_state_var TransSys.trans_base actual_sv; 
                 E.cur_term_of_state_var TransSys.trans_base shadow_sv]
            in

            (* Shadow variable takes its previous value *)
            let i = 
              Term.mk_eq
                [E.cur_term_of_state_var TransSys.trans_base shadow_sv; 
                 E.pre_term_of_state_var TransSys.trans_base shadow_sv]
            in

            (* Add shadow variable and equations to accumulator *)
            (D.add formal_idx shadow_sv shadow_inputs,
             shadow_sv :: node_locals,
             p_i :: propagate_inputs_init, 
             p_t :: propagate_inputs_trans, 
             i :: interpolate_inputs))

        inputs
        call_inputs

        (D.empty, node_locals, [], [], [])

    in

    let 

      state_var_map_up, 
      state_var_map_down, 
      node_locals, 
      node_props,
      node_hist_svars,
      node_crt_svars,
      node_assumes,
      call_locals,
      init_term, 
      init_term_trans, 
      trans_term =

      call_terms_of_node_call
        mk_fresh_state_var
        globals
        comp_type
        (* Modify node call to use shadow inputs *)
        { node_call with N.call_inputs = shadow_inputs }
        node_locals
        node_props
        node_hist_svars
        node_crt_svars
        node_def
    in

    
    let clock_init = 
      E.base_term_of_state_var TransSys.init_base clock 
    in

    let clock_trans = 
      E.cur_term_of_state_var TransSys.trans_base clock 
    in

    let clock_prop = 
      E.cur_term_of_state_var TransSys.prop_base clock 
    in

    let clock_trans_pre = 
      E.pre_term_of_state_var TransSys.trans_base clock 
    in

    let has_ticked =
      let name =
        let row, col = row_col_of_pos call_pos in
        Format.asprintf "tck_%a_l%dc%d_%a"
          (I.pp_print_ident true) (NI.get_internal_name call_node_id |> I.of_hstring)
          row col 
          StateVar.pp_print_state_var clock
      in
      mk_fresh_state_var
        ?is_const:None
        ?for_inv_gen:(Some false)
        ?inst_for_sv:(Some clock)
        name
        Type.t_bool
    in

    let node_locals = 
      has_ticked :: node_locals
    in

    let has_ticked_init = 
      E.base_term_of_state_var TransSys.init_base has_ticked
    in

    let has_ticked_trans = 
      E.cur_term_of_state_var TransSys.trans_base has_ticked
    in

    let has_ticked_trans_pre = 
      E.pre_term_of_state_var TransSys.trans_base has_ticked
    in

    let init_flags = 
      List.map (fun sv -> SVM.find sv state_var_map_up) init_flags
    in

    let init_flags_init =
      List.map
        (E.base_term_of_state_var TransSys.init_base) 
        init_flags
    in

    (* Add restart conditions if any *)
    let trans_term = match other_conds with
      | [] -> trans_term
      | [N.CRestart restart] ->
        let restart_trans =
          E.cur_term_of_state_var TransSys.trans_base restart in
        (* Reset state of node to initial state when restart condition is
           true *)
        Term.mk_ite restart_trans
          (Term.bump_state
             Numeral.(TransSys.trans_base - E.cur_offset) init_term)
          trans_term
      | _ -> assert false
    in

    
    let init_term = 

      Term.mk_and 

        ([
          
          (* [has_ticked] is false in the first instant, because
             it becomes true only after the first clock tick. *)
          Term.negate has_ticked_init;
          
          (* Propagate input values to shadow variables on clock
             tick *)
          Term.mk_implies 
            [clock_init;
             Term.mk_and propagate_inputs_init];
          
          (* Initial state constraint on clock tick *)
          Term.mk_implies [clock_init; init_term]
            
        ] @

          (match call_defaults with
            
            (* No defaults for outputs *)
            | None -> 

              (* Init flags are false if clock is not ticking *)
              [Term.mk_implies 
                 [Term.mk_not clock_init;
                  Term.mk_and init_flags_init]]

            (* Defaults for outputs *)
            | Some d -> 

              (* Init flags are true and defaults for outputs if no
                 clock tick *)
              [Term.mk_implies 
                 [Term.mk_not clock_init;
                  Term.mk_and
                    (D.fold2
                       (fun _ sv { E.expr_init } accum ->
                          Term.mk_eq 
                            [E.base_term_of_state_var TransSys.init_base sv;
                             E.base_term_of_expr TransSys.init_base expr_init] :: 
                          accum)
                       call_outputs
                       d
                       init_flags_init)]]))
          
    in

    let trans_term =
      Term.mk_and
        [

          (* has_ticked flag becomes true in the instant after
             the first clock tick and stays true *)
          Term.mk_eq 
            [has_ticked_trans;
             Term.mk_or
               [has_ticked_trans_pre; 
                clock_trans_pre]];

          (* Propagate input values to shadow variables on clock
             tick *)
          Term.mk_implies 
            [clock_trans;
             Term.mk_and propagate_inputs_trans];

          (* Interpolate input values in shadow variable between
             clock ticks *)
          Term.mk_implies 
            [Term.mk_not clock_trans; 
             Term.mk_and interpolate_inputs];

          (* Transition relation with true activation condition
               on the first clock tick *)
          Term.mk_implies
            [Term.mk_and 
               [clock_trans; Term.negate has_ticked_trans];
             init_term_trans];

          (* Transition relation with true activation condition
             on following clock ticks *)
          Term.mk_implies
            [Term.mk_and
               [clock_trans; has_ticked_trans];
             trans_term];

          (* Transition relation with false activation
             condition *)
          Term.mk_implies 
            [Term.mk_not clock_trans;
             Term.mk_and 
               (List.fold_left
                  (fun accum state_var ->
                     Term.mk_eq 
                       [E.cur_term_of_state_var
                          TransSys.trans_base 
                          state_var; 
                        E.pre_term_of_state_var
                          TransSys.trans_base
                          state_var] :: 
                     accum)
                  []
                  call_locals
                |> D.fold
                  (fun _ state_var accum -> 
                     Term.mk_eq 
                       [E.cur_term_of_state_var
                          TransSys.trans_base 
                          state_var; 
                        E.pre_term_of_state_var
                          TransSys.trans_base
                          state_var] :: 
                     accum)
                  call_outputs) ]

        ]

    in

    (* Guard lifted property with activation and restart conditions of node *)
    let guard_prop one_state =
      match other_conds with
      | _ when one_state -> clock_prop
      | [] -> clock_prop
      | [N.CRestart restart] ->
        let restart_prop = E.cur_term_of_state_var TransSys.prop_base restart in
        Term.mk_and [clock_prop; Term.negate restart_prop]
      | _ -> assert false
    in
    
    let node_props =
      List.map
        (fun ({ P.prop_term } as p) ->
           let is_one_state =
             match Term.var_offsets_of_term prop_term with
             | Some lo, Some up -> Numeral.(equal lo up)
             | _ -> true
           in
           { p with
             P.prop_term =
               Term.mk_implies [guard_prop is_one_state; prop_term] })
        node_props
    in

    (* Candidate invariants from when-block ties: once the activation clock
       has ticked, the when-block variable (which holds its previous value
       whenever the clock is off) and the corresponding call output (which is
       frozen whenever the clock is off) agree; and before the first tick, the
       when-block variable still has its initial value. Both hold by
       construction of the when-block encoding, but stating them as candidate
       properties (proven before they are used) makes the hold semantics
       visible to k-induction, which otherwise cannot relate the frozen state
       of the called node instance to the properties of the calling node. *)
    let node_props =
      match node_call.N.call_ties with
      | [] -> node_props
      | ties ->
        let has_ticked_prop =
          E.cur_term_of_state_var TransSys.prop_base has_ticked
        in
        let ticked = Term.mk_or [clock_prop; has_ticked_prop] in
        let row, col = row_col_of_pos call_pos in
        let mk_candidate guard tie_sv name =
          let tie_prop = E.cur_term_of_state_var TransSys.prop_base tie_sv in
          { P.prop_name = name;
            P.prop_source =
              P.Candidate (Some (P.Generated (Some call_pos, [tie_sv], P.Body)));
            P.prop_term = Term.mk_implies [guard; tie_prop];
            P.prop_status = P.PropUnknown;
            P.prop_kind = P.Invariant;
            P.prop_expr = None;
          }
        in
        List.fold_left (fun acc (tie_sv, init_tie_sv, x) ->
          let acc =
            mk_candidate ticked tie_sv
              (Format.asprintf
                "Held value of '%s' consistent with clocked call at l%dc%d"
                (HString.string_of_hstring x) row col)
            :: acc
          in
          match init_tie_sv with
          | None -> acc
          | Some init_tie_sv ->
            mk_candidate (Term.negate ticked) init_tie_sv
              (Format.asprintf
                "Held value of '%s' initial before clocked call at l%dc%d"
                (HString.string_of_hstring x) row col)
            :: acc
        ) node_props ties
    in

    let guard_clock =
      match other_conds with
      | [] ->
        (fun i t ->
           Term.mk_implies
             [Var.mk_state_var_instance clock i |> Term.mk_var;
              t])
      | [N.CRestart restart] ->
        (fun i t ->
           Term.mk_implies
             [Term.mk_and [Var.mk_state_var_instance clock i |> Term.mk_var;
                           Var.mk_state_var_instance restart i |> Term.mk_var
                           |> Term.mk_not];
              t])
      | _ -> assert false
    in
    
    (* Add node instance as subsystem *)
    let subsystems =
      add_subsystem
        trans_sys
        call_id
        call_pos
        state_var_map_up
        state_var_map_down
        guard_clock
        node_assumes
        subsystems
    in

    constraints_of_node_calls
      mk_fresh_state_var
      globals
      comp_type
      num_unrollings_map
      trans_sys_defs
      node_locals
      (init_flags @ node_init_flags)
      node_props
      node_hist_svars
      node_crt_svars
      subsystems
      (init_term :: init_terms)
      (trans_term :: trans_terms)
      tl


  | _ -> assert false

let constraints_of_ctr ctr_svars trans_terms =
  let rec loop acc = function
  | [] | [_] -> acc
  | sv1 :: sv2 :: tl ->
    let v1 =
      Var.mk_state_var_instance sv1 TransSys.trans_base |> Term.mk_var
    in
    let v2 =
      Var.mk_state_var_instance sv2 TransSys.trans_base |> Term.mk_var
    in
    let eq = Term.mk_eq [v1; v2] in
    loop (eq :: acc) (sv2 :: tl)
  in
  let eqs = loop [] ctr_svars in
  match eqs with
  | [] -> trans_terms
  | _ -> Term.mk_and eqs :: trans_terms

let constraints_of_history_congruence
  mk_fresh_state_var
  history_svars
  init_terms
  trans_terms
=
  let pairs =
    let mk_eq sv1 sv2 =
      let v1 = Var.mk_state_var_instance sv1 TransSys.init_base in
      let v2 = Var.mk_state_var_instance sv2 TransSys.init_base in
      Term.mk_eq [Term.mk_var v1; Term.mk_var v2]
    in
    let rec mk_pairs acc = function
    | [] -> acc
    | (sv1, h_sv1) :: tl ->
      let acc =
        List.fold_left
          (fun acc (sv2, h_sv2) ->
            let cond =
              if StateVar.equal_state_vars sv1 sv2 then None
              else
                let name =
                  Format.sprintf "eq_vars_%d_%d" (StateVar.uid sv1) (StateVar.uid sv2)
                in 
                Some (name, mk_eq sv1 sv2)
            in
            (cond, mk_eq h_sv1 h_sv2) :: acc
          )
          acc
          tl
      in
      mk_pairs acc tl
    in
    TM.fold
      (fun _ m acc ->
        let l =
          SVM.bindings m
          |> List.map (fun (sv, l) -> (sv, List.hd l))
        in
        SVM.fold (fun _ l' acc ->
          match l' with
          | []  -> assert false
          | [_] -> acc
          | _ -> (
            let eqs =
              l' |> List.map (fun h_sv ->
                Var.mk_state_var_instance h_sv TransSys.init_base
                |> Term.mk_var
              )
              |> Term.mk_eq
            in
            (None, eqs) :: acc
          )
        )
        m
        (mk_pairs acc l)
      )
      history_svars
      []
  in

  (* Split [pairs] in two lists to handle separately the cases where
     variables are syntactically equal from the rest of cases
  *)
  let all_inputs_equal, rest =
    pairs
    |> List.fold_left (fun (l1, l2) (cond, o) ->
        match cond with
        | None -> (o :: l1, l2)
        | Some (name, i) -> (l1, (name, (i, o)) :: l2)
      )
      ([], [])
  in

  let add_constraints_for_vars_equal init_terms trans_terms =
    let init_terms =
      all_inputs_equal
      |> List.fold_left (fun init_terms o_base ->
        o_base :: init_terms
      )
      init_terms
    in

    let trans_terms =
      all_inputs_equal
      |> List.fold_left (fun trans_terms o_base ->
        let offset =
          Numeral.(TransSys.trans_base - TransSys.init_base)
        in
        let o_trans = Term.bump_state offset o_base in
        o_trans :: trans_terms
      )
      trans_terms
    in
    init_terms, trans_terms
  in

  let add_constraints_for_rest init_terms trans_terms =
    let local_and_terms =
      rest |> List.map (fun (name, terms) ->
        let fresh_svar =
          mk_fresh_state_var
            ?is_const:(Some false)
            ?for_inv_gen:(Some true)
            ?inst_for_sv:None
            name
            Type.t_bool
        in
        (fresh_svar, terms)
      )
    in

    let locals = List.map fst local_and_terms in

    let init_terms =
      local_and_terms
      |> List.fold_left (fun init_terms (l, (i_base,o_base)) ->
        let vi =
          Var.mk_state_var_instance l TransSys.init_base |> Term.mk_var
        in
        Term.mk_eq [vi; i_base]
        :: Term.mk_implies [vi; o_base]
        :: init_terms
      )
      init_terms
    in

    let trans_terms =
      local_and_terms
      |> List.fold_left (fun trans_terms (l, (i_base,o_base)) ->
        let vt =
          Var.mk_state_var_instance l TransSys.trans_base |> Term.mk_var
        in
        let vp = Term.bump_state (Numeral.of_int (-1)) vt in
        let offset = Numeral.(TransSys.trans_base - TransSys.init_base) in
        let i_trans = Term.bump_state offset i_base in
        let o_trans = Term.bump_state offset o_base in
        Term.mk_eq [vt; Term.mk_and [i_trans; vp]]
        :: Term.mk_implies [vt; o_trans]
        :: trans_terms
      )
      trans_terms
    in
    locals, init_terms, trans_terms
  in

  let init_terms, trans_terms =
    match all_inputs_equal with
    | [] -> init_terms, trans_terms
    | _  -> add_constraints_for_vars_equal init_terms trans_terms
  in

  match rest with
  | [] -> [], init_terms, trans_terms
  | _  -> add_constraints_for_rest init_terms trans_terms


(* Add constraints from assertions to initial state constraint and
   transition relation *)
let rec constraints_of_asserts init_terms trans_terms = function

  (* All assertions consumed, return term for initial state
     constraint and transition relation *)
  | [] -> (init_terms, trans_terms)
          
  (* Assertion with term for initial state and term for transitions *)
  | (_,sv) :: tl ->

    let expr = E.mk_var sv in
    let init_terms = (expr |> E.base_term_of_t TransSys.init_base) :: init_terms in
    let trans_terms = (expr |> E.cur_term_of_t TransSys.trans_base) :: trans_terms in

    (* Continue with next assertions *)
    constraints_of_asserts init_terms trans_terms tl


module MBounds = Map.Make (struct
    type t = E.expr E.bound_or_fixed list
    let compare_bounds b1 b2 = match b1, b2 with
      | E.Unbound None, E.Unbound None -> 0
      | E.Fixed e1, E.Fixed e2
      | E.Bound e1, E.Bound e2
      | E.Unbound (Some e1), E.Unbound (Some e2) -> E.compare_expr e1 e2
      | E.Fixed _, _ -> -1
      | _, E.Fixed _ -> 1
      | E.Unbound _, _ -> 1
      | _, E.Unbound _ -> -1
    let compare l1 l2 =
      let n1, n2 = List.length l1, List.length l2 in
      let c = n2 - n1 in
      if c <> 0 then c else
        let rec cmp = function
          | b1 :: r1, b2 :: r2 ->
            let c = compare_bounds b1 b2 in
            if c <> 0 then c else cmp (r1, r2)
          | [], [] -> 0
          | _ -> assert false
        in
        cmp (l1, l2)
  end)


(* Add constraints from equations to initial state constraint and
   transition relation *)
let rec constraints_of_equations_wo_arrays transfer_defs node
    eq_bounds init stateful_vars terms (lets, lets_dependencies) definition_set = function
  (* Constraints for all equations generated *)
  | [] -> terms, lets, eq_bounds, definition_set

  (* Stateful variable must have an equational constraint *)
  (* If we are doing experimental slicing the let binding optimization is
     skipped and this is not relevant *)
  | ((state_var, []), { E.expr_init; E.expr_step }) :: tl 
    when
      (Flags.slice_nodes () != `Experimental) &&
      (List.exists (StateVar.equal_state_vars state_var) stateful_vars) ->

    (* Equation for stateful variable *)
    let def = 
      Term.mk_eq 
        (if init then 
            (* Equation for initial constraint on variable *)
            [E.base_term_of_state_var TransSys.init_base state_var; 
            E.base_term_of_expr TransSys.init_base expr_init] 
          else
            (* Equation for transition relation on variable *)
            [E.cur_term_of_state_var TransSys.trans_base state_var; 
            E.cur_term_of_expr TransSys.trans_base expr_step])
      (* Convert select operators to uninterpreted functions *)
      |> Term.convert_select
    in

    (* Add terms of equation *)
    constraints_of_equations_wo_arrays transfer_defs node
      eq_bounds init stateful_vars (def :: terms) (lets, lets_dependencies) (Term.TermSet.add def definition_set) tl

  (* Can define state variable with a let binding *)
  (* Let binding optimization is not performed when experimental slicing is
     performed *)
  | ((state_var, []), ({ E.expr_init; E.expr_step } as expr)) :: tl
    when ( Flags.slice_nodes () != `Experimental )
    ->

    if transfer_defs then (
    (* TODO: Factor out and optimize this code *)
    (*if not (E.is_var expr) then ( *)
      (* We update the let dependencies *)
      let add_dependency sv acc =
        let old =
          try SVM.find sv acc
          with Not_found -> SVS.empty
        in
        SVM.add sv (SVS.add state_var old) acc
      in
      let svs_in_expr { E.expr_init; E.expr_step } =
        let aux t = Term.state_vars_of_term t in
        let bt expr = E.base_term_of_expr Numeral.zero expr in
        SVS.union (aux (bt expr_init)) (aux (bt expr_step))
      in
      let lets_dependencies =
        SVS.fold add_dependency (svs_in_expr expr) lets_dependencies
      in

      (* We must transfer the defs of this state variable
      to all the state variables that depend on it or one of its dependencies *)
      let dependencies =
        try SVM.find state_var lets_dependencies
        with Not_found -> SVS.empty
      in
      let dependencies = SVS.add state_var dependencies in
      let defs = N.get_state_var_defs state_var |> fun (x, y) -> x @ y in
      let add_defs_to_sv sv =
        (* These state var defs are dependencies, so ?is_dep is 'true' here *)
        List.iter (fun def -> N.add_state_var_def ~is_dep:true sv def) defs
      in
      let depends_on_this_sv expr =
        SVS.inter dependencies (svs_in_expr expr)
        |> SVS.is_empty |> not
      in
      let transfer_defs_to_eq_if_needed ((sv,_),eq) =
        if not (StateVar.equal_state_vars sv state_var) && depends_on_this_sv eq
        then add_defs_to_sv sv
      in
      List.iter transfer_defs_to_eq_if_needed node.N.equations
    ) ;

    (* Let binding for stateless variable, in closure form *)
    let let_closure =
      Term.mk_let
        (if init then
            (* Binding for the variable at the base instant only *)
            [(E.base_var_of_state_var TransSys.init_base state_var,
              E.base_term_of_expr TransSys.init_base expr_init)]
          else
            (* Binding for the variable at the current instant *)
            (E.cur_var_of_state_var TransSys.trans_base state_var,
            E.cur_term_of_expr TransSys.trans_base expr_step) ::
            (if
              (* Does the state variable occur at the previous
                instant? *)
              try
              Term.state_vars_at_offset_of_term
                Numeral.(TransSys.trans_base |> pred)
                (Term.mk_and terms)
              |> SVS.mem state_var
              with Invalid_argument _ -> true

            then
              ((* Definition must not contain a [pre] operator, otherwise we'd
                  have a double [pre]. The state variable is not stateless in
                  this case, and we should not be here. *)
                assert (not (E.has_pre_var E.base_offset expr));
                (* Binding for the variable at the previous instant *)
                [(E.pre_var_of_state_var TransSys.trans_base state_var,
                  E.pre_term_of_expr TransSys.trans_base expr_step)])
            else (* No binding for the variable at the previous instant
                    necessary *)
              [])
            )
    in

    (* Start with singleton lists of let-bound terms *)
    constraints_of_equations_wo_arrays transfer_defs node
      eq_bounds init stateful_vars terms (let_closure :: lets, lets_dependencies) definition_set tl

  (* Array state variable *)
  | (((_, bounds), _) as eq) :: tl -> 

    let other_eqs = try MBounds.find bounds eq_bounds with Not_found -> [] in

    (* map equation to its bounds for future treatment and continue *)
    let eq_bounds = MBounds.add bounds (eq :: other_eqs) eq_bounds in

    constraints_of_equations_wo_arrays transfer_defs node
      eq_bounds init stateful_vars terms (lets, lets_dependencies) definition_set tl


(* create quantified (or no) constraints for recursive arrays definitions *)
let constraints_of_arrays init terms eq_bounds =
    (* Return the i-th index variable *)
  let index_var_of_int_and_ty i kt = 
    E.var_of_expr (E.mk_array_index_var i kt) in

    (* Add quantifier or let binding for indexes of variable *)
  let add_bounds term bounds =
    let term, quant_v, _ =
      List.fold_left (fun (term, quant_v, i) bound -> 
          let v = match bound with 
          | E.Unbound None -> index_var_of_int_and_ty i Type.t_int
          | E.Bound e 
          | E.Fixed e 
          | E.Unbound (Some e) -> 
            index_var_of_int_and_ty i (E.type_of_expr e) in
          match bound with 
          | E.Fixed e ->
            Term.mk_let [v, E.unsafe_term_of_expr e] term, quant_v, pred i

          | E.Bound e when Flags.Arrays.inline () && E.is_numeral e ->
            (* inline if static bound and option given *)
            let b = E.numeral_of_expr e |> Numeral.to_int in
            let cj = ref [] in
            for x = (b - 1) downto 0 do
              cj := Term.mk_let [v, Term.mk_num_of_int x] term :: !cj
            done;
            Term.mk_and !cj, quant_v, pred i

          | E.Bound e ->
            let term =
              if Flags.Arrays.recdef () then term
              else
                let te = E.unsafe_term_of_expr e
                         |> fun t -> if init then t
                            else Term.bump_state Numeral.one t in
                Term.(
                  mk_implies [
                    mk_leq [mk_num Numeral.zero; mk_var v; 
                            mk_minus [te; mk_num Numeral.one]];
                    term])
            in
            term, v :: quant_v, pred i

          | E.Unbound None ->
            (* let v' = Term.free_var_of_term (E.unsafe_term_of_expr v) in *)
            term, v :: quant_v, pred i

          | E.Unbound (Some e) -> (
            match Type.node_of_type (E.type_of_expr e) with
            | Enum (l, u) ->
              let l' = Numeral.to_int l in
              let u' = Numeral.to_int u in
              let cj = ref [] in
              for x = u' downto l' do
                cj := Term.mk_let [v, Term.mk_num_of_int x] term :: !cj
              done;
              Term.mk_and !cj, quant_v, pred i
            | _ -> term, v :: quant_v, pred i
          )
                             
        ) (term, [], List.length bounds - 1) bounds
    in


    match quant_v with
    | [] -> term
    | _ -> Term.mk_forall ~fundef:(Flags.Arrays.recdef ()) quant_v term
     
    in
  MBounds.fold (fun bounds eqs (terms, definition_set) ->
      let cstrs_eqs =
        List.map (function
            | (state_var, bounds), { E.expr_init; E.expr_step } ->
              (* Array state variable term *)
              let sv_term =
                if init then E.base_term_of_state_var TransSys.init_base state_var
                else E.cur_term_of_state_var TransSys.trans_base state_var
              in
              (* Select array *)
              let select_term, _ =
                List.fold_left
                  (fun (st, i) bound ->
                     let kt = match bound with 
                     | E.Bound b 
                     | E.Unbound (Some b) 
                     | E.Fixed b -> E.type_of_expr b 
                     | E.Unbound None -> Type.t_int 
                     in
                     let v = (index_var_of_int_and_ty i kt) in 
                     Term.mk_select st (Term.mk_var v),
                     succ i)
                  (sv_term, 0)
                  (List.rev bounds)
              in
              (*Format.printf "select_term: %a\n"
                Term.pp_print_term select_term;*)
              (* Assign value to array position *)
                  (Term.mk_eq
                    [select_term;
                      if init then
                        (* Expression at base instant *)
                        E.base_term_of_expr TransSys.init_base expr_init
                      else
                        (* Expression at current instant *)
                        E.cur_term_of_expr TransSys.trans_base expr_step]
                    (* Convert select operators to uninterpreted functions *)
                  ) |> Term.convert_select 
              ) eqs
      in

      let definition_set = Term.TermSet.(of_list cstrs_eqs |> union definition_set) in

      (* group constraints under same quantifier when not using recursive
         encoding *)
      let cstrs =
        if Flags.Arrays.recdef () then cstrs_eqs
        else [Term.mk_and cstrs_eqs] in

      (* Wrap equations in let binding and/or quantifiers for indexes and add
         definitions to terms *)
      (List.fold_left (fun terms cstr ->
            add_bounds cstr bounds :: terms
        ) terms cstrs, definition_set)

    ) eq_bounds terms 

let constraints_of_equations node init stateful_vars terms equations definition_set =

  (* make constraints for equations which do not redefine arrays first *)
  let terms, lets, eq_bounds, definition_set =
    let transfer_defs =
      Flags.IVC.compute_ivc () || List.mem `MCS (Flags.enabled ())
    in
    constraints_of_equations_wo_arrays transfer_defs node
      MBounds.empty init stateful_vars terms ([], SVM.empty) definition_set equations
    in

  (* then make constraints for recursive arrays so as to merge quantifiers as
     much as possible *)
  let terms, definition_set = constraints_of_arrays init (terms, definition_set) eq_bounds in

  if lets = [] then terms, definition_set
  else
    (* Apply let bindings *)
    [List.fold_left (fun t let_bind -> let_bind t)
       (Term.mk_and terms) (List.rev lets)
     |> Term.convert_select], definition_set


let rec trans_sys_of_node' options globals top_name analysis_param
  trans_sys_defs output_input_dep nodes definition_set = function

  (* Transition system for all nodes created *)
  | [] -> trans_sys_defs

  (* Create transition system for top node *)
  | ((node_id, num_unrollings) as node_instance) :: tl ->

    (* Transition system for node has been created and added to
       accumulator meanwhile? *)
    if NodeInstanceMap.mem node_instance trans_sys_defs then

      (* Continue with next transition systems *)
      trans_sys_of_node'
        options globals top_name analysis_param trans_sys_defs output_input_dep
        nodes definition_set tl

    (* Transition system has not been created *)
    else

      (* Node to create a transition system for *)
      let node =

        try 

          (* Find node in abstract or implementation nodes by name *)
          N.node_of_node_id node_id nodes

        with Not_found ->

          (* Node must be in the list of nodes *)
          raise
            (Invalid_argument
               (Format.asprintf 
                  "trans_sys_of_node: node %a not found"
                  NI.pp_print_node_id_user_name node_id))

      in
        
      let reached_limit =
        match NI.Map.find_opt node_id num_unrollings with
        | Some n -> n >= 1
        | None -> false
      in

      let { N.init_flag;
            N.inputs;
            N.oracles;
            N.outputs;
            N.locals;
            N.equations;
            N.calls;
            N.asserts;
            N.props;
            N.history_svars;
            N.contract;
            N.comp_type } as node =

        if reached_limit then
          S.slice_node_to_abstraction node
        else
          node
      in

      let scope, suffix =
        let base_scope =
          [I.string_of_ident false (NI.get_internal_name node_id |> I.of_hstring)]
        in
        if N.is_recursive node && not (NI.Map.is_empty num_unrollings) then
          let node_num_id = get_node_num_id () in
          let rec_tag = get_rec_tag node_num_id in
          rec_tag :: base_scope, Format.sprintf "_%s" rec_tag
        else
          base_scope, ""
      in

      (* Create a fresh state variable *)
      let mk_fresh_state_var
          ?is_const
          ?for_inv_gen
          ?inst_for_sv
          name
          state_var_type =

        (* Increment counter for fresh state variables *)
        (*let index = index_of_scope scope in*)

        (* Create state variable *)
        let fsv =
          StateVar.mk_state_var
            ~is_input:false
            ?is_const:is_const
            ?for_inv_gen:for_inv_gen
            name
            (*((I.push_index I.inst_ident index) 
             |> I.string_of_ident true)*)
            (N.scope_of_node node @ I.reserved_scope)
            state_var_type
        in

          (* Register bounds *)
        let bounds = match inst_for_sv with
          | None -> []
          | Some sv ->
            try StateVar.StateVarHashtbl.find globals.G.state_var_bounds sv
            with Not_found -> []
        in
          StateVar.StateVarHashtbl.add globals.G.state_var_bounds fsv bounds;
          
          fsv
          
      in

      (* Subnodes for which we have not created a transition
         system

         Collect only the nodes to add here, thus we can eliminate
         duplicates from tl'. A node may need to appear in both tl'
         and tl. *)
      let tl', num_unrollings_map = 

        let num_unrollings' =
          if N.is_recursive node then
            let num_unrollings_node =
              match NI.Map.find_opt node_id num_unrollings with
              | Some n -> n
              | None -> 0
            in
            NI.Map.add node_id (num_unrollings_node + 1) num_unrollings
          else
            num_unrollings
        in

        List.fold_left 
          (fun (accum, nu_map) { N.call_node_id } -> 

             let called_node =
               N.node_of_node_id call_node_id nodes
             in

             let num_unrollings'' =
               if N.is_recursive node && N.is_recursive called_node then
                 num_unrollings'
               else
                 num_unrollings
             in

             let nu_map = NI.Map.add call_node_id num_unrollings'' nu_map in

             let reached_limit =
               match NI.Map.find_opt call_node_id num_unrollings'' with
               | Some n -> n >= 2
               | None -> false
             in

             if 
               reached_limit ||

               (* Transition system for node created? *)
               NodeInstanceMap.mem (call_node_id, num_unrollings'') trans_sys_defs || 

               (* Node with current number of unrollings already pushed to
                  stack before this node? *)
               List.exists
                 (fun e -> NodeInstance.equal e (call_node_id, num_unrollings''))
                 accum

             then 

               (* Continue with stack unchanged *)
               accum, nu_map

             else

               (* Push node to top of stack *)
               (call_node_id, num_unrollings'') :: accum, nu_map)

          ([], NI.Map.empty)
          calls

      in

      (* Are there subnodes for which a transition system needs to
         be created first? *)
      match tl' with

        (* Some transitions systems of called nodes have not been
           created *)
        | _ :: _ -> 

          (* We could check here that the call graph does not have
             cycles, although that should not be allowed as long as
             we don't accept recursive calls in Lustre. *)

          (* Recurse to create transition system for called nodes,
             then return to this node *)
          trans_sys_of_node'
            options
            globals
            top_name
            analysis_param
            trans_sys_defs
            output_input_dep
            nodes
            definition_set
            (tl' @ (node_id, num_unrollings) :: tl)

        (* All transitions systems of called nodes have been
           created *)
        | [] ->

          (* Used for functions and subranges *)
          let undefined_outputs =
            let defined_svars = List.fold_left
              (fun set ((sv,_),_) -> SVS.add sv set) SVS.empty equations
            in
            let is_undefined svar = SVS.mem svar defined_svars |> not in
            List.filter is_undefined (D.values outputs)
          in

          (* If node is a function, for each undefined output,
          create the term `(= (f <inputs>) output)` to add it to `init` and
          `trans`. *)
          let function_ufs, function_constraints_at_0 =
            match comp_type with
            | Function { uf_symbols; rec_info } when options.add_functional_constraints -> (
              (* For a recursive function we tie the outputs of *every*
                 instance (expanded or abstracted) to the global functional
                 UF, not just the abstracted leaves whose outputs are
                 undefined. On an expanded instance the output is also
                 constrained by the body equation, so this forces the UF to
                 satisfy the function's defining equation at that argument
                 (one unrolling). Without it the recurrence is only known for
                 the inlined interior and is lost at the uninterpreted leaf,
                 so calls to the function at arguments separated by the
                 induction's shift never relate (see Even_Odd lemma). *)
              let constrained_outputs =
                if rec_info <> None then D.values outputs
                else undefined_outputs
              in
              let function_ufs =
                constrained_outputs |> List.map (fun sv ->
                  match SVM.find_opt sv uf_symbols with
                  | Some uf -> uf
                  | None -> assert false
                )
              in
              let constraints =
                let term_0_of svar =
                  Var.mk_state_var_instance svar Numeral.zero
                  |> Term.mk_var
                in
                let input_terms_at_0 =
                  let inputs = D.values inputs in
                  List.map (fun input -> term_0_of input) inputs
                in
                constrained_outputs
                |> List.map (fun output ->
                  let uf = SVM.find output uf_symbols in
                  Term.mk_eq [
                    term_0_of output ;
                    Term.mk_uf uf input_terms_at_0
                  ]
                )
              in
              function_ufs, constraints
            )
            | _ -> [], []
          in


          (* Filter assumptions for this node's assumptions *)
          let node_assumptions =
            (* No assumptions if abstract. *)
            if A.param_scope_is_abstract analysis_param scope then
              Invs.empty ()
            else
              A.param_assumptions_of_scope analysis_param scope
          in


          (* ****************************************************** *)
          (* Assertions from contracts and init flag                *)

          (* Start with asserts and properties for contracts *)
          let contract_asserts, properties = match contract with
            | None -> [], []
            | Some contract ->

              let interpreter_mode =
                match analysis_param with
                | A.ContractMonitor _
                | A.Interpreter _ -> true
                | _ -> false
              in

              let include_assumption =
                NI.equal node_id top_name && not interpreter_mode
              in

              (* Add requirements to invariants if node is the top node *)
              let contract_asserts, properties = 
                if include_assumption then
                  (* Node is top, forcing contract assumption. *)
                  [ assumption_of_contract contract ],
                  (* Add property for completeness of modes if top node is
                    abstract. *)
                  if A.param_scope_is_abstract analysis_param scope then
                    List.rev_append
                      (mode_non_vacuity_checks scope contract)
                      (one_mode_active scope contract)
                  else []
                else
                  [], []
              in

              (* Add mode implications to invariants if node is abstract,
                 otherwise add ensures as properties *)
              (*Want to be in else branch with new interpreter param mode*)
              match analysis_param, (reached_limit || A.param_scope_is_abstract analysis_param scope) with
              | A.ContractMonitor _, _ 
              | _, false ->  
                (*First is assertions, second are proof obligations, want contract to go in proof obligation*)
                contract_asserts,
                guarantees_of_contract scope contract @ properties
              | _, true -> 
                abstraction_of_contract include_assumption contract :: contract_asserts,
                properties
            
               
          in

          (* Initial state constraint *)
          let init_terms = 

            (* Init flag is true on first tick of node *)
            E.base_term_of_state_var TransSys.init_base init_flag :: 

            (* Add invariants from contracts as assertions *)
            List.map
              (E.base_term_of_t TransSys.init_base)
              contract_asserts

            (* Add functional constraints on ouputs if any. *)
            |> List.rev_append function_constraints_at_0

          in

          (* Transition relation *)
          let trans_terms = 

            (* Init flag becomes and stays false at the second
               tick *)
            (E.cur_term_of_state_var TransSys.trans_base init_flag
             |> Term.negate) :: 

            (* Add invariants from contracts as assertions *)
            List.map
              (E.cur_term_of_t TransSys.trans_base)
              contract_asserts

            (* Add functional constraints on ouputs if any. *)
            |> List.rev_append (
              (* Bump to `1`. *)
              function_constraints_at_0
              |> List.map (Term.bump_state Numeral.one)
            )

          in


          (* ****************************************************** *)
          (* Assertions from types                                  *)

          let all_state_vars = 
            (D.values inputs) @
            oracles @
            (D.values outputs) @ 
            (List.concat (List.map D.values locals))
          in

          (* Only keep assumptions that are defined given the current sys. *)
          let node_assumptions =
            node_assumptions |> Invs.filter (
              fun _ term _ ->
                Term.state_vars_of_term term
                |> SVS.for_all (
                  fun svar -> List.mem svar all_state_vars
                )
            )
          in

          let filter_enum_svars =
            List.filter (fun state_var ->
              let state_var_type = StateVar.type_of_state_var state_var in
              if Type.is_array state_var_type then
                let base_type = Type.last_elem_type_of_array state_var_type in
                Type.is_enum base_type
              else
                Type.is_enum state_var_type
            )
          in

          (* Enforce creation of 'select' functions required to retrieve models, even if
             the array variable is not used in the input.
             - When no slicing is applied, unused variables are not removed.
             - There are cases where slicing doesn't remove unused variable (e.g.
               record value with an array field that is unused, but
               the record value is still passed to a node or a function).
             - The experimental slicing algorithm also requires this.
          *)
          all_state_vars |> List.iter (fun state_var ->
            let state_var_type = StateVar.type_of_state_var state_var in
            if Type.is_array state_var_type then (
              StateVar.encode_select state_var |> ignore
            )
          );

          let subrange_and_enum_state_vars =
            let enum_state_vars = filter_enum_svars all_state_vars in
            (* Inputs, defined outputs, and locals require a proof obligation.
               This is currently done in lustreAstNormalizer.
            *)
            let subrange_state_vars =
              let svars =
                if A.param_scope_is_abstract analysis_param scope then
                  oracles
                else
                  List.rev_append undefined_outputs oracles
              in
              svars |> List.filter (fun state_var ->
                let state_var_type = StateVar.type_of_state_var state_var in
                if Type.is_array state_var_type then
                  let base_type = Type.last_elem_type_of_array state_var_type in
                  Type.is_int_range base_type
                else
                  Type.is_int_range state_var_type
              )
            in
            List.rev_append subrange_state_vars enum_state_vars
          in

          let init_terms =
            List.fold_left
              (add_constraints_of_type true)
              init_terms
              subrange_and_enum_state_vars
          in

          let trans_terms =
            List.fold_left
              (add_constraints_of_type false)
              trans_terms
              subrange_and_enum_state_vars
          in

          (* ****************************************************** *)
          (* Node calls 

             We must add node calls before equations so that local
             variables can be let bound in
             {!constraints_of_equations}.                           *)

          (* Instantiated state variables and constraints from node
             calls *)
          let
            subsystems, 
            lifted_locals, 
            init_flags,
            lifted_props,
            lifted_hist_svars,
            lifted_ctr_svars,
            init_terms, 
            trans_terms
          =
            constraints_of_node_calls
              mk_fresh_state_var
              globals
              comp_type
              num_unrollings_map
              trans_sys_defs
              []  (* No lifted locals *)
              [init_flag]
              []  (* No lifted properties *)
              TM.empty  (* No lifted history_svars *)
              [] (* No lifted crt_vars *)
              []  (* No subsystems *)
              init_terms
              trans_terms
              calls
          in

          let history_svars =
            let history_svars' =
              history_svars |> TM.map (fun l ->
                l |> List.fold_left (fun acc (sv, h_sv) ->
                  if List.exists (StateVar.equal_state_vars sv) all_state_vars
                     &&
                     List.exists (StateVar.equal_state_vars h_sv) all_state_vars
                  then
                    SVM.add sv [h_sv] acc
                  else
                    acc
                )
                SVM.empty
              )
            in
            TM.union
              (fun _ m1 m2 -> Some (SVM.union (fun _ l1 l2 ->
                Some (l1 @ l2)
              ) m1 m2))
              history_svars'
              lifted_hist_svars
          in

          let
            equiv_locals,
            init_terms,
            trans_terms
          =
            if NI.equal node_id top_name then
              constraints_of_history_congruence
                mk_fresh_state_var
                history_svars
                init_terms
                trans_terms
            else
              [], init_terms, trans_terms
          in

          (* Add lifted properties *)
          let properties = properties @ lifted_props in

          (* ****************************************************** *)
          (* Assertions 

             We must add contracts before equations so that local
             variables can be let bound in
             {!constraints_of_equations}.                           *)

          (* Constraints from assertions *)
          let init_terms, trans_terms = 
              constraints_of_asserts init_terms trans_terms asserts in


          (* ****************************************************** *)
          (* Equations                                              *)

          (* Stateful variables in node, including state
             variables for node instance, first tick flag, and state
             variables capturing outputs of node calls *)
          let stateful_vars_of_node =
            N.stateful_vars_of_node globals.state_var_bounds node
            |> SVS.elements
          in
          let stateful_vars = 
            init_flag :: stateful_vars_of_node
              @ lifted_locals @ equiv_locals in

          let ctr_svars =
            let is_ctr =
              let ctr_str =
                HString.string_of_hstring GeneratedIdentifiers.ctr_id
              in
              fun sv -> StateVar.name_of_state_var sv = ctr_str
            in
            match List.find_opt is_ctr stateful_vars_of_node with
            | None -> lifted_ctr_svars
            | Some sv -> sv :: lifted_ctr_svars
          in

          let trans_terms =
            if NI.equal node_id top_name then
              constraints_of_ctr ctr_svars trans_terms
            else
              trans_terms
          in

          let global_consts =
            (* Format.eprintf "Global constants: %d@." *)
            (*   (List.length globals.G.free_constants); *)
            List.fold_left (fun acc (_, vt, _) ->
                D.fold (fun _ v acc ->
                    (* Format.eprintf "Gobal constant: %a@." Var.pp_print_var v; *)
                    v :: acc) vt acc
              ) [] globals.G.free_constants
            |> List.rev
          in
          
          let global_const_svars =
            List.map Var.state_var_of_state_var_instance global_consts
          in

          global_const_svars |> List.iter (fun state_var ->
              let state_var_type = StateVar.type_of_state_var state_var in
              if Type.is_array state_var_type then (
                (* Enforce creation of 'select' functions. Globals are never sliced.*)
                StateVar.encode_select state_var |> ignore
              )
            )
          ;

          let global_constraints =
            List.map
              (E.base_term_of_t TransSys.init_base)
              globals.G.global_constraints
          in

          let global_constraints =
            let enum_consts = filter_enum_svars global_const_svars in
            List.fold_left
              (add_constraints_of_type true)
              global_constraints
              enum_consts
          in

          let stateful_vars =
            let global_const_svars =
              SVS.of_list global_const_svars
            in
            List.filter
              (fun sv -> not (SVS.mem sv global_const_svars))
              stateful_vars
          in

          (* Order initial state equations by dependency and
             generate terms *)
          let (init_terms, definition_set), svar_dep_init, node_output_input_dep_init =
            S.order_equations true output_input_dep node
              |> (fun (e, sv_d, io_d) ->
               constraints_of_equations
                node
                true
                stateful_vars
                init_terms
                (List.rev e)
                definition_set
                , sv_d, io_d)
          in

          (* Order transition relation equations by dependency and
             generate terms *)
          let (trans_terms, definition_set ), svar_dep_trans, node_output_input_dep_trans =
            S.order_equations false output_input_dep node
              |> (fun (e, sv_d, io_d) ->
               constraints_of_equations node
                    false stateful_vars trans_terms (List.rev e) definition_set, sv_d, io_d)
          in

          (* We compute an overapproximation of the set of variables
             whose value is constrained by an assumption or an assert
             by collecting the variables in the cone of influence of
             all assume and assert expressions
          *)
          let constrained_svars =
            let roots = (* assume and assert state variables *)
              List.map snd asserts |> SVS.of_list
              |> fun roots' -> (
                match contract with
                | None -> roots'
                | Some { C.assumes; C.sofar_assump } ->
                  match sofar_assump with
                  | None -> SVS.of_list (List.map (fun { C.svar } -> svar) assumes)
                  | Some sofar_assump -> SVS.add sofar_assump roots'
              )
            in
            List.rev_append svar_dep_init svar_dep_trans |>
            List.fold_left
              (fun svars (sv, deps) ->
                if SVS.mem sv roots then SVS.union svars deps else svars
              )
              SVS.empty
          in

          (* This is currently used for path compression when the equivalence
             relation is based on equal states modulo inputs.
             TODO: Refine this set to consider only inputs _temporally_ constrained.
             This should be enough to ensure existence of equal state successors.
          *)
          let unconstrained_inputs =
            SVS.diff
              (SVS.of_list (D.values inputs))
              constrained_svars
          in

          (* ****************************************************** *)
          (* Properties                                         

             We can only add properties after node calls, because
             properties may have been lifted from calls.            *)

          (* Create properties from annotations *)
          let properties = 

            (* Property status is unknown *)
            let prop_status = P.PropUnknown in

            (* Iterate over each property annotation *)
            List.map (
              fun (state_var, prop_name, prop_source, prop_kind, prop_expr) -> 

              (* Property is just the state variable *)
              let prop_term =
                E.cur_term_of_state_var
                  TransSys.prop_base
                  state_var
              in

              { P.prop_name; 
                P.prop_source; 
                P.prop_term;
                P.prop_status;
                P.prop_kind; 
                P.prop_expr = Some prop_expr}
            ) props
              
            (* Add to existing properties *)
            @ properties 

          in

          (* Extract requirements. *)
          let mode_requires = ass_and_mode_requires_of_contract contract in

          (* ****************************************************** *)
          (* Turn assumed properties into assertions                *)

          let valid_prop_terms =
            List.fold_left
              (fun acc ({ P.prop_term } as p) ->
                match Invs.find node_assumptions prop_term with
                | None -> acc
                | Some cert -> (
                  P.set_prop_invariant p cert; (* Set property valid *)
                  prop_term :: acc
                )
              )
              [] properties
          in

          let assumption =
            if
              not (NI.equal node_id top_name) &&
              not (A.param_scope_is_abstract analysis_param scope) &&
              valid_prop_terms <> []
            then
              match contract with
              | Some contract when contract.C.assumes <> [] -> (
                let mk_var v offset =
                  Term.mk_var (Var.mk_state_var_instance v offset)
                in
                match contract.C.sofar_assump with
                | None ->
                  let conj =
                    List.map (fun {C.svar} -> mk_var svar TransSys.prop_base) contract.C.assumes
                  in
                  [Term.mk_and conj]
                | Some v ->
                  [mk_var v TransSys.prop_base]
              )
              | _ -> []
            else []
          in

          (* Make assumed properties assertions *)
          let init_terms, trans_terms =

            (* Iterate over each valid property term *)
            List.fold_left
              (fun
                (init_terms, trans_terms) prop_term ->

                (* Bump term to offset of initial state constraint *)
                let prop_term_init =
                  Term.bump_state
                    Numeral.(TransSys.init_base - TransSys.prop_base)
                    (* If assumption is [], then it is trivially prop_term *)
                    (Term.mk_implies (List.rev_append assumption [prop_term]))
                in

                (* Bump term to offset of transition relation *)
                let prop_term_trans =
                  Term.bump_state
                    Numeral.(TransSys.trans_base - TransSys.prop_base)
                    (* If assumption is [], then it is trivially prop_term *)
                    (Term.mk_implies (List.rev_append assumption [prop_term]))
                in

                (* Add property as assertion *)
                (prop_term_init :: init_terms,
                 prop_term_trans :: trans_terms)
              )

              (init_terms, trans_terms)

              valid_prop_terms

          in

          (* ****************************************************** *)
          (* Signatures of predicates                               *)

          (* State variables that are inputs, outputs or oracles and
             thus have instances in each caller *)
          let signature_state_vars = 
            (D.values inputs) @ 
            oracles @
            (D.values outputs)
          in

          (* Stateful variables that are not inputs, outputs or
             oracles, and must be instantiated in each caller *)
          let stateful_locals =
            List.filter
              (fun sv -> 
                 not
                   (List.exists
                      (fun sv' -> StateVar.equal_state_vars sv sv')
                      signature_state_vars))
              stateful_vars
          in

            (* State variables in the signature of the initial state constraint
               in correct order *)
          let signature_state_vars = 
            signature_state_vars @ stateful_locals
          in

          (* Formal parameters of initial state constraint *)
          let init_formals = 
            List.map
              (fun sv -> 
                 Var.mk_state_var_instance sv TransSys.init_base)
              signature_state_vars
          in

          (* Create uninterpreted symbol for initial state predicate *)
          let init_uf_symbol = 
            UfSymbol.mk_uf_symbol
              (Format.asprintf
                 "%s_%a_%d%s"
                 Ids.init_uf_string
                 HString.pp_print_hstring (NI.get_internal_name node_id)
                 (A.info_of_param analysis_param).A.uid
                 suffix)
              (List.map Var.type_of_var init_formals)
              Type.t_bool
          in

          (* Create instances of state variables in signature *)
          let trans_formals = 

            (* All state variables at the current instant. *)
            List.map 
              (fun sv ->
                 Var.mk_state_var_instance sv TransSys.trans_base)
              signature_state_vars @

            (* Non-constant state variables at the previous instant *)
            List.map 
              (fun sv -> 
                 Var.mk_state_var_instance 
                   sv
                   (TransSys.trans_base |> Numeral.pred))
              (List.filter
                 (fun sv -> not (StateVar.is_const sv)) 
                 signature_state_vars)
          in

            (* Create uninterpreted symbol for transition relation predicate *)
          let trans_uf_symbol = 
            UfSymbol.mk_uf_symbol
              (Format.asprintf
                 "%s_%a_%d%s"
                 Ids.trans_uf_string
                 HString.pp_print_hstring (NI.get_internal_name node_id)
                 (A.info_of_param analysis_param).A.uid
                 suffix)
              (List.map Var.type_of_var trans_formals)
              Type.t_bool
          in

          (* UFs of the system. *)
          let ufs = function_ufs in
          
          (* let ty_args_opt = match node_id with 
          | (_, tags) -> Lib.find_map (fun tag -> match tag with 
            | LustreAst.Monomorphization (ty_args, _) -> Some ty_args
            | _ -> None
          ) tags in 
          let ty_args = match ty_args_opt with 
          | Some ty_args -> ty_args 
          | None -> []
          in *)
          
          (* ****************************************************** *)
          (* Create transition system                               *)
          (* ****************************************************** *)

          (* Create transition system *)
          let trans_sys, _ = 
            TransSys.mk_trans_sys 
              scope
              None (* instance_state_var *)
              init_flag
              (* [] *) (* global_state_vars *)
              signature_state_vars
              unconstrained_inputs
              globals.G.state_var_bounds
              global_consts
              global_constraints
              ufs
              init_uf_symbol
              init_formals
              (Term.mk_and init_terms)
              trans_uf_symbol
              trans_formals
              (Term.mk_and trans_terms)
              subsystems
              properties
              mode_requires
              node_assumptions
              (NI.get_node_type node_id <> NodeId.FreeConstant &&
               NI.get_node_type node_id <> NodeId.TypeAscription &&
               NI.get_node_type node_id <> NodeId.ClockedExpr)
          in
          trans_sys_of_node'
            options
            globals
            top_name
            analysis_param
            (NodeInstanceMap.add 
               node_instance
               { node;
                 trans_sys;
                 init_uf_symbol;
                 trans_uf_symbol;
                 stateful_locals;
                 init_flags;
                 properties;
                 history_svars;
                 ctr_svars;
                 definition_set;
              }
               trans_sys_defs)
            ((node_id, 
              (node_output_input_dep_init, node_output_input_dep_trans))
             :: output_input_dep)
            nodes
            definition_set
            tl

let trans_sys_of_nodes
    ?(options=default_settings)
    globals
    subsystems analysis_param
  =

  (* Prevent the garbage collector from running too often during the frontend
     operations *)
  Lib.set_liberal_gc ();
  
  let { A.top } =
    A.info_of_param analysis_param
  in
  (* Make sure top level system is not abstract

     Contracts would be trivially satisfied otherwise *)
  ( match analysis_param with
    | A.Interpreter _
    | A.ContractCheck _ 
    | A.ContractMonitor _-> ()
    | _ -> if A.param_scope_is_abstract analysis_param top then raise (
      Invalid_argument
        "trans_sys_of_nodes: Top-level system must not be abstract"
    )
  );

  let subsystem' = SubSystem.find_subsystem_of_list subsystems top in

  let { SubSystem.source = { N.node_id = top_name } } as subsystem' =

  if options.slice_nodes != `Experimental then
    let preserve_sig, slice_nodes =
      options.preserve_sig, options.slice_nodes
    in
    match options.slice_to_prop with
    | None -> 
      S.slice_to_abstraction
        ~preserve_sig (slice_nodes == `On) analysis_param subsystem'
    | Some prop ->
      S.slice_to_abstraction_and_property
        ~preserve_sig analysis_param prop subsystem'
  else
    subsystem'
  in

  let nodes = N.nodes_of_subsystem subsystem' in

  let { trans_sys; definition_set} =

    try

      (* Create a transition system for each node *)
      trans_sys_of_node'
        options
        globals
        top_name
        analysis_param
        NodeInstanceMap.empty
        [] 
        nodes
        Term.TermSet.empty
        [(top_name, NI.Map.empty)]

      (* Return the transition system of the top node *)
      |> NodeInstanceMap.find (top_name, NI.Map.empty)

    (* Transition system must have been created *)
    with Not_found -> assert false

  in

  ( match analysis_param with
    | A.Refinement (_,result) ->
      (* The analysis that's going to run is a refinement. *)
      TransSys.get_prop_status_all_nocands result.A.sys
      |> List.iter (function
        | _, P.PropUnknown -> (* Unknown is still unknown, do nothing. *)
          ()
        
        | name, (P.PropKTrue _ as status) -> (* K-true is still k-true. *)
          TransSys.set_prop_status trans_sys name status
        
        | name, P.PropInvariant cert -> (* Invariant is still invariant. *)
          TransSys.set_prop_invariant trans_sys name cert;
          (* Adding to invariants of the system. *)
          let t = TransSys.get_prop_term trans_sys name in
          TransSys.add_invariant trans_sys t cert false
          |> ignore
        
        | name, P.PropFalse cex -> (
          match P.length_of_cex cex with
          | l when l > 1 -> (* False at k>0 is now (k-1)-true. *)
            (* Minus 2 because l = k + 1. *)
            TransSys.set_prop_status trans_sys name (P.PropKTrue (l-2))
          | _ -> (* False at 0 is now unknown, do nothing. *)
            ()
        )
      )
    | _ -> ()
  ) ;

  (* Reset garbage collector to its initial settings *)
  Lib.reset_gc_params ();

  let trans_sys =
    if options.slice_nodes == `Experimental then (
      let graph =
        DependencyGraph.dependency_graph_of_system definition_set trans_sys
      in

      let roots = TransSys.get_properties trans_sys
        |> List.to_seq
        |> Seq.map Property.get_prop_term
        |> Seq.map Term.state_vars_of_term
        |> Seq.fold_left SVS.union SVS.empty
      in

      let coi =
        DependencyGraph.cone_of_influence
          graph
          roots
      in

      TransSys.slice_system trans_sys coi)
    else trans_sys
  in

  trans_sys, subsystem'



(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
