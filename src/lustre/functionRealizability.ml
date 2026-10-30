(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

(* Realizability of a function contract with temporal operators.

   A function is applied pointwise: its outputs at each instant are a
   function [f] of its inputs at that instant. Its contract [C], which may
   have temporal operators, is realizable by a function if there is a
   function [f] such that, for every input stream [s], the streams [s] and
   [f(s)] satisfy [C]. This is stronger than the realizability of [C] by a
   reactive component, which the realizability check decides, since the
   output of such a component may depend on the past inputs: the contract
   [guarantee y = (0 -> pre x)] is realizable by a node, not by a function.
   Both coincide when the contract has no state.

   The check is counterexample-guided. It keeps a finite set [S] of input
   traces, and asks whether some function satisfies the contract on each
   of them: the outputs at each instant are an uninterpreted function [u]
   of the inputs at that instant, shared by all the traces and instants.

   - If not, no function satisfies the contract on every input stream, and
     the traces are a certificate that the contract is unrealizable by a
     function.
   - Otherwise, the model of [u] at the inputs of the traces is generalized
     to a total function [f], a decision list whose guards and leaves are
     taken from the contract and the points of the model. The contract
     system is checked with its outputs defined by [f]. If its guarantees
     hold, [f] realizes the contract; otherwise, the inputs of the
     counterexamples are added to [S], and the check is repeated.

   The answers are sound both ways, but the check is incomplete: the
   generalization may not find a function that realizes the contract, and
   a contract with infinitely many output values may be unrealizable by a
   function while every finite set of traces is satisfiable. *)

module TSys = TransSys
module ISys = InputSystem
module N = LustreNode
module C = LustreContract
module D = LustreIndex
module E = LustreExpr
module NI = NodeId
module A = Analysis
module SVS = StateVar.StateVarSet
module VS = Var.VarSet

type trace = (StateVar.t * Model.value list) list

type result =
  | Realizable of (StateVar.t * Term.t) list
  | Unrealizable of (int * trace) list
  | Unknown

exception Unsupported of string

(* ********************************************************************** *)
(* Applicability                                                          *)
(* ********************************************************************** *)

(* Whether a Lustre expression has state: a previous value, or an initial
   value that differs from the value at the following instants *)
let expr_has_state e =
  E.has_pre_var E.base_offset e
  || not (E.equal_expr (E.init_expr e) (E.step_expr e))

(* Whether the contract of the function [node] has state. The equation of
   the variable for the assumptions so far always has state, and is left
   out: a contract without temporal operators only constrains the current
   values of the streams. *)
let contract_has_state ({ N.oracles; N.equations; N.contract } as node) =
  N.is_function node
  && contract <> None
  &&
  let sofar =
    match contract with
    | Some { C.sofar_assump = Some sv } -> Some sv
    | _ -> None
  in
  let is_sofar sv =
    match sofar with
    | Some sv' -> StateVar.equal_state_vars sv sv'
    | None -> false
  in
  oracles <> []
  || List.exists
       (fun ((sv, _), e) -> not (is_sofar sv) && expr_has_state e)
       equations

let applies in_sys param =
  let scope = (A.info_of_param param).A.top in
  match NI.get_node_type (ISys.get_node_id in_sys scope) with
  | NI.Component when not (ISys.is_lemma in_sys scope) -> (
    match ISys.get_lustre_node in_sys scope with
    | Some node -> contract_has_state node
    | None -> false
  )
  | _ -> false

(* ********************************************************************** *)
(* Contract system                                                        *)
(* ********************************************************************** *)

(* The system of the contract with the outputs of the function left free,
   the assumptions assumed, and the guarantees as properties. The function
   is imported, so its outputs are undefined when it is not abstract. Its
   signature is preserved: an input the contract does not mention is still
   an argument of the function.

   A fresh system is built for each analysis: the systems made from one
   with [TSys.set_subsystem_equations] share its properties, and the
   invariants an analysis proves of one candidate function would be taken
   to hold of the next. *)
let contract_system in_sys param =
  let info = A.info_of_param param in
  let param' =
    A.ContractCheck {
      info with
      A.uid = A.get_uid () ;
      A.abstraction_map = Scope.Map.add info.A.top false info.A.abstraction_map ;
    }
  in
  let sys, _ =
    ISys.trans_sys_of_analysis
      ~preserve_sig:true ~add_functional_constraints:false in_sys param'
  in
  param', sys

(* The engines the contract system is checked with *)
let modules = [`BMC; `IND; `IC3]

(* The guarantees of the contract system. Its other properties, such as
   the reachability of the modes, do not constrain the outputs. *)
let guarantees sys =
  TSys.get_real_properties sys
  |> List.filter (fun { Property.prop_kind } -> prop_kind = Property.Invariant)

(* Check the properties of [sys] with [analyze], and return the
   counterexamples of the falsified ones, or [None] if a property is left
   undecided *)
let check_properties analyze in_sys param sys =
  TSys.get_real_properties sys
  |> List.iter (fun { Property.prop_name } -> TSys.set_prop_unknown sys prop_name) ;
  let old_log_level = Lib.get_log_level () in
  Lib.set_log_level L_off ;
  (try analyze false modules in_sys param sys
   with e -> Lib.set_log_level old_log_level ; raise e) ;
  Lib.set_log_level old_log_level ;
  guarantees sys
  |> List.fold_left (fun acc { Property.prop_status } ->
    match acc, prop_status with
    | None, _ -> None
    | Some cexs, Property.PropFalse cex -> Some (cex :: cexs)
    | Some cexs, Property.PropInvariant _ -> Some cexs
    | Some _, _ -> None)
    (Some [])

(* ********************************************************************** *)
(* Traces and points                                                      *)
(* ********************************************************************** *)

let term_of_value = function
  | Model.Term t -> t
  | Model.Lambda _ | Model.Map _ ->
    raise (Unsupported "an input of the function is not of a scalar type")

(* Evaluate a closed term to a constant *)
let eval t =
  Eval.eval_term [] (Var.VarHashtbl.create 0) t |> Eval.term_of_value

(* A trace with its length, which a function without inputs needs *)
type sized_trace = int * trace

(* The restriction of a counterexample to the environment variables *)
let trace_of_cex env cex : sized_trace =
  let length =
    match cex with
    | (_, values) :: _ -> List.length values
    | [] -> 0
  in
  length,
  env |> List.map (fun sv ->
    match List.find_opt (fun (sv', _) -> StateVar.equal_state_vars sv sv') cex with
    | Some (_, values) -> sv, values
    | None ->
      raise (Unsupported "a counterexample has no value for an input"))

let length_of_trace ((n, _) : sized_trace) = n

(* The values of the variables [svs] of [trace] at instant [i] *)
let values_at ((_, trace) : sized_trace) svs i =
  svs |> List.map (fun sv ->
    let _, values =
      List.find (fun (sv', _) -> StateVar.equal_state_vars sv sv') trace
    in
    List.nth values i |> term_of_value |> eval)

(* ********************************************************************** *)
(* Refutation query                                                       *)
(* ********************************************************************** *)

let add_uf = function
  | `Inferred l -> `Inferred (TermLib.FeatureSet.add TermLib.UF l)
  | l -> l

(* The constraints of a trace starting at offset [base]: the system is
   unrolled along the trace, the environment has the values of the trace,
   the outputs are the uninterpreted functions [ufs] of the inputs, and the
   guarantees hold *)
let constraints_of_trace sys env inputs ufs base trace =
  let n = length_of_trace trace in
  let at i = Numeral.of_int (base + i) in
  let var sv i = Term.mk_var (Var.mk_state_var_instance sv (at i)) in
  List.init n (fun i ->
    let unrolling =
      if i = 0 then TSys.init_of_bound None sys (at 0)
      else TSys.trans_of_bound None sys (at i)
    in
    let env_eqs =
      List.map2
        (fun sv v -> Term.mk_eq [var sv i; v])
        env (values_at trace env i)
    in
    let x = values_at trace inputs i in
    let out_eqs =
      List.map (fun (y, uf) -> Term.mk_eq [var y i; Term.mk_uf uf x]) ufs
    in
    let props =
      guarantees sys
      |> List.map (fun { Property.prop_term } ->
        Term.bump_state (at i) prop_term)
    in
    unrolling :: env_eqs @ out_eqs @ props)
  |> List.flatten
  |> Term.mk_and

type query_result =
  | Points of (Term.t list * Term.t list) list
  (* The values of the outputs at the distinct inputs of the traces *)
  | Refuted of sized_trace list
  (* A subset of the traces no function satisfies the contract on *)

(* Whether some function satisfies the contract of [sys] on each of the
   [traces] *)
let solve_query sys env inputs outputs traces =
  let total = List.fold_left (fun acc t -> acc + length_of_trace t) 0 traces in
  let solver =
    SMTSolver.create_instance
      ~produce_models:true
      ~produce_unsat_assumptions:true
      (add_uf (TSys.get_logic sys))
      (Flags.Smt.solver ())
  in
  Fun.protect ~finally:(fun () -> SMTSolver.delete_instance solver) (fun () ->
    SMTSolver.trace_comment solver "Function realizability: refutation query" ;
    TSys.define_and_declare_of_bounds
      sys
      (SMTSolver.define_fun solver)
      ~define_rec:(SMTSolver.define_funs_rec solver)
      (SMTSolver.declare_fun solver)
      (SMTSolver.declare_sort solver)
      Numeral.zero (Numeral.of_int (max 0 (total - 1))) ;
    TSys.assert_global_constraints sys (SMTSolver.assert_term solver) ;
    let ufs =
      outputs |> List.map (fun y ->
        let uf =
          UfSymbol.mk_fresh_uf_symbol
            (List.map StateVar.type_of_state_var inputs)
            (StateVar.type_of_state_var y)
        in
        SMTSolver.declare_fun solver uf ;
        y, uf)
    in
    (* Each trace is asserted under an activation literal, so that the
       certificate can be minimized *)
    let actlits, _ =
      List.fold_left (fun (acc, base) trace ->
        let actlit = Actlit.fresh_actlit () in
        SMTSolver.declare_fun solver actlit ;
        let act = Actlit.term_of_actlit actlit in
        SMTSolver.assert_term solver
          (Term.mk_implies
             [act; constraints_of_trace sys env inputs ufs base trace]) ;
        (act, trace) :: acc, base + length_of_trace trace)
        ([], 0) traces
    in
    let actlits = List.rev actlits in
    let points =
      traces
      |> List.concat_map (fun trace ->
        List.init (length_of_trace trace) (values_at trace inputs))
      |> List.sort_uniq (List.compare Term.compare)
    in
    let point_terms =
      points |> List.concat_map (fun x ->
        List.map (fun (_, uf) -> Term.mk_uf uf x) ufs)
    in
    let sat = SMTSolver.check_sat_assuming_and_get_term_values solver
      (fun _ values ->
        let value t = List.assoc t values |> eval in
        Some (points |> List.map (fun x ->
          x, List.map (fun (_, uf) -> value (Term.mk_uf uf x)) ufs)))
      (fun _ -> None)
      (List.map fst actlits)
      point_terms
    in
    match sat with
    | Some points -> Points points
    | None ->
      (* Remove the traces the refutation does not need *)
      let is_unsat = function
        | [] -> false (* Every function satisfies the contract on no trace *)
        | acts ->
          SMTSolver.check_sat_assuming solver
            (fun _ -> false) (fun _ -> true) (List.map fst acts)
      in
      let core =
        List.fold_left (fun kept a ->
          let without = List.filter (fun a' -> a' != a) kept in
          if is_unsat without then without else kept)
          actlits actlits
      in
      Refuted (List.map snd core)
  )

(* ********************************************************************** *)
(* Generalization                                                         *)
(* ********************************************************************** *)

(* The subterms of [t] *)
let rec subterms acc t =
  let acc = t :: acc in
  match Term.destruct t with
  | Term.T.App (_, args) -> List.fold_left subterms acc args
  | Term.T.Var _ | Term.T.Const _ -> acc
  | exception _ -> acc

(* The subterms of the equations of [node] whose only variables are the
   current values of [inputs], with the current instant at offset zero *)
let contract_terms node inputs =
  let is_input_var v =
    Var.is_state_var_instance v
    && Numeral.equal (Var.offset_of_state_var_instance v) Numeral.zero
    && List.exists
         (StateVar.equal_state_vars (Var.state_var_of_state_var_instance v))
         inputs
  in
  node.N.equations
  |> List.concat_map (fun (_, e) ->
    [ E.base_term_of_expr Numeral.zero (E.init_expr e) ;
      E.cur_term_of_expr Numeral.zero (E.step_expr e) ])
  |> List.fold_left subterms []
  |> List.filter (fun t ->
    let vars = Term.vars_of_term t in
    not (VS.is_empty vars) && VS.for_all is_input_var vars)
  |> List.sort_uniq Term.compare

let input_vars inputs =
  List.map (fun sv -> Var.mk_state_var_instance sv Numeral.zero) inputs

(* The value of [t] at the point [x] of the inputs *)
let eval_at inputs t x =
  eval (Term.apply_subst (List.combine (input_vars inputs) x) t)

(* The guards of the decision lists: the Boolean terms of the contract over
   the inputs and the Boolean inputs, with their negations, and, for each
   numeric input, a threshold at each value of the points *)
let guards_of terms inputs points =
  let inputs_vars = input_vars inputs in
  let atoms =
    List.filter (fun t -> Type.is_bool (Term.type_of_term t)) terms
    @ List.filter_map (fun v ->
      if Type.is_bool (Var.type_of_var v) then Some (Term.mk_var v) else None)
      inputs_vars
  in
  let thresholds =
    List.mapi (fun k v ->
      let ty = Var.type_of_var v in
      if Type.is_int ty || Type.is_int_range ty || Type.is_real ty then
        points
        |> List.map (fun (x, _) -> List.nth x k)
        |> List.sort_uniq Term.compare
        |> List.map (fun c -> Term.mk_leq [Term.mk_var v; c])
      else [])
      inputs_vars
    |> List.flatten
  in
  atoms @ List.map Term.mk_not atoms @ thresholds

(* The leaves of the decision list of an output of type [ty]: the inputs
   and the terms of the contract of that type, and the values of the output
   at the points *)
let leaves_of terms inputs ty values =
  let fits t = Type.check_type (Term.type_of_term t) ty in
  List.filter fits (List.map Term.mk_var (input_vars inputs))
  @ List.filter fits terms
  @ List.sort_uniq Term.compare values

(* A decision list [if g1 then e1 elif ... else en] that has the value [b]
   at each point [(a, b)] of [points]. A guard selects some of the points
   not selected yet, and its leaf has their values. The guard of a single
   point, the conjunction of the equalities of the inputs to its values,
   always selects it, so a decision list is always found. *)
let decision_list inputs guards leaves points =
  let inputs_vars = input_vars inputs in
  let fits e (a, b) = Term.equal (eval_at inputs e a) b in
  let holds g (a, _) = Term.equal (eval_at inputs g a) Term.t_true in
  let cube (a, _) =
    Term.mk_and
      (List.map2 (fun v c -> Term.mk_eq [Term.mk_var v; c]) inputs_vars a)
  in
  let rec loop remaining rules =
    match List.find_opt (fun e -> List.for_all (fits e) remaining) leaves with
    | Some e ->
      List.fold_left (fun f (g, e') -> Term.mk_ite g e' f) e rules
    | None ->
      let candidates =
        List.map (fun g -> g, List.filter (holds g) remaining) guards
        @ List.map (fun p -> cube p, [p]) remaining
      in
      let best =
        List.fold_left (fun best (g, selected) ->
          if selected = [] then best
          else
            match List.find_opt (fun e -> List.for_all (fits e) selected) leaves with
            | None -> best
            | Some e ->
              match best with
              | Some (_, _, n) when n >= List.length selected -> best
              | _ -> Some (g, e, List.length selected))
          None candidates
      in
      match best with
      | None -> assert false
      | Some (g, e, _) ->
        let remaining = List.filter (fun p -> not (holds g p)) remaining in
        loop remaining ((g, e) :: rules)
  in
  loop points []

(* A total function with the values of the outputs at the [points] *)
let generalize node inputs outputs points =
  let terms = contract_terms node inputs in
  List.mapi (fun k y ->
    let points_y = List.map (fun (a, b) -> a, List.nth b k) points in
    let guards = guards_of terms inputs points_y in
    let leaves =
      leaves_of terms inputs (StateVar.type_of_state_var y) (List.map snd points_y)
    in
    y, decision_list inputs guards leaves points_y)
    outputs

(* The contract system with the outputs defined by [witness], and, if
   [restrict] is given, the inputs restricted to its points *)
let with_outputs ?restrict inputs sys witness =
  let scope = TSys.scope_of_trans_sys sys in
  let at off t = Term.bump_state off t in
  let eqs off =
    witness
    |> List.map (fun (y, f) ->
      Term.mk_eq [Term.mk_var (Var.mk_state_var_instance y off); at off f])
  in
  let restriction off =
    match restrict with
    | None -> []
    | Some points ->
      [ points
        |> List.map (fun x ->
          Term.mk_and
            (List.map2
               (fun v c -> Term.mk_eq [Term.mk_var v; c])
               (input_vars inputs) x))
        |> Term.mk_or
        |> at off ]
  in
  let constraints off = Term.mk_and (eqs off @ restriction off) in
  let _, init, trans = TSys.init_trans_open sys in
  TSys.set_subsystem_equations sys scope
    (Term.mk_and [init; constraints TSys.init_base])
    (Term.mk_and [trans; constraints TSys.trans_base])

(* ********************************************************************** *)
(* Check                                                                  *)
(* ********************************************************************** *)

let check analyze in_sys param =
  let scope = (A.info_of_param param).A.top in
  let node =
    match ISys.get_lustre_node in_sys scope with
    | Some node -> node
    | None -> assert false
  in
  try
    (* The system the refutation queries unroll, which is never analyzed *)
    let _, sys = contract_system in_sys param in
    let in_sys_vars = SVS.of_list (TSys.state_vars sys) in
    if SVS.exists StateVar.is_const in_sys_vars then
      raise (Unsupported "the contract has constant streams") ;
    let present svs = List.filter (fun sv -> SVS.mem sv in_sys_vars) svs in
    let inputs = present (D.values node.N.inputs) in
    let outputs = present (D.values node.N.outputs) in
    let env = inputs in
    if List.exists
         (fun sv -> Type.is_array (StateVar.type_of_state_var sv))
         (inputs @ outputs)
    then raise (Unsupported "an input or output is of an array type") ;
    let traces_of_cexs = List.map (trace_of_cex env) in
    let check_with_outputs ?restrict witness =
      let param', sys' = contract_system in_sys param in
      check_properties analyze in_sys param'
        (with_outputs ?restrict inputs sys' witness)
    in
    (* A candidate is checked first with the inputs restricted to the points
       of the traces. A counterexample then goes through points whose
       outputs other traces already constrain, and is more likely to
       conflict with them: the values a model checker picks for the inputs
       of a counterexample would otherwise seldom repeat. A candidate is
       only found to realize the contract by the check without the
       restriction. *)
    let check_candidate points witness =
      match
        if inputs = [] then Some []
        else check_with_outputs ~restrict:(List.map fst points) witness
      with
      | Some (_ :: _) as cexs -> cexs
      | Some [] | None -> check_with_outputs witness
    in
    let rec loop traces iter =
      if iter > Flags.Contracts.function_realizability_iter () then Unknown
      else
        match solve_query sys env inputs outputs traces with
        | Refuted traces -> Unrealizable traces
        | Points points ->
          let witness = generalize node inputs outputs points in
          KEvent.log L_info "Function realizability: candidate %d:@ %a" iter
            (Lib.pp_print_list
               (fun fmt (y, f) ->
                 Format.fprintf fmt "%a = %a"
                   StateVar.pp_print_state_var y
                   (ISys.pp_print_term_as_expr in_sys sys) f)
               ";@ ")
            witness ;
          match check_candidate points witness with
          | None -> Unknown
          | Some [] -> Realizable witness
          | Some cexs -> loop (traces @ traces_of_cexs cexs) (iter + 1)
    in
    (* The initial traces are the inputs of the counterexamples of the
       guarantees with the outputs left free *)
    match check_with_outputs [] with
    | None -> Unknown
    | Some [] -> Realizable []
    | Some cexs -> loop (traces_of_cexs cexs) 1
  with Unsupported msg ->
    KEvent.log L_note
      "Realizability by a function was not checked: %s." msg ;
    Unknown

let pp_print_witness in_sys sys fmt witness =
  Format.fprintf fmt "@[<v>%a@]"
    (Lib.pp_print_list
       (fun fmt (y, f) ->
         Format.fprintf fmt "@[<hov 2>%s =@ %a@]"
           (StateVar.name_of_state_var y)
           (ISys.pp_print_term_as_expr in_sys sys) f)
       "@,")
    witness

(* The values of an input of a certificate *)
let pp_print_values fmt (sv, values) =
  let as_type = StateVar.type_of_state_var sv in
  Lib.pp_print_list (Model.pp_print_value ~as_type) " " fmt values

let pp_print_certificate_pt fmt traces =
  Format.fprintf fmt
    "@[<hov>No function satisfies the contract on all of the following \
     input traces, since the outputs of a function only depend on its \
     current inputs.@]@.@." ;
  List.iteri (fun i (n, trace) ->
    Format.fprintf fmt "@[<v 2>Conflicting input trace %d (%d step%s):%a@]@.@."
      (i + 1) n (if n = 1 then "" else "s")
      (fun fmt -> List.iter (fun (sv, values) ->
         Format.fprintf fmt "@,%a: %a"
           (E.pp_print_lustre_var false) sv pp_print_values (sv, values)))
      trace)
    traces

let pp_print_certificate_json fmt traces =
  let pp_input fmt (sv, values) =
    let as_type = StateVar.type_of_state_var sv in
    Format.fprintf fmt "{\"name\" : \"%a\", \"values\" : [%a]}"
      (E.pp_print_lustre_var false) sv
      (Lib.pp_print_list (Model.pp_print_value_json ~as_type) ", ") values
  in
  Format.fprintf fmt "[@[<v 1>%a@]]"
    (Lib.pp_print_list
       (fun fmt (n, trace) ->
         Format.fprintf fmt "{\"length\" : %d, \"inputs\" : [%a]}"
           n (Lib.pp_print_list pp_input ", ") trace)
       ",@,")
    traces

let pp_print_certificate_xml fmt traces =
  List.iter (fun (n, trace) ->
    Format.fprintf fmt "@,@[<v 2><ConflictingInputTrace length=\"%d\">%a@]@,</ConflictingInputTrace>"
      n
      (fun fmt -> List.iter (fun (sv, values) ->
         let as_type = StateVar.type_of_state_var sv in
         Format.fprintf fmt "@,<Input name=\"%a\">%a</Input>"
           (E.pp_print_lustre_var false) sv
           (Lib.pp_print_list (Model.pp_print_value_xml ~as_type) " ") values))
      trace)
    traces
