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

module SSet = Set.Make (String)

(* The functions whose cutoff a counterexample reached, and that are below
   the limit *)
let requested_functions = ref Scope.Set.empty

(* The instances of the recursive functions in the system the engines run
   on, and in the one before it: how fast the unrollings multiply them *)
let current_count = ref 0
let previous_count = ref 0

(* The properties whose counterexample reached the cutoff of a function at
   the limit *)
let exhausted = ref SSet.empty

(* The properties falsified by a counterexample that the recursive functions
   as they are, rather than their contracts, violate the property with: the
   counterexample executes instances of the functions that their contracts
   abstract, and does not rely on outputs the functions do not have *)
let genuine_props = ref SSet.empty

(* The functions at the limit whose cutoff a counterexample reached, and
   that were reported *)
let reported = ref Scope.Set.empty

let depth param f =
  match Analysis.param_unrollings_of_scope param f with
  | Some n -> n
  | None -> 1

(* The time given to the solver for a query, in seconds *)
let query_timeout = 2

(* The time given to the solver to evaluate a function at concrete
   arguments, in milliseconds: a call is cheap to evaluate, or it is deep
   enough that the time it takes grows faster than its depth *)
let evaluation_timeout = 500

(* The time the checks of the counterexamples of a round may take in all,
   in seconds. A check may be undecidable in practice, for a function that
   is expensive to evaluate, such as Ackermann's, and every counterexample
   of a round tends to need the same evaluations: past this budget, the
   counterexamples of the round are left undecided without a check, which
   is the safe answer, rather than each costing its timeouts. *)
let round_budget = 5.

(* The time the checks of the round took so far *)
let round_time = ref 0.

(* The solver the queries of a round are put to: one per round, with the
   system declared and its initial state asserted once, and every query
   under a push and a pop. A query is a whole system to send to a solver,
   and a round can bring dozens of counterexamples at once: starting a
   solver for each took longer than the analysis itself, and on a slow
   machine longer than the wall clock timeout. A solver that takes a
   timeout per query keeps the round's queries; one that does not is
   started for every query, with its own timeout, and dies with it. *)
type round_solver = {
  solver : SMTSolver.t ;
  (* The state variables are declared up to this bound *)
  mutable declared_to : Numeral.t ;
  (* Whether the solver takes a timeout per query, and is kept for the
     round *)
  kept : bool ;
}

let round_solver : round_solver option ref = ref None

(* The values of the recursive functions at the concrete arguments the
   supervisor evaluated them at in the round, by functional symbol and
   arguments: facts about the functions, which every query of the round is
   given *)
module FactKey = struct
  type t = UfSymbol.t * Term.t list
  let equal (f, a) (g, b) =
    UfSymbol.equal_uf_symbols f g && List.equal Term.equal a b
  let hash (f, a) =
    Hashtbl.hash (UfSymbol.hash_uf_symbol f, List.map Term.hash a)
end
module Facts = Hashtbl.Make (FactKey)
let facts : Term.t Facts.t = Facts.create 64

(* The calls of the round whose function's defining equation is
   instantiated at their arguments in the round's solver, and the
   applications of the defined functions in those instances, each with
   the condition under which the instance executes it *)
let instantiated : Term.t Facts.t = Facts.create 16
let pending : (UfSymbol.t * Term.t list * Term.t) list ref = ref []

(* The applications of the defined symbols in a term, each with the
   condition under which the term executes it: the conditions of the
   branches of the if-then-elses it is under. The let bindings the
   applications are under are substituted into their arguments and
   conditions, which are terms whose values are asked of the solver, and
   the solver knows nothing of the variables the lets bind. An application
   under a quantifier, whose arguments are not closed, is left out.

   An application on a branch the model does not take is not executed,
   and must not be evaluated: the branch that ends the recursion of a
   function applies it again on the other branch, at arguments the
   recursion never reaches, and evaluating the function there would go on
   past the end of the recursion.

   The definition of a function that is neither recursive nor imported,
   among [helpers], is given to the solver (see
   [TransSys.define_and_declare_of_bounds]), and its application is not
   evaluated: the applications it executes are those in the body of its
   definition at its arguments, as when the definitions that call it
   inlined its body. *)
let rec applications helpers definitions term =
  let definition uf =
    List.find_opt (fun (uf', _, _) -> UfSymbol.equal_uf_symbols uf uf') definitions
  in
  let defined uf = Option.is_some (definition uf) in
  let helper uf = List.exists (UfSymbol.equal_uf_symbols uf) helpers in
  (* The applications the body of a helper executes at closed arguments *)
  let of_helper uf args =
    match definition uf with
    | Some (_, formals, body) ->
      Term.apply_subst (List.combine formals args) body
      |> applications helpers definitions
      |> List.map (fun (uf, args, guard) -> (uf, args, [ guard ]))
    | None -> []
  in
  let closed t = Var.VarSet.is_empty (Term.vars_of_term t) in
  let add calls ((uf, args, guard) as call) =
    if List.exists
         (fun (uf', args', guard') ->
            FactKey.equal (uf, args) (uf', args')
            && List.equal Term.equal guard guard')
         calls
    then calls
    else call :: calls
  in
  let under cond calls =
    List.map (fun (uf, args, guard) -> (uf, args, cond :: guard)) calls
  in
  Term.eval_t ~fail_on_quantifiers:false
    (fun flat calls ->
       match flat, calls with
       | Term.T.App (s, [ cond ; _ ; _ ]), [ in_cond ; in_then ; in_else ]
         when Symbol.equal_symbols s Symbol.s_ite ->
         if closed cond then
           List.fold_left add in_cond
             (under cond in_then @ under (Term.mk_not cond) in_else)
         else
           List.fold_left add in_cond (in_then @ in_else)
       | Term.T.App (s, args), _ ->
         let calls = List.fold_left (List.fold_left add) [] calls in
         if Symbol.is_uf s && List.for_all closed args then
           let uf = Symbol.uf_of_symbol s in
           if helper uf then List.fold_left add calls (of_helper uf args)
           else if defined uf then add calls (uf, args, [])
           else calls
         else calls
       | Term.T.Const s, _
         when Symbol.is_uf s && helper (Symbol.uf_of_symbol s) ->
         of_helper (Symbol.uf_of_symbol s) []
       | _, calls -> List.concat calls)
    term
  |> List.map (fun (uf, args, guard) -> (uf, args, Term.mk_and guard))

let fact_term (uf, args) value = Term.mk_eq [ Term.mk_uf uf args ; value ]

(* The evaluator of the functions: their definitions, and nothing of the
   system but its sorts (see [FunEval]) *)
let evaluator : FunEval.t option ref = ref None

let drop_round_solver () =
  ( match !round_solver with
    | Some { solver } -> (try SMTSolver.delete_instance solver with _ -> ())
    | None -> () ) ;
  round_solver := None

let drop_evaluator () =
  Option.iter FunEval.delete !evaluator ;
  evaluator := None

let set_per_query_timeout solver =
  FunEval.set_per_query_timeout ~ms:(query_timeout * 1000) solver

(* The value of the functional symbol at the concrete arguments (see
   [FunEval.evaluate]) *)
let evaluate sys uf args =
  let evaluator =
    match !evaluator with
    | Some evaluator -> evaluator
    | None ->
      let features =
        match TransSys.get_logic sys with
        | `Inferred features -> features
        | _ -> TermLib.FeatureSet.empty
      in
      let logic =
        `Inferred
          TermLib.FeatureSet.(
            features |> add TermLib.UF |> add TermLib.Q |> add TermLib.RF)
      in
      let e =
        FunEval.create ~logic ~timeout_ms:evaluation_timeout (fun solver ->
          TransSys.define_check_defs sys
            ~define_rec:(SMTSolver.define_funs_rec solver)
            (SMTSolver.declare_fun solver)
            (SMTSolver.declare_sort solver))
      in
      evaluator := Some e ;
      e
  in
  FunEval.evaluate evaluator uf args

(* The solver for a query on a counterexample of length [k + 1] of the
   system: the one of the round if there is one, with the state variables
   declared up to [k] if they were not, or a new one *)
let solver_for sys k =
  match !round_solver with
  | Some ({ solver ; declared_to ; kept = true } as rs) when Numeral.(declared_to < k) ->
    TransSys.declare_vars_of_bounds sys (SMTSolver.declare_fun solver)
      Numeral.(succ declared_to) k ;
    rs.declared_to <- k ;
    rs
  | Some ({ kept = true } as rs) -> rs
  | _ ->
    drop_round_solver () ;
    let logic = TransSys.get_logic sys in
    let solver =
      SMTSolver.create_instance ~produce_models:true logic (Flags.Smt.solver ())
    in
    let kept = set_per_query_timeout solver in
    let solver =
      if kept then solver
      else (
        SMTSolver.delete_instance solver ;
        SMTSolver.create_instance ~timeout:query_timeout ~produce_models:true
          logic (Flags.Smt.solver ()))
    in
    TransSys.define_and_declare_of_bounds ~with_check_ufs:true sys
      (SMTSolver.define_fun solver)
      ~define_rec:(SMTSolver.define_funs_rec solver)
      (SMTSolver.declare_fun solver)
      (SMTSolver.declare_sort solver)
      Numeral.zero k ;
    TransSys.assert_global_constraints sys (SMTSolver.assert_term solver) ;
    TransSys.init_of_bound (Some (SMTSolver.declare_fun solver)) sys Numeral.zero
    |> SMTSolver.assert_term solver ;
    (* The values of the functions known in the round, and the defining
       equations instantiated in it *)
    Facts.iter
      (fun call value -> SMTSolver.assert_term solver (fact_term call value))
      facts ;
    Facts.iter (fun _ equation -> SMTSolver.assert_term solver equation)
      instantiated ;
    let rs = { solver ; declared_to = k ; kept } in
    round_solver := Some rs ;
    rs

let reset () =
  round_time := 0. ;
  drop_round_solver () ;
  drop_evaluator () ;
  Facts.reset facts ;
  Facts.reset instantiated ;
  pending := [] ;
  requested_functions := Scope.Set.empty ;
  exhausted := SSet.empty ;
  genuine_props := SSet.empty ;
  reported := Scope.Set.empty ;
  current_count := 0 ;
  previous_count := 0

let start_round sys =
  round_time := 0. ;
  drop_round_solver () ;
  drop_evaluator () ;
  Facts.reset facts ;
  Facts.reset instantiated ;
  pending := [] ;
  requested_functions := Scope.Set.empty ;
  previous_count := !current_count ;
  current_count :=
    List.fold_left
      (fun n f -> n + TransSys.count_instances sys f)
      0 (TransSys.cutoff_functions sys)

(* Whether unrolling further is expected to exceed the number of instances
   allowed: the instances of the recursive functions, counted together
   since the unrolling of one multiplies the instances of the functions it
   calls, are expected to multiply as they did over the last unrolling, or
   to double when there was none yet *)
let too_many_instances () =
  let c = !current_count and p = !previous_count in
  let expected = if p > 0 && c > p then c * c / p else 2 * c in
  expected > Flags.Contracts.rec_instances ()

let request param prop reached =
  let limit = Flags.Contracts.rec_unrollings () in
  let too_many = too_many_instances () in
  let below, at_limit =
    List.partition
      (fun f -> depth param f < limit && not too_many)
      reached
  in
  match below with
  | [] ->
    exhausted := SSet.add prop !exhausted ;
    let unreported =
      List.filter (fun f -> not (Scope.Set.mem f !reported)) at_limit
    in
    reported :=
      List.fold_left (fun s f -> Scope.Set.add f s) !reported unreported ;
    `At_limit
      (List.partition (fun f -> depth param f < limit) unreported)
  | _ ->
    requested_functions :=
      List.fold_left (fun s f -> Scope.Set.add f s) !requested_functions below ;
    `Requested

let requested () = Scope.Set.elements !requested_functions

(* The number of times the calls past the unrollings a model uses are
   evaluated before the counterexample is given up on as undecided *)
let max_evaluation_rounds = 8

(* Whether the counterexample is genuine. The system is unrolled along the
   counterexample, its inputs and constants are fixed to the values of the
   counterexample, and the property is asserted to fail at the last step.
   The outputs of the calls past the unrollings are then free, and the
   query asks whether the property can fail with them; if it cannot, the
   counterexample is not genuine. If it can, the calls the model executes
   are at concrete arguments, which the functions are evaluated at; their
   values are given to the query as facts, and the query is put again,
   until the model only executes calls whose values are facts, and the
   counterexample is genuine: the functions as they are violate the
   property with these inputs. A call may be what the path relies on, such
   as an assumption of the top node, and not only the property, which is
   why the facts are about the calls and not about the property.

   A query the solver cannot decide in time, a call that cannot be
   evaluated, or too many rounds of evaluation, leave the counterexample
   undecided, and it is not taken as genuine: it is not reported, and the
   function is unrolled further.

   With [~abstracted:true], the calls whose values are evaluated include
   those of the instances that the contracts of their functions abstract,
   whose outputs are constrained by the contracts only, besides the calls
   past the unrollings. *)
let genuine ?(abstracted = false) sys prop cex =
  let path = Model.path_of_list cex in
  let k = Numeral.of_int (Model.path_length path - 1) in
  let steps = List.init (Numeral.to_int k + 1) Numeral.of_int in
  let instances =
    TransSys.cutoff_instances sys
    @ (if abstracted then TransSys.abstracted_instances sys else [])
  in
  let evaluable =
    TransSys.evaluable_functions sys
    @ (if abstracted then TransSys.abstracted_evaluable_functions sys else [])
  in
  let definitions = TransSys.check_definitions sys in
  let helpers = TransSys.check_helper_symbols sys in
  (* A system sliced to the property may not have all the variables of the
     counterexample, which was found on the whole system: the others are
     not in the cone of influence of the property *)
  let state_vars = StateVar.StateVarSet.of_list (TransSys.state_vars sys) in
  let var_at sv i = Term.mk_var (Var.mk_state_var_instance sv i) in
  (* The terms whose values tell the calls the model executes *)
  let observed () =
    List.concat_map
      (fun i ->
         List.concat_map
           (fun (_, active, inputs, _) ->
              Term.bump_state i active :: List.map (fun sv -> var_at sv i) inputs)
           instances)
      steps
    @ List.concat_map (fun (_, args, guard) -> guard :: args) !pending
  in
  (* The calls the model executes that are not facts yet, or [None] if one
     of them cannot be evaluated: those of the instances past the
     unrollings, and those the instantiated definitions apply *)
  let new_calls values =
    let value_of t = List.find_opt (fun (t', _) -> Term.equal t t') values in
    let known call =
      Facts.mem facts call || Facts.mem instantiated call
    in
    let from_pending =
      List.fold_left
        (fun acc (uf, args, guard) ->
           match acc with
           | None -> None
           | Some calls ->
             match value_of guard with
             | None -> None
             | Some (_, v) when not (Term.equal v Term.t_true) -> Some calls
             | Some _ ->
             let args = List.map value_of args in
             if List.exists Option.is_none args then None
             else
               let call = (uf, List.map (fun a -> snd (Option.get a)) args) in
               if known call || List.exists (FactKey.equal call) calls
               then Some calls
               else Some (call :: calls))
        (Some []) !pending
    in
    List.fold_left
      (fun acc i ->
         List.fold_left
           (fun acc (f, active, inputs, outputs) ->
              match acc with
              | None -> None
              | Some calls ->
                match value_of (Term.bump_state i active) with
                | Some (_, v) when Term.equal v Term.t_true ->
                  if not (List.exists (Scope.equal f) evaluable) then None
                  else
                    let args =
                      List.map
                        (fun sv ->
                           match value_of (var_at sv i) with
                           | Some (_, v) -> Some v
                           | None -> None)
                        inputs
                    in
                    if List.exists Option.is_none args then None
                    else
                      let args = List.map Option.get args in
                      Some
                        (List.fold_left
                           (fun calls (_, uf) ->
                              let call = (uf, args) in
                              if known call
                              || List.exists (FactKey.equal call) calls
                              then calls
                              else call :: calls)
                           calls outputs)
                | _ -> Some calls)
           acc instances)
      from_pending steps
  in
  (* The call is given its value if it has a unique one, or else the
     defining equation of its function is instantiated at its arguments,
     which shares the symbols of the definition the value depends on with
     the rest of the query; the calls the equation applies are then
     executed calls in turn *)
  let settle ((uf, args) as call) =
    match evaluate sys uf args with
    | `Unknown -> false
    | `Value value ->
      Facts.replace facts call value ;
      ( match !round_solver with
        | Some { solver } -> SMTSolver.assert_term solver (fact_term call value)
        | None -> () ) ;
      true
    | `Not_unique ->
      match
        List.find_opt
          (fun (uf', _, _) -> UfSymbol.equal_uf_symbols uf uf') definitions
      with
      | None -> false
      | Some (_, formals, body) ->
        let instance = Term.apply_subst (List.combine formals args) body in
        let equation = Term.mk_eq [ Term.mk_uf uf args ; instance ] in
        Facts.replace instantiated call equation ;
        ( match !round_solver with
          | Some { solver } -> SMTSolver.assert_term solver equation
          | None -> () ) ;
        pending := applications helpers definitions instance @ !pending ;
        true
  in
  let rec loop n =
    if n = 0 then `Undecided else
    let observed = observed () in
    let { solver ; kept } = solver_for sys k in
    SMTSolver.push solver ;
    let rec assert_trans i =
      if Numeral.(i <= k) then (
        TransSys.trans_of_bound (Some (SMTSolver.declare_fun solver)) sys i
        |> SMTSolver.assert_term solver ;
        assert_trans Numeral.(succ i))
    in
    assert_trans Numeral.one ;
    (* The inputs and the constants at every step of the counterexample *)
    cex |> List.iter (fun (sv, values) ->
      if (StateVar.is_input sv || StateVar.is_const sv)
      && StateVar.StateVarSet.mem sv state_vars then
        values |> List.iteri (fun i value ->
          match value with
          | Model.Term t ->
            Term.mk_eq [ var_at sv (Numeral.of_int i) ; t ]
            |> SMTSolver.assert_term solver
          | Model.Lambda _ | Model.Map _ -> ())) ;
    TransSys.get_prop_term sys prop
    |> Term.bump_state k
    |> Term.mk_not
    |> SMTSolver.assert_term solver ;
    let outcome =
      (* A query the solver gives up on in time leaves the solver as it
         was, for the next counterexample of the round, which saves
         sending it the whole system again *)
      try
        SMTSolver.check_sat_and_get_term_values solver
          (fun _ values -> `Sat values)
          (fun _ -> `Unsat)
          observed
      with SMTSolver.Unknown -> `Unknown
    in
    if kept then SMTSolver.pop solver else drop_round_solver () ;
    match outcome with
    | `Unknown -> `Undecided
    | `Unsat -> `Result false
    | `Sat values ->
      match (try new_calls values with Exit -> None) with
      | None -> `Undecided
      | Some [] -> `Result true
      | Some calls ->
        if List.for_all settle calls then loop (n - 1) else `Undecided
  in
  let result =
    try loop max_evaluation_rounds with
    | SMTSolver.Timeout ->
      (* The solver was killed on its timeout, the instance is gone *)
      round_solver := None ;
      `Undecided
    | SMTSolver.Unknown -> drop_round_solver () ; `Undecided
    | Failure _ | Unix.Unix_error _ | End_of_file | Sys_error _
    | SMTSolver.Exiting as e ->
      (* A solver that stops on its own timeout answers in its own way,
         which reads as a failure: the query is undecided, as well, and the
         solver is not to be trusted with the next one. Any other
         exception, the wall clock timeout first of all, is not about the
         query and goes on unwinding. *)
      KEvent.log L_debug
        "Query on the counterexample to %s failed: %s" prop
        (Printexc.to_string e) ;
      drop_round_solver () ;
      `Undecided
    | e ->
      drop_round_solver () ;
      raise e
  in
  match result with
  | `Result r -> r
  | `Undecided -> false

(* The recursive functions the counterexample to the property may be
   spurious for: a cutoff of theirs is reached, and the counterexample is
   not known to be genuine *)
let suspect sys prop cex =
  match TransSys.cutoffs_reached sys cex with
  | [] -> []
  | reached ->
    (* The functions are all to be unrolled further already: whether the
       counterexample is spurious or not, the engines run again on the
       system with them unrolled, and a genuine counterexample is found
       again there. The query is spared, which matters where every query
       is a solver process to start: a round that falsifies a hundred
       properties on their first counterexample would otherwise put a
       hundred queries to as many solvers before it ends. *)
    if List.for_all (fun f -> Scope.Set.mem f !requested_functions) reached
    then reached
    (* A function the supervisor has no definition of, because it is not
       definable or the solver does not take recursive definitions, cannot
       be evaluated: a counterexample that reaches its calls past the
       unrollings is never known to be genuine *)
    else
      let evaluable = TransSys.evaluable_functions sys in
      if not (List.for_all (fun f -> List.exists (Scope.equal f) evaluable) reached)
      then reached
      else if !round_time > round_budget then reached
      else (
        let started = Unix.gettimeofday () in
        let genuine =
          Fun.protect
            ~finally:(fun () ->
              round_time := !round_time +. (Unix.gettimeofday () -. started))
            (fun () -> genuine sys prop cex)
        in
        if genuine then [] else reached)

(* Run [f] with a round solver, an evaluator and tables of facts of its own,
   for a system other than the one of the round, whose symbols the round's
   solver and facts may not have, and restore those of the round after *)
let isolated f =
  let saved_solver = !round_solver
  and saved_evaluator = !evaluator
  and saved_facts = Facts.copy facts
  and saved_instantiated = Facts.copy instantiated
  and saved_pending = !pending in
  round_solver := None ;
  evaluator := None ;
  Facts.reset facts ;
  Facts.reset instantiated ;
  pending := [] ;
  Fun.protect
    ~finally:(fun () ->
      drop_round_solver () ;
      drop_evaluator () ;
      round_solver := saved_solver ;
      evaluator := saved_evaluator ;
      Facts.reset facts ;
      Facts.iter (Facts.replace facts) saved_facts ;
      Facts.reset instantiated ;
      Facts.iter (Facts.replace instantiated) saved_instantiated ;
      pending := saved_pending)
    f

let check_abstractions ~sliced sys prop cex =
  if Flags.Contracts.compositional ()
  && Flags.modular ()
  && Flags.Contracts.refinement ()
  && TransSys.abstracted_instances sys = []
  then
    (* No recursive function is abstracted by its contract in the system,
       sliced as it is to what the properties depend on: refining one
       cannot change what the counterexample relies on *)
    genuine_props := SSet.add prop !genuine_props
  else if Flags.Contracts.compositional ()
  && Flags.modular ()
  && Flags.Contracts.refinement ()
  && !round_time <= round_budget
  then (
    let started = Unix.gettimeofday () in
    let genuine =
      Fun.protect
        ~finally:(fun () ->
          round_time := !round_time +. (Unix.gettimeofday () -. started))
        (fun () ->
           (* On the system sliced to the property, the counterexample only
              executes the calls the property depends on, or an assertion
              or an assumption does: a call it executes on the whole
              system, but that cannot change the answer, would leave it
              undecided if it cannot be evaluated *)
           match sliced () with
           | Some sliced_sys ->
             isolated (fun () -> genuine ~abstracted:true sliced_sys prop cex)
           | None -> genuine ~abstracted:true sys prop cex)
    in
    if genuine then genuine_props := SSet.add prop !genuine_props)

let genuine_properties () = SSet.elements !genuine_props

let is_exhausted prop = SSet.mem prop !exhausted

let all_settled sys =
  TransSys.get_properties sys
  |> List.for_all (fun ({ Property.prop_name ; Property.prop_status } as p) ->
    Property.is_candidate p
    || (match prop_status with
        | Property.PropInvariant _ | Property.PropFalse _ -> true
        | _ -> SSet.mem prop_name !exhausted))
