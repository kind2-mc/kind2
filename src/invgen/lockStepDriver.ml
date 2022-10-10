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


(** Lock Step Driver for graph-based invariant generation.

Provides structures to abstract SMT-solvers for the base / step case, as well
as trivial invariant pruning.

*)





(* |===| Aliases. *)

module Smt = SMTSolver
module Sys = TransSys
module Num = Numeral
module Uf = UfSymbol

type solver = Smt.t
type term = Term.t
type sys = Sys.t
type num = Num.t



(* |===| Helper functions. *)

let sys_name sys =
  Sys.scope_of_trans_sys sys |> Scope.to_string

(** Counter for actlit's uids. *)
let actlit_uid = ref 0

(** Maximal number of actlit created before solvers are reset. *)
let max_actlit_count_before_reset = 50

(** Indicates whether we should reset or not base on the number of actlits
created so far. *)
let shall_reset () = max_actlit_count_before_reset <= ! actlit_uid

(** Resets the actlit uid counter. BEWARE OF COLLISIONS. *)
let reset_actlit_uids () = actlit_uid := 0

(* Returns an actlit built from a uid. Beware of name collisions. *)
let fresh_actlit_of uid =
  UfSymbol.mk_uf_symbol (
    Format.sprintf "%%actlit_%d" uid
  ) [] (Type.mk_bool ())

(* Returns an actlit built from a uid. Beware of name collisions. *)
let fresh_actlit () =
  let fresh = ! actlit_uid |> fresh_actlit_of in
  actlit_uid := 1 + ! actlit_uid ;
  fresh

(* Returns the term corresponding to the input actlit. *)
let term_of_actlit actlit = Term.mk_uf actlit []




(* |===| Base checker.

The base checker is used to check whether some candidate invariants hold [k]
steps away from the initial state. *)


(** A base checker. *)
type base = {
  mutable solver: solver ;
  sys: sys ;
  mutable init_actlit: term ;
  k: num ;
}

(** Kills a base checker. *)
let kill_base { solver } = Smt.delete_instance solver

(** Creates a solver for the base case. *)
let mk_base_checker_solver sys k =
  let solver = (* Creating solver. *)
    Smt.create_instance ~produce_assignments: true
      (Sys.get_logic sys) (Flags.Smt.solver ())
  in


  Format.asprintf (* Logging stuff in smt trace. *)
    "[Base/Step] Setting up system [%s], k = %a."
    (sys_name sys) Num.pp_print_numeral k
  |> Smt.trace_comment solver ;


  let init_actlit = (* Creating actlit for initial predicate. *)
    fresh_actlit ()
  in

  Format.asprintf (* Logging stuff in smt trace. *)
    "Actlit for initial predicate: [%a]." Uf.pp_print_uf_symbol init_actlit
  |> Smt.trace_comment solver ;
  Smt.declare_fun solver init_actlit ;


  let init_actlit = (* Getting term of actlit UF. *)
    term_of_actlit init_actlit
  in


  (* Smt.trace_comment solver (* Logging stuff in smt trace. *)
     "Declaring system's constants." ;
     Sys.declare_const_vars sys (Smt.declare_fun solver) ; *)


  Smt.trace_comment solver (* Logging stuff in smt trace. *)
    "Declaring system's svars at [0]." ;
  Sys.define_and_declare_of_bounds
    sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.zero Numeral.zero ;


  Smt.trace_comment solver (* Logging stuff in smt trace. *)
    "Conditional initial predicate." ;

  Term.mk_implies (* Conditionally asserting the initial predicate. *)
    [ init_actlit ;
      Sys.init_of_bound (Some (SMTSolver.declare_fun solver)) sys Num.zero ]
  |> Smt.assert_term solver ;


  Smt.trace_comment solver (* Logging stuff in smt trace. *)
    "Asserting invariants at [0]." ;

  Sys.invars_of_bound
    ~one_state_only:true sys Numeral.zero (* Invariants at [0]. *)
  |> List.iter (Smt.assert_term solver) ;


  (* Unrolls the transition relation as needed. *)
  let rec unroll i =
    if Num.(i <= k) then (
      Format.asprintf "Declaring svars at [%a]." Num.pp_print_numeral i
      |> Smt.trace_comment solver ;
      Sys.declare_vars_of_bounds sys (Smt.declare_fun solver) i i ;

      Format.asprintf
        "Asserting transition relation at [%a]." Num.pp_print_numeral i
      |> Smt.trace_comment solver ;

      Sys.trans_of_bound (Some (SMTSolver.declare_fun solver)) sys i
      |> Smt.assert_term solver ;

      Format.asprintf
        "Asserting invariants at [%a]." Num.pp_print_numeral i
      |> Smt.trace_comment solver ;
      Sys.invars_of_bound sys i |> List.iter (Smt.assert_term solver) ;

      Num.succ i |> unroll
    )
  in

  (* Unroll from one to [k]. *)
  unroll Num.one ;

  solver, init_actlit

(** Creates a checker for the base case of invariant generation. *)
let mk_base_checker sys k =
  let solver, init_actlit = mk_base_checker_solver sys k in
  { solver ; sys ; init_actlit ; k }

(** Resets the solver in a base checker if needed. *)
let conditional_base_solver_reset (
  { solver ; sys ; k } as base_checker
) = if shall_reset () then (
  (* KEvent.log_uncond "[LSD] RESTARTING BASE" ; *)
  Smt.delete_instance solver ;
  reset_actlit_uids () ;
  let solver, init_actlit = mk_base_checker_solver sys k in
  base_checker.solver <- solver ;
  base_checker.init_actlit <- init_actlit
)

(** Adds invariants to a base checker. *)
let base_add_invariants t ts invs =
  let { solver ; k } = t in
  let eub = Num.succ k in (* Exclusive upper bound. *)
  invs |> (
    if ts then List.iter (Unroller.assert_1_to solver eub)
    else List.iter (Unroller.assert_0_to solver eub)
  )


(** Queries base, returns an option of the model. *)
let query_base base_checker candidates =
  (* Restarting solver if necessary. *)
  conditional_base_solver_reset base_checker ;

  let { sys ; solver ; k ; init_actlit } = base_checker in
  let actlit = fresh_actlit () in

  Format.asprintf
    "Querying base with actlit [%a] (%d candidates)."
    Uf.pp_print_uf_symbol actlit (List.length candidates)
  |> Smt.trace_comment solver ;

  Smt.declare_fun solver actlit ; (* Declaring actlit. *)

  let actlit = (* Getting term of actlit UF. *)
    term_of_actlit actlit
  in

  (* Conditionally asserting negation of candidates at [k+1]. *)
  Term.mk_implies [
    actlit ; Term.mk_and candidates |> Term.mk_not |> Term.bump_state k
  ] |> Smt.assert_term solver ;

  let res =
    Smt.check_sat_assuming solver (
      (* If sat, get model and return that. *)
      fun solver ->

        let minus_k = Numeral.(~- k) in
        (* Variables we want to know the value of. *)
        ( if Numeral.(equal k zero)
          then TransSys.vars_of_bounds sys k k
          else TransSys.vars_of_bounds sys (Numeral.pred k) k
        )
        (* Getting their value. *)
        |> SMTSolver.get_var_values solver
          (TransSys.get_state_var_bounds sys)
        (* Bumping to -k. *)
        |> Model.bump_var minus_k 
        (* Making an option out of it. *)
        |> (fun model -> Some model)
    ) (
      (* If unsat then no model. *)
      fun _ -> None
    ) [ init_actlit ; actlit ]
  in

  (* Deactivating actlit. *)
  Term.mk_not actlit |> Smt.assert_term solver ;

  res




(* |===| Step checker.

The step checker is used to check whether some candidate invariants hold in the
[k]-inductive step instance. *)


(* A step checker. *)
type step = {
  mutable solver: solver ;
  sys: sys ;
  k: num ;
}

(** Kills a step checker. *)
let kill_step { solver } = Smt.delete_instance solver

(** Transforms a base instance solver in a step instance solver. *)
let to_step_solver { solver ; sys ; k ; init_actlit } =
  Smt.trace_comment solver "Switching to step mode." ;

  Smt.trace_comment solver "Deactivating actlit for initial predicate." ;
  Term.mk_not init_actlit |> Smt.assert_term solver ;

  let kp1 = Num.succ k in

  Format.asprintf "Declaring svars at [%a]." Num.pp_print_numeral kp1
  |> Smt.trace_comment solver ;
  Sys.declare_vars_of_bounds sys (Smt.declare_fun solver) kp1 kp1  ;

  Format.asprintf
    "Asserting transition relation at [%a]." Num.pp_print_numeral kp1
  |> Smt.trace_comment solver ;
  Sys.trans_of_bound (Some (Smt.declare_fun solver)) sys kp1
  |> Smt.assert_term solver ;

  Format.asprintf
    "Asserting invariants at [%a]." Num.pp_print_numeral kp1
  |> Smt.trace_comment solver ;
  Sys.invars_of_bound sys kp1 |> List.iter (Smt.assert_term solver) ;

  solver, kp1

(** Transforms a base checker into a step checker. *)
let to_step ( { sys } as base_checker : base ) =
  let solver, k = to_step_solver base_checker in
  { solver ; sys ; k }

(** Certificate ([k]) of a step checker. *)
let step_cert { k } = 1 + Num.to_int k

(** Resets the solver in a step checker if needed. *)
let conditional_step_solver_reset (
  { solver ; sys ; k } as step_checker
) = if shall_reset () then (
  (* KEvent.log_uncond "[LSD] RESTARTING STEP" ; *)
  Smt.delete_instance solver ;
  reset_actlit_uids () ;
  let solver, _ = mk_base_checker sys Num.(pred k) |> to_step_solver in
  step_checker.solver <- solver
)


(** Adds invariants to a step checker. *)
let step_add_invariants t ts invs =
  let { solver ; k } = t in
  let eub = Num.succ k in (* Exclusive upper bound. *)
  invs |> (
    if ts then List.iter (Unroller.assert_1_to solver eub)
    else List.iter (Unroller.assert_0_to solver eub)
  )


(** Queries step.

[candidates] is a list of elements of type [(Term.t, 'a)]. The second element
is understood as some information about the candidate.

The "information" represented by ['a] is used when checking equality candidate
invariants coming from equivalence classes from the graph. The info is then a
pair representative / eq class member meaning that if the candidate is indeed
invariant, we can drop the class member from the equivalence class.

Returns the elements of [candidates] for which the first element of the pair
(the term) is an invariant. *)
let query_step two_state step_checker candidates =
  (* Format.printf "query_step (%d)@.@." (List.length candidates) ; *)

  let rec loop candidates =
    (* Restarting solver if necessary. *)
    conditional_step_solver_reset step_checker ;

    let { solver ; k } = step_checker in
    let actlit = fresh_actlit () in

    Format.asprintf
      "Querying step with actlit [%a] (%d candidates)."
      Uf.pp_print_uf_symbol actlit (List.length candidates)
    |> Smt.trace_comment solver ;
    
    Smt.declare_fun solver actlit ; (* Declaring actlit. *)

    let actlit = (* Getting term of actlit UF. *)
      term_of_actlit actlit
    in

    let assert_fun =
      if two_state then Unroller.assert_1_to else Unroller.assert_0_to
    in

    (* Conditionally asserting candidates from [0] to [k-1], and their negation
    at [k]. *)
    let cands =
      candidates |> List.map (
        fun (candidate, _) ->
          Term.mk_implies [ actlit ; candidate ] |> assert_fun solver k ;
          Term.bump_state k candidate
      )
    in
    Term.mk_implies [
      actlit ; Term.mk_and cands |> Term.mk_not
    ] |> Smt.assert_term solver ;

    (* Format.printf "check sat (%d)@.@." (List.length candidates) ; *)

    (* Will be [None] if all candidates are invariants. Otherwise, will be
    the candidates that were **not** falsified, at 0, with their info. *)
    let unfalsified_opt =
      let minus_k = Num.(~- k) in
      Smt.check_sat_assuming_and_get_term_values solver (
        (* If sat, get values and remove falsified candidates. *)
        fun _ term_values -> Some (
          term_values |> List.fold_left (fun acc ->
            function
            | (cand, b_val) when b_val = Term.t_true ->
              let candidate = Term.bump_state minus_k cand in
              (candidate, List.assq candidate candidates) :: acc
            | _ -> acc
          ) []
        )
      ) (
        (* If unsat. *)
        fun _ -> None
      ) [ actlit ] cands
    in
    (* Format.printf "done@.@." ; *)

    (* Deactivate actlit. *)
    Smt.trace_comment solver "Deactivating actlit for check." ;
    Term.mk_not actlit |> Smt.assert_term solver ;

    match unfalsified_opt with
    | None -> candidates
    | Some candidates -> loop candidates
  in

  (* control_query_size [] candidates *)
  loop candidates

(** Queries step, returns an option of the model. *)
let nu_query_step two_state step_checker candidates =
  (* Restarting solver if necessary. *)
  conditional_step_solver_reset step_checker ;

  let { sys ; solver ; k } = step_checker in
  let actlit = fresh_actlit () in

  Format.asprintf
    "Querying base with actlit [%a] (%d candidates)."
    Uf.pp_print_uf_symbol actlit (List.length candidates)
  |> Smt.trace_comment solver ;

  Smt.declare_fun solver actlit ; (* Declaring actlit. *)

  let actlit = (* Getting term of actlit UF. *)
    term_of_actlit actlit
  in

  let assert_fun =
    if two_state then Unroller.assert_1_to else Unroller.assert_0_to
  in

  (* Conditionally asserting candidates from [0] to [k-1], and their negation
  at [k]. *)
  let cands =
    candidates |> List.map (
      fun candidate ->
        Term.mk_implies [ actlit ; candidate ] |> assert_fun solver k ;
        Term.bump_state k candidate
    )
  in
  Term.mk_implies [
    actlit ; Term.mk_and cands |> Term.mk_not
  ] |> Smt.assert_term solver ;

  let res =
    Smt.check_sat_assuming solver (
      (* If sat, get model and return that. *)
      fun solver ->

        let minus_k = Numeral.(~- k) in
        (* Variables we want to know the value of. *)
        TransSys.vars_of_bounds sys (Numeral.pred k) k
        (* Getting their value. *)
        |> SMTSolver.get_var_values solver
          (TransSys.get_state_var_bounds sys)
        (* Bumping to -k. *)
        |> Model.bump_var minus_k 
        (* Making an option out of it. *)
        |> (fun model -> Some model)
    ) (
      (* If unsat then no model. *)
      fun _ -> None
    ) [ actlit ]
  in

  (* Deactivating actlit. *)
  Term.mk_not actlit |> Smt.assert_term solver ;

  res






(* |===| Pruning checker.

Used to check whether some invariants are implied by the transition relation
alone. That is, [T(0,1) and (not inv(1))] is unsat. *)


(** A pruning checker. *)
type pruning = {
  mutable solver: solver ;
  sys: sys ;
  mutable actlit_uid: int ;
}

(** Returns the system associated with this pruner. *)
let pruning_sys { sys } = sys

(*
(** Fresh actlit based on the uid counter in a pruning checker. *)
let pruning_fresh_actlit pruning_checker =
  let fresh = fresh_actlit_of pruning_checker.actlit_uid in
  pruning_checker.actlit_uid <- 1 + pruning_checker.actlit_uid ;
  fresh
*)

(** Kills a pruning checker. *)
let kill_pruning { solver } = Smt.delete_instance solver

(** Creates a new pruning solver. *)
let mk_pruning_checker_solver sys two_state =
  let solver = (* Creating solver. *)
    Smt.create_instance ~produce_assignments:true
      (Sys.get_logic sys) (Flags.Smt.solver ())
  in


  sys_name sys
  |> Format.asprintf (* Logging stuff in smt trace. *)
    "[Pruning] Setting up system [%s]."
  |> Smt.trace_comment solver ;


  Sys.define_and_declare_of_bounds
    sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.zero (if two_state then Numeral.one else Numeral.zero);

  Smt.trace_comment solver (* Logging stuff in smt trace. *)
    "Asserting invariants at [0]." ;

  Sys.invars_of_bound
    ~one_state_only:true sys Numeral.zero (* Invariants at [0]. *)
  |> List.iter (Smt.assert_term solver) ;

  if two_state then (
    Smt.trace_comment solver (* Logging stuff in smt trace. *)
      "Asserting invariants at [1]." ;

    Sys.invars_of_bound sys Numeral.one (* Invariants at [1]. *)
    |> List.iter (Smt.assert_term solver) ;

    Format.asprintf "Asserting transition relation."
    |> Smt.trace_comment solver ;

    Sys.trans_of_bound (Some (Smt.declare_fun solver)) sys Num.one
    |> Smt.assert_term solver
  ) ;

  solver

(** Creates a new pruning checker. *)
let mk_pruning_checker sys two_state =
  { solver = mk_pruning_checker_solver sys two_state; sys ; actlit_uid = 0 }


(** Resets the solver in a pruning checker if needed. *)
let conditional_pruning_solver_reset two_state (
  { solver ; sys ; actlit_uid } as pruning_checker
) = if actlit_uid >= max_actlit_count_before_reset then (
  (* KEvent.log_uncond "[LSD] RESTARTING PRUNING" ; *)
  Smt.delete_instance solver ;
  let solver = mk_pruning_checker_solver sys two_state in
  pruning_checker.solver <- solver ;
  pruning_checker.actlit_uid <- 0
)


(** Adds invariants to a pruning checker. *)
let pruning_add_invariants t ts invs =
  let { solver } = t in
  let eub = Num.(succ one) in (* Exclusive upper bound. *)
  invs |> (
    if ts then List.iter (Unroller.assert_1_to solver eub)
    else List.iter (Unroller.assert_0_to solver Num.one)
  )


(** Separates the trivial invariants from a list of candidates. *)
let query_pruning pruning_checker two_state =

  let { solver } = pruning_checker in
  
  let rec loop non_trivial candidates =

    (* Restarting solver if necessary. *)
    conditional_pruning_solver_reset two_state pruning_checker ;
    let actlit = Actlit.fresh_actlit () in

    Format.asprintf
      "Querying pruning with actlit [%a] (%d candidates)."
      Uf.pp_print_uf_symbol actlit (List.length candidates)
    |> Smt.trace_comment solver ;
    
    Smt.declare_fun solver actlit ; (* Declaring actlit. *)

    let actlit = (* Getting term of actlit UF. *)
      Actlit.term_of_actlit actlit
    in

    let k = if two_state then Num.one else Num.zero in

    (* Bumping everyone for query and get values. *)
    let cands = candidates |> List.map (Term.bump_state k) in
    (* Conditionally asserting negation of candidates at [1]. *)
    Term.mk_implies [
      actlit ; cands |> Term.mk_and |> Term.mk_not
    ] |> Smt.assert_term solver ;

    (* Will be [None] if all candidates are invariants. Otherwise, will be
    the candidates that were **not** falsified, at 0, with their info. *)
    let unfalsified_opt =
      let minus_k = Num.(~- k) in
      Smt.check_sat_assuming_and_get_term_values solver (
        fun _ term_values -> Some (
          term_values |> List.fold_left (
            fun (non_triv, rest) (cand, b_val) ->
              if b_val = Term.t_true then
                non_triv, (Term.bump_state minus_k cand) :: rest
              else
                (Term.bump_state minus_k cand) :: non_triv, rest
          ) ([], [])
        )
      ) (
        (* If unsat. *)
        fun _ -> None
      ) [ actlit ] cands
    in

    (* Deactivate actlit. *)
    Smt.trace_comment solver "Deactivating actlit for previous check." ;
    Term.mk_not actlit |> Smt.assert_term solver ;

    match unfalsified_opt with
    | None ->
      Smt.trace_comment solver "|===| Done." ;
      (non_trivial, candidates)
    | Some (non_triv, rest) ->
      loop (List.rev_append non_triv non_trivial) rest
    (*| Some (non_triv :: non_trivs, rest) ->
      (* pruning_add_invariants pruning_checker two_state [non_triv]; *)
      loop (non_triv :: non_trivial) (List.rev_append non_trivs rest)
    | Some ([], _) ->
      KEvent.log L_fatal
        "[pruning] satisfiable instance but no falsifiable candidate" ;
      exit 2*)
  in

  loop []
  








(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
