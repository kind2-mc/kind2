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


(** Asserts some terms from [0] to [k-1]. *)
let assert_0_to solver k term =
  let rec loop i =
    if Num.(i < k) then (
      Term.bump_state i term |> Smt.assert_term solver ;
      Num.succ i |> loop
    )
  in
  loop Num.zero




(* |===| Base checker. *)


(** A base checker. *)
type base = {
  solver: solver ;
  sys: sys ;
  init_actlit: term ;
  k: num ;
}

(** Kills a base checker. *)
let kill_base { solver } = Smt.delete_instance solver

(** Creates an LSD instance to check the base case. *)
let mk_base_checker sys k =
  let solver = (* Creating solver. *)
    Smt.create_instance ~produce_assignments: true
      (Sys.get_logic sys) (Flags.Smt.solver ())
  in


  Format.asprintf (* Logging stuff in smt trace. *)
    "[Base/Step] Setting up system [%s], k = %a."
    (sys_name sys) Num.pp_print_numeral k
  |> Smt.trace_comment solver ;


  let init_actlit = (* Creating actlit for initial predicate. *)
    Actlit.fresh_actlit ()
  in

  Format.asprintf (* Logging stuff in smt trace. *)
    "Actlit for initial predicate: [%a]." Uf.pp_print_uf_symbol init_actlit
  |> Smt.trace_comment solver ;
  
  Smt.declare_fun solver init_actlit ; (* Declaring actlit. *)


  let init_actlit = (* Getting term of actlit UF. *)
    Actlit.term_of_actlit init_actlit
  in


  Smt.trace_comment solver (* Logging stuff in smt trace. *)
    "Declaring system's svars at [-1] and [0]." ;

  Sys.declare_vars_of_bounds (* Declaring unrolled vars at [-1] and [0]. *)
    sys (Smt.declare_fun solver) Numeral.(~- one) Numeral.zero ;


  Smt.trace_comment solver (* Logging stuff in smt trace. *)
    "Conditional initial predicate." ;

  Term.mk_implies (* Conditionally asserting the initial predicate. *)
    [ init_actlit ; Sys.init_of_bound sys Num.zero ]
  |> Smt.assert_term solver ;


  Smt.trace_comment solver (* Logging stuff in smt trace. *)
    "Asserting invariants at [0]." ;

  Sys.invars_of_bound sys Numeral.zero (* Invariants at [0]. *)
  |> List.iter (Smt.assert_term solver) ;


  (* Unrolls the transition relation as needed. *)
  let rec unroll i = if Num.(i <= k) then
    Format.asprintf "Declaring svars at [%a]." Num.pp_print_numeral i
    |> Smt.trace_comment solver ;
    Sys.declare_vars_of_bounds sys (Smt.declare_fun solver) i i ;

    Format.asprintf
      "Asserting transition relation at [%a]." Num.pp_print_numeral i
    |> Smt.trace_comment solver ;
    Sys.trans_of_bound sys i |> Smt.assert_term solver ;

    Format.asprintf
      "Asserting invariants at [%a]." Num.pp_print_numeral i
    |> Smt.trace_comment solver ;
    Sys.invars_of_bound sys i |> List.iter (Smt.assert_term solver)
  in

  (* Unroll from one to [k]. *)
  unroll Num.one ;

  { solver ; sys ; init_actlit ; k }


(** Adds invariants to a base checker. *)
let base_add_invariants { solver ; k } =
  let eub = Num.succ k in (* Exclusive upper bound. *)
  List.iter (
    fun invar -> assert_0_to solver eub invar
  )


(** Queries base, returns an option of the model. *)
let query_base { solver ; k ; init_actlit } candidates =
  let actlit = Actlit.fresh_actlit () in
  
  Format.asprintf
    "Querying base with actlit [%a] (%d candidates)."
    Uf.pp_print_uf_symbol actlit (List.length candidates)
  |> Smt.trace_comment solver ;
  
  Smt.declare_fun solver actlit ; (* Declaring actlit. *)

  let actlit = (* Getting term of actlit UF. *)
    Actlit.term_of_actlit actlit
  in

  (* Conditionally asserting negation of candidates at [k+1]. *)
  candidates |> List.iter (
    fun candidate ->
      Term.mk_implies [
        actlit ; Term.bump_state k candidate |> Term.mk_not
      ] |> Smt.assert_term solver ;
  ) ;

  Smt.check_sat_assuming solver (
    (* If sat, get model and return that. *)
    fun solver -> Some (Smt.get_model solver)
  ) (
    (* If unsat then no model. *)
    fun _ -> None
  ) [ init_actlit ; actlit ]




(* |===| Step checker. *)


(* A step checker. *)
type step = {
  solver: solver ;
  sys: sys ;
  k: num ;
}

(** Kills a step checker. *)
let kill_step { solver } = Smt.delete_instance solver

(** Transforms a base instance in a step instance. *)
let to_step { solver ; sys ; k ; init_actlit } =
  Smt.trace_comment solver "Switching to step mode." ;

  let kp1 = Num.succ k in

  Format.asprintf "Declaring svars at [%a]." Num.pp_print_numeral kp1
  |> Smt.trace_comment solver ;
  Sys.declare_vars_of_bounds sys (Smt.declare_fun solver) kp1 kp1  ;

  Format.asprintf
    "Asserting transition relation at [%a]." Num.pp_print_numeral kp1
  |> Smt.trace_comment solver ;
  Sys.trans_of_bound sys kp1 |> Smt.assert_term solver ;

  Format.asprintf
    "Asserting invariants at [%a]." Num.pp_print_numeral kp1
  |> Smt.trace_comment solver ;
  Sys.invars_of_bound sys kp1 |> List.iter (Smt.assert_term solver) ;

  Smt.trace_comment solver "Deactivating actlit for initial predicate." ;
  Term.mk_not init_actlit |> Smt.assert_term solver ;

  { solver ; sys ; k = kp1 }



(** Queries step.

[candidates] is a list of elements of type [(Term.t, 'a)]. The second element
is understood as some information about the candidate.

Returns the elements of [candidates] for which the first element of the pair
(the term) is an invariant. *)
let rec query_step ( { solver ; k } as lsd ) candidates =
  let actlit = Actlit.fresh_actlit () in

  Format.asprintf
    "Querying step with actlit [%a] (%d candidates)."
    Uf.pp_print_uf_symbol actlit (List.length candidates)
  |> Smt.trace_comment solver ;
  
  Smt.declare_fun solver actlit ; (* Declaring actlit. *)

  let actlit = (* Getting term of actlit UF. *)
    Actlit.term_of_actlit actlit
  in

  (* Conditionally asserting candidates from [0] to [k-1], and their negation
  at [k]. *)
  let cands =
    candidates |> List.map (
      fun (candidate, _) ->
        Term.mk_implies [ actlit ; candidate ] |> assert_0_to solver k ;
        let cand = Term.bump_state k candidate in
        Term.mk_implies [
          actlit ; cand |> Term.mk_not
        ] |> Smt.assert_term solver ;
        cand
    )
  in

  (* Will be [None] if all candidates are invariants. Otherwise, will be
  the candidates that were **not** falsified, at 0, with their info. *)
  let unfalsified_opt =
    let minus_k = Num.(~- k) in
    Smt.check_sat_assuming solver (
      (* If sat, get values and remove falsified candidates. *)
      fun solver -> Some (
        Smt.get_term_values solver cands
        |> List.fold_left (fun acc ->
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
    ) [ actlit ]
  in

  (* Deactivate actlit. *)
  Smt.trace_comment solver "Deactivating actlit for check." ;
  Term.mk_not actlit |> Smt.assert_term solver ;

  match unfalsified_opt with
  | None -> candidates
  | Some candidates -> query_step lsd candidates






(* |===| Pruning checker. *)


(** A pruning checker. *)
type pruning = {
  solver: solver ;
  sys: sys ;
}

(** Kills a pruning checker. *)
let kill_pruning { solver } = Smt.delete_instance solver

(** Creates a new pruning solver. *)
let mk_pruning_checker sys =
  let solver = (* Creating solver. *)
    Smt.create_instance ~produce_assignments:false
      (Sys.get_logic sys) (Flags.Smt.solver ())
  in


  sys_name sys
  |> Format.asprintf (* Logging stuff in smt trace. *)
    "[Pruning] Setting up system [%s]."
  |> Smt.trace_comment solver ;


  Smt.trace_comment solver (* Logging stuff in smt trace. *)
    "Declaring system's svars at [-1] and [1]." ;

  Sys.declare_vars_of_bounds (* Declaring unrolled vars at [-1] and [1]. *)
    sys (Smt.declare_fun solver) Numeral.(~- one) Numeral.one ;


  Smt.trace_comment solver (* Logging stuff in smt trace. *)
    "Asserting invariants at [0] and [1]." ;

  Sys.invars_of_bound sys Numeral.zero (* Invariants at [0]. *)
  |> List.iter (Smt.assert_term solver) ;

  Sys.invars_of_bound sys Numeral.one (* Invariants at [1]. *)
  |> List.iter (Smt.assert_term solver) ;

  Format.asprintf
    "Asserting transition relation."
  |> Smt.trace_comment solver ;

  { solver ; sys }


(** Adds invariants to a pruning checker. *)
let pruning_add_invariants { solver } =
  let eub = Num.(succ one) in (* Exclusive upper bound. *)
  List.iter (
    fun invar -> assert_0_to solver eub invar
  )


(** Prunes the trivial invariants from a list of candidates. *)
let rec query_pruning ( { solver } as lsd ) candidates =
  let actlit = Actlit.fresh_actlit () in

  Format.asprintf
    "Querying pruning with actlit [%a] (%d candidates)."
    Uf.pp_print_uf_symbol actlit (List.length candidates)
  |> Smt.trace_comment solver ;
  
  Smt.declare_fun solver actlit ; (* Declaring actlit. *)

  let actlit = (* Getting term of actlit UF. *)
    Actlit.term_of_actlit actlit
  in

  let k = Num.one in

  (* Conditionally asserting negation of candidates at [1]. *)
  let cands =
    candidates |> List.map (
      fun candidate ->
        let cand = Term.bump_state k candidate in
        Term.mk_implies [
          actlit ; cand |> Term.mk_not
        ] |> Smt.assert_term solver ;
        cand
    )
  in

  (* Will be [None] if all candidates are invariants. Otherwise, will be
  the candidates that were **not** falsified, at 0, with their info. *)
  let unfalsified_opt =
    let minus_k = Num.(~- k) in
    Smt.check_sat_assuming solver (
      (* If sat, get values and remove falsified candidates. *)
      fun solver -> Some (
        Smt.get_term_values solver cands
        |> List.fold_left (fun acc ->
          function
          | (cand, b_val) when b_val = Term.t_true ->
            (Term.bump_state minus_k cand) :: acc
          | _ -> acc
        ) []
      )
    ) (
      (* If unsat. *)
      fun _ -> None
    ) [ actlit ]
  in

  (* Deactivate actlit. *)
  Smt.trace_comment solver "Deactivating actlit for check." ;
  Term.mk_not actlit |> Smt.assert_term solver ;

  match unfalsified_opt with
  | None ->
    Smt.trace_comment solver "|===| Done." ;
    candidates
  | Some candidates -> query_pruning lsd candidates
  








(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)