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


(** TODO: optimize multi-property reset. See [reset_props_of]. *)



(** |===| Shorthand for modules, types and functions. *)

(** Modules. *)
module Candidate = C2ICandidate
module Solver = SMTSolver
module Sys = TransSys

(** Types. *)
type model = Model.t
type term = Term.t

(** Functions. *)

(*
(** Deactivates an activation literal. *)
let deactivate s actlit = actlit |> Term.mk_not |> Solver.assert_term s

(** Updates the white, grey and black sets of models. *)
let update_colors = C2Imodel.update_colors

(** Declares a fresh actlit and returns its term. *)
let fresh_actlit s =
  let actlit = Actlit.fresh_actlit () in
  Solver.declare_fun s actlit ;
  Actlit.term_of_actlit actlit

(** Evaluation function from a system and a model. *)
let eval sys model bump = (fun term ->
  Term.bump_state bump term
  |> Eval.eval_term (Sys.uf_defs sys) model
  |> Eval.bool_of_value
)
*)


(** Log prefix. *)
(*let pref = "C2I(cnf) "*)


(** Output statistics. *)
let print_stats () = KEvent.stat [
  Stat.misc_stats_title, Stat.misc_stats ;
  Stat.c2i_stats_title, Stat.c2i_stats ;
  Stat.smt_stats_title, Stat.smt_stats ;
]

(** Stop all timers. *)
let stop () = Stat.c2i_stop_timers ()

(** Clean exit. *)
let on_exit _ =
  stop () ;
  (* Outputing stats. *)
  print_stats ()

(** Context maintained by the C2I CNF version. *)
type contex = {
  sys           : TransSys.t           ;
  props         : (string * term )list ;
  mutable white : model list           ;
  mutable grey  : (model * model) list ;
  mutable black : model list           ;
  solver1       : Solver.t             ;
  solver2       : Solver.t             ;
  solver3       : Solver.t             ;
}


(** |===| Solver-related stuff. *)


(** Creates a solver. If [init], then variables are be declared at -1 and 0
    and init are asserted at 0. Otherwise, variables are declared at -1, 0 and
    1, and a transition between 0 and 1 is asserted. *)
let mk_solver sys init =
  let solver = Solver.create_instance
    ~produce_assignments:true
    (Sys.get_logic sys)
    (Flags.Smt.solver ())
  in

  (* Variable declaration upper bound, predicate to assert. *)
  let var_ub, pred =
    if init
    then Numeral.zero,
         Sys.init_of_bound (Some (Solver.declare_fun solver)) sys Numeral.zero
    else Numeral.one,
         Sys.trans_of_bound (Some (Solver.declare_fun solver)) sys Numeral.one
  in

  (* Defining and declaring everything. *)
  Sys.define_and_declare_of_bounds
    sys
    (Solver.define_fun solver)
    (Solver.declare_fun solver)
    (Solver.declare_sort solver)
    Numeral.zero var_ub ;

  (* Asserting predicate. *)
  Solver.assert_term solver pred ;

  (* Asserting invariants at 0. *)
  Sys.invars_of_bound
    ~one_state_only:true sys Numeral.zero
  |> Term.mk_and
  |> Solver.assert_term solver ;

  if not init then
    (* Asserting invariants at 1. *)
    Sys.invars_of_bound sys Numeral.one |> Term.mk_and
    |> Solver.assert_term solver ;

  solver

(** Creates the three solvers used by C2I. Initializes them and updates the
    solver references (deletes previous solvers). *)
let mk_solvers sys =

  (* Creating solvers. *)
  let s1, s2, s3 =
    mk_solver sys true,
    mk_solver sys false,
    mk_solver sys false
  in

  s1, s2, s3

(** Resets the solvers of a context if enough actlits have been created. *)
(*
let reset_solvers_of t =
  if (Actlit.fresh_actlit_count () / 3) mod 20 = 0 then (
    (* Reset solvers. *)
    let solver1, solver2, solver3 = mk_solvers t.sys in
    (* Reset actlits. *)
    Actlit.reset_fresh_actlit_count () ;
    { t with solver1 ; solver2 ; solver3 }
  ) else t
*)



(** |===| Context-related stuff. *)


(** Creates a context. *)
let mk_context sys props =

  (* Extracting property terms. *)
  let props =
    props |> List.map (fun name ->
      name, (Sys.property_of_name sys name).Property.prop_term
    )
  in

  (* Creating solvers. *)
  let solver1, solver2, solver3 = mk_solvers sys in

  (* Original model sets. *)
  let white, grey, black = [], [], [] in

  (* Returning context. *)
  { sys ; props ; white ; grey ; black ; solver1 ; solver2 ; solver3 }

(*
(** Resets a context with a new prop. Changes [prop] and resets [black].
    
    So actually, since we're (possibly) doing multi-property we could keep the
    black models for properties in [props]. *)
let reset_props_of t props = { t with props ; black = [] }

(** Resets the grey set of a context. *)
(*let reset_grey_of t = { t with grey = [] }*)

(** Returns the conjunction of the properties from a context. *)
let prop_term_of props = props |> List.map snd |> Term.mk_and


(** |===| Check-related stuff. *)


(** Split a list of subcandidates based on the value they evaluate to. *)
let split eval candidate =
  (* Reverse candidate to preserve order in result. *)
  candidate |> List.rev
  |> List.fold_left (fun (ok, falsified) ((index, term) as sc) ->
    if eval term then sc :: ok, falsified else ok, index :: falsified
  ) ([], [])

let base_off = Sys.init_base
let step_one = Sys.trans_base
let step_zer = Numeral.pred step_one

(** Recursively separates the sub-candidates that can be falsified
    at [bump] when put in conjunction with [f candidate]. Returns a list of
    pairs models / index of sub-candidate falsified. *)
let rec check_candidate sys solver bump f candidate falsifiable =
  (* Creating actlit, declaring it, extracting term. *)
  let actlit = fresh_actlit solver in
  (* Building implication and asserting it. *)
  Term.mk_implies [
    actlit ; Term.mk_and [
      candidate |> List.map (
        fun (i, disj) -> disj |> Term.bump_state bump |> Term.mk_not
      ) |> Term.mk_or ;
      f candidate
    ]
  ] |> Solver.assert_term solver ;

  (* Check sat. *)
  match
    Solver.check_sat_assuming solver
      (* If sat. *)
      ( fun _ ->
        (* Deactivating actlit. *)
        deactivate solver actlit ;
        Some (Solver.get_model solver) )
      (* If unsat. *)
      ( fun _ ->
        (* Deactivating actlit. *)
        deactivate solver actlit ;
        None )
      (* Single actlit. *)
      [ actlit ]
  with
  | Some model ->
    let eval = eval sys model bump in
    (* Separate indices of falsifiable sub-candidates. *)
    let candidate, falsified = split eval candidate in
    (* Check if termination was requested. *)
    KEvent.check_termination () ;
    (* Update the falsifiable sub-candidates and recurse. *)
    (model, falsified) :: falsifiable
    |> check_candidate sys solver bump f candidate
  | None -> candidate, falsifiable


(** Checks (1). *)
let check_1 sys solver candidate =
  check_candidate sys solver base_off (fun _ -> Term.t_true) candidate []

(** Checks (2). *)
let check_2 sys solver candidate =
  check_candidate sys solver step_one (fun c ->
    c |> List.map (fun (i, disj) ->
      Term.bump_state step_zer disj
    ) |> Term.mk_and
  ) candidate []

(** Checks (3). Does multi-property reasoning on [props]. Returns the list of
    properties entailed by the candidate, and those falsified. *)
let check_3 sys solver candidate props =
  (* Creating actlit for candidate, declaring it, extracting term. *)
  let candidate_actlit = fresh_actlit solver in
  (* Asserting implication. *)
  Term.mk_implies [
    candidate_actlit ;
    candidate |> List.map snd |> Term.mk_and |> Term.bump_state step_zer
  ] |> Solver.assert_term solver ;

  (* Multi-property split on props. *)
  let rec loop props falsifiable =
    (* Creating actlit, declaring it, extracting term. *)
    let actlit = fresh_actlit solver in
    (* Extracting the conjunction of all properties. *)
    let props_term = props |> prop_term_of in
    (* Building implication and asserting it. *)
    Term.mk_implies [
      actlit ; Term.mk_and [
        props_term |> Term.bump_state step_zer ;
        props_term |> Term.mk_not |> Term.bump_state step_one
      ]
    ] |> Solver.assert_term solver ;
    (* Check sat. *)
    match
      Solver.check_sat_assuming solver
        (* If sat. *)
        ( fun _ ->
          (* Deactivating actlit. *)
          deactivate solver actlit ;
          Some (Solver.get_model solver) )
        (* If unsat. *)
        ( fun _ ->
          (* Deactivating actlit. *)
          deactivate solver actlit ;
          None )
        [ candidate_actlit ; actlit ]
    with
    | Some model ->
      let eval = eval sys model step_one in
      (* Separate indices of falsifiable sub-candidates. *)
      let props, falsified = split eval props in
      (* Check if termination was requested. *)
      KEvent.check_termination () ;
      (* Update the falsifiable sub-candidates and recurse. *)
      (model, falsified) :: falsifiable |> loop props
    | None -> props, falsifiable
  in

  (* Run loop. *)
  loop props [] |> fun res ->
    (* Deactivate candidate actlit. *)
    deactivate solver candidate_actlit ;
    (* Done. *)
    res




(** Checks (1), (2) and (3) for a candidate invariant. *)
let query_solvers { sys ; props ; solver1 ; solver2 ; solver3 } candidate =
  let _, candidate =
    Candidate.terms_of candidate
    (* Reversing to have the right ordering after the fold left. *)
    |> List.rev
    (* Indexing and constructing disjunction. *)
    |> List.fold_left (fun (index, l) terms ->
      index + 1, (index, Term.mk_or terms) :: l
    ) (0, [])
  in
  check_1 sys solver1 candidate,
  check_2 sys solver2 candidate,
  check_3 sys solver3 candidate props*)

  (* match ... with
  | (_, []), (_, []), ([], _) ->
    KEvent.log L_info "%sInvariant found." pref ;
  | (_, []), (_, []), (str, fal) ->
    KEvent.log L_info
      "%s@[<v>Strengthening invariant found for @   @[<hv>\
              %a\
      @]@]"
      pref
      (pp_print_list
        (fun fmt (n,_) -> Format.fprintf fmt "%s" n)
        ",@ ")
      str ;
    candidate |> List.map snd |> Term.mk_and
    |> KEvent.invariant (
      Sys.scope_of_trans_sys sys
    ) ;
  | info -> info *)





(** Runs C2I cnf version. *)
let [@ocaml.warning "-27"] run context candidate = ()



(** Entry point. *)
let [@ocaml.warning "-27"] main input_sys aparam sys =

  match Sys.get_split_properties sys with
  | _, _, [] ->
    (* No properties to strengthen. *)
    ()
  | _, _, props ->

    (* Extracting property names. *)
    let props = List.map (fun p -> p.Property.prop_name) props in

    (* Start timers. *)
    Stat.start_timer Stat.c2i_total_time ;
    (* New candidate. *)
    let candidate = Candidate.mk sys in
    (* Building context. *)
    let context = mk_context sys props in

    (* Running. *)
    run context candidate ;

    (* Done. *)
    stop ()


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
