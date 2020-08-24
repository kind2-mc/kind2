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

(**
  Wraps a solver and provides a convenient interface for test generation.

  The goal is to be able to trigger the transition relations up to some [k].
  The wrapper thus maintains a list of actlits [a0 ; a1 ; a2 ; ... ; aN] such
  that, in the solver:
    a0 => Init(0)
    a1 => (and a0 T(0,1))
    a2 => (and a1 T(1,2))
    ...
    aN => (and aN-1 T(N-1,N))

  The client does not see this however, only the [k] at which the query should
  be made is specified. The wrapper unrolls the transition relation lazily
  whenever it is needed. See [nth_actlit_of].

  Note: [a0] is not really needed but is here for consistency.
*)

open Actlit

module S = SMTSolver
module Sys = TransSys
module Num = Numeral

type actlit = Term.t

let zero = Num.zero

(* Stores the transition system, the solver, and the list of actlits. *)
type t = {
  sys: Sys.t ;
  solver: S.t ;
  mutable actlits: actlit list ;
}

let println = Format.printf "| %s@."

(* Creates a new solver wrapper. The first actlit activates init@0. *)
let mk sys =
  (* println "creating solver" ; *)
  (* Creating solver. *)
  let solver =
    S.create_instance
      ~produce_assignments:true
      (Sys.get_logic sys)
      (Flags.Smt.solver ())
  in
  (* println "declaring vars@0" ; *)
  (* Declaring variables at 0. *)
  TransSys.define_and_declare_of_bounds
    sys
    (S.define_fun solver)
    (S.declare_fun solver)
    (S.declare_sort solver)
    zero zero ;

  (* Getting fresh actlit. *)
  let actlit =
    let fresh = fresh_actlit () in
    S.declare_fun solver fresh ;
    term_of_actlit fresh
  in

  (* Asserting init conditionally. *)
  S.trace_comment solver "|===| Conditional init." ;
  Term.mk_implies [ actlit ;
                    Sys.init_of_bound (Some (S.declare_fun solver)) sys zero ]
  |> S.assert_term solver ;

  (* println "done" ; *)

  { sys ; solver ; actlits = [ actlit ] }

(* Destroys the underlying solver. *)
let rm { solver } = S.delete_instance solver

(* Destroys the underlying solver and creates a new one. *)
let restart t = rm t ; mk t.sys

(* Comment trace for the underlying solver. *)
let comment { solver } = S.trace_comment solver

(* Returns the actlit activating the [n]th first transition relations. Creates
   fresh actlits and unrolls if necessary. *)
let nth_actlit_of ({ sys ; solver ; actlits } as t) n =
  let rec loop map_prefix cpt = function
    | actlit :: tail ->
      if Num.(cpt = n) then
        (* Found the right actlit. *)
        actlit
      else
        (* Need to loop. *)
        loop (actlit :: map_prefix) (Num.succ cpt) tail
    | [] ->
      (* Getting fresh actlit. *)
      let actlit =
        let fresh = fresh_actlit () in
        S.declare_fun solver fresh ;
        term_of_actlit fresh
      in
      (* Unrolling. *)
      ( match map_prefix with
        | prev_actlit :: _ ->
          (* Declaring variables at the new [k]. *)
          Sys.vars_of_bounds sys cpt cpt
          |> Var.declare_vars (S.declare_fun solver) ;
          S.trace_comment solver "|===| Conditional trans." ;
          (* Asserting trans@k conditionally with the previous actlit. *)
          Term.mk_implies [
            actlit ;
            Term.mk_and
              [ prev_actlit ;
                Sys.trans_of_bound (Some (S.declare_fun solver)) sys cpt ]
          ] |> S.assert_term solver
        | [] -> failwith "unreachable: \
          list of activation literals can never be empty" ) ;
      if Num.(cpt = n) then (
        (* Done, updating [t] and returning actlit. *)
        t.actlits <- List.rev (actlit :: map_prefix) ;
        actlit
      ) else
        (* Need to unroll further, looping. *)
        loop (actlit :: map_prefix) (Num.succ cpt) []
  in
  loop [] zero actlits


(* Checks the satisfiability of term [term] in conjunction with activation
   literals [actlits] with the system unrolled up to [n]. A fresh actlit is
   created for [term], and a check-sat with assumptions [term :: actlits] will
   be performed. The fresh actlit is deactivated at the end of the check.

   [terms] is an association map, the values of which are terms. If sat,
   returns some of a map mapping the keys of [terms] to the value of the
   corresponding term in the model, along with whatever the [f] returns when
   ran on the solver.
   Returns none otherwise. *)
let checksat ({ solver } as t) n term actlits terms f =
  (* Getting fresh actlit, declaring it at the same time. *)
  let actlit =
    let fresh = fresh_actlit () in
    S.declare_fun solver fresh ;
    term_of_actlit fresh
  in
  (* Getting actlit for the depth asked. *)
  let unrolling_actlit = nth_actlit_of t n in
  (* Asserting implication. *)
  Term.mk_implies [ actlit ; term ] |> S.assert_term solver ;
  (* Check-sat on the actual actlit list. *)
  terms
  |> List.map snd
  |> S.check_sat_assuming_and_get_term_values solver
    (* If sat. *)
    ( fun solver values ->
        (* Running f. *)
        let whatever = f solver in
        (* Deactivating actlit. *)
        Term.mk_not actlit |> S.assert_term solver ;
        Some (
          terms |> List.map (fun (key, term) ->
            key, List.assq term values
          ),
          whatever
        ) )
    (* If unsat. *)
    ( fun _ ->
        (* Deactivating actlit. *)
        Term.mk_not actlit |> S.assert_term solver ;
        None )
    (actlit :: unrolling_actlit :: actlits)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
