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


(* Typical usage of external calls follows:

   [ let system_candidates =
       mine_system
         synthesis mine_init mine_trans system
     in

     let rec loop ignore =

       (* Generate some terms to mine. *)
       let terms = generate_terms () in

       (* Then, either... *)
       if you_want then
         (* ...first mine candidates... *)
         let all_candidates =
           mine_terms
             (* Mined candidates are added to [system_candidates]. *)
             system terms system_candidates
         in

         Term.TermSet.cardinal all_candidates
         |> Event.log L_ino "Got %i candidate terms."

         (* ...then run invariant generation. *)
         let invariants', ignore' =
           run system ignore maxK all_candidates
         in

         (* Bla. *)
         Term.TermSet.cardinal invariants'
         |> Event.log L_info "Found %i invariants."

         loop ignore'

       else
         (* ...or just run directly. *)
         let invariants', ignore' =
           mine_terms_run
             system ignore maxK terms system_candidates
         in

         (* Bla. *)
         Term.TermSet.cardinal invariants'
         |> Event.log L_info "Found %i invariants."

         loop ignore'
    in

    loop Term.TermSet.empty
  ]

  Note that you can accumulate candidate terms:

   [ let rec loop ignore candidates =
       (* Generate terms. *)
       let terms = generate_terms () in

       (* Mine them, adding to the candidate accumulator. *)
       let candidates' =
         mine_terms system terms candidates
       in

       (* Run invariant generation on all candidates. *)
       let invariants', ignore' =
         run system ignore maxK candidates'
       in

       (* Bla. *)
       Term.TermSet.cardinal invariants'
       |> Event.log L_info "Found %i invariants."

       loop ignore' candidates'
     in

     mine_system
       synthesis mine_init mine_trans system
     |> loop Term.TermSet.empty
   ]

 *)


(** One state graph-based invariant generation module. *)
module OneState : sig

  (** Invariant generation entry point. *)
  val main : TransSys.t -> unit

  (** Destroys the underlying solver and cleans things up. *)
  val on_exit : TransSys.t option -> unit

  (** Launches invariant generation with a max [k] and a set of
      candidate terms. More precisely, [run sys ignore maxK
      candidates] will find invariants from set [candidates] by going
      up to [maxK] for [sys] and ignoring any term appearing in
      [ignore]. The result is a pair composed of the invariants
      discovered and the new set of ignored terms. *)
  val run :
    TransSys.t -> Term.TermSet.t -> Numeral.t -> Term.TermSet.t ->
    Term.TermSet.t * Term.TermSet.t

  (** Mines candidate terms from a system.  First bool flag activates
      synthesis, i.e. mining based on the state variables of the
      system. Second (resp. third) bool flag activates init
      (resp. transition) predicate mining. *)
  val mine_system :
    bool -> bool -> bool -> TransSys.t -> Term.TermSet.t

  (** Mines candidate terms from a list of terms, and adds them to the
      input set. *)
  val mine_terms :
    TransSys.t -> Term.t list -> Term.TermSet.t -> Term.TermSet.t

  (** Mines candidate terms from the list of terms. More precisely,
      [mine_terms_run sys ignore maxK candidates set] will mine
      candidate terms from list of terms [candidates], and add them to
      [set].  It then runs goes up to [maxK] for [sys] and ignores any
      term appearing in [ignore]. The result is a pair composed of the
      invariants discovered and the new set of ignored terms. *)
  val mine_terms_run :
    TransSys.t -> Term.TermSet.t -> Numeral.t -> Term.t list -> Term.TermSet.t ->
    Term.TermSet.t * Term.TermSet.t

end

(** Two state graph-based invariant generation module. *)
module TwoState : sig

  (** Invariant generation entry point. *)
  val main : TransSys.t -> unit

  (** Destroys the underlying solver and cleans things up. *)
  val on_exit : TransSys.t option -> unit

  (** Launches invariant generation with a max [k] and a set of
      candidate terms. More precisely, [run sys ignore maxK
      candidates] will find invariants from set [candidates] by going
      up to [maxK] for [sys] and ignoring any term appearing in
      [ignore]. The result is a pair composed of the invariants
      discovered and the new set of ignored terms. *)
  val run :
    TransSys.t -> Term.TermSet.t -> Numeral.t -> Term.TermSet.t ->
    Term.TermSet.t * Term.TermSet.t

  (** Mines candidate terms from a system.  First bool flag activates
      synthesis, i.e. mining based on the state variables of the
      system. Second (resp. third) bool flag activates init
      (resp. transition) predicate mining. *)
  val mine_system :
    bool -> bool -> bool -> TransSys.t -> Term.TermSet.t

  (** Mines candidate terms from a list of terms, and adds them to the
      input set. *)
  val mine_terms :
    TransSys.t -> Term.t list -> Term.TermSet.t -> Term.TermSet.t

  (** Mines candidate terms from the list of terms. More precisely,
      [mine_terms_run sys ignore maxK candidates set] will mine
      candidate terms from list of terms [candidates], and add them to
      [set].  It then runs goes up to [maxK] for [sys] and ignores any
      term appearing in [ignore]. The result is a pair composed of the
      invariants discovered and the new set of ignored terms. *)
  val mine_terms_run :
    TransSys.t -> Term.TermSet.t -> Numeral.t -> Term.t list -> Term.TermSet.t ->
    Term.TermSet.t * Term.TermSet.t

end

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

