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
open TypeLib
open Actlit


module Solver = SolverMethods.Make(SMTSolver.Make(SMTLIBSolver))

(* Type of a lock step kind context. *)
type t = {
  (* The transition system. *)
  trans: TransSys.t ;
  (* Indicates whether the lsd is two state. *)
  two_state: bool ;
  (* The solver. *)
  solver: Solver.t ;
  (* The k we are currently at. Means that the transition predicates
     are unrolled up to k+1 (so that step is meaningful). *)
  mutable k: Numeral.t ;
  (* Actlit for the initial predicates of all the nodes of the
     systems. *)
  init_actlit: Term.t ;
  (* All variables for all nodes of the system. *)
  all_vars: Var.t list ;
  (* All transition predicates for all the nodes of the system. *)
  all_transitions: Term.t ;
  (* Invariants asserted up to k+1. *)
  mutable invariants: Term.t list ;
  mutable step_mode: bool
}

(* Creates a lock step driver based on a transition system. *)
let create two_state trans =
  
  (* Creating solver. *)
  let solver =
    TransSys.get_logic trans
    |> Solver.new_solver ~produce_assignments: true
  in

  (* Declaring the init flag. *)
  TransSys.init_flag_uf
  |> Solver.declare_fun solver ;

  (* Creating the list of all initial predicates, the list of all
     transition predicates and the list of all vars at 0. Also does
     all the necessary declare/define-fun-s. *)
  let all_inits, all_transitions, all_vars =
    (* Iterating on all the predicates of the system. *)
    TransSys.uf_defs_pairs trans
    |> List.fold_left
         ( fun
             (init_list, trans_list, var_list)
             ((i_uf,(i_vars,i_term)),
              (t_uf,(t_vars,t_term))) ->

           (* Declaring i_vars to be able to use this node's init
                 predicate directly as a term. *)
           i_vars
           |> List.iter
                (fun var ->
                 Var.state_var_of_state_var_instance var
                 |> StateVar.uf_symbol_of_state_var
                 |> Solver.declare_fun solver) ;

           (* Defining this node's init predicate. *)
           Solver.define_fun solver i_uf i_vars i_term ;

           (* Defining this node's transition predicate. *)
           Solver.define_fun solver t_uf t_vars t_term ;

           (* Building the list of all init and transition
                 terms. *)
           i_term :: init_list,
           t_term :: trans_list,
           List.rev_append i_vars var_list)
         
         ([ TransSys.init_flag_var Numeral.zero
            |> Term.mk_var ],
          
          [ TransSys.init_flag_var Numeral.one
            |> Term.mk_var
            |> Term.mk_not ],
          
          [ TransSys.init_flag_var Numeral.zero ])
  in

  (* Declaring path compression function. *)
  Compress.init (Solver.declare_fun solver) trans ;

  (* Building the conjunction of all transition predicates. *)
  let all_transitions_conj =
    all_transitions |> Term.mk_and
  in

  (* Getting a fresh actlit for init. *)
  let init_actlit = fresh_actlit () in
  (* Declaring it. *)
  init_actlit |> Solver.declare_fun solver ;
  (* Term version for init_actlit. *)
  let init_actlit_term = term_of_actlit init_actlit in

  (* Asserting implication between the init actlit and all init
        predicates. *)
  [ init_actlit_term ; (Term.mk_and all_inits) ]
  |> Term.mk_implies
  |> Solver.assert_term solver ;

  (* (\* Asserting all transitions predicates at zero for step. *\) *)
  (* all_transitions_conj *)
  (* |> Term.bump_state Numeral.zero *)
  (* |> Solver.assert_term solver ; *)

  (* Return the context of the solver. *)
  { trans = trans ;
    two_state = two_state ;
    solver = solver ;
    all_vars = all_vars ;
    all_transitions = all_transitions_conj ;
    init_actlit = init_actlit_term ;
    k = Numeral.zero ;
    invariants = [] ;
    step_mode = false }


let check_satisfiability { solver } =
  (* Making sure the transitions are satisfiable. *)
  debug lsd "Checking if instance is sat." in
  if Solver.check_sat solver
  then (
    debug lsd "Sat." in ()
  ) else (
    debug lsd "Unsat, crashing." in assert false
  )

(* Asserts all transition relations at k and all invariants at k+1. *)
let assert_all_trans_at_k
      ({ solver ; k ; all_transitions ;
         invariants ; step_mode } as context) =

  (* Making sure we are not in step mode. *)
  assert (not step_mode) ;

  (* k plus 1. *)
  let kp1 = Numeral.succ k in

  (* Asserting all transitions predicates at k+1. *)
  all_transitions
  |> Term.bump_state k
  |> Solver.assert_term solver ;

  (* Asserting all invariants at k. *)
  if invariants <> [] then
    invariants
    |> Term.mk_and
    |> Term.bump_state kp1
    |> Solver.assert_term solver ;

  (* We are now in base mode. *)
  context.step_mode <- true
  

(* Increments the k of a lock step driver. If we are already in step
   mode, the transition relations and the invariants for base at the
   next k are already asserted. If we are not in step mode, then they
   will be asserted. *)
let increment
      ({ solver ; k ; all_transitions ; invariants ; step_mode } as context) =

  (* Asserting transition relations at current k if not in
     step_mode. *)
  if not step_mode then assert_all_trans_at_k context ;

  (* Updating context. *)
  context.k <- Numeral.succ k ;

  (* We are now in base mode. *)
  context.step_mode <- false

(* Deletes a lock step driver. *)
let delete context =
  Solver.delete_solver context.solver

(* The k of the lock step driver. *)
let get_k { k } = k

(* Unrolls a term from 1 to k, returns the list of unrolled terms. *)
let unroll_term_up_to_k exclude_zero k term =
  let condition =
    if exclude_zero
    then (fun num -> Numeral.(num > zero))
    else (fun num -> Numeral.(num >= zero))
  in
  let rec loop i unrolled =
    if condition i then
      Term.bump_state i term :: unrolled
      |> loop Numeral.(i - one)
    else
      unrolled
  in
  loop k []

(* Adds new invariants to a lock step driver. *)
let new_invariants ({ solver ; k ; invariants ; step_mode } as context) = function
  | [] -> ()
  | new_invariants ->

    (* Maximal k at which the invariants will be asserted. *)
    let up_to = if step_mode then Numeral.(k + one) else k in
    
    (* Asserting new invariants from 0 to k+1, memorizing them at the
       same time. *)
    new_invariants
    |> List.fold_left
         (* Taking one invariant. *)
         ( fun list inv ->
           (* Asserting it from 0 to k+1 as a conjunction. *)
           unroll_term_up_to_k false up_to inv
           |> Term.mk_and
           |> Solver.assert_term solver ;
           (* Appending to old invariants. *)
           inv :: list )
         invariants
    |> (fun invs -> context.invariants <- invs)


(* Checks if some of the input terms are falsifiable k steps from the
   initial states. Returns Some of a counterexample if some are, None
   otherwise.  Note that query_base is only safe to call if no
   query_step was performed since the last increment. Otherwise, the
   transition relations are asserted at k/k+1 and the invariants at
   k+1. *)
let query_base { solver ; k ; init_actlit ; all_vars } terms =

  (* Getting a fresh actlit. *)
  let terms_actlit = fresh_actlit () in

  (* Declaring it. *)
  terms_actlit |> Solver.declare_fun solver ;

  (* Term version of the actlit. *)
  let terms_actlit_term = term_of_actlit terms_actlit in

  (* Building the list of terms at k. *)
  let terms_at_k =
    terms
    |> List.map
         (* Bumping term to kp1. *)
         ( Term.bump_state k )
  in

  (* Asserting the implication between the actlit and the negation
        of the terms. *)
  [ terms_actlit_term ;
    terms_at_k |> Term.mk_and |> Term.mk_not ]
  |> Term.mk_implies
  |> Solver.assert_term solver ;

  let k_m_1 = Numeral.pred k in

  (* Bumping the variables to k. *)
  let var_at_k =
    all_vars
    |> List.fold_left
         ( fun var_list v ->
           ( (Var.bump_offset_of_state_var_instance k v) ::
               (Var.bump_offset_of_state_var_instance k_m_1 v) ::
                 var_list ))
         []
  in

  (* Memorizing the result so that we can deactivate the actlit
     before returning. *)
  let result =

    (* Check-sat-assuming time. *)
    Solver.check_sat_assuming

      solver

      (* Function ran if sat. Returns Some of the
         model. *)
      ( fun () ->
        Some
          (* Getting the model. *)
          ( let model = Solver.get_model solver var_at_k in
            (* model *)
            (* |> List.iter *)
            (*      ( fun (var,t) -> *)
            (*        Printf.printf "  %s -> %s\n" *)
            (*               (Var.string_of_var var) *)
            (*               (Term.string_of_term t) ) ; *)
            model
            |> List.map
                 ( fun (v,t) ->
                   Var.bump_offset_of_state_var_instance
                     Numeral.(~-k) v,
                   t ) ) )

      (* Function ran if unsat. Returns None. *)
      ( fun () -> None )
      (* The actlit activates everything. *)
      [ init_actlit ; terms_actlit_term ]
  in

  (* Deactivating actlits. *)
  terms_actlit_term
  |> Term.mk_not
  |> Solver.assert_term solver ;

  (* Returning the result. *)
  result

(* Splits terms between those that are falsifiable at k+1 and those
   that are not. 

   Optimisation: while getting the values, prepare terms for the
   next iteration. *)
let rec split_closure two_state solver k kp1 all_vars falsifiable terms =
  match terms with
  | _ :: _ ->

     (* Getting a fresh actlit. *)
     let terms_actlit = fresh_actlit () in

     (* Declaring it. *)
     terms_actlit |> Solver.declare_fun solver ;

     (* Term version of the actlit. *)
     let terms_actlit_term = term_of_actlit terms_actlit in

     (* Building the list of terms at k+1. At the same time, we create
        the implications between actlit and terms from 0 to k. *)
     let terms_at_kp1 =
       terms
       |> List.map
            ( fun term ->

              (* Asserting that actlit implies term from 0 to k. The
                 actlit gets overloaded for each term. *)
              [ terms_actlit_term ;
                unroll_term_up_to_k two_state k term |> Term.mk_and ]
              |> Term.mk_implies
              |> Solver.assert_term solver ;

              (* Bumping term to kp1. *)
              Term.bump_state kp1 term )
     in

     (* Overloading the actlit one last time for the negation of the
        terms. *)
     [ terms_actlit_term ;
       (terms_at_kp1 |> Term.mk_and |> Term.mk_not) ]
     |> Term.mk_implies
     |> Solver.assert_term solver ;

     (* Checking if we received a termination message. *)
     Event.check_termination () ;

     (* Building a small continuation to deactivate the actlit before
        we go on. *)
     let continue =
       ( match
           (* Check-sat-assuming time. *)
           Solver.check_sat_assuming
             solver

             (* Function ran if sat. Returns Some of the falsifiable
                terms, INCLUDING THE ONES WE ALREADY KNOW ARE
                FALSIFIABLE, and the unknown ones. *)
             ( fun () ->
               Solver.get_values solver terms_at_kp1
               |> List.fold_left
                    ( fun (flsbl_list, uknwn_list)
                          (term_at_kp1, value) ->
                      (* Unbumping term. *)
                      let term_at_0 =
                        Term.bump_state Numeral.(~- kp1) term_at_kp1
                      in

                      if not (Term.bool_of_term value) then
                        (* Term is falsifiable. *)
                        term_at_0 :: flsbl_list, uknwn_list
                      else
                        (* Term is unknown. *)
                        flsbl_list, term_at_0 :: uknwn_list )
                    (* Note that we add the new falsifiable terms to
                       the old ones to avoid going through the list
                       again. *)
                    (falsifiable, [])
               |> (fun p -> Some p ) )

             (* Function ran if unsat. Returns None. *)
             ( fun () -> None )

             (* The actlit activates everything. *)
             [ term_of_actlit terms_actlit ]
         with

         | Some (new_falsifiable, new_unknown) ->
            (* Some terms are falsifiable, we shall loop. *)
            fun () ->
            split_closure
              two_state solver k kp1 all_vars new_falsifiable new_unknown

         | None ->
            (* The terms left are unfalsifiable, we shall return the
               result. *)
            fun () -> (falsifiable, terms)
       )
     in

     (* Deactivating actlits. *)
     term_of_actlit terms_actlit
     |> Term.mk_not
     |> Solver.assert_term solver ;

     (* Calling the tiny continuation. *)
     continue ()

  | _ ->
     (* No term left, we're done. *)
     (falsifiable, [])

       


(* Checks if some of the input terms are k-inductive. Returns a pair
   composed of the falsifiable terms and the unfalsifiable ones. *)
let query_step
      ({ solver ; two_state ; k ; all_vars ; step_mode } as context) terms =

  debug lsd "Query step." in

  terms
  |> List.iter
       ( fun t -> debug lsd "%s" (Term.string_of_term t) in () ) ;

  if not step_mode then assert_all_trans_at_k context ;

  (* Spliting the terms. *)
  split_closure two_state solver k Numeral.(k + one) all_vars [] terms


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

