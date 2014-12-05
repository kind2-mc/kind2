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

type t = {

  (* Associates a transition systems to the k at which they are
     unrolled in the solver, and an actlit (as a term) activating
     their initial state at 0. *)
  mutable systems: (TransSys.t * (Numeral.t * Term.t)) list ;

  (* The solver used to query step and base. *)
  solver: Solver.t ;

  (* Indicates whether this instance is two state or not. *)
  two_state: bool ;

  (* The k at which this lsd instance is. *)
  mutable k: Numeral.t ;

  (* Invariants asserted up to [k+1]. *)
  mutable invariants: Term.t list ;
  
}

(* The k this lsd instance is at. *)
let get_k { k } = k

(* Makes sure the solver of a lsd instance is consistent. *)
let check_consistency { systems ; k ; solver } =

  let kp1 = Numeral.succ k in

  (* Making sure the systems are unrolled at k or k+1.*)
  assert
    ( systems
      |> List.for_all
           ( fun (_, (k',_)) -> Numeral.(k' = k)
                                || Numeral.(k' = kp1) ) ) ;

  (* Making sure the solver instance is satisfiable. *)
  assert
    ( Solver.check_sat solver )

(* Applies [f] to term bumped from [lbound] to [ubound]. *)
let rec bump_and_apply_bounds f lbound ubound term =
  if Numeral.( lbound <= ubound ) then (
    (* Bumping and applying f. *)
    Term.bump_state lbound term |> f ;
    (* Looping. *)
    bump_and_apply_bounds f Numeral.(succ lbound) ubound term
  )

(* Adds new invariants to a lsd instance. Invariants are asserted up
   to k+1 so that they are active for step. *)
let add_invariants ({ k ; solver ; invariants } as context)
  = function
  | [] -> ()
  | invariants' ->
     
     let kp1 = Numeral.succ k in
     
     (* Building the conjunction of new invariants. *)
     Term.mk_and invariants'
     (* Asserting all invariants from 0 to k+1. *)
     |> bump_and_apply_bounds
          (Solver.assert_term solver)
          Numeral.zero
          kp1 ;
     
     (* Updating context. *)
     context.invariants <- List.rev_append invariants' invariants

     (* Making sure everything makes sense. *)
     (* check_consistency context *)


(* Unrolls [sys] at [k+1] if it is only unrolled up to [k]. *)
let soft_increment ({ systems ; k ; solver } as context) system =

  let rec loop prefix = function
      
    | (sys, (sys_k,actlit)) :: tail when sys == system ->
       
       if Numeral.( k = sys_k ) then
         let kp1 = Numeral.succ k in
         (* Asserting transition relation at [k+1]. *)
         TransSys.trans_of_bound sys kp1
         |> Solver.assert_term solver ;
         (* Updating with updated associative list. *)
         context.systems <-
           (sys, (kp1, actlit)) :: tail
           |> List.rev_append prefix

       else
         (* Making sure [sys_k] is legal. *)
         assert ( Numeral.( sys_k = succ k ) ) ;
         (* Nothing to do. *)
       ()

    | head :: tail -> loop (head :: prefix) tail

    | [] -> raise Not_found

  in
       
  
  try
    loop [] systems
  with
  | Not_found ->
     raise
       (Invalid_argument
          (Printf.sprintf
             "Unexpected system [%s]."
             (TransSys.get_scope system |> String.concat "/")))


(* Increments the [k] of a lsd instance. Performs soft increment while
   doing so. *)
let increment ({ systems ; k ; solver ; invariants } as context) =

  (* Soft incrementing every system. *)
  systems
  |> List.iter
       (fun (sys, _) -> soft_increment context sys) ;

  (* Asserting invariants at k+2 (k+1+1, for step. Invariants are
     already asserted at k+1.). *)
  ( match invariants with
    | [] -> ()
    | invariants ->
       Term.mk_and invariants
       |> Term.bump_state Numeral.(succ (succ k))
       |> Solver.assert_term solver ) ;

  (* Incrementing the k. *)
  context.k <- Numeral.succ context.k

  (* Making sure everything is legal. *)
  (* check_consistency context *)

  
(* Creates a lsd instance. *)
let create two_state top_only sys =

  (* Creating solver. *)
  let solver =
    TransSys.get_logic sys
    |> Solver.new_solver ~produce_assignments: true
  in

  (* Building the associative list from (sub)systems to the k up to
     which they are asserted and their init actlit. *)
  let systems =
    let rec loop all_sys = function
        
      | sys :: tail ->
         
         if List.mem_assq sys all_sys then
           (* We already know [sys], skipping. *)
           loop all_sys tail
                
         else
           (* First time seeing [sys], adding it to [all_sys] and
              recursing on its kids and the tail of unvisited sys. *)

           (* Fresh actlit. *)
           let actlit = Actlit.fresh_actlit () in
           (* Declaring it. *)
           Solver.declare_fun solver actlit ;
           (* Term version. *)
           let actlit_term = Actlit.term_of_actlit actlit in

           let all_sys' =
             (sys, (Numeral.zero, actlit_term)) :: all_sys
           in

           if top_only then
             (* If top only then we do not recurse. *)
             all_sys'
           else
             (* Otherwise recursing. *)
             loop
               all_sys'
               (List.rev_append (TransSys.get_subsystems sys) tail)

      | [] -> all_sys
    in

    loop [] [sys]
  in

  (* Declaring the init flag. *)
  Solver.declare_fun solver TransSys.init_flag_uf ;

  (* Defining things. *)
  TransSys.iter_uf_definitions sys (Solver.define_fun solver) ;

  (* For each system, declare things and assert the implication
     between its init actlit and its init predicate. Also, declare
     system invariants at 0 and extract them. *)
  let invariants =
    systems
    |> List.fold_left
        ( fun list (sys, (zero, actlit)) ->

          (* Declaring things. *)
          TransSys.iter_state_var_declarations
            sys (fun sv ->
              if sv != TransSys.init_flag_uf
              then Solver.declare_fun solver sv) ;
         
          (* Building the init implication. *)
          Term.mk_implies
            [ actlit ; TransSys.init_of_bound sys zero ]
            |> Solver.assert_term solver ;

          (* Invariants if the system at 0. *)
          let invariants =
            TransSys.invars_of_bound sys Numeral.zero
          in

          (* Asserting trans sys invariants. *)
          Solver.assert_term solver invariants ;
          
          invariants :: list )
        []
  in


  (* Constructing the lsd context. *)
  let lsd = {
    systems ;
    solver ;
    two_state ;
    k = Numeral.zero ;
    invariants = invariants ;
  } in

  (* Making the lsd instance is consistent. *)
  (* check_consistency lsd ; *)

  (* Incrementing if we are in two state mode. *)
  if two_state then (
    (* Asserting invariants at 1 if in two_state mode. *)
    List.iter
      (fun inv -> Term.bump_state Numeral.one inv
                  |> Solver.assert_term solver)
      invariants ;
    
    increment lsd
  ) ;

  (* Returning the lsd instance. *)
  lsd


(* Deletes the lsd solver. *)
let delete { solver } = Solver.delete_solver solver



let query_base ({ systems ; solver ; two_state ; k } as context)
               system
               terms_to_check =

  try

    (* Getting the actlit for the init predicate of [system]. *)
    let _, init_actlit =
      List.assq system systems
    in

    (* Fresh actlit for the check (as a term). *)
    let actlit =
      (* Uf version. *)
      let actlit_uf = Actlit.fresh_actlit () in
      (* Declaring it. *)
      Solver.declare_fun solver actlit_uf ;
      (* Term version. *)
      Actlit.term_of_actlit actlit_uf
    in

    (* Bumped, negated conjunction of the terms to check. *)
    let terms_falsification_at_k =
      (* Making a conjunction of the terms to check. *)
      Term.mk_and terms_to_check
      (* Negating it. *)
      |> Term.mk_not
      (* Bumping it. *)
      |> Term.bump_state k
    in

    (* Building the implication. *)
    Term.mk_implies [ actlit ; terms_falsification_at_k ]
    (* Asserting it. *)
    |> Solver.assert_term solver ;

    (* Function to run if sat. *)
    let if_sat () =

      let minus_k = Numeral.(~- k) in

      (* Variables we want to know the value of. *)
      TransSys.vars_of_bounds
        system
        (if two_state then Numeral.pred k else k)
        k
      (* Getting their value. *)
      |> Solver.get_model solver
      (* Bumping to -k. *)
      |> List.map
           ( fun (v,t) ->
             (Var.bump_offset_of_state_var_instance
                minus_k v),
             t )
      (* Making an option out of it. *)
      |> (fun model -> Some model)
    in

    (* Function to run if unsat. *)
    let if_unsat () = None in

    (* Checking if we should terminate before doing anything. *)
    Event.check_termination () ;

    (* Checksat-ing. *)
    let result =
      Solver.check_sat_assuming
        solver if_sat if_unsat [ actlit ; init_actlit ]
    in

    (* Deactivating actlit. *)
    Term.mk_not actlit
    |> Solver.assert_term solver ;

    (* Returning result. *)
    result


  with
  | Not_found ->
     raise
       (Invalid_argument
          (Printf.sprintf
             "Unexpected system [%s]."
             (TransSys.get_scope system |> String.concat "/")))



let rec split_closure solver two_state k falsifiable = function

  | [] -> (falsifiable, [])

  | terms_to_check ->

     (* Fresh actlit for the check (as a term). *)
     let actlit =
       (* Uf version. *)
       let actlit_uf = Actlit.fresh_actlit () in
       (* Declaring it. *)
       Solver.declare_fun solver actlit_uf ;
       (* Term version. *)
       Actlit.term_of_actlit actlit_uf
     in

     (* Conjunction of terms to check. *)
     let conjunction =
       Term.mk_and terms_to_check
     in
     
     (* Asserting positive implications. *)
     bump_and_apply_bounds
       ( fun bumped ->
         (* Building the implication. *)
         Term.mk_implies [ actlit ; bumped ]
         (* Asserting it. *)
         |> Solver.assert_term solver )
       (* In the two state case we start at one. *)
       (if two_state then Numeral.one else Numeral.zero)
       (* Going up to k. *)
       k
       conjunction ;

     let kp1 = Numeral.succ k in

     (* Asserting negative implication. *)
     Solver.assert_term
       solver
       (Term.mk_implies
          [ actlit ;
            (* Bumping conjunction. *)
            Term.bump_state kp1 conjunction
            (* Negating it. *)
            |> Term.mk_not ]) ;

     (* Function to run if sat. *)
     let if_sat () =

       let minus_kp1 = Numeral.(~- kp1) in
       
       let falsifiable', unknown =
         terms_to_check
         (* We want the value of the terms a k+1. *)
         |> List.map (Term.bump_state kp1)
         |> Solver.get_values solver

         (* Separating falsifiable ones from the rest, bumping back at
            the same time. *)
         |> List.fold_left

              ( fun (falsifiable, unknown) (term,value) ->                
                (* Unbumping term. *)
                let unbumped_term =
                  Term.bump_state minus_kp1 term
                in
                if value == Term.t_true then
                  falsifiable, unbumped_term :: unknown
                else
                  unbumped_term :: falsifiable, unknown )
              
              (falsifiable, [])
       in

       (* Deactivating actlit. *)
       Term.mk_not actlit
       |> Solver.assert_term solver ;

       (* Looping. *)
       split_closure solver two_state k falsifiable' unknown
                     
     in

     (* Function to run if unsat. *)
     let if_unsat () =
       (* Deactivating actlit. *)
       Term.mk_not actlit
       |> Solver.assert_term solver ;
       
       (* Returning result. *)
       falsifiable, terms_to_check
     in

     (* Checking if we should terminate before doing anything. *)
     Event.check_termination () ;

     (* Checksat-ing. *)
     Solver.check_sat_assuming
       solver
       if_sat
       if_unsat
       [ actlit ]



(* Prunes the terms which are a direct consequence of the transition
   relation. Assumes [T(0,1)] is asserted. *)
let rec prune_obvious solver result = function
  | [] -> result
  | terms ->

     (* Fresh actlit for the check (as a term). *)
     let actlit =
       (* Uf version. *)
       let actlit_uf = Actlit.fresh_actlit () in
       (* Declaring it. *)
       Solver.declare_fun solver actlit_uf ;
       (* Term version. *)
       Actlit.term_of_actlit actlit_uf
     in

     (* Bumping terms to one. *)
     let bumped_terms =
       List.map (Term.bump_state Numeral.one) terms
     in

     (* Asserting implication between actlit and terms@1. *)
     Term.mk_implies
       [ actlit ;
         Term.mk_and bumped_terms |> Term.mk_not ]
     |> Solver.assert_term solver ;

     let if_sat () =
       Some (
         (* Getting the values of terms@1. *)
         Solver.get_values
           solver bumped_terms
         (* Partitioning the list based on the value of the terms. *)
         |> List.fold_left
             ( fun (unknowns,falsifiables) (term_at_1, value) ->
               if value == Term.t_true then
                 (Term.bump_state Numeral.(~- one) term_at_1)
                 :: unknowns,
                 falsifiables
               else
                 unknowns,
                 (Term.bump_state Numeral.(~- one) term_at_1)
                 :: falsifiables )
             ([],[])
       )
     in

     let if_unsat () = None in

     match Solver.check_sat_assuming
       solver if_sat if_unsat [actlit]
     with
       | None ->
         debug lsd "Pruning %i invariants." (List.length terms) in
         (* Deactivating actlit. *)
         Term.mk_not actlit |> Solver.assert_term solver ;
         (* Unsat, the terms cannot be falsified. *)
         result
       | Some (unknowns, falsifiables) ->
         (* Deactivating actlit. *)
         Term.mk_not actlit |> Solver.assert_term solver ;
         (* Looping. *)
         prune_obvious
           solver (List.concat [ result ; falsifiables ]) unknowns

let query_step ({ systems ; solver ; two_state ; k } as context)
               system
               terms_to_check =

  (* Soft incrementing the system. *)
  soft_increment context system ;

  (* Splitting terms. *)
  split_closure solver two_state k [] terms_to_check
    (* Pruning direct consequences of the transition relation. *)
  |> snd (*|> prune_obvious solver []*)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

