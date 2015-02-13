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
open TermLib
open Actlit


type t = {

  (* Associates a transition systems to the k at which they are
     unrolled in the solver, an actlit (as a term) activating their
     initial state at 0, an actlit (as a term) activating the
     transition relations and the invariants, and an actlit (as a
     term) activating the transition relation at zero (and one for two
     state). *)
  mutable systems :
    (TransSys.t * (Numeral.t * Term.t)) list ;

  (* Solver used to query base. *)
  base_solver: SMTSolver.t ;

  (* Solver used to query step. *)
  step_solver: SMTSolver.t ;

  (* Solver used to prune trivial invariants. *)
  pruning_solver: SMTSolver.t ;

  mutable last_k : Numeral.t ;

  (* Indicates whether this instance is two state or not. *)
  two_state: bool ;
  
}

let name = TransSys.get_name

let shall_check_consistency = false

let check_consistency_sys solver k sys actlit called_by =

  if shall_check_consistency then (

    name sys
    |> Printf.sprintf
         "Checking consistency at %i for [%s]."
         Numeral.(to_int k)
    |> SMTSolver.trace_comment solver ;

    SMTSolver.check_sat_assuming
      solver
      (fun () ->
       (* Instance is sat for [sys], fine. *)
       ())
      (fun () ->
       (* Instance is unsat, let's crash. *)
       Event.log
         L_info
         "LSD @[<v>solver inconsistent at %i@ \
          for system [%s].@ \
          called by [%s].@]"
         (Numeral.to_int k)
         (TransSys.get_scope sys |> String.concat "/")
         called_by ;
       assert false)
      [ actlit ]
  )

(* Makes sure the solver of a lsd instance is consistent. *)
let check_consistency
      { systems ; base_solver ; step_solver }
      called_by =

  if shall_check_consistency then

    (* Making sure the solver instance is satisfiable for every
       system. *)
    systems
    |> List.iter

         ( fun (sys, (k, actlit)) ->
           (* Checking base consistency. *)
           check_consistency_sys base_solver k sys actlit called_by ;
           (* Checking step consistency. *)
           check_consistency_sys step_solver k sys actlit called_by )

(* Applies [f] to term bumped from [lbound] to [ubound]. *)
let rec bump_and_apply_bounds f lbound ubound term =
  if Numeral.( lbound <= ubound ) then (
    (* Bumping and applying f. *)
    Term.bump_state lbound term |> f ;
    (* Looping. *)
    bump_and_apply_bounds f Numeral.(succ lbound) ubound term
  )

let common_setup depth_opt (solver,sys,actlit) =

  name sys
  |> Printf.sprintf
       "Setting up system [%s]."
  |> SMTSolver.trace_comment solver ;

  SMTSolver.declare_fun solver actlit ;
  
  (* Defining uf's and declaring variables. *)
  TransSys.init_define_fun_declare_vars_of_bounds
    ~sub_define_top_only:true
    sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    Numeral.zero Numeral.(~- one);

  SMTSolver.trace_comment solver "Done defining, declaring now." ;

  (* Declaring unrolled vars at [-1] and [0]. *)
  TransSys.declare_vars_of_bounds
    sys
    (SMTSolver.declare_fun solver)
    Numeral.(~- one) Numeral.zero ;

  let actlit_term = Actlit.term_of_actlit actlit in

  solver, sys, actlit_term

let base_setup (solver,sys,actlit) =

  SMTSolver.trace_comment solver "Base setup." ;

  (* Conditionally asserting initial predicate at [0]. *)
  Term.mk_implies
    [ actlit ; TransSys.init_of_bound sys Numeral.zero ]
  |> SMTSolver.assert_term solver ;

  (* Conditionally asserting invariants of the system at [0]. *)
  Term.mk_implies
    [ actlit ; TransSys.invars_of_bound sys Numeral.zero ]
  |> SMTSolver.assert_term solver

let step_setup (solver, sys, actlit) =

  SMTSolver.trace_comment solver "Step setup." ;

  (* Conditionally asserting invariants of the system at [0]. *)
  Term.mk_implies
    [ actlit ; TransSys.invars_of_bound sys Numeral.zero ]
  |> SMTSolver.assert_term solver ;

  (* Declaring unrolled vars at [1]. *)
  TransSys.declare_vars_of_bounds
    sys
    (SMTSolver.declare_fun solver)
    Numeral.one Numeral.one ;
  
  (* Conditionally asserting transition predicate at [1]. *)
  Term.mk_implies
    [ actlit ; TransSys.trans_of_bound sys Numeral.one ]
  |> SMTSolver.assert_term solver ;

  (* Conditionally asserting invariants of the system at [1]. *)
  Term.mk_implies
    [ actlit ; TransSys.invars_of_bound sys Numeral.one ]
  |> SMTSolver.assert_term solver

let pruning_setup = step_setup

let unroll_solver solver sys actlit k =

  name sys
  |> Printf.sprintf
       "Unroll at %i for [%s]."
       Numeral.(to_int k)
  |> SMTSolver.trace_comment solver ;

  (* Declaring unrolled vars at [k+1]. *)
  TransSys.declare_vars_of_bounds
    sys (SMTSolver.declare_fun solver) k k ;

  (* Conditionally asserting transition predicate at [k]. *)
  Term.mk_implies
    [ actlit ; TransSys.trans_of_bound sys k ]
  |> SMTSolver.assert_term solver ;

  (* Conditionally asserting invariants of the system at [k]. *)
  Term.mk_implies
    [ actlit ; TransSys.invars_of_bound sys k ]
  |> SMTSolver.assert_term solver

let add_invariants_solver solver sys actlit k invariants =

  name sys
  |> Printf.sprintf
       "Add invariants at %i for [%s]."
       Numeral.(to_int k)
  |> SMTSolver.trace_comment solver ;

  Term.mk_and invariants
  |> Term.bump_and_apply_k
       (fun inv ->
        Term.mk_implies [ actlit ; inv ]
        |> SMTSolver.assert_term solver)
       k


(* Deletes the lsd solver. *)
let delete { base_solver ; step_solver ; pruning_solver } =
  SMTSolver.delete_instance base_solver ;
  SMTSolver.delete_instance step_solver ;
  SMTSolver.delete_instance pruning_solver

(* Returns the [k] at which a system is unrolled. *)
let get_k { systems } system =
  let k, _ = List.assq system systems in k

(* Adds new invariants to a lsd instance for system [sys]. Invariants
   are asserted up to the system [k]. *)
let add_invariants
      ({ systems ; base_solver ; step_solver } as lsd)
      sys = function
  | [] -> ()
  | invariants ->

     (* Finding the right system. *)
     let k, actlit =
       List.assq sys systems
     in

     (* Adding invariants in base at [k]. *)
     add_invariants_solver
       base_solver sys actlit k invariants ;
     (* Adding invariants in base at [k+1]. *)
     add_invariants_solver
       step_solver sys actlit Numeral.(succ k) invariants ;
     
     check_consistency lsd "add_invariants"

(* If mapping key [system] is defined in mapping [systems], swaps its
   value [info] with the result of applying [f] to [info]. *)
let swap_system_binding system f =
  
  let rec loop prefix = function
      
    | [] ->
       raise
         (Invalid_argument
            (Printf.sprintf
               "swap_system_binding: \
                unexpected system [%s]."
               (TransSys.get_scope system
                |> String.concat "/")))

    | (system', info) :: tail
         when system' == system ->
       (* Applying [f], appending to [tail]. *)
       (system', f info) :: tail
       (* Rev appending the prefix. *)
       |> List.rev_append prefix

    | head :: tail ->
       loop (head :: prefix) tail

  in

  loop []

(* Unrolls a system one step further. *)
let unroll_sys
      ( { systems ;
          base_solver ; step_solver ;
          last_k }
        as lsd)
      system =

  lsd.systems <- (
    systems
    |> swap_system_binding
         system
         (fun (k, actlit) ->

          (* Getting the next [k]. *)
          let kp1 = Numeral.succ k in

          (* Unrolling base solver at [k+1]. *)
          unroll_solver base_solver system actlit kp1 ;
          (* Unrolling step solver at [k+2]. *)
          unroll_solver step_solver system actlit Numeral.(succ kp1) ;

          (* Building new value for [system] in [systems]. *)
          kp1, actlit)
  ) ;

  check_consistency lsd "unroll_sys" ;

  ()

(* Creates a lsd instance. *)
let create two_state top_only sys depth_opt =

  let new_inst_sys () =
    SMTSolver.create_instance
      ~produce_assignments: true
      (TransSys.get_scope sys) depth_opt
      (TransSys.get_logic sys) (Flags.smtsolver ())
  in

  (* Solvers. *)
  let base_solver, step_solver, pruning_solver =
    new_inst_sys (), new_inst_sys (), new_inst_sys ()
  in

  (* let init_solver solver = *)
  (*   TransSys.declare_vars_global_const *)
  (*     (SMTSolver.declare_fun solver) *)
  (* in *)

  (* init_solver base_solver ; *)
  (* init_solver step_solver ; *)
  (* init_solver pruning_solver ; *)

  (* Building the associative list from (sub)systems to the k up to
     which they are asserted, their init and trans actlit. *)
  let systems =
    let rec loop all_sys = function
        
      | sys :: tail ->
         
         if List.mem_assq sys all_sys then
           (* We already know [sys], skipping. *)
           loop all_sys tail
                
         else
           (* First time seeing [sys], adding it to [all_sys], setting
              everything up in the solver and recursing on its kids
              and the tail of unvisited sys if not it top mode. *)

           (* Getting a fresh actlit for [sys]. *)
           let actlit = Actlit.fresh_actlit () in

           (* Setting up base. *)
           (base_solver, sys, actlit)
           |> common_setup depth_opt |> base_setup ;

           (* Setting up step. *)
           (step_solver, sys, actlit)
           |> common_setup depth_opt |> step_setup ;

           (* Setting up pruning. *)
           (pruning_solver, sys, actlit)
           |> common_setup depth_opt |> pruning_setup ;

           let actlit_term = Actlit.term_of_actlit actlit in

           (* Updating the map of all systems. *)
           let all_sys' =
             (sys, (Numeral.zero, actlit_term)) :: all_sys
           in

           if top_only then
             (* If top only then stop at the top level. *)
             all_sys'
           else
             (* Otherwise recursing to get subsystems. *)
             loop
               all_sys'
               (List.rev_append (TransSys.get_subsystems sys) tail)

      | [] -> all_sys
    in

    loop [] [sys]
  in

  (* Constructing the lsd context. *)
  let lsd =
    { systems ;
      base_solver ;
      step_solver ;
      pruning_solver ;
      last_k = Numeral.zero ;
      two_state }
  in

  if two_state then
    (* Unrolling all systems once in two-state mode. *)
    List.iter (fun (sys,_) -> unroll_sys lsd sys) systems ;

  (* Returning the lsd instance. *)
  lsd


let query_base
      { systems ; base_solver ; two_state }
      system terms_to_check =

  (* Getting the system info. *)
  let k, sys_actlit =
    List.assq system systems
  in

  Printf.sprintf
    "query_base at %i for [%s]."
    (Numeral.to_int k)
    (TransSys.get_scope system |> String.concat "/")
  |> SMTSolver.trace_comment base_solver ;

  (* Fresh actlit for the check (as a term). *)
  let actlit =
    (* Uf version. *)
    let actlit_uf = Actlit.fresh_actlit () in
    (* Declaring it. *)
    SMTSolver.declare_fun base_solver actlit_uf ;
    (* Term version. *)
    Actlit.term_of_actlit actlit_uf
  in

  (* Building the implication. *)
  Term.mk_implies
    [ actlit ;
      (* Making a conjunction of the terms to check. *)
      Term.mk_and terms_to_check
      (* Negating it. *)
      |> Term.mk_not
      (* Bumping it. *)
      |> Term.bump_state k ]
  (* Asserting implication. *)
  |> SMTSolver.assert_term base_solver ;

  (* Function to run if sat. *)
  let if_sat () =

    let minus_k = Numeral.(~- k) in

    (* Variables we want to know the value of. *)
    TransSys.vars_of_bounds
      system
      (if two_state then Numeral.pred k else k)
      k
    (* Getting their value. *)
    |> SMTSolver.get_model base_solver
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
    SMTSolver.check_sat_assuming
      base_solver
      if_sat if_unsat [ actlit ; sys_actlit ]
  in

  (* Deactivating actlit. *)
  Term.mk_not actlit
  |> SMTSolver.assert_term base_solver ;

  (* Returning result. *)
  result

(* Splits its input list of terms between the falsifiable and the
   unfalsifiable ones at [k+1]. The terms are asserted from 0 (1 if
   [two_state] is true) up to [k]. *)
let rec split_closure
  solver two_state trans_actlit k falsifiable = function

  | [] -> (falsifiable, [])

  | terms_to_check ->

     (* Fresh actlit for the check (as a term). *)
     let actlit =
       (* Uf version. *)
       let actlit_uf = Actlit.fresh_actlit () in
       (* Declaring it. *)
       SMTSolver.declare_fun solver actlit_uf ;
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
         |> SMTSolver.assert_term solver )
       (* In the two state case we start at one. *)
       (if two_state then Numeral.one else Numeral.zero)
       (* Going up to k. *)
       k
       conjunction ;

     let kp1 = Numeral.succ k in

     (* Asserting negative implication. *)
     SMTSolver.assert_term
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
         |> SMTSolver.get_values solver

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
       |> SMTSolver.assert_term solver ;

       (* Looping. *)
       split_closure
        solver two_state trans_actlit k falsifiable' unknown
                     
     in

     (* Function to run if unsat. *)
     let if_unsat () =
       (* Deactivating actlit. *)
       Term.mk_not actlit
       |> SMTSolver.assert_term solver ;
       
       (* Returning result. *)
       falsifiable, terms_to_check
     in

     (* Checking if we should terminate before doing anything. *)
     Event.check_termination () ;

     (* Checksat-ing. *)
     SMTSolver.check_sat_assuming
       solver
       if_sat
       if_unsat
       [ actlit ; trans_actlit ]



(* Prunes the terms which are a direct consequence of the transition
   relation. Assumes [T(0,1)] is asserted. *)
let rec prune_trivial
          solver result trivial_actlit = function
  | [] -> result, []
  | terms ->

     (* Fresh actlit for the check (as a term). *)
     let actlit =
       (* Uf version. *)
       let actlit_uf = Actlit.fresh_actlit () in
       (* Declaring it. *)
       SMTSolver.declare_fun solver actlit_uf ;
       (* Term version. *)
       Actlit.term_of_actlit actlit_uf
     in

     let bump_num = Numeral.one in

     let unbump_num = Numeral.(~- bump_num) in

     (* Bumping terms to one. *)
     let bumped_terms =
       terms
       |> List.map
            (Term.bump_state bump_num)
     in

     (* Asserting implication between actlit and terms@1. *)
     Term.mk_implies
       [ actlit ;
         Term.mk_and bumped_terms |> Term.mk_not ]
     |> SMTSolver.assert_term solver ;

     let if_sat () =
       Some (
         (* Getting the values of terms@1. *)
         SMTSolver.get_values
           solver bumped_terms
         (* Partitioning the list based on the value of the terms. *)
         |> List.fold_left
             ( fun (unknowns,falsifiables) (bumped_term, value) ->
               if value == Term.t_true then
                 (Term.bump_state unbump_num bumped_term)
                 :: unknowns,
                 falsifiables
               else
                 unknowns,
                 (Term.bump_state unbump_num bumped_term)
                 :: falsifiables )
             ([],[])
       )
     in

     let if_unsat () = None in

     match SMTSolver.check_sat_assuming
       solver if_sat if_unsat [actlit ; trivial_actlit]
     with
       | None ->
          (* Deactivating actlit. *)
          Term.mk_not actlit |> SMTSolver.assert_term solver ;
          (* Unsat, the terms cannot be falsified. *)
          result, terms
       | Some (unknowns, falsifiables) ->
          (* Deactivating actlit. *)
          Term.mk_not actlit |> SMTSolver.assert_term solver ;
          (* Looping. *)
          prune_trivial
            solver
            (List.concat [ result ; falsifiables ])
            trivial_actlit
            unknowns

(* Unrolls [system] one step further ([k+1), and returns the terms
   from [terms_to_check] which are unfalsifiable in the [k]-induction
   step instance. *)
let increment_and_query_step
      ({ systems ; step_solver ; pruning_solver ; two_state } as lsd)
      system
      terms_to_check =

  (* Getting system info. *)
  let k, actlit = List.assq system systems in

  name system
  |> Printf.sprintf
       "prune_trivial for [%s]."
  |> SMTSolver.trace_comment pruning_solver ;

  let not_trivial, trivial =
    (* Pruning direct consequences of the transition relation if
          the flag requests it. *)
    if Flags.invgengraph_prune_trivial () then
      prune_trivial
        pruning_solver [] actlit terms_to_check
    else terms_to_check, []
  in

  match not_trivial with
  | [] ->
     (* Unrolling system. *)
     unroll_sys lsd system ;
     
     [], trivial
  | _ ->

     name system
     |> Printf.sprintf
          "query_step at %i for [%s]."
          (Numeral.to_int k)
     |> SMTSolver.trace_comment step_solver ;

     let invariants =
       (* Splitting terms. *)
       split_closure
         step_solver two_state actlit k [] not_trivial
       (* Discarding falsifiable terms. *)
       |> snd
     in

     (* Unrolling system. *)
     unroll_sys lsd system ;

     invariants, trivial


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

