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

let solver_ref = ref None

(* Output statistics *)
let print_stats () =

  Event.stat 
    [Stat.misc_stats_title, Stat.misc_stats;
     Stat.ind_stats_title, Stat.ind_stats;
     Stat.smt_stats_title, Stat.smt_stats]

(* Clean up before exit *)
let on_exit _ =

  (* Stopping all timers. *)
  Stat.ind_stop_timers ();
  Stat.smt_stop_timers ();

  (* Output statistics *)
  print_stats ();

  (* Deleting solver instance if created. *)
  (try
      match !solver_ref with
      | None -> ()
      | Some solver ->
         Solver.delete_solver solver |> ignore ;
         solver_ref := None
    with
    | e -> 
       Event.log L_error
                 "Error deleting solver_init: %s" 
                 (Printexc.to_string e))

let exit solver =
  (* Stat.ind_stop_timers (); *)
  (* Stat.smt_stop_timers (); *)
  (* Solver.delete_solver solver |> ignore ; *)
  (* solver_ref := None *)
  ()

(* Returns true if the property is not falsified or valid. *)
let shall_keep trans (s,_) =
  match TransSys.get_prop_status trans s with
  | TransSys.PropInvariant | TransSys.PropFalse _ -> false
  | _ -> true

let is_confirmed trans k (s,_) =
  match TransSys.get_prop_status trans s with
  | TransSys.PropKTrue k' -> k' >= k - 1
  | _ -> false

let rec confirm trans solver continuation unfalsifiable k =

  let k_int = Numeral.to_int k in

  let rec loop invariants to_check =
    (* Getting new invariants and valid / falsified properties. *)
    let new_invariants, new_valids, new_falsifieds =
      Event.recv () |> Event.update_trans_sys_tsugi trans
    in

    let new_to_check =
      List.filter (shall_keep trans) to_check
    in
    match new_falsifieds with
    | [] ->
       if List.for_all (is_confirmed trans k_int) new_to_check
       then
         (List.iter
            (fun (s, _) ->
             Event.prop_status TransSys.PropInvariant trans s)
            new_to_check ;
          None)
       else
         (minisleep 0.001 ;
          loop
            (List.rev_append new_invariants invariants)
            new_to_check)
    | _ ->
       Some (trans, solver, k,
            List.rev_append new_invariants invariants,
            [], new_to_check)
  in

  match loop [] unfalsifiable with
  | None ->
     debug step "[Step@%i] exiting." (Numeral.to_int k) in
     exit solver
  | Some context -> continuation context

(* Deactivates an actlit by asserting its negation. *)
let deactivate solver actlit =
  actlit
  |> Term.mk_not
  |> Solver.assert_term solver

(* Creating a fresh actlit for path compression. *)
let path_comp_actlit = fresh_actlit ()
(* Term version. *)
let path_comp_act_term = path_comp_actlit |> term_of_actlit

(* Check-sat and splits properties.. *)
let split trans solver k to_split actlits =

  (* Function to run if sat. *)
  let if_sat () =
    (* Get-model function. *)
    let get_model = Solver.get_model solver in
    (* Extracting the counterexample and returning it. *)
    Some(TransSys.path_from_model trans get_model k,
         TransSys.vars_of_bounds trans k k |> get_model)
  in

  (* Function to run if unsat. *)
  let if_unsat () = None in

  (* Appending to the list of actlits. *)
  let all_actlits = path_comp_act_term :: actlits in

  (* Loops as long as counterexamples can be compressedp *)
  let rec loop () = 
    match
      (* Check sat assuming with actlits. *)
      Solver.check_sat_assuming
        solver if_sat if_unsat all_actlits
    with

    | Some (cex,model) ->
       (* Attempting to compress path. *)
       ( match
           if not (Flags.ind_compress ()) then [] else
             Compress.check_and_block
               (Solver.declare_fun solver) trans cex
         with

         | [] ->
            (* Cannot compress path, splitting properties. *)

            (* Evaluation function. *)
            let eval term =
              Eval.eval_term (TransSys.uf_defs trans) model term
              |> Eval.bool_of_value in

            (* Splitting properties. *)
            let new_to_split, new_falsifiable =
              List.partition
                ( fun (_, term) ->
                  Term.bump_state k term |> eval )
                to_split in

            (* Building result. *)
            Some (new_to_split, new_falsifiable)

         | compressor ->
            (* Path compressing, building term and asserting it. *)
            Term.mk_or
              [ path_comp_act_term |> Term.mk_not ;
                compressor |> Term.mk_and ]
            |> Solver.assert_term solver ;
            (* Rechecking satisfiability. *)
            loop () )

    | None -> None
  in

  loop ()

(* Splits its input list of properties between those that can be
   falsified and those that cannot. Actlits activate the properties to
   split AND optimistic ones from 0 to k-1. Optimistics at k are added
   with the negation of the properties to split and are activated by
   the same actlit. This makes backtracking easy since positive
   actlits are not overloaded. *)
let split_closure trans solver k actlits optimistics to_split =

  let rec loop falsifiable list =
    (* Building negative term. *)
    let neg_term =
      list
      |> List.map snd
      |> Term.mk_and |> Term.mk_not |> Term.bump_state k in
    (* Adding optimistic properties at k. *)
    let term =
      neg_term ::
        ( optimistics
          |> List.map
               (fun (_, t) -> t |> Term.bump_state k) )
      |> Term.mk_and
    in
    (* Getting a fresh actlit for it. *)
    let actlit = fresh_actlit () in
    (* Declaring actlit. *)
    actlit |> Solver.declare_fun solver ;
    (* Transforming it to a term. *)
    let actlit_term = actlit |> term_of_actlit in
    (* Asserting implication. *)
    Term.mk_or
        [ actlit_term |> Term.mk_not ; term ]
    |> Solver.assert_term solver ;
    (* All actlits. *)
    let all_actlits = actlit_term :: actlits in
    (* Splitting. *)
    match split trans solver k list all_actlits with
    | None ->
       (* Deactivating negative actlit. *)
       deactivate solver actlit_term ;
       list, falsifiable
    | Some ([], new_falsifiable) ->
       (* Deactivating negative actlit. *)
       deactivate solver actlit_term ;
       [], List.rev_append new_falsifiable falsifiable
    | Some (new_list, new_falsifiable) ->
       (* Deactivating negative actlit. *)
       deactivate solver actlit_term ;
       loop (List.rev_append new_falsifiable falsifiable) new_list
  in

  loop [] to_split

(* Performs the next iteration, called by next after handling
   falsifieds properties. *)
let rec next_no_falsifieds
          continuation
          (trans, solver, k,
           nu_invariants, nu_optimistics, nu_unknowns) =

  let k_minus_one = Numeral.(k-one) in

  match nu_unknowns, nu_optimistics with
  | [], [] -> exit solver

  | [], _ ->
     confirm trans solver
             (next_no_falsifieds continuation) nu_optimistics k

  | _ ->
     let k_int = Numeral.to_int k in

     (* Notifying framework of our progress. *)
     Stat.set k_int Stat.ind_k ;
     Event.progress k_int ;
     Stat.update_time Stat.ind_total_time ;

     (* Building the positive actlits and corresponding implications
        at k-1 for unknowns. *)
     let actlits, implications =
       nu_unknowns
       |> List.fold_left
            ( fun (actlits,implications) (_,term) ->
              (* Building the actlit. *)
              let actlit_term =
                generate_actlit term |> term_of_actlit
              in

              (* Appending it to the list of actlits. *)
              actlit_term :: actlits,
              (* Building the implication and appending. *)
              (Term.mk_or [
                   Term.mk_not actlit_term ;
                   Term.bump_state k_minus_one term
              ]) :: implications )
            ([], [])
     in

     (* Doing the same for optimistics and appending to those for
        unknowns. *)
     let all_actlits, all_implications =
       nu_optimistics
       |> List.fold_left
            ( fun (actlits,implications) (_,term) ->
              (* Building the actlit. *)
              let actlit_term =
                generate_actlit term |> term_of_actlit
              in

              (* Appending it to the list of actlits. *)
              actlit_term :: actlits,
              (* Building the implication and appending. *)
              (Term.mk_or [
                   Term.mk_not actlit_term ;
                   Term.bump_state k_minus_one term
              ]) :: implications )
            (actlits, implications)
     in

     (* Asserting all the implications. *)
     all_implications
     |> Term.mk_and
     |> Solver.assert_term solver ;

     (* Splitting (asserts the actlit implications). *)
     let unfalsifiable, falsifiable =
       split_closure
         trans solver k
         all_actlits nu_optimistics nu_unknowns
     in

     (* Output statistics *)
     if output_on_level L_info then print_stats ();

     (* Looping. *)
     continuation
       (trans, solver, Numeral.(k+one),
        nu_invariants,
        List.rev_append unfalsifiable nu_optimistics,
        falsifiable)

(* Performs the next check after updating its context with new
   invariants and falsified properties. Assumes the solver is
   in the following state:

   actlit(prop) => prop@i
     for all 0 <= i <= k-2 and prop      in 'unknowns'
                                        and 'optimistics';

   invariant@i
     for all 0 <= i <= k-1 and invariant in 'invariants';

   T[i-1,i]
     for all 1 <= i <= k.

   Note that the transition relation for the current iteration is
   already asserted. *)
let rec next (trans, solver, k,
              invariants, optimistics, unknowns) =

  (* Asserts terms from 0 to k. *)
  let assert_new_invariants k terms =
    terms
    |> Term.mk_and
    |> Term.bump_and_apply_k
         (Solver.assert_term solver) k
  in

  (* Asserts terms at k+1. *)
  let assert_old_invariants terms =
    terms
    |> Term.mk_and
    |> Term.bump_state k
    |> Solver.assert_term solver
  in

  (* Getting new invariants and valid / falsified properties. *)
  let new_invariants, new_valids, new_falsifieds =
    Event.recv () |> Event.update_trans_sys_tsugi trans
  in

  (* Cleaning unknowns and optimistics by removing invariants and
     falsifieds. *)
  let nu_unknowns, nu_optimistics =
    match new_valids, new_falsifieds with
    | [], [] -> unknowns, optimistics
    | _ ->
       unknowns    |> List.filter (shall_keep trans),
       optimistics |> List.filter (shall_keep trans)
  in

  match new_falsifieds, nu_optimistics with
  | [], _ | _, [] ->

     (* Asserting transition relation. *)
     TransSys.trans_of_bound trans k
     |> Solver.assert_term solver
     |> ignore ;

     (* Merging old and new invariants and asserting them. *)
     let nu_invariants =
       match invariants, new_invariants with
       | [],[] -> []
       | _, [] ->
          assert_old_invariants invariants ;
          invariants
       | [], _ ->
          assert_new_invariants k new_invariants ;
          new_invariants
       | _ ->
          assert_old_invariants invariants ;
          assert_new_invariants k new_invariants ;
          List.rev_append new_invariants invariants
     in

     (* No need to backtrack, moving on. *)
     next_no_falsifieds
       next
       (trans, solver, k,
        nu_invariants, nu_optimistics, nu_unknowns)

  | _ ->

     (* Merging old and new invariants and asserting only the new ones
        up to k-1 since we are backtracking. *)
     let nu_invariants =
       match invariants, new_invariants with
       | [],[] -> []
       | _, [] ->
          invariants
       | [], _ ->
          assert_new_invariants Numeral.(k-one) new_invariants ;
          new_invariants
       | _ ->
          assert_new_invariants Numeral.(k-one) new_invariants ;
          List.rev_append new_invariants invariants
     in

     (* Backtracking, i.e. cancelling optimistics and relaunching at
        k-1. *)
     next_no_falsifieds
       next
       (trans, solver, Numeral.(k-one),
        nu_invariants,
        [],
        List.rev_append nu_optimistics nu_unknowns)

(* Initializes the solver for the first check. *)
let init trans =
  (* Starting the timer. *)
  Stat.start_timer Stat.ind_total_time;

  (* Getting properties. *)
  let unknowns =
    (TransSys.props_list_of_bound trans Numeral.zero)
  in

  (* Creating solver. *)
  let solver =
    TransSys.get_logic trans
    |> Solver.new_solver ~produce_assignments:true
  in

  (* Memorizing solver for clean on_exit. *)
  solver_ref := Some solver ;

  (* Declaring uninterpreted function symbols. *)
  TransSys.iter_state_var_declarations
    trans
    (Solver.declare_fun solver) ;

  (* Declaring positive actlits. *)
  List.iter
    (fun (_, prop) ->
     generate_actlit prop
     |> Solver.declare_fun solver)
    unknowns ;

  (* Declaring path compression actlit. *)
  path_comp_actlit |> Solver.declare_fun solver ;

  (* Declaring path compression function. *)
  Compress.init (Solver.declare_fun solver) trans ;

  (* Defining functions. *)
  TransSys.iter_uf_definitions
    trans
    (Solver.define_fun solver) ;

  (* Returning context. *)
  (trans, solver, Numeral.one, [], [], unknowns)

(* Runs the step instance. *)
let main trans = init trans |> next


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

