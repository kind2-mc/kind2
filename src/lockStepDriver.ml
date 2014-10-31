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
  mutable invariants: Term.t list
}

(* Creates a lock step driver based on a transition system. *)
let create trans =
  (* Creating solver. *)
  let solver =
    TransSys.get_logic trans
    |> Solver.new_solver ~produce_assignments: true
  in

  (* (\* Building the list of top node vars at 0, declaring their *)
  (*    uninterpreted function symbols at the same time. *\) *)
  (* let top_node_vars = *)
  (*   TransSys.state_vars trans *)
  (*   |> List.map *)
  (*        ( fun sv -> *)
  (*          StateVar.uf_symbol_of_state_var sv *)
  (*          |> Solver.declare_fun solver ; *)
  (*          Var.mk_state_var_instance sv Numeral.zero ) *)
  (* in *)

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
         
         ([], [], [])
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

  (* Asserting all transitions predicates at one for step. *)
  all_transitions_conj
  |> Term.bump_state Numeral.zero
  |> Solver.assert_term solver ;

  (* Return the context of the solver. *)
  { trans = trans ;
    solver = solver ;
    all_vars = (TransSys.init_flag_var Numeral.zero) :: all_vars ;
    all_transitions = all_transitions_conj ;
    init_actlit = init_actlit_term ;
    k = Numeral.zero ;
    invariants = [] }

(* Deletes a lock step driver. *)
let delete context =
  Solver.delete_solver context.solver

(* The k of the lock step driver. *)
let get_k { k } = k

(* Increments the k of a lock step driver. Basically asserts the
   transition relation and unrolls the invariants one step further. *)
let increment
      ({ solver ; k ; all_transitions ; invariants } as context) =

  (* New k. *)
  let new_k = Numeral.(k + one) in
  (* New k + 1. *)
  let new_kp1 = Numeral.(new_k + one) in

  (* Asserting all transitions predicates at k+1. *)
  all_transitions
  |> Term.bump_state new_k
  |> Solver.assert_term solver ;

  (* Asserting all invariants at k. *)
  invariants
  |> Term.mk_and
  |> Term.bump_state new_kp1
  |> Solver.assert_term solver ;

  (* Updating context. *)
  context.k <- Numeral.(context.k + one)

(* Unrolls a term from 0 to k, returns the list of unrolled terms. *)
let unroll_term_up_to_k k term =
  let rec loop i unrolled =
    if Numeral.(i > zero) then
      Term.bump_state i term :: unrolled
      |> loop Numeral.(i - one)
    else if Numeral.(i = zero) then
      (Term.bump_state i term) :: unrolled
    else
      Failure
        (Printf.sprintf "Illegal negative k: %i." (Numeral.to_int i))
      |> raise
  in
  loop k []

(* Adds new invariants to a lock step driver. *)
let new_invariants ({ solver ; k ; invariants } as context)
                   new_invariants =

  (* We will be asserting them up to k+1 for step. *)
  let kp1 = Numeral.(k + one) in
  
  (* Asserting new invariants from 0 to k+1, memorizing them at the
     same time. *)
  new_invariants
  |> List.fold_left
       (* Taking one invariant. *)
       ( fun list inv ->
         (* Asserting it from 0 to k+1 as a conjunction. *)
         unroll_term_up_to_k kp1 inv
         |> Term.mk_and
         |> Solver.assert_term solver ;
         (* Appending to old invariants. *)
         inv :: list )
       invariants
  |> (fun invs -> context.invariants <- invs)


(* Checks if some of the input terms are falsifiable k steps from the
   initial states. Returns Some of a counterexample if some are, None
   otherwise. *)
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
        Solver.get_values solver terms_at_k |> ignore ;
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
let rec split_closure solver k kp1 all_vars falsifiable terms =
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
                unroll_term_up_to_k k term |> Term.mk_and ]
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
            split_closure solver k kp1 all_vars new_falsifiable new_unknown

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

(* (\* Splits terms between those that are falsifiable at k+1 and those *)
(*    that are not.  *)

(*    Optimisation: while getting the values, prepare terms for the *)
(*    next iteration. *\) *)
(* let rec split_closure_path_comp *)
(*           trans solver k kp1 all_vars falsifiable terms = *)
(*   match terms with *)
(*   | _ :: _ -> *)

(*      (\* Getting a fresh actlit. *\) *)
(*      let terms_actlit = fresh_actlit () in *)

(*      (\* Declaring it. *\) *)
(*      terms_actlit |> Solver.declare_fun solver ; *)

(*      (\* Term version of the actlit. *\) *)
(*      let terms_actlit_term = term_of_actlit terms_actlit in *)

(*      (\* Building the list of terms at k+1. At the same time, we create *)
(*         the implications between actlit and terms from 0 to k. *\) *)
(*      let terms_at_kp1 = *)
(*        terms *)
(*        |> List.map *)
(*             ( fun term -> *)

(*               (\* Asserting that actlit implies term from 0 to k. The *)
(*                  actlit gets overloaded for each term. *\) *)
(*               [ terms_actlit_term ; *)
(*                 unroll_term_up_to_k k term |> Term.mk_and ] *)
(*               |> Term.mk_implies *)
(*               |> Solver.assert_term solver ; *)

(*               (\* Bumping term to kp1. *\) *)
(*               Term.bump_state kp1 term ) *)
(*      in *)

(*      (\* Overloading the actlit one last time for the negation of the *)
(*         terms. *\) *)
(*      [ terms_actlit_term ; *)
(*        (terms_at_kp1 |> Term.mk_and |> Term.mk_not) ] *)
(*      |> Term.mk_implies *)
(*      |> Solver.assert_term solver ; *)

(*      (\* Building a small continuation to deactivate the actlit before *)
(*         we go on. *\) *)
(*      let continue = *)
(*        let rec loop () = *)
(*          ( match *)
(*              (\* Check-sat-assuming time. *\) *)
(*              Solver.check_sat_assuming *)
(*                solver *)

(*                (\* Function ran if sat. Returns Some of the falsifiable *)
(*                   terms, INCLUDING THE ONES WE ALREADY KNOW ARE *)
(*                   FALSIFIABLE, and the unknown ones. *\) *)
(*                ( fun () -> *)
(*                  (\* Get-model function. *\) *)
(*                  let get_model = Solver.get_model solver in *)
(*                  (\* Extracting the counterexample. *\) *)
(*                  let cex = *)
(*                    TransSys.path_from_model trans get_model k in *)
(*                  (\* Attempting to compress path. *\) *)
(*                  ( match *)
(*                      Compress.check_and_block *)
(*                        (Solver.declare_fun solver) trans cex *)
(*                    with *)

(*                    | [] -> *)
(*                       Solver.get_values solver terms_at_kp1 *)
(*                       |> List.fold_left *)
(*                            ( fun (flsbl_list, uknwn_list) *)
(*                                  (term_at_kp1, value) -> *)
(*                              (\* Unbumping term. *\) *)
(*                              let term_at_0 = *)
(*                                Term.bump_state *)
(*                                  Numeral.(~- kp1) term_at_kp1 *)
(*                              in *)

(*                              if not (Term.bool_of_term value) then *)
(*                                (\* Term is falsifiable. *\) *)
(*                                term_at_0 :: flsbl_list, uknwn_list *)
(*                              else *)
(*                                (\* Term is unknown. *\) *)
(*                                flsbl_list, term_at_0 :: uknwn_list ) *)
(*                            (\* Note that we add the new falsifiable *)
(*                               terms to the old ones to avoid going *)
(*                               through the list again. *\) *)
(*                            (falsifiable, []) *)
(*                       |> (fun p -> Some p ) *)

(*                    | compressor -> *)
(*                       (\* Path compressing. *\) *)
(*                       compressor |> Term.mk_and *)
(*                       |> Solver.assert_term solver ; *)

(*                       (\* Returning nothing. *\) *)
(*                       Printf.printf "Path compressing, looping.\n" ; *)
(*                       Some ( [], [] ) *)
                      
(*                  ) *)

(*                ) *)

(*                (\* Function ran if unsat. Returns None. *\) *)
(*                ( fun () -> None ) *)

(*                (\* The actlit activates everything. *\) *)
(*                [ terms_actlit_term ] *)
(*            with *)

(*            | Some ([], []) -> *)
(*               (\* Path compressing, we need to recheck. *\) *)
(*               Printf.printf "Path compressing, looping.\n" ; *)
(*               loop () *)

(*            | Some (new_falsifiable, new_unknown) -> *)
(*               (\* Some terms are falsifiable, we shall loop. *\) *)
(*               fun () -> *)
(*               split_closure_path_comp *)
(*                 trans solver k kp1 all_vars new_falsifiable new_unknown *)

(*            | None -> *)
(*               (\* The terms left are unfalsifiable, we shall return the *)
(*                result. *\) *)
(*               fun () -> (falsifiable, terms) *)
(*          ) *)
(*        in *)

(*        loop () *)
(*      in *)

(*      (\* Deactivating actlit. *\) *)
(*      terms_actlit_term *)
(*      |> Term.mk_not *)
(*      |> Solver.assert_term solver ; *)

(*      (\* Calling the tiny continuation. *\) *)
(*      continue () *)

(*   | _ -> *)
(*      (\* No term left, we're done. *\) *)
(*      (falsifiable, []) *)


(* Checks if some of the input terms are k-inductive. Returns a pair
   composed of the falsifiable terms and the unfalsifiable ones. *)
let query_step { solver ; k ; all_vars } terms =
  split_closure solver k Numeral.(k + one) all_vars [] terms

(* (\* Checks if some of the input terms are k-inductive. Returns a pair *)
(*    composed of the falsifiable terms and the unfalsifiable ones. *\) *)
(* let query_step_path_comp { trans ; solver ; k ; all_vars } terms = *)
(*   split_closure_path_comp *)
(*     trans solver k Numeral.(k + one) all_vars [] terms *)

(* Tests the lock step driver on the system below. *)
let test trans =
  let lsk = create trans in

  let build_var string =
    UfSymbol.uf_symbol_of_string string
    |> StateVar.state_var_of_uf_symbol
    |> (fun sv -> Var.mk_state_var_instance sv Numeral.zero)
    |> Term.mk_var
  in

  let corrupted, warning =
    build_var "relCount.corrupted", build_var "relCount.warning"
  in

  let invariant = Term.mk_implies [ corrupted ; warning ] in

  let not_invariant_1 = Term.mk_not corrupted in

  let not_invariant_2 =
    Term.mk_implies
      [ Term.mk_not corrupted |> Term.bump_state Numeral.(~- one) ;
        corrupted ]
  in

  let terms_to_try = [ invariant ;
                       not_invariant_1 ;
                       not_invariant_2 ] in

  let print_terms prefix terms =
    Printf.printf "%s\n" prefix ;
    terms
    |> List.iter
         ( fun t -> Printf.printf "  - %s\n" (Term.string_of_term t) )
  in

  let print_model prefix model =
    Printf.printf "%s\n" prefix ;
    model
    |> List.iter
         ( fun (v,t) ->
           Printf.printf
             "  - %s = %s\n"
             (Var.string_of_var v)
             (Term.string_of_term t) )
  in

  let space () = Printf.printf "\n" in

  print_terms "Running with:" terms_to_try ;
  space () ;

  let readLine () =
    match read_line () with
    | "exit" ->
       delete lsk ;
       exit 0
    | _ -> ()
  in

  let rec base_loop falsifiable unknown =
    print_terms "Querying base with" unknown ;
    match
      query_base lsk unknown
    with
    | None ->
       Printf.printf "Unsat.\n" ;
       let _ = readLine () in
       unknown
    | Some model ->
       print_model "Got a model" model ;
       Printf.printf "Evaluating.\n" ;
       let nu_unknwn, nu_flsbl =
         unknown
         |> List.partition
              ( fun t -> Eval.bool_of_value (Eval.eval_term [] model t) )
       in
       print_terms "Nu falsifiable:" nu_flsbl ;
       print_terms "Nu unknown:" nu_unknwn ;
       let _ = readLine () in
       base_loop
         (List.rev_append nu_flsbl falsifiable)
         nu_unknwn
  in

  let rec loop unknown =
    Printf.printf "Now at %i.\n" (Numeral.to_int (get_k lsk)) ;
    match unknown with
    | [] -> Printf.printf "No more unknown, done.\n"
    | _ ->
       (match base_loop [] unknown with
        | [] -> Printf.printf "No more unknown, done.\n"
        | new_unknown ->
           Printf.printf "Querying step.\n" ;
           let (nu_unknown, proved) =
             query_step lsk new_unknown
           in
           print_terms "Proved:" proved ;
           print_terms "Unknown:" nu_unknown ;
           let _ = readLine () in
           Printf.printf "\nIncrementing k.\n" ;
           increment lsk ;
           loop nu_unknown)
  in

  loop terms_to_try ;

(*
node relCount(a,b,c:bool) returns(warning, corrupted:bool);
var
  pre_x,x,pre_y,y: int;
  nX,nY: int;
let

  -- Ranges over the state variables, can be found easily
  -- by AI or template-based techniques.
  assert (0 <= x) and (x <= nX) and (0 <= y) and (y <= nY);

  nX=10;
  nY=2;
  pre_x = 0-> pre(x);
  pre_y = 0-> pre(y);

  x = if (b or c) then 0
      else (if (a and pre_x < nX) then pre_x + 1 else pre_x);

  y = if (c) then 0 
      else (if (a and pre_y < nY) then pre_y + 1 else pre_y);


  corrupted = x >= nX;
  warning = y >= nY;

  -- Proof objective.
  -- ok = ((x = nX) => (y = nY));

-- PROPERTY ok;
-- MAIN;
tel

node master(in: real) returns (out: real; warning, corrupted: bool);
var
  safe, min, max, sat: real;
  outOfRange: bool;
let
  safe = 0.0;
  min = -1.0;
  max =  1.0;
  sat = if in < min then min
        else if in > max then max
             else in;

  outOfRange = in < min or max < in;

  warning, corrupted =
    relCount(outOfRange,
             not outOfRange,
             not outOfRange and (false -> not pre outOfRange));

  out = if corrupted then safe else sat;
tel
 *)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

