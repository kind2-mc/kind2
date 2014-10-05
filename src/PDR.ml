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


(* All remaining properties are valid *)
exception Success of int

(* A bad state is reachable *)
exception Bad_state_reachable

(* Counterexample trace for some property *)
exception Counterexample of (Clause.t * Clause.t) list 

(* Property disproved by other module *)
exception Disproved of string

(* Restart for other reason *)
exception Restart


(* Use configured SMT solver *)
module PDRSolver = SMTSolver.Make (SMTLIBSolver)


(* High-level methods for PDR solver *)
module S = SolverMethods.Make (PDRSolver)


(* ********************************************************************** *)
(* Solver instances and cleanup                                           *)
(* ********************************************************************** *)


(* Solver instance if created *)
let ref_solver_init = ref None

(* Solver instance if created *)
let ref_solver_frames = ref None

(* Solver instance if created *)
let ref_solver_misc = ref None

(* Formatter to output inductive clauses to *)
let ppf_inductive_assertions = ref Format.std_formatter


(* Output statistics *)
let print_stats () = 

  Event.stat
    [Stat.misc_stats_title, Stat.misc_stats;
     Stat.pdr_stats_title, Stat.pdr_stats;
     Stat.smt_stats_title, Stat.smt_stats]


(* Cleanup before exit *)
let on_exit _ = 

  (* Stop all timers *)
  Stat.pdr_stop_timers ();
  Stat.smt_stop_timers ();

  (* Output statistics *)
  print_stats ();

  (* Delete solver instance if created *)
  (try 
     match !ref_solver_init with 
       | Some solver_init -> 
         S.delete_solver solver_init; 
         ref_solver_init := None
       | None -> ()
   with 
     | e -> 
       Event.log L_error 
         "Error deleting solver_init: %s" 
         (Printexc.to_string e));

  (* Delete solver instance if created *)
  (try 
     match !ref_solver_frames with 
       | Some solver_frames -> 
         S.delete_solver solver_frames;
         ref_solver_frames := None
       | None -> ()
   with 
     | e -> 
       Event.log L_error 
         "Error deleting solver_frames: %s" 
         (Printexc.to_string e));

  (* Delete solver instance if created *)
  (try 
     match !ref_solver_misc with 
       | Some solver_misc -> 
         S.delete_solver solver_misc;
         ref_solver_misc := None
       | None -> ()
   with 
     | e -> 
       Event.log L_error 
         "Error deleting solver_misc: %s" 
         (Printexc.to_string e));

  (* Delete solvers in quantifier elimination*)
  QE.on_exit ()


  
(* ********************************************************************** *)
(* Pretty-printing                                                        *)
(* ********************************************************************** *)


(* Pretty-print the list of frames with the index of each frame *)
let rec pp_print_frames' ppf i = function 

  | [] -> ()

  | r :: tl -> 

    Format.fprintf 
      ppf 
      "Frame R_k%t@\n%a%t" 
      (function ppf -> if i = 0 then () else Format.fprintf ppf "-%d" i)
      CNF.pp_print_cnf r
      (function ppf -> if not (tl = []) then Format.fprintf ppf "@\n" else ());

    pp_print_frames' ppf (succ i) tl


(* Pretty-print the list of frames *)
let pp_print_frames ppf frames = pp_print_frames' ppf 0 frames


(* ********************************************************************** *)
(* Utility functions                                                      *)
(* ********************************************************************** *)


(* Compute the frame sizes of a delta-encoded list of frames *)
let frame_sizes frames = 

  let rec aux accum = function 

    (* All frames added up, return accumulator *)
    | [] -> accum
      
    (* Take first frame *)
    | f :: tl -> 

      match accum with 

        (* No previous frame: take size of frame *)
        | [] -> aux [CNF.cardinal f] tl

        (* Add size of frame to size of previous frame *)
        | h :: _ -> aux (((CNF.cardinal f) + h) :: accum) tl

  in

  (* Start with empty accumulator *)
  aux [] frames


(* Convert the delta-encoded set of clauses of a list of frames to a
   formula of the last frame *)
let term_of_frames frames =

  (* Append clauses of each frame to accumulator and finally return a
     conjunction of clauses *)
  let rec aux accum = function 

    (* Make one conjunction of all clauses in all frames *)
    | [] -> Term.mk_and accum

    (* Append list of clauses of current frame to accumulator *)
    | f :: tl -> 
      aux 
        (List.rev_append (List.map Clause.to_term (CNF.elements f)) accum) 
        tl
  in

  (* Start with empty accumulator *)
  aux [] frames 


(* Given a model and a two formulas f and g return a conjunction of
   literals such that 
   (1) x = s |= B[x] 
   (2) B[x] |= exists y.f[x] & T[x,x'] & g[x'] *)
let generalize trans_sys state f g = 

  let term, primed_vars = 

(*

    (* Eliminate only input variables, unfold all definitions *)
    if trans_sys.TransSys.init_constr = [] && trans_sys.TransSys.constr_constr = [] then 

      (* Get invariants of transition system *)
      let invars = TransSys.invars_of_bound 0 trans_sys in
      let invars' = TransSys.invars_of_bound 1 trans_sys in
 
      (* Get state variables occurring primed in g[x'] and in invariants *)
      let var_defs = 
        TransSys.constr_defs_of_state_vars 
          trans_sys 
          ((List.map 
              Var.state_var_of_state_var_instance 
              (TransSys.vars_at_offset_of_term 0 g)) @
             (List.map 
                Var.state_var_of_state_var_instance 
                (TransSys.vars_at_offset_of_term 1 invars)))
      in
      
      (* Bind variables to their definitions *)
      let constr_def_g = 
        List.fold_left
          (fun a d -> Term.mk_let [d] a)
          (Term.mk_and [Term.bump_state Numeral.one g; invars; invars'])
          var_defs
      in
      
      debug pdr
          "@[<v>G and invariants with variables bound to definitions:@,@[<hv>%a@]@]" 
          Term.pp_print_term constr_def_g 
      in

      (* Equivalent to f[x] & T[x,x'] & g[x'] with all primed
         variables being input *)
      let term = Term.mk_and [f; constr_def_g] in
      
      (* Get primed variables in term *)
      let primed_vars = TransSys.vars_at_offset_of_term 1 constr_def_g in
      
      term, primed_vars 

    (* Eliminate all primed variables (old) *)
    else

*)
      
      (* Construct term to be generalized with the transition relation and
         the invariants *)
      let term = 
        Term.mk_and 
          [f; 
           TransSys.trans_of_bound trans_sys Numeral.one; 
           TransSys.invars_of_bound trans_sys Numeral.one; 
           Term.bump_state Numeral.one g]
      in
      
      (* Get primed variables in the transition system *)
      let primed_vars = 
        Var.VarSet.elements
          (Term.vars_at_offset_of_term (Numeral.one) term) 
      in 
      
      term, primed_vars 

  in

    Stat.start_timer Stat.pdr_generalize_time;
    
    (* Generalize term by quantifying over and eliminating primed
       variables *)
    let gen_term = 
      QE.generalize 
        trans_sys
        (TransSys.uf_defs trans_sys) 
        state
        primed_vars
        term 
    in
    
    Stat.record_time Stat.pdr_generalize_time;
    
    (* Return generalized term *)
    gen_term



(* Partition list of terms into two lists, the first list containing
   terms in the unsatisfiable core, the second list the other terms

   [partition_core s m t] gets an unsatisfiable core from the solver
   instance [s], uses the association list [m] to map the
   unsatisfiable core to terms and returns those terms in the first
   list, the terms that are not in the first list but in the list [t]
   as the second list. *)
let partition_core solver clause =

  (* Get names of terms in the unsatifiable core *)
  let terms_in_core = S.get_unsat_core solver in

  (* Create set of terms in unsat core *)
  let core_clause = Clause.of_literals terms_in_core in

  (* Subtract term in core from all terms *)
  let rest_clause = Clause.diff clause core_clause in

  (* Return list of terms in core and remaining terms *)
  core_clause, rest_clause


let trim_clause solver_init solver_frames clause =

  
  (* Linearly traverse the list of literals in the clause, trying to remove one at a time and maintain unsatisfiability *)
  
  let rec linear_search kept discarded = function
      
    | c :: cs ->
       let kept_woc = Clause.remove c kept in

       let block_term = Clause.to_term kept_woc in
       let primed_term = Term.mk_and (List.map (fun t -> Term.bump_state Numeral.one (Term.negate t)) (Clause.elements kept_woc)) in

       let init = S.check_sat_term solver_init [block_term] in
       let cons = S.check_sat_term solver_frames [(Term.mk_and [block_term;primed_term])] in

       (* If, by removing the literal c, the blocking clause then
       either a. becomes reachable in the inital state or b. satisfies
       consecution then we need to keep it *)
       if (not cons) && init then (
	 debug pdr "Removing literal" in
	 linear_search kept_woc (c :: discarded) cs
       )
       else (
	 linear_search kept discarded cs
       )
    | [] ->  kept, Clause.of_literals discarded
				      

				      
  in

  
  linear_search clause [] (Clause.elements clause)


(* Check if [prop] is always satisfied in one step from [state] and
   return a generalized counterexample if not. If the counterexample
   holds in the initial state, raise the exception
   {!Counterexample} 

   [find_cex s z frame state prop] takes a pair of solver instances
   [s], a transition system [z], the set of clauses [frame] of a
   frame, an additional constraint [state] on the frame and a property
   [prop]. The solver instance [solver_frame] must have the transition
   relation, invariants and all clauses in [frame] already asserted.

   If the entailment f & state & T |= prop' holds, the function
   returns [true, _]. If the entailment does not hold, the
   counterexample is generalized to a cube [cex_gen]. If the [cex_gen]
   holds in the initial state (checked in [solver_init]), the
   exception [Counterexample] is raised. If [cex_gen] does not hold in
   the initial state, [false, cex_gen] is returned.

*)
let find_cex 
      ((solver_init, solver_frames, _) as solvers) 
      trans_sys 
      all_props
      frame 
      (state_core, state_rest)
      (prop_core, prop_rest) = 

  (* Prime variables in property *)
  let prop_core', prop_rest' =
    (Clause.map (Term.bump_state Numeral.one) prop_core, 
     Clause.map (Term.bump_state Numeral.one) prop_rest)
  in

  (* Join the two subclauses *)
  let state_clause, prop_clause, neg_prop_clause' = 
    (Clause.union state_core state_rest, 
     Clause.union prop_core prop_rest,
     Clause.map Term.negate (Clause.union prop_core' prop_rest'))
  in

  (* List of literals in clauses *)
  let state_terms, neg_prop_terms' = 
    (Clause.elements state_clause, 
     Clause.elements neg_prop_clause')
  in

  (* Clause of two subclauses *)
  let state, prop = 
    (Clause.to_term state_clause, 
     Clause.to_term prop_clause) 
  in

  debug pdr
	"Searching for counterexample"
    in

    debug pdr
	  "@[<v>Current context@,@[<hv>%a@]@]"
	  HStringSExpr.pp_print_sexpr_list
	  (let r, a = 
             S.T.execute_custom_command solver_frames "get-assertions" [] 1 
	   in
	   S.fail_on_smt_error r;
	   a)
    in

    debug pdr
	  "@[<v>Current frames@,@[<hv>%a@]@]"
	  SMTExpr.pp_print_expr (SMTExpr.smtexpr_of_term (CNF.to_term frame))
    in

    (* Push a new scope to the context *)
    S.push solver_frames;

    (debug smt
	   "Asserting constraints on current frame"
     in

     (* Assert blocking clause in current frame *)
     S.assert_term solver_frames state);

    (debug smt
	   "Asserting bad property"
     in

     (* Assert bad property of next frame *)
     List.iter 
       ((if Flags.pdr_tighten_to_unsat_core () then
           S.assert_named_term
	 else
           S.assert_term)
          solver_frames) 
       neg_prop_terms');

    if 

      (debug smt
             "Checking entailment"
       in

       (* Check if we can get outside the property in one step 

         R_k[x] & state[x] & T[x,x'] |= prop[x'] *)
       S.check_sat solver_frames)

    then

      (

	debug pdr 
              "Counterexample found"
	in

	(*      
      debug pdr
          "@[<v>Current context@,@[<hv>%a@]@]"
          HStringSExpr.pp_print_sexpr_list
          (let r, a = 
            S.T.execute_custom_command solver_frames "get-assertions" [] 1 
           in
           S.fail_on_smt_error r;
           a)
      in
	 *)     

	(* Get counterexample to entailment from satisfiable formula *)
	let cex = 
          S.get_model 
            solver_frames
            (TransSys.vars_of_bounds trans_sys Numeral.zero Numeral.one) 
	in

	(debug pdr
               "@[<v>%a@]"
               (pp_print_list 
		  (fun ppf (v, t) -> 
		   Format.fprintf ppf 
				  "(%a %a)"
				  Var.pp_print_var v
				  Term.pp_print_term t)
		  "@,")
               cex
	 in

	 (* Remove scope from the context *)
	 S.pop solver_frames);

	(* R_k[x] & state[x] & T[x,x'] |= prop[x'] *)
	(* exists y.f[x] & T[x,x'] & g[x'] *)

	(* Generalize the counterexample to a formula *)
	let cex_gen = 
          generalize 
            trans_sys 
            cex 
            (Term.mk_and 
               [all_props; CNF.to_term frame; state])
            (Term.negate prop)
	in

	debug pdr 
              "@[<v>Generalized counterexample:@,@[<hv>%a@]@]"
              (pp_print_list Term.pp_print_term ",@,")
              cex_gen
	in

	(* Create clause of counterexample, must negate all literals
         later but not now *)
	let cex_gen_clause = 
          List.fold_left 
            (fun a t -> Clause.add t a)
            Clause.empty
            cex_gen
	in              

	(* Push a new scope level to the context *)
	S.push solver_init;

	(* Assert each literal of the counterexample in the initial
         state *)
	List.iter 
          ((if Flags.pdr_tighten_to_unsat_core () then
              S.assert_named_term
            else
              S.assert_term) 
             solver_init) 
          cex_gen;

	if

          debug smt
		"Checking if counterexample holds in the initial state"
          in

          (* Is the counterexample a model of the initial state? 

           We must check with the generalized counterexample here, not
           with the specific model. *)
          S.check_sat solver_init 

	then

          (

            debug pdr 
		  "Counterexample holds in the initial state"
            in

            debug pdr
		  "@[<v>Current context@,@[<hv>%a@]@]"
		  HStringSExpr.pp_print_sexpr_list
		  (let r, a = 
                     S.T.execute_custom_command solver_init "get-assertions" [] 1 
		   in
		   S.fail_on_smt_error r;
		   a)
            in

            (* Pop scope level from the context *)
            S.pop solver_init;

            (* Counterexample holds in the initial state *)
            raise Bad_state_reachable

          )

	else

          (

            (debug pdr 
		   "Counterexample does not hold in the initial state"
             in

             (* Partition counterexample into subclause in the unsat
              core and subclause of remaining literals *)
             let core, rest = 

               if Flags.pdr_tighten_to_unsat_core () then 

		 partition_core 
                   solver_init 
                   cex_gen_clause

               else

		 cex_gen_clause, Clause.empty

             in

             debug pdr
		   "@[<v>Unsat core of cube is@,@[<v>%a@]"
		   (pp_print_list Term.pp_print_term "@,") 
		   (Clause.elements core)
             in

             if Clause.is_empty core then 

               (Event.log
                  L_info
                  "Reduced blocking clause to empty clause. Restarting.";
		
		raise Restart);

             S.pop solver_init;

             (* Negate all literals in clause now *)
             let ncore, nrest = 
               Clause.map Term.negate core,
               Clause.map Term.negate rest
             in

             (* Return generalized counterexample *)
             false, ( ncore,  nrest ))

          )

      )

    else

      (

	(debug pdr 
               "No counterexample found"
	 in

	 (* Partition counterexample into subclause in the unsat core
          and subclause of remaining literals *)
	 let core', rest' = 

           if Flags.pdr_tighten_to_unsat_core () then 

             partition_core 
               solver_frames 
               neg_prop_clause'

           else

             neg_prop_clause', Clause.empty 

	 in

	 (* Unprime and unnegate variables in literals of core and rest *)
	 let core, rest = 
           (Clause.map 
              Term.negate
              (Clause.map (Term.bump_state Numeral.(- one)) core'),
            Clause.map 
              Term.negate
              (Clause.map (Term.bump_state Numeral.(- one)) rest'))
	 in

	 (* Remove scope from the context *)
	 S.pop solver_frames;

	 if not (Clause.is_empty rest) then 

           (debug pdr
		  "@[<v>Reduced blocking clause to unsat core:@,%a@,%a@]"
		  Clause.pp_print_clause core
		  Clause.pp_print_clause rest
            in

            Stat.incr Stat.pdr_tightened_blocking_clauses);

	 let core =

	   let reduced, discarded = trim_clause
				      solver_init
				      solver_frames
				      core
	   in

	   debug pdr
                 "@[<v>Reduced blocking clause to@,@[<v>%a@]"
                 (pp_print_list Term.pp_print_term "@,") 
                 (Clause.elements reduced)
	 in
	 
	 reduced
	   
	 in

	 (* Entailment holds, no counterexample *)
	 (true, (Clause.union core prop_core, Clause.union rest prop_rest)))

      )

      
      
(* ********************************************************************** *)
(* Counterexample extraction                                              *)
(* ********************************************************************** *)

(* Assert current blocking clauses from frames, and transition relation *)
let rec assert_block_clauses solver trans_sys i = function 

  (* Finish when blocking clauses for all frames asserted *)
  | [] -> ()

  (* Only assert core literals *)
  | (b_i, _) :: tl -> 

    (* Blocking clause to term at instant i *)
    let t_i = 
      Term.bump_state
        i
        (Clause.to_term b_i)
    in

    (* Assert blocking clause *)
    S.assert_term solver (Term.negate t_i);

    (* Assert transition relation from previous frame *)
    S.assert_term 
      solver
      (TransSys.trans_of_bound trans_sys i);

    (* Recurse for remaining blocking clauses *)
    assert_block_clauses solver trans_sys (Numeral.succ i) tl



(* Extract a concrete counterexample from a trace of blocking clauses *)
let extract_cex_path
    (solver_init, solver_frames, solver_misc) 
    trans_sys 
    trace = 

  debug pdr
      "@[<v>Current context@,@[<hv>%a@]@]"
      HStringSExpr.pp_print_sexpr_list
      (let r, a = 
        S.T.execute_custom_command solver_misc "get-assertions" [] 1 
       in
       S.fail_on_smt_error r;
       a)
  in

  S.push solver_misc;

  let k_plus_one = Numeral.(of_int (List.length trace)) in

  (* Assert initial state constraint *)
  S.assert_term 
    solver_misc
    (TransSys.init_of_bound trans_sys Numeral.zero);

  (* Assert blocking clause and transition relation for tail of
     trace *)
  assert_block_clauses solver_misc trans_sys Numeral.one trace;

  (* Get a model of the execution path *)
  if S.check_sat solver_misc then 

    (* Extract concrete values from model *)
    let res = 
      TransSys.path_from_model 
        trans_sys
        (S.get_model solver_misc)
        k_plus_one
    in

    S.pop solver_misc;

    res

  else

    (* Must be satisfiable *)
    assert false
  


(* ********************************************************************** *)
(* Blocking of counterexamples to induction                               *)
(* ********************************************************************** *)


(* Add cube to block in future frames *)
let add_to_block_tl block_clause block_trace = function
  
  (* Last frame has no successors *)
  | [] -> [] 
          
  (* Add cube as proof obligation in next frame *)
  | (block_clauses, r_succ_i) :: block_clauses_tl -> 
    (block_clauses @ [block_clause, block_trace], r_succ_i) :: block_clauses_tl



(* Recursively block counterexamples 

   [block s z c f] takes a pair of solver instances [s], the
   transition system [z], a stack of pairs of counterexamples and
   their frame [c] and the list of lower frames in descending order
   [f].

   The frames on the stack [c] are in ascending order such that
   reversing them and appending the frames [f] yields the frames in
   descending order. Each element on the stack is a pair of a
   generalized cube and a frame where this cube has to be blocked. In
   the solver instance [solver_frames] the clauses of each frame on
   the stack have been asserted on a new scope in the order they were
   pushed onto the stack.

   If there are no lower frames in [f], we are in frame R_1 and know
   the counterexample is not reachable from the initial state. We pop
   the counterexample and the frame from the stack, add the cube as
   blocking clause to its accompanying frame and pop one scope from
   the solver instance, thus removing the assertions of R_1.

   If we are in some frame R_i with i > 1 and have a counterexample
   cube B_i on the stack, we assert the clauses of R_i-1 on a new
   scope level of the solver instance and check if there is a
   counterexample to the unreachability of B_i.

   If B_i is reachable from R_i-1, we push the frame R_i-1 and the
   witness B_i-1 to the stack and recurse to block this new
   counterexample B_i-1.

   If B_i is not reachable from R_i-1, we pop the counterexample B_i
   and the frame R_i from the stack, add the cube as blocking clause
   to R_i and pop two scope levels from the solver instance to remove
   both the clauses in R_i-1 and R_i. We then recurse to block the
   remaining counterexamples on the stack.

*)
let rec block ((solver_init, solver_frames, solver_misc) as solvers) trans_sys props = 

  function 

  (* No more proof obligations, return frames *)
  | [] -> 

     (function frames ->           

               debug pdr
		     "All counterexamples in R_k blocked"
      in

      (* Return frames unchanged and no new counterexamples *)
      frames

     )


  (* No more cubes to block in R_i *)
  | ([], r_i) :: block_tl -> 

     (function frames ->

               (debug pdr
		      "All cubes blocked in R_%d"
		      (succ (List.length frames))
		in

		(* Pop clauses in R_i *)
		S.pop solver_frames;
		
		(* Return to counterexamples to block in R_i+1 *)
		block solvers trans_sys props block_tl (r_i :: frames)))


  (* Take the first cube to be blocked in current frame *)
  | (((((core_block_clause, rest_block_clause) as block_clause), 
       block_trace)
      :: block_clauses_tl), r_i)
    :: block_tl as trace -> 

     (function 
         
       (* No preceding frames, we are in the lowest frame R_1 *)
       | [] -> 
          
          (debug pdr
		 "Blocking reached successor of initial state"
           in
           
           Event.log L_trace "Blocking reached R_1";

	   (*
           if Flags.pdr_print_blocking_clauses () then
             
             (Format.fprintf 
                !ppf_inductive_assertions
                "@[<v>-- Blocking clause@,@[<hv 2>assert@ %a;@]@]@." 
                Lustre.pp_print_term (Clause.to_term core_block_clause));
	    *)
	   
           (debug pdr
		  "@[<v>Adding blocking clause to R_1@,@[<hv>%a@]@]"
		  Clause.pp_print_clause core_block_clause
            in

            (* Add blocking clause to all frames up to where it has
               to be blocked *)
            let r_i' = CNF.add_subsume core_block_clause r_i in 

            (* Add cube to block to next higher frame if flag is set *)
            let block_tl' = 

              if Flags.pdr_block_in_future () then 

                add_to_block_tl block_clause block_trace block_tl

              else

                block_tl

            in

            (* Return frame with blocked counterexample *)
            block 
              solvers 
              trans_sys 
              props
              ((block_clauses_tl, r_i') :: block_tl') 
              []))

       (* Block counterexample in preceding frame *)
       | r_pred_i :: frames_tl as frames -> 

          debug pdr
		"@[<v>Context before visiting or re-visiting frame@,@[<hv>%a@]@]"
		HStringSExpr.pp_print_sexpr_list
		(let r, a = 
                   S.T.execute_custom_command solver_frames "get-assertions" [] 1 
		 in
		 S.fail_on_smt_error r;
		 a)
      in

      debug pdr
            "Adding clauses in frame R_%d, %d clauses to block" 
            (succ (List.length frames_tl))
            ((List.length block_clauses_tl) + 1)
      in

      (* Push a new scope onto the context *)
      S.push solver_frames;

      (* Assert all clauses only in R_i in this context

             The property is implicit in every frame and has been
             asserted in the context before *)
      CNF.iter 
        (function c -> S.assert_term solver_frames (Clause.to_term c)) 
        r_pred_i;

      (* Combine clauses from higher frames to get the actual
             clauses of the delta-encoded frame R_i *)
      let r_pred_i_full =
        List.fold_left
          (fun a (_, r) -> CNF.union r a)
          r_pred_i
          trace
      in

      match 

        (try

            (* Find counterexamples where we can get outside the
                  property in one step and generalize to a cube. The
                  counterexample does not hold in the initial state. *)
            Stat.time_fun Stat.pdr_find_cex_time (fun () ->
						  find_cex 
						    solvers 
						    trans_sys 
						    props
						    r_pred_i_full
						    block_clause
						    block_clause)

          with Bad_state_reachable -> 

            (

              List.iter
                (fun _ -> S.pop solver_frames)
                block_tl;

              S.pop solver_frames;
              
              (debug pdr
                     "@[<v>Current context@,@[<hv>%a@]@]"
                     HStringSExpr.pp_print_sexpr_list
                     (let r, a = 
			S.T.execute_custom_command solver_frames "get-assertions" [] 1 
                      in
                      S.fail_on_smt_error r;
                      a)
               in
               
               raise (Counterexample (block_clause :: block_trace)))

            )

        )

      with

      (* No counterexample, nothing to block in lower frames *)
      | true, ((core_block_clause, _) as block_clause) -> 

         Event.log L_trace
                   "Counterexample is unreachable in R_%d"
                   (succ (List.length frames_tl));

	 (*
              if Flags.pdr_print_blocking_clauses () then
                
                (Format.fprintf 
                   !ppf_inductive_assertions
                   "@[<v>-- Blocking clause@,@[<hv 2>assert@ %a;@]@]@." 
                   Lustre.pp_print_term (Clause.to_term core_block_clause));
	  *)
	 
         (debug pdr
                "@[<v>Adding blocking clause to R_k%t@,@[<hv>%a@]@]"
                (function ppf -> if block_tl = [] then () else 
				   Format.fprintf ppf "-%d" (succ (List.length block_tl)))
                Clause.pp_print_clause core_block_clause
          in


          (* Add blocking clause to all frames up to where it has
                  to be blocked *)
          let r_i' = CNF.add_subsume core_block_clause r_i in 

          (* Pop the previous frame from the context *)
          S.pop solver_frames;

          (* Add cube to block to next higher frame if flag is set *)
          let block_tl' = 

            if Flags.pdr_block_in_future () then 

              add_to_block_tl block_clause block_trace block_tl

            else

              block_tl

          in

          (* Return frame with blocked counterexample *)
          block 
            solvers 
            trans_sys 
            props
            ((block_clauses_tl, r_i') :: block_tl') 
            frames)

      (* We have found a counterexample we need to block recursively *)
      | false, block_clause' ->

         (debug pdr
                "Trying to block counterexample in preceding frame"
          in

          Event.log L_trace
                    "Counterexample is reachable in R_%d, blocking recursively"
                    (succ (List.length frames_tl));

          block 
            solvers 
            trans_sys 
            props
            (([block_clause', (block_clause :: block_trace)], 
              r_pred_i) :: trace) 
            frames_tl))


(* Find counterexamples to induction, that is, where we get outside
   the property in one step from the last frame. Then strengthen the
   last frame and recursively all lower frames by blocking
   counterexamples reaching ~P in one step until all successors of the
   last frame are within P, see {!block}.

   The list of frames must not be empty, we start with k=1. *)
let rec strengthen
    ((_, solver_frames, _) as solvers) trans_sys props = 

  function 

    (* k > 0, must have at least one frame *)
    | [] -> invalid_arg "strengthen"

    (* Head of frames is the last frame *)
    | r_k :: frames_tl as frames -> 

      (debug smt
          "strengthen: asserting clauses of R_k"
       in

       S.push solver_frames;

       (* Assert all clauses of R_k in this context *)
       CNF.iter 
         (function c -> S.assert_term solver_frames (Clause.to_term c)) 
         r_k);

      let prop_clause = 
        Clause.singleton props, Clause.empty
      in
      
      match 
        
        (try

            (* Find counterexamples where we can get outside the property
               in one step and generalize to a cube. The counterexample
               does not hold in the initial state. *)
            Stat.time_fun Stat.pdr_find_cex_time (fun () ->
                find_cex 
                  solvers 
                  trans_sys 
                  props
                  r_k
                  (Clause.top, Clause.empty)
                  prop_clause)

          with Bad_state_reachable -> 
            
            (

              (* Remove assertions of frame from context *)
              S.pop solver_frames;
              
              raise (Counterexample [prop_clause]))

        )


      with

        (* No counterexample, return frames unchanged *)
        | true, _ -> 

          (debug pdr
              "Property holds in all states reachable from the last frame"
           in

           debug pdr
               "@[<v>Current context@,@[<hv>%a@]@]"
               HStringSExpr.pp_print_sexpr_list
               (let r, a = 
                 S.T.execute_custom_command 
                   solver_frames 
                   "get-assertions" 
                   [] 
                   1 
                in
                S.fail_on_smt_error r;
                a)
           in

           (* Remove assertions of frame from context *)
           S.pop solver_frames;

           (* Return frames and counterexamples *)
           (r_k :: frames_tl))

        (* We have found a counterexample we need to block
           recursively *)
        | false, ((_, _) as block_clause) -> 

          (debug pdr
              "Trying to block counterexample in all frames"
           in

           Stat.incr Stat.pdr_counterexamples_total;
           Stat.incr_last Stat.pdr_counterexamples;

           Event.log L_trace
             "Counterexample to induction in last frame R_%d, \
              blocking recursively"
             (List.length frames);

           (* Block counterexample in all lower frames *)
           let frames' = 
             block 
               solvers 
               trans_sys 
               props
               [([block_clause, [prop_clause]], r_k)] 
               frames_tl
           in

           (* Find next counterexample to block *)
           strengthen solvers trans_sys props frames')
        


(* ********************************************************************** *)
(* Forward propagation                                                    *)
(* ********************************************************************** *)

(* Check for inductive clauses simultaneously

   The context of the solver must contain the transition relation and
   the invariants. *)
let rec partition_inductive solver accum terms =

  (* Add prime to all terms *)
  let terms' = List.map (Term.bump_state Numeral.one) terms in 

  match 

    (* Check if all clauses are inductive *)
    S.check_sat_term_model 
      solver 
      ((Term.mk_not (Term.mk_and terms')) :: terms)

  with 

    (* Some clauses are not inductive *)
    | true, model -> 
      
      (* Separate not inductive terms from potentially inductive
         terms. 

         C_1 & ... & C_n & T & ~ (C_1' & ... & C_n') is satisfiable,
         partition C_1', ..., C_n' by their model value, false terms
         are certainly not inductive, true terms can be inductive *)
      let maybe_inductive', not_inductive' =
        List.partition 
          (function t -> Eval.bool_of_value (Eval.eval_term [] model t))
          terms'
      in

      (* Remove primes from not inductive terms *)
      let not_inductive = 
        List.map (Term.bump_state Numeral.(- one)) not_inductive' 
      in

      (* Remove primes from potentially inductive terms *)
      let maybe_inductive =
        List.map (Term.bump_state Numeral.(- one)) maybe_inductive' 
      in

      Event.log L_trace
        "%d clauses not inductive, %d maybe" 
        (List.length not_inductive)
        (List.length maybe_inductive);

      (* Continue checking remaining terms for inductiveness *)
      partition_inductive solver (not_inductive @ accum) maybe_inductive 
        
    (* All term are inductive, return not inductive and inductive terms *)
    | false, _ -> 

      Event.log L_trace
        "All %d clauses inductive" 
        (List.length terms);

      terms, accum
      

(* Check which clauses can be propagated to the next frame simultaneously

   The context of the solver must contain the transition relation,
   the invariants and the clauses in the previous frame. 

   Clauses that cannot be propagated are in [accum], clauses in [term]
   can possibly be propagated. *)
let rec partition_propagate solver accum = function

  (* No clause can be propagated *)
  | [] -> [], accum

  | terms -> 

    (* Add prime to all terms *)
    let terms' = List.map (Term.bump_state Numeral.one) terms in 

    (* Assert ~ (C_1' & ... & C_n') where the C_i are the possibly
       propagatable clauses *)
    S.assert_term solver (Term.mk_not (Term.mk_and terms'));

    match 

      (* Check if all clauses can be forward propagated simultaneously *)
      S.check_sat solver 

    with 

      (* Some clauses cannot be propagated *)
      | true -> 

        (* Get variables in clauses *)
        let vars = 
          Var.VarSet.elements (Term.vars_of_term (Term.mk_and terms')) 
        in

        (* Get a model of the satisfiable context *)
        let model = S.get_model solver vars in

        (* Separate clauses that can certainly not be propagated from
           clauses that may be propagated.

           R & T & ~ (C_1' & ... & C_n') is satisfiable, partition the
           clauses in C_1', ..., C_n' by their model value, false terms
           can certainly not be propagated, true terms may be
           propagated. *)
        let maybe_propagate', cannot_propagate' =
          List.partition 
            (function t -> Eval.bool_of_value (Eval.eval_term [] model t))
            terms'
        in

        (* Remove primes from not propagatable terms *)
        let cannot_propagate = 
          List.map (Term.bump_state Numeral.(- one)) cannot_propagate' 
        in

        (* Remove primes from potentially propagatable terms *)
        let maybe_propagate =
          List.map (Term.bump_state Numeral.(- one)) maybe_propagate' 
        in

        Event.log L_trace
          "%d clauses cannot be propagated, %d maybe" 
          (List.length cannot_propagate)
          (List.length maybe_propagate);

        (* Continue checking remaining terms for inductiveness *)
        partition_propagate solver (cannot_propagate @ accum) maybe_propagate 

      (* All clauses can be propagated, return propagated and
         not propagated terms *)
      | false -> 

        Event.log L_trace
          "All %d clauses can be propagated" 
          (List.length terms);

        terms, accum


(* Assert each clause in the CNF in a new scope in the solver instance *)
let push_and_assert solver cnf =

  (* Push context *)
  S.push solver;
  
  (* Assert each clause in in the cnf *)
  CNF.iter (function c -> S.assert_term solver (Clause.to_term c)) cnf
      

(* Forward propagate clauses to higher frames and add a new frame at
   the end

   Frames are delta-encoded and in a list in descending order. The
   clauses of each frame are asserted on a new scope, then we iterate
   over the frames in reverse, i.e. ascending order, check for each
   clause C in R_i if R_i & T |= C' and move C to R_i+1 if the
   entailment holds. After all clauses of one frame have been
   processed, we pop one scope of the solver instance and continue
   with the clauses of the next frame. After all frames have been
   processed, a new frame is added and initialised with the clauses
   that could be propagated from the highest frame if any.

   If at some point all clauses of one frame could be propagated to
   the next, we have two equal frames, reached a fixpoint and can
   terminate having proved all properties.

   TODO: 

   - For each clause check if it is invariant: C & T |= C'

   - For each clause being propagated check for forward and backward
     subsumption in its new frame

*)
let fwd_propagate
    ((solver_init, solver_frames, solver_misc) as solvers) 
    trans_sys 
    frames =

  (* Recursively forward propagate from lower frame to higher frames *)
  let rec fwd_propagate_aux 
      ((solver_init, solver_frames, solver_misc) as solvers) 
      trans_sys 
      prop 
      accum = 

    function 

      (* After the last frame *)
      | [] -> 

        (

          (* Check inductiveness of blocking clauses? *)
          if Flags.pdr_check_inductive () then 

            (

              (* Push new scope level in generic solver *)
              S.push solver_misc;

              Stat.start_timer Stat.pdr_inductive_check_time;

              (* Assert transition relation from current frame *)
              S.assert_term 
                solver_misc
                (TransSys.trans_of_bound trans_sys Numeral.one);

              (* Partition clause into inductive and non-inductive *)
              let inductive_terms, non_inductive_terms = 
                partition_inductive 
                  solver_misc
                  []
                  (List.map Clause.to_term (CNF.elements prop))
              in

              (* Turn terms into clauses *)
              let inductive, non_inductive = 
                List.map Clause.of_term inductive_terms,
                List.map Clause.of_term non_inductive_terms
              in
(*
              if Flags.pdr_print_inductive_assertions () then

                (

                  List.iter
                    (Format.fprintf 
                       !ppf_inductive_assertions
                       "@[<v>-- Inductive clause@,@[<hv 2>assert@ %a;@]@]@." 
                       Lustre.pp_print_term) 
                    inductive_terms

                );
*)
              (* Send invariant *)
              List.iter 
                (fun c -> Event.invariant (Clause.to_term c))
                inductive;

              Stat.record_time Stat.pdr_inductive_check_time;

              (* Pop scope level in generic solver *)
              S.pop solver_misc;

              Stat.incr 
                ~by:(List.length inductive_terms) 
                Stat.pdr_inductive_blocking_clauses;

              (debug pdr 
                  "@[<v>New inductive terms:@,@[<hv>%t@]@]"
                  (function ppf -> 
                    (List.iter 
                       (Format.fprintf ppf "%a@," Term.pp_print_term) 
                       inductive_terms)) 
               in

               (* Add inductive blocking clauses as invariants *)
               List.iter (TransSys.add_invariant trans_sys) inductive_terms);

              (* Add invariants to solver instance *)
              List.iter 
                (S.assert_term solver_init)
                inductive_terms;

              (* Add invariants to solver instance *)
              List.iter 
                (S.assert_term solver_init)
                (List.map (Term.bump_state Numeral.one) inductive_terms);

              (* Add invariants to solver instance *)
              List.iter 
                (S.assert_term solver_frames)
                inductive_terms;

              (* Add invariants to solver instance *)
              List.iter 
                (S.assert_term solver_frames)
                (List.map (Term.bump_state Numeral.one) inductive_terms);

              (* Add a new frame with the non-inductive clauses *)
              (CNF.of_list non_inductive) :: accum

            )

          else

            (

              (* Add a new clause with propagated clauses *)
              prop :: accum

            )

        )

      (* Take the first frame from the list, which is the lowest frame *)
      | f :: tl -> 

        debug pdr
            "forward propagating for frame R_k%t"
            (function ppf -> 
              if accum = [] then () else 
                Format.fprintf ppf "-%d" (List.length accum))
        in

        debug pdr 
            "@[<v>Frames before forward propagation@,@[<hv>%a@]@]"
            pp_print_frames (f :: accum)
        in

        (* Assert clauses propagated to this frame *)
        CNF.iter
          (fun c -> S.assert_term solver_frames (Clause.to_term c))
          prop;

(*
        if not (S.check_sat solver_frames) then 

          (debug pdr 
              "Frame is unsatisfiable without propagated clauses:@,%a@,%a"
              CNF.pp_print_cnf prop
              HStringSExpr.pp_print_sexpr_list
              (let r, a = 
                S.T.execute_custom_command 
                  solver_frames
                  "get-assertions"
                  [] 
                  1 
               in
               S.fail_on_smt_error r;
               a)
           in

           assert false);
*)

        (* Add clauses propagated from the previous frame 

           No check for subsumption necessary: if a clause is not
           subsumed in one frame, it cannot be subsumed in the next
           frame, which is a subset of the previous frame *)
        let f' = CNF.union_subsume prop f in

(*
        (* Split into clauses that can and cannot be propagated 

           Check if context is satisfiable with negated clause of the
           next state.

           This is equivalent to checking R_i[x] & T[x,x'] |= C[x'] *)
        let keep, fwd =
        in
*)

        (* Turn terms into clauses *)
        let keep, fwd = 

          (* Simultaneous check for propagation? *)
          if Flags.pdr_fwd_prop_check_multi () then

            (* Partition clauses into propagatable and not propagatable *)
            let fwd_terms, keep_terms = 
              partition_propagate
                solver_frames 
                []
                (List.map Clause.to_term (CNF.elements f'))
            in

            (* Convert list of terms to sets of clauses *)
            CNF.of_list (List.map Clause.of_term keep_terms),
            CNF.of_list (List.map Clause.of_term fwd_terms)

          else

          if false then

            (* Partition clauses into propagatable and not propagatable *)
            CNF.partition 
              (function c -> 
                S.check_sat_term        
                  solver_frames
                  [Term.negate 
                     (Term.bump_state Numeral.one (Clause.to_term c))])
              f'

          else

            CNF.fold
              (fun clause (keep, fwd) ->

                 debug pdr
                     "@[<v>Checking if clause can be propagated@,%a@]"
                     Clause.pp_print_clause clause
                 in

                 (* Negate and prime literals *)
                 let clause' = 
                   Clause.map 
                     (fun c -> (Term.negate (Term.bump_state Numeral.one c)))
                     clause
                 in

                 let literals' = Clause.elements clause' in

                 S.push solver_frames;

                 (* Assert negated literals *)
                 List.iter
                   ((if Flags.pdr_tighten_to_unsat_core () then
                       S.assert_named_term
                     else
                       S.assert_term)
                      solver_frames)
                   literals';

                 (* Check for entailment *)
                 if S.check_sat solver_frames then

                   (S.pop solver_frames;

                    (* Clause does not propagate *)
                    (CNF.add_subsume clause keep, fwd))

                 else

                   (* Get clause literals in unsat core *)
                   let clause'_core, clause'_rest = 

                     (* Get unsat core only if flag is set *)
                     if Flags.pdr_tighten_to_unsat_core () then 

                       partition_core
                         solver_frames
                         (Clause.of_literals literals')

                     else

                       (* Return entire clause as core, empty clause
                          as rest *)
                       (Clause.of_literals literals'), Clause.empty

                   in

                   (* Remove primes and negate literals *)
                   let clause_core =
                     Clause.map
                       (fun l -> 
                          (Term.negate (Term.bump_state Numeral.(- one) l)))
                       clause'_core
                   in

                   if Clause.is_empty clause_core then 

                     (Event.log
                        L_info
                        "Reduced blocking clause to empty clause. Restarting.";
                      
                      raise Restart);

(*
                   if Clause.is_empty clause_core then 

                     (debug pdr 
                         "Context is unsatisfiable without clause:@,%a@,%a"
                         Clause.pp_print_clause clause
                         HStringSExpr.pp_print_sexpr_list
                         (let r, a = 
                           S.T.execute_custom_command 
                             solver_frames
                             "get-assertions"
                             [] 
                             1 
                          in
                          S.fail_on_smt_error r;
                          a)
                      in

                      assert false);
*)

                   S.pop solver_frames;

                   (* Clause was tightened? *)
                   if not (Clause.is_empty clause'_rest) then 

                     (

                       (* Get literals in clause *)
                       let literals = 
                         List.map
                           Term.negate
                           (Clause.elements clause) 
                       in

                       S.push solver_init;

                       (* Assert literals in initial state *)
                       List.iter
                         (S.assert_named_term solver_init)
                         literals;

                       (* Check for entailment *)
                       if S.check_sat solver_init then

                         (debug pdr
                             "Blocking clause intersects with initial state@ %a"
                             Clause.pp_print_clause clause
                          in

                          assert false)

                       else

                         (

                           (* Get clause literals in unsat core *)
                           let clause_core_init, clause_rest_init = 

                             partition_core
                               solver_init
                               (Clause.of_literals literals)

                           in

                           S.pop solver_init;

                           let clause_core = 
                             Clause.union 
                               clause_core
                               (Clause.map Term.negate clause_core_init)
                           in

                           (debug pdr
                               "Tightened clause@ %a to@ %a@ dropping@ %a"
                               Clause.pp_print_clause clause
                               Clause.pp_print_clause clause_core
                               Clause.pp_print_clause clause'_rest
                            in

                            (* Extra checks
                               S.push solver_frames;

                               S.assert_term 
                               solver_frames
                               (Clause.to_term clause_core);

                               (* Shortening the clause must not make the frame
                               unsatisfiable *)
                               assert (S.check_sat solver_frames);

                               S.assert_term 
                               solver_frames 
                               (Term.negate 
                                 (Term.bump_state
                                    1
                                    (Clause.to_term clause_core)));

                               (* The shortened clause must propagate *)
                               assert (not (S.check_sat solver_frames));

                               S.pop solver_frames;
                            *)

                            Stat.incr Stat.pdr_tightened_propagated_clauses;

                            (keep, CNF.add_subsume clause_core fwd))))

                   else

                     (

                       (* Propagate unchanged clause *)
                       (keep, CNF.add_subsume clause fwd)))
              f'
              (CNF.empty, CNF.empty)

        in

        Stat.incr 
          ~by:(CNF.cardinal fwd) 
          Stat.pdr_fwd_propagated;

        Event.log L_trace
          "Propagating %d clauses from F_%d to F_%d"
          (CNF.cardinal fwd)
          (succ (List.length accum))
          (succ (succ (List.length accum)));

        (debug pdr 
            "@[<v>Frames after forward propagation@,@[<hv>%a@]@]"
            pp_print_frames 
            (match tl with 
              | [] -> fwd :: keep :: accum 
              | h :: tl -> (CNF.union fwd h) :: keep :: accum)
         in

         ());

        (* All clauses in R_i-1 \ R_i can be propagated to R_i, hence
            we have R_i-1 = R_i and terminate *)
        if CNF.cardinal keep = 0 then 

          (

            Event.log L_trace
              "Fixpoint reached: F_%d and F_%d are equal"
              (succ (List.length accum))
              (succ (succ (List.length accum)));

            Stat.set 
              (succ (List.length accum))
              Stat.pdr_fwd_fixpoint;
            (*            
            if Flags.pdr_print_inductive_invariant () then

              (Format.fprintf 
                 !ppf_inductive_assertions
                 "@[<v>-- Inductive invariant:@,assert@ %a@]"
                 Lustre.pp_print_term (term_of_frames (fwd :: tl)));
  *)          

            (* Unprimed property *)
            let props = TransSys.props_of_bound trans_sys Numeral.zero in

            (* Unprimed inductive invariant *)
            let ind_inv = 
              Term.mk_and
                [term_of_frames (fwd :: tl); props] 
            in

            if Flags.pdr_print_inductive_invariant () then 

              Event.log L_off
                "@[<hv>Inductive invariant:@ %a@]"
                Term.pp_print_term ind_inv;

            if Flags.pdr_check_inductive_invariant () then 


              (

                (* Initial state constraint *)
                let init = TransSys.init_of_bound trans_sys Numeral.zero in

                (* Transition relation *)
                let trans_01 = TransSys.trans_of_bound trans_sys Numeral.one in

                (* Transition relation to constrain unprimed variables *)
                let trans_0 = TransSys.trans_of_bound trans_sys Numeral.zero in

                (* Unprimed nvariants *)
                let invars_0 = TransSys.invars_of_bound trans_sys Numeral.zero in

                (* Primed invariants *)
                let invars_1 = TransSys.invars_of_bound trans_sys Numeral.one in

                (* Primed inductive invariant *)
                let ind_inv_1 = Term.bump_state Numeral.one ind_inv in

                (* Push new scope level in generic solver *)
                S.push solver_misc;

                (* Assert initial state constraint *)
                S.assert_term solver_misc init;

                (* Assert unprimed invariants if not empty *)
                if not (invars_0 == Term.t_true) then 
                  S.assert_term solver_misc invars_0;

                (* Assert negation of inductive invariant *)
                S.assert_term solver_misc (Term.mk_not ind_inv);

                (* Check I |= R_i *)
                if not (S.check_sat solver_misc) then 

                  (Event.log L_off
                     "OK: The initial state implies the inductive \
                      invariant.")

                else

                  (Event.log L_off
                     "FAILURE: The initial state does not imply the \
                      inductive invariant.");

                (* Pop scope level *)
                S.pop solver_misc;

                (* Push new scope level *)
                S.push solver_misc;

                (* Assert transition relation between unprimed and primed variables *)
                S.assert_term solver_misc trans_01;

                (* Assert transition relation to constrain unprimed variables *)
                (* S.assert_term solver_misc trans_0; *)

                (* Assert unprimed and primed invariants if not empty *)
                if not (invars_0 == Term.t_true) then 
                  (S.assert_term solver_misc invars_0;
                   S.assert_term solver_misc invars_1);

                (* Assert unprimed inductive invariant *)
                S.assert_term solver_misc ind_inv;

                (* Assert negated primed inductive invariant *)
                S.assert_term solver_misc (Term.mk_not ind_inv_1);

                (* Check R_i & T |= R_i' *)
                if not (S.check_sat solver_misc) then 

                  (Event.log L_off
                     "OK: The inductive invariant is preserved by the \
                      transition relation.")

                else

                  (Event.log L_off 
                     "FAILURE: The inductive invariant is not preserved by \
                      the transition relation.");

                (* Pop scope level in generic solver *)
                S.pop solver_misc;

              );

            S.pop solver_frames;

            raise (Success (List.length frames))

          );

        (* Remove clauses of this frame from the context *)
        S.pop solver_frames;

        (* Propagate in next frame *)
        fwd_propagate_aux solvers trans_sys fwd (keep :: accum) tl

  in

  (debug smt
      "forward propagating: asserting all frames"
   in

   (* Assert clauses in CNF of each frame on a new scope starting with
      the last frame. The top context contains the clauses only in the
      lowest frame. *)
   List.iter (push_and_assert solver_frames) frames);

  (* Forward propagate all clauses and add a new frame *)
  fwd_propagate_aux
    solvers
    trans_sys
    CNF.empty
    []
    (List.rev frames)
  

(* Check if the property is valid in the initial state and in the
   successor of the initial state, raise exception [Counterexample] if
   not *)
let bmc_checks solver_init trans_sys props =

  (* Conjunction of property terms *)
  let props_term = Term.mk_and (List.map snd props) in

  (* Push new scope onto context of solver *)
  S.push solver_init;

  (* Assert negated property in the first state *)
  S.assert_term 
    solver_init 
    (Term.negate props_term);

  (* Check if the property is violated in the initial state *)
  if S.check_sat solver_init then 

    (S.pop solver_init;

     raise (Counterexample []));

  (* Remove assertions for 0-step counterexample check *)
  S.pop solver_init;

  (* Mark all properties as 0-true *)
  List.iter
    (fun (p, _) -> TransSys.set_prop_ktrue trans_sys 0 p)
    props;

  Event.log L_info "All properties hold in the initial state.";

  (* Push new scope onto context of solver *)
  S.push solver_init;

  (debug smt 
      "Asserting negated property in the second state"
   in

   (* Assert negated property in the second state *)
   S.assert_term 
     solver_init 
     (Term.negate (Term.bump_state Numeral.one props_term)));

  (debug smt 
      "Asserting transition relation"
   in

   (* Assert transition relation *)
   S.assert_term solver_init (TransSys.trans_of_bound trans_sys Numeral.one));

  (debug smt 
      "Asserting invariants for second state"
   in

   (* Assert invariants for second state *)
   S.assert_term 
     solver_init
     (TransSys.invars_of_bound trans_sys Numeral.one));

  (* Check if the property is violated in the second state *)
  if S.check_sat solver_init then 

    (S.pop solver_init;

     raise
       (Counterexample
          [Clause.singleton 
             (TransSys.props_of_bound trans_sys Numeral.zero), 
           Clause.empty]));

  (* Remove assertions for 1-step counterexample check *)
  S.pop solver_init;

  (* Mark all properties as 1-true *)
  List.iter
    (fun (p, _) -> TransSys.set_prop_ktrue trans_sys 1 p)
    props;

  Event.log L_info
    "All properties hold in the successor states of the initial state."


(* ********************************************************************** *)
(* Main loop and top-level function                                       *)
(* ********************************************************************** *)

(*

(* Handle events from the queue and return the current k in the BMC process *)
let handle_events
    ((solver_init, solver_frames, _) as solvers) 
    trans_sys 
    bmc_k = 
  
  (* Add invariant to the transition system and assert in solver
     instances *)
  let add_invariant inv = 

    (* Add invariant to the transition system *)
    TransSys.add_invariant trans_sys inv;

    (* Add prime to invariant *)
    let inv_1 = Term.bump_state Numeral.one inv in

    (* Assert invariant in solver instance for initial state *)
    S.assert_term solver_init inv;
    S.assert_term solver_init inv_1;
    
    (* Assert invariant and primed invariant in solver instance for
       transition relation *)
    S.assert_term solver_frames inv;
    S.assert_term solver_frames inv_1

  in

  (* Receive all queued messages 

     Side effect: Terminate when ControlMessage TERM is received.*)
  let messages = Event.recv () in

  List.fold_left 
    (function bmc_k -> function
        
         (* Invariant discovered by other module *)
         | Event.Invariant (_, inv) -> 
           
           (debug pdr
              "@[<hv>Received invariant@ @[<hv>%a@]@]"
              Term.pp_print_term inv 
            in
    
            (* Add invariant to the transition system and assert in
               solver instances *)
            add_invariant inv);
       
            (* No new k in BMC *)
            bmc_k
           
         (* Pass new k in BMC *)
         | Event.BMCState (bmc_k', _) -> bmc_k'

         (* Property has been proved by other module *)
         | Event.Proved (_, _, prop) -> 

           (debug pdr
               "@[<hv>Received proved property %s@]"
               prop
            in
            
            (try 
               
               (* Add invariant to the transition system and assert in
                  solver instances *)
               add_invariant 
                 (List.assoc prop trans_sys.TransSys.props)
                 
             with Not_found -> ()));
           
           (* No new k in BMC *)
           bmc_k
           
         (* Property has been disproved by other module *)
         | Event.Disproved (_, _, prop) -> 

           if 

             (* Property already disproved here? *)
             List.exists
               (fun (p, _) -> p = prop)
               trans_sys.TransSys.props_invalid

           then

             (* Skip *)
             bmc_k

           else
           
             (* Restart upon disproved property *)
             raise (Disproved prop)
           
       )
       bmc_k
       messages

  *)

let handle_events
    ((solver_init, solver_frames, _) as solvers) 
    trans_sys
    props =

  (* Receive queued messages 

     Side effect: Terminate when ControlMessage TERM is received.*)
  let messages = Event.recv () in

  (* Update transition system from messages *)
  let invariants_recvd, prop_status = 
    Event.update_trans_sys trans_sys messages 
  in

  (* Add invariant to the transition system and assert in solver
     instances *)
  let add_invariant inv = 

    (* Add prime to invariant *)
    let inv_1 = Term.bump_state Numeral.one inv in

    (* Assert invariant in solver instance for initial state *)
    S.assert_term solver_init inv;
    S.assert_term solver_init inv_1;

    (* Assert invariant and primed invariant in solver instance for
       transition relation *)
    S.assert_term solver_frames inv;
    S.assert_term solver_frames inv_1

  in

  (* Assert all received invariants *)
  List.iter (fun (_, i) -> add_invariant i) invariants_recvd;

  (* Restart if one of the properties to prove has been disproved *)
  List.iter
    (fun (p, _) -> match TransSys.get_prop_status trans_sys p with 
       | TransSys.PropFalse _ -> raise (Disproved p)
       | _ -> ())
    props


(* PDR main loop

   [frames] is a list of clause sets in reverse order, the head of the
   list is the highest frame.

   Frames are delta-encoded, that is, every frame stores only the
   difference to the previous frame. The property is implicit in each
   frame and not stored there. The initial state is not a frame.

   Let [frames = \[ F_k; ... F_1 \], then let R_i be the union of all
   F_j with j <= i. Let R_0 be the initial state I.

   By construction two invariants of PDR are satisfied:

   (1) R_0 = I
   (2) R_i+1 is a subset of R_i for i = 1,...,k-1

   The procedure further maintains the invariants 

   (3) R_i |= P for i = 1,...,k
   (4) R_i & T |= R'_i+1 for i = 0,...,k

   and uses two SMT solver instances [solver_init] and [solver_frames].

   The instance [solver_init] is assumed to have the initial state
   constraint as well as the unprimed invariants asserted. The
   instance [solver_frames] is assumed to have the transition
   relation, the unprimed and primed invariants and the unprimed
   property asserted. The procedure restores the state of the solver
   instances to the state upon entry.

   A new frame is added to the head of [frames] and beginning with k=1
   all clauses are moved to the highest frame they can be propagated
   to, see {!fwd_propagate}. The last frame is strengthened by adding
   clauses to F_k and lower frames until the all successor states of
   R_k are within the property. If this fails, the exception
   [Counterexample] is raised, see {!strengthen}.

*)
let rec pdr
    ((solver_init, solver_frames, _) as solvers) 
    trans_sys
    props
    frames = 

  (* Conjunction of property terms *)
  let props_term = Term.mk_and (List.map snd props) in

  (* Must have checked for 0 and 1 step counterexamples *)
  let bmc_checks_passed props =
    
    List.for_all 
      (fun (p, _) -> match TransSys.get_prop_status trans_sys p with
         | TransSys.PropInvariant -> true
         | TransSys.PropKTrue k when k >= 1 -> true
         | _ -> false)
      props

  in

  (debug pdr 
      "Main loop, k=%d" 
      (succ (List.length frames))
   in

   let pdr_k = succ (List.length frames) in

   Event.log L_info "PDR main loop at k=%d" pdr_k;

   Event.progress pdr_k;

   Stat.set pdr_k Stat.pdr_k);

  handle_events solvers trans_sys props;

  (debug pdr 
      "@[<v>Frames before forward propagation@,@[<hv>%a@]@]"
      pp_print_frames frames
   in
   
   debug pdr
       "@[<v>Context only contains properties, invariants and the \
        transition relation@,@[<hv>%a@]@]"
       HStringSExpr.pp_print_sexpr_list
       (let r, a = 
         S.T.execute_custom_command solver_frames "get-assertions" [] 1 
        in
        S.fail_on_smt_error r;
        a)
    in
    
    Stat.start_timer Stat.pdr_fwd_prop_time);

  (* Frames after forward propagation *)
  let frames' = 

    try 

      (* Forward propagate and add a new frame *)
      fwd_propagate solvers trans_sys frames 

    (* Fixed point reached *)
    with Success pdr_k -> 

      if 

        (* No 0- or 1-step countexample? *)
        bmc_checks_passed props 

      then

        raise (Success pdr_k) 

      else
        
        (* Wait until BMC process has passed k=1 *)
        let rec wait_for_bmc () = 

          (* Receive messages and update transition system *)
          handle_events solvers trans_sys props;

          (* No 0- or 1-step countexample? *)
          if bmc_checks_passed props then

            (* Raise exception again *)
            raise (Success pdr_k)

          else

            (

              (* Delay *)
              minisleep 0.1;

              (* Wait *)
              wait_for_bmc ()

            )

        in

        (* Wait until BMC has passed k=1 *)
        wait_for_bmc ()

  in

  Stat.record_time Stat.pdr_fwd_prop_time;

  Stat.set_int_list (frame_sizes frames') Stat.pdr_frame_sizes;

  (debug pdr 
      "@[<v>Frames after forward propagation@,@[<hv>%a@]@]"
      pp_print_frames frames'
   in

   Stat.append 0 Stat.pdr_counterexamples;

   Stat.start_timer Stat.pdr_strengthen_time;

   (* Recursively block counterexamples in frontier state *)
   let frames'' = 
     strengthen
       solvers
       trans_sys
       props_term
       frames' 
   in

   Stat.record_time Stat.pdr_strengthen_time;

   Stat.set_int_list (frame_sizes frames'') Stat.pdr_frame_sizes;

   Stat.update_time Stat.pdr_total_time; 

   (* Output statistics *)
   if output_on_level L_info then print_stats ();

   (* No reachable state violates the property, continue with next k *)
   pdr solvers trans_sys props frames'')


(* Entry point

     Create two solver instances: [solver_init] which has the initial
     state constraint and the invariants permanently asserted and
     [solver_frames] which has the transition relation and the
     invariants for the current and the next state permanently asserted.

     If BMC is not running in parallel, check for zero and one step
     counterexamples.

     Run PDR main loop and catch [Success] and [Counterexample]
     exceptions.

*)
let main trans_sys =

  (* PDR solving starts now *)
  Stat.start_timer Stat.pdr_total_time;

  (* Determine logic for the SMT solver *)
  let logic = TransSys.get_logic trans_sys in

  let produce_cores = Flags.pdr_tighten_to_unsat_core () in

  (* Create new solver instance to reason about the initial state *)
  let solver_init = 
    S.new_solver
      ~produce_assignments:true
      ~produce_cores:produce_cores
      logic
  in

  (* Declare uninterpreted function symbols *)
  TransSys.iter_state_var_declarations trans_sys (S.declare_fun solver_init);

  (* Define functions *)
  TransSys.iter_uf_definitions trans_sys (S.define_fun solver_init);

  (* Save solver instance for clean exit *)
  ref_solver_init := Some solver_init;

  (debug smt
      "Permanently asserting initial state constraint"
   in

   (* Assert initial state constraint in solver instance *)
   S.assert_term 
     solver_init
     (TransSys.init_of_bound trans_sys Numeral.zero));

(*
  (debug smt 
      "Permanently asserting transition relation"
   in

   (* Assert transition relation from current frame *)
   S.assert_term 
     solver_init
     (TransSys.trans_of_bound trans_sys Numeral.one));
*)

  (* Create new solver instance to reason about counterexamples in
     frames *)
  let solver_frames = 
    S.new_solver
      ~produce_models:true
      ~produce_assignments:true
      ~produce_cores:produce_cores
      logic
  in

  (* Declare uninterpreted function symbols *)
  TransSys.iter_state_var_declarations 
    trans_sys 
    (S.declare_fun solver_frames);

  (* Define functions *)
  TransSys.iter_uf_definitions 
    trans_sys 
    (S.define_fun solver_frames);

  (* Save solver instance for clean exit *)
  ref_solver_frames := Some solver_frames;

  (debug smt 
      "Permanently asserting transition relation"
   in

   (* Assert transition relation from current frame *)
   S.assert_term 
     solver_frames
     (TransSys.trans_of_bound trans_sys Numeral.one));

  (* Create new solver instance for all other queries (subsumption,
     invariance of blocking clauses) *)
  let solver_misc = 
    S.new_solver
      ~produce_models:true
      ~produce_assignments:true 
      logic
  in

  (* Declare uninterpreted function symbols *)
  TransSys.iter_state_var_declarations 
    trans_sys
    (S.declare_fun solver_misc);

  (* Define functions *)
  TransSys.iter_uf_definitions
    trans_sys
    (S.define_fun solver_misc);

  (* Save Solver instance for clean exit *)
  ref_solver_misc := Some solver_misc;

  (match Flags.pdr_print_to_file () with 

    (* Keep default formatter *)
    | None -> ()

    (* Output to given file *)
    | Some f -> 

      (* Output channel on file *)
      let oc = 
        try open_out f with
          | Sys_error _ -> 
            failwith "Could not open file for inductive assertions"
      in 

      (* Create formatter and store in reference *)
      ppf_inductive_assertions := Format.formatter_of_out_channel oc);

  (* Helper function for restarts *)
  let rec restart_loop props = 

    if props = [] then () else

      (* Properties to prove after restart *)
      let props' = 

        try 

          S.push solver_frames;

          (* Get invariants of transition system *)
          let invars_1 = TransSys.invars_of_bound trans_sys Numeral.one in

          (* Get invariants for current state *)
          let invars_0 = TransSys.invars_of_bound trans_sys Numeral.zero in

          (* Assert invariants for current state if not empty *)
          if not (invars_0 == Term.t_true) then 

            (debug smt 
                "Permanently asserting invariants"
             in

             S.assert_term solver_init invars_0;
             S.assert_term solver_init invars_1);

          (* Assert invariants for current state if not empty *)
          if not (invars_0 == Term.t_true) then 

            (

              (debug smt 
                  "Permanently asserting invariants"
               in

               S.assert_term solver_frames invars_0;
               S.assert_term solver_frames invars_1)

            );

          (* BMC module running in parallel? 

             If BMC is running in parallel, delegate check for zero and one
             step counterexamples to it. All results are tentative until BMC
             has shown that there are no such counterexamples. *)
          if List.mem `BMC (Flags.enable ()) then 

            (Event.log L_info
               "Delegating check for zero and one step counterexamples \
                to BMC process.")

          else

            (* Do check for zero and one step counterexample in solver
               instance [solver_init] *)
            (bmc_checks solver_init trans_sys props);

          (debug smt 
              "Permanently asserting property constraint"
           in

           (* The property is implicit in every R_i *)      
           S.assert_term 
             solver_frames
             (Term.mk_and (List.map snd props));

           (* Reset statistics about frames on restart *)
           Stat.set_int_list [] Stat.pdr_frame_sizes;
           Stat.set_int_list [] Stat.pdr_counterexamples;

           (* Run PDR procedure *)
           pdr
             (solver_init, solver_frames, solver_misc) 
             trans_sys 
             props
             [])

        with 

          (* All propertes are valid *)
          | Success k -> 

            (

              (* Send out valid properties *)
              List.iter
                (fun (p, _) -> 
                   Event.prop_status TransSys.PropInvariant trans_sys p) 
                props;

              (* No more properties remaining *)
              []

            )

          (* Some property is invalid *)
          | Counterexample trace -> 

            (

              (* Extract counterexample from sequence of blocking
                 clauses *)
              let cex_path =
                extract_cex_path
                  (solver_init, solver_frames, solver_misc)
                  trans_sys
                  trace
              in

              debug pdr
                "@[<v>Counterexample:@,@[<hv>%a@]@]"
                (Event.pp_print_path_pt trans_sys false) cex_path
              in

              (* Check which properties are disproved *)
              let props', props_false =

                List.fold_left
                  (fun (props', props_false) (p, t) -> 

                     if 

                       (* Property is false along path? *)
                       TransSys.exists_eval_on_path
                         (TransSys.uf_defs trans_sys)
                         ((=) (Eval.ValBool false))
                         t
                         cex_path

                     then

                       (Event.prop_status 
                          (TransSys.PropFalse cex_path) 
                          trans_sys 
                          p;

                        Event.log
                          L_info 
                          "Property %s disproved by PDR"
                          p;

                        (props', p :: props_false))

                     else

                       (Event.log
                          L_info 
                          "Property %s not disproved by PDR"
                          p;
                        
                        ((p, t) :: props', props_false)))

                  ([], [])
                  props
              in
              
              debug pdr
                  "Disproved %a, continuing with %a"
                  (pp_print_list
                     (fun ppf n -> Format.fprintf ppf "%s" n)
                     "@ ")
                  props_false
                  (pp_print_list
                     (fun ppf (n, _) -> Format.fprintf ppf "%s" n)
                     "@ ")
                  props'
              in

              assert (not (props_false = []));

              props'

            )

          | Disproved prop -> 


            (* Check which properties are disproved *)
            let props' =

              List.fold_left
                (fun accum (p, t) -> 

                   (* Property is disproved? *)
                   if TransSys.is_disproved trans_sys p then

                     (* Remove property disproved property from
                          properties to prove *)
                     accum

                   else 

                     (* Keep property *)
                     (p, t) :: accum)

                []
                props
            in

            props'

          (* Formuala is not in linear intege arithmetic *)
          | Presburger.Not_in_LIA -> 

            (

              Event.log
                L_info
                "Problem contains real valued variables, \
                 switching off approximate QE";

              Flags.set_pdr_qe `Z3;

              props

            )

          (* Restart for other reason *)
          | Restart -> props
            
      in

      S.pop solver_frames;

      if not (props' = []) then 

        (              

          Event.log
            L_info 
            "@[<h>Restarting PDR with properties @[<h>%a@]@]"
            (pp_print_list
               (fun ppf (n, _) -> Format.fprintf ppf "%s" n)
               "@ ")
            props';
          
          Stat.incr Stat.pdr_restarts);

      (* Restart with remaining properties *)
      restart_loop props'

  in

  (* Prove all properties with restarting after invalid counterexamples *)
  restart_loop (TransSys.props_list_of_bound trans_sys Numeral.zero)



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
*)
