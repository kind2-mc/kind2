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


(* Raised when the properties have been proved *)
exception Success of int


(* Raised when one property has been disproved *)
exception Counterexample 


(* Use configured SMT solver *)
module PDRSolver = SMTSolver.Make (Config.SMTSolver)


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

(*
(* Output statistics *)
let pp_print_stat ppf = 

  Format.fprintf
    ppf
    "Statistics of %a module:@.@.%t@.%t@.%t"
    pp_print_kind_module `PDR
    Stat.pp_print_misc_stats
    Stat.pp_print_pdr_stats
    Stat.pp_print_smt_stats
*)


(* Cleanup before exit *)
let on_exit () = 

  (* Stop all timers *)
  Stat.pdr_stop_timers ();
  Stat.smt_stop_timers ();

  (* Output statistics *)
  Event.stat
    `PDR 
    [Stat.misc_stats_title, Stat.misc_stats;
     Stat.pdr_stats_title, Stat.pdr_stats;
     Stat.smt_stats_title, Stat.smt_stats];

  (* Delete solver instance if created *)
  (try 
     match !ref_solver_init with 
       | Some solver_init -> 
         S.delete_solver solver_init; 
         ref_solver_init := None
       | None -> ()
   with 
     | e -> 
       Event.log `PDR Event.L_error 
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
       Event.log `PDR Event.L_error 
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
       Event.log `PDR Event.L_error 
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


(* Add clause to frame with syntactic and semantic forward and
   backward subsumption *)
let add_to_frame (_, _, solver) clause = function 

  (* List of frames must not be empty *)
  | [] -> invalid_arg "add_to_frame"

  (* Add clause to frame at head of list *)
  | frame :: frames_tl as frames -> 

    if 

      (* Clause is syntactically subsumed by a clause in some frame? *)
      List.exists (CNF.fwd_subsume clause) frames 

    then 

      (* Drop clause and return frames unchanged *)
      frames 

    else if 

      (* Push new scope level to context *)
      S.push solver;

      (* Assert all clauses in frame *)
      List.iter
        (CNF.iter 
           (function c -> S.assert_term solver (Clause.to_term c)))
        frames;

      (* [true] if clause is subsumed in frame *)
      let res = 

        (* Clause is semantically subsumed in some frame? *) 
        try 

          (* Check if clause is entailed by frame *)
          S.check_entailment 
            ~timeout:(Flags.pdr_subs_timeout ()) 
            solver 
            [] 
            (Clause.to_term clause)

        (* Treat unknown result (after timeout) as not subsumed *)
        with S.Unknown -> false

      in

      (* Pop scope level from context *)
      S.pop solver;

      (* Return computed subsumption of clause *)
      res

    then

      (* Drop clause and return frames unchanged *)
      frames 

    else

      (* Syntactic backward subsumption in all frames *)
      let frames' = List.map (CNF.bwd_subsume clause) frames in 

      (* Semantic backward subsumption in all frames *)
      let frame'' :: frames_tl'' = frames' in

      (* Add clause to last frame *)
      CNF.add clause frame'' :: frames_tl''


(* Given a model and a two formulas f and g return a conjunction of
   literals such that 
   (1) x = s |= B[x] 
   (2) B[x] |= exists y.f[x] & T[x,x'] & g[x'] *)
let generalize transSys state f g = 

  let term, primed_vars = 

    (* Eliminate only input variables, unfold all definitions *)
    if true then 

      (* Get invariants of transition system *)
      let invars = TransSys.invars_of_bound 0 transSys in
      let invars' = TransSys.invars_of_bound 1 transSys in
 
      (* Get state variables occurring primed in g[x'] and in invariants *)
      let var_defs = 
        TransSys.constr_defs_of_state_vars 
          transSys 
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
          (Term.mk_and [TransSys.bump_state 1 g; invars; invars'])
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
      
      (* Construct term to be generalized with the transition relation and
         the invariants *)
      let term = 
        Term.mk_and 
          [f; 
           TransSys.constr_of_bound 1 transSys; 
           TransSys.invars_of_bound 1 transSys; 
           TransSys.bump_state 1 g]
      in
      
      (* Get primed variables in the transition system *)
      let primed_vars = TransSys.vars_at_offset_of_term 1 term in 
      
      term, primed_vars 

  in

    Stat.start_timer Stat.pdr_generalize_time;
    
  (* Generalize term by quantifying over and eliminating primed
     variables *)
    let gen_term = QE.generalize state primed_vars term in
    
    Stat.record_time Stat.pdr_generalize_time;
    
  (* Return generalized term *)
    gen_term


(*
let rec tighten_to_subset 
    ((solver_init, solver_frames, _) as solvers) 
    accum = 

  function

    | [] -> accum

    | h :: tl -> 

      let c = Term.mk_and (h :: accum) in
      let c' = TransSys.bump_state 1 c in

      if 

        (* Check if R_i[x] & T[x,x'] & C[x] |= C[x'] *)
        S.check_entailment solver_frames [c] c'

      then

        (

          if 

            (* Check if I[x] |= C[x] *)
            S.check_entailment solver_init [] c

          then 

            (

              (* Both entailments hold, found a strong enough subset *)
              h :: accum

            )

          else

            (

              (* Add literal to clause and recurse to check rest of
                 original clause *)
              tighten_to_subset solvers (h :: accum) tl

            )

        )

      else

        (

          (* Add literal to clause and recurse to check rest of
             original clause *)
          tighten_to_subset solvers (h :: accum) tl

        )


let tighten_to_unsat_core 
    (solver_init, solver_frames, _) 
    clause =

  (* Literals of clause *)
  let literals = Clause.elements clause in

  (* Association list of names to named terms *)
  let literals_named = 
    List.fold_left
      (fun a l -> 
         Term.mk_named l :: a)
      []
      literals
  in

  (* Clause of named literals *)
  let clause_named = Term.mk_or (List.map snd literals_named) in

  (* Clause with primed variables *)
  let clause' = TransSys.bump_state 1 (Clause.to_term clause) in

  (* Push new scope on context *)
  S.push solver_frames;

  (* Assert clause with named literals *)
  S.assert_term solver_frames clause_named;

  (* Assert negation of clause with unnamed primed literals *)
  S.assert_term solver_frames (Term.mk_not clause');

  (* Check if R_i[x] & T[x,x'] & C[x] |= C[x'] *)
  if S.check_sat solver_frames then 

    (* Entailment holds, query must be unsatisfiable *)
    assert false

  else

    (* Get unsatisfiable core of query *)
    let unsat_core = S.get_unsat_core solver_frames in

    (* Get literals in unsatisfiable core *)
    let res = 
      List.map (function l -> List.assoc l literals_named) unsat_core 
    in

    S.pop solver_frames;

    res

        
(* Tighten a counterexample cube to a blocking clause 

   At the moment, just negate each minterm in the cube and form the
   disjunction *)
let tighten ((solver_init, solver_frames, _) as solvers) cube = 

  (* Form blocking clause of negated cube *)
  let clause = Clause.of_literals (List.map Term.negate cube) in

  (* Tighten clause to a subset *)
  let clause' = 

    if Flags.pdr_tighten_to_subset () then 

      (

        Stat.start_timer Stat.pdr_tighten_to_subset_time;

        (* Push contexts of solvers *)
        S.push solver_frames;
        S.push solver_init;

        (* Tighten clause D to a subset C that satisfies 
           R_i[x] & T[x,x'] & C[x] |= C[x'] and
           I[x] |= C[x] *)
        let res = 
          Clause.of_literals 
            (tighten_to_subset solvers [] (Clause.elements clause))
            (*            (tighten_to_unsat_core solvers clause) *)
        in

        if Clause.cardinal clause > Clause.cardinal res then 
          Stat.incr Stat.pdr_tightened_blocking_clauses;

        (* Restore contexts of solvers *)
        S.pop solver_frames;
        S.pop solver_init;

        Stat.record_time Stat.pdr_tighten_to_subset_time;

        (* Continue with tightened clause *)
        res

      )

    else

      (* Do not tighten clause *)
      clause

  in

  (* Return clause *)
  clause'
*)

let rec minimize_cex 
    ((solver_init, solver_frames, _) as solvers) 
    accum = 

  function

    | [] -> accum

    | (v, t) :: tl -> 

      (* Term x != t of assignment to variable v in model *)
      let n_vt = Term.mk_not (Term.mk_eq [Term.mk_var v; t]) in

      if 

        (* Check if value of variable is relevant for counterexample *)
        S.check_sat_term solver_frames [n_vt] && 
        S.check_sat_term solver_init [n_vt] 

      then

        (debug pdr
            "Assignment to %a is not relevant for counterexample"
            Var.pp_print_var v 
         in

         (* Fresh constant to replace assignment to variable *)
         let c = 
           Term.mk_uf (UfSymbol.mk_fresh_uf_symbol [] (Var.type_of_var v)) []
         in

         (* Counterexample both with x = t and x != t, assignment to x is
            irrelevant *)
         minimize_cex solvers ((v, c) :: accum) tl)

      else

        (debug pdr
            "Assignment %a = %a is relevant for counterexample"
            Var.pp_print_var v 
            Term.pp_print_term t
         in

         (* Assignment to x is relevant to obtain counterexample *)
         minimize_cex solvers ((v, t) :: accum) tl)


(* Return a list of named terms and a map from names to the original
   terms *)
let name_terms terms =
  List.fold_left 
    (fun (l, m) t -> 
       let (n, t') = Term.mk_named t in
       t' :: l, (n, t) :: m)
    ([], [])
    terms


(* Partition list of terms into two lists, the first list containing
   terms in the unsatisfiable core, the second list the other terms

   [partition_core s m t] gets an unsatisfiable core from the solver
   instance [s], uses the association list [m] to map the
   unsatisfiable core to terms and returns those terms in the first
   list, the terms that are not in the first list but in the list [t]
   as the second list. *)
let partition_core solver name_to_term_map all_clause =

  (* Get names of terms in the unsatifiable core *)
  let names_in_core = S.get_unsat_core solver in

  (* Create set of terms in unsat core *)
  let core_clause = 
    List.fold_left 
      (fun a n -> 
         try Clause.add (List.assoc n name_to_term_map) a with Not_found -> a)
      Clause.empty
      names_in_core
  in

  (* Subtract term in core from all terms *)
  let rest_clause = Clause.diff all_clause core_clause in

  (* Return list of terms in core and remaining terms *)
  core_clause, rest_clause



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
    transSys 
    frame 
    (state_core, state_rest)
    (prop_core, prop_rest) = 
  
  (* Prime variables in property *)
  let prop_core', prop_rest' =
    (Clause.map (TransSys.bump_state 1) prop_core, 
     Clause.map (TransSys.bump_state 1) prop_rest)
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
  
  (* Give a unique name to each literal in the blocking clause *)
  let (state_named, state_name_to_term), (neg_prop_named', neg_prop_name_to_term') = 
    
    (* Naming for unsat core only if flag is set *)
    if Flags.pdr_tighten_to_unsat_core () then 
      
      (* Only name terms in property *)
      (state_terms, []), (name_terms neg_prop_terms')
                         
    else
      
      (* Don't name any term *)
      (state_terms, []), (neg_prop_terms', [])
                         
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
   S.assert_term solver_frames (Term.mk_or state_named));
  
  (debug smt
      "Asserting bad property"
   in
   
   (* Assert bad property of next frame *)
   List.iter 
     (S.assert_term solver_frames) 
     neg_prop_named');
  
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
        S.get_model solver_frames (TransSys.vars transSys) 
      in
      
      (* Find a small satisfying assignment *)
      let cex_min = 
        
        if Flags.pdr_minimize_cex () then 
          
          minimize_cex solvers [] cex 
            
        else
          
          cex 
            
      in
      
      (* Remove scope from the context *)
      S.pop solver_frames;
      
      (* R_k[x] & state[x] & T[x,x'] |= prop[x'] *)
      (* exists y.f[x] & T[x,x'] & g[x'] *)
      
      (* Generalize the counterexample to a formula *)
      let cex_gen = 
        generalize 
          transSys 
          cex_min 
          (Term.mk_and 
             [TransSys.props_of_bound 0 transSys;
              CNF.to_term frame;
              state])
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
      
      (* Give a unique name to each literal in the counterexample *)
      let cex_gen_named, cex_gen_name_to_term = 
        
        if Flags.pdr_tighten_to_unsat_core () then 
          
          name_terms cex_gen 
            
        else
          
          cex_gen, []
                   
      in
      
      (* Push a new scope level to the context *)
      S.push solver_init;
      
      (* Assert each literal of the counterexample in the initial
         state *)
      List.iter (S.assert_term solver_init) cex_gen_named;
      
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
          raise Counterexample
            
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
                 cex_gen_name_to_term 
                 cex_gen_clause
                 
             else
               
               cex_gen_clause, Clause.empty
                                 
           in

           debug pdr
               "@[<v>Unsat core of cube is@,@[<v>%a@]"
               (pp_print_list Term.pp_print_term "@,") (Clause.elements core)
           in
           
           S.pop solver_init;
           
           (* Negate all literals in clause now *)
           let ncore, nrest = 
             Clause.map Term.negate core,
             Clause.map Term.negate rest
           in
           
           (* Return generalized counterexample *)
           false, (ncore, nrest))
          
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
             neg_prop_name_to_term' 
             neg_prop_clause'
             
         else

           neg_prop_clause', Clause.empty 
                           
       in
       
       (* Unprime and unnegate variables in literals of core and rest *)
       let core, rest = 
         (Clause.map Term.negate (Clause.map (TransSys.bump_state (- 1)) core'),
          Clause.map Term.negate (Clause.map (TransSys.bump_state (- 1)) rest'))
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

       (* Entailment holds, no counterexample *)
       (true, (Clause.union core prop_core, Clause.union rest prop_rest)))

    )

      
(* ********************************************************************** *)
(* Blocking of counterexamples to induction                               *)
(* ********************************************************************** *)


(* Add cube to block in future frames *)
let add_to_block_tl block_clause = function
  
  (* Last frame has no successors *)
  | [] -> [] 
          
  (* Add cube as proof obligation in next frame *)
  | (block_clauses, r_succ_i) :: block_clauses_tl -> 
    (block_clauses @ [block_clause], r_succ_i) :: block_clauses_tl



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
let rec block ((_, solver_frames, _) as solvers) transSys = 

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
         block solvers transSys block_tl (r_i :: frames)))


    (* Take the first cube to be blocked in current frame *)
    | ((core_block_clause, rest_block_clause) as block_clause :: block_clauses_tl, r_i) :: 
        block_tl as trace -> 

      (function 
        
        (* No preceding frames, we are in the lowest frame R_1 *)
        | [] -> 
          
          (debug pdr
              "Blocking reached successor of initial state"
           in
           
           Event.log `PDR Event.L_trace "Blocking reached R_1";

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

                add_to_block_tl block_clause block_tl

              else

                block_tl

            in

            (* Return frame with blocked counterexample *)
            block 
              solvers 
              transSys 
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

            (* Find counterexamples where we can get outside the
               property in one step and generalize to a cube. The
               counterexample does not hold in the initial state. *)
            Stat.time_fun Stat.pdr_find_cex_time (fun () ->
                find_cex 
                  solvers 
                  transSys 
                  r_pred_i_full
                  block_clause
                  block_clause)

          with

            (* No counterexample, nothing to block in lower frames *)
            | true, ((core_block_clause, _) as block_clause) -> 

              Event.log `PDR Event.L_trace
                "Counterexample is unreachable in R_%d"
                 (succ (List.length frames_tl));

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

                   add_to_block_tl block_clause block_tl

                 else

                   block_tl

               in

               (* Return frame with blocked counterexample *)
               block 
                 solvers 
                 transSys 
                 ((block_clauses_tl, r_i') :: block_tl') 
                 frames)

            (* We have found a counterexample we need to block recursively *)
            | false, block_clause' ->

              (debug pdr
                  "Trying to block counterexample in preceding frame"
               in

               Event.log `PDR Event.L_trace
                 "Counterexample is reachable in R_%d, blocking recursively"
                 (succ (List.length frames_tl));

               block 
                 solvers 
                 transSys 
                 (([block_clause'], r_pred_i) :: trace) 
                 frames_tl))


(* Find counterexamples to induction, that is, where we get outside
   the property in one step from the last frame. Then strengthen the
   last frame and recursively all lower frames by blocking
   counterexamples reaching ~P in one step until all successors of the
   last frame are within P, see {!block}.

   The list of frames must not be empty, we start with k=1. *)
let rec strengthen
    ((_, solver_frames, _) as solvers) transSys = 

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

      match 

        (* Find counterexamples where we can get outside the property
           in one step and generalize to a cube. The counterexample
           does not hold in the initial state. *)
        Stat.time_fun Stat.pdr_find_cex_time (fun () ->
            find_cex 
              solvers 
              transSys 
              r_k
              (Clause.top, Clause.empty)
              (Clause.singleton (TransSys.props_of_bound 0 transSys), Clause.empty))

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

           Event.log `PDR Event.L_trace
             "Counterexample to induction in last frame R_%d, \
              blocking recursively"
             (List.length frames);

           (* Block counterexample in all lower frames *)
           let frames' = 
             block 
               solvers 
               transSys 
               [([block_clause], r_k)] 
               frames_tl
           in

           (* Find next counterexample to block *)
           strengthen solvers transSys frames')
        

(*
let block_propagated_cex 
    ((_, solver_frames, solver_misc) as solvers) 
    transSys 
    cex = 

  function 

    (* k > 0, must have at least one frame *)
    | [] -> invalid_arg "block_propagated_cex"

    (* Head of frames is the last frame *)
    | r_k :: frames_tl as frames -> 

      (* No counterexamples to block *)
      if cex = [] then 

        (* Return unchanged *)
        (frames, cex)

      else

        (debug smt
            "block_propagated_cex: asserting clauses of R_k"
         in

         S.push solver_misc;

         (* Assert all clauses of R_k in this context *)
         CNF.iter 
           (function c -> S.assert_term solver_misc (Clause.to_term c)) 
           r_k;

         (* Filter for counterexamples that are in the frame *)
         let actual_cex =
           List.filter 
             (function t -> S.check_sat_term solver_misc [Term.mk_and t])
             cex
         in

         (* Remove assertions of frame from context *)
         S.pop solver_misc;

         (* No counterexamples to block *)
         if actual_cex = [] then 

           (

             (* Remove assertions of frame from context *)
             S.pop solver_frames;

             (* Return unchanged *)
             (frames, cex)

           )

         else

           (

             S.push solver_frames;

             (* Assert all clauses of R_k in this context *)
             CNF.iter 
               (function c -> S.assert_term solver_frames (Clause.to_term c)) 
               r_k;


             (* Block counterexamples, we get changed frame and new
                counterexamples *)
             let frames', cex' = 
               block solvers transSys cex [(actual_cex, r_k)] frames_tl 
             in
(*
           (* Remove assertions of frame from context *)
           S.pop solver_frames;
*)
             (* Return changed frames and new counterexamples *)
             (frames', cex'))

        )

*)

(* ********************************************************************** *)
(* Forward propagation                                                    *)
(* ********************************************************************** *)

(*
(* Check if clause is inductive *)
let is_inductive solver clause = 

  (* Term of clause *)
  let term = Clause.to_term clause in

  (* Primed term of clause *)
  let term' = TransSys.bump_state 1 term in

  (* Check entailment *)
  S.check_entailment solver [term] term' 
*)
  
(* Check for inductive clauses simultaneously

   The context of the solver must contain the transition relation and
   the invariants. *)
let rec partition_inductive solver accum terms =

  (* Add prime to all terms *)
  let terms' = List.map (TransSys.bump_state 1) terms in 

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
          (function t -> Eval.bool_of_value (Eval.eval_term t model))
          terms'
      in

      (* Remove primes from not inductive terms *)
      let not_inductive = 
        List.map (TransSys.bump_state (- 1)) not_inductive' 
      in

      (* Remove primes from potentially inductive terms *)
      let maybe_inductive =
        List.map (TransSys.bump_state (- 1)) maybe_inductive' 
      in

      Event.log `PDR Event.L_trace
        "%d clauses not inductive, %d maybe" 
        (List.length not_inductive)
        (List.length maybe_inductive);

      (* Continue checking remaining terms for inductiveness *)
      partition_inductive solver (not_inductive @ accum) maybe_inductive 
        
    (* All term are inductive, return not inductive and inductive terms *)
    | false, _ -> 

      Event.log `PDR Event.L_trace
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
    let terms' = List.map (TransSys.bump_state 1) terms in 

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
        let vars = TransSys.vars_of_term (Term.mk_and terms') in

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
            (function t -> Eval.bool_of_value (Eval.eval_term t model))
            terms'
        in

        (* Remove primes from not propagatable terms *)
        let cannot_propagate = 
          List.map (TransSys.bump_state (- 1)) cannot_propagate' 
        in

        (* Remove primes from potentially propagatable terms *)
        let maybe_propagate =
          List.map (TransSys.bump_state (- 1)) maybe_propagate' 
        in

        Event.log `PDR Event.L_trace
          "%d clauses cannot be propagated, %d maybe" 
          (List.length cannot_propagate)
          (List.length maybe_propagate);

        (* Continue checking remaining terms for inductiveness *)
        partition_propagate solver (cannot_propagate @ accum) maybe_propagate 

      (* All clauses can be propagated, return propagated and
         not propagated terms *)
      | false -> 

        Event.log `PDR Event.L_trace
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
let fwd_propagate ((_, solver_frames, _) as solvers) transSys frames =

  (* Recursively forward propagate from lower frame to higher frames *)
  let rec fwd_propagate_aux 
      ((solver_init, solver_frames, solver_misc) as solvers) 
      transSys 
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
              S.assert_term solver_misc (TransSys.constr_of_bound 1 transSys);

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

              if Flags.pdr_dump_inductive_assertions () then

                (

                  List.iter
                    (Format.fprintf 
                       !ppf_inductive_assertions
                       "@[<hv 2>assert@ %a;@]@." 
                       Lustre.pp_print_term) 
                    inductive_terms

                );

              (* Send invariant *)
              List.iter 
                (fun c -> Event.invariant `PDR (Clause.to_term c))
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
               transSys.TransSys.invars <- 
                 inductive_terms @ transSys.TransSys.invars);

              (* Add invariants to solver instance *)
              List.iter 
                (S.assert_term solver_init)
                inductive_terms;

              (* Add invariants to solver instance *)
              List.iter 
                (S.assert_term solver_init)
                (List.map (TransSys.bump_state 1) inductive_terms);

              (* Add invariants to solver instance *)
              List.iter 
                (S.assert_term solver_frames)
                inductive_terms;

              (* Add invariants to solver instance *)
              List.iter 
                (S.assert_term solver_frames)
                (List.map (TransSys.bump_state 1) inductive_terms);

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

        (* Add clauses propagated from the previous frame 

           No check for subsumption necessary: if a clause is not
           subsumed in one frame, it cannot be subsumed in the next
           frame, which is a subset of the previous frame *)
        let f' = CNF.union prop f in

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
                  [Term.negate (TransSys.bump_state 1 (Clause.to_term c))])
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
                     (fun c -> (Term.negate (TransSys.bump_state 1 c)))
                     clause
                 in

                 let literals' = Clause.elements clause' in

                 (* Add a name to each literal *)
                 let literals'_named, name_to_literal = 
                   name_terms literals'
                 in

                 S.push solver_frames;

                 (* Assert negated literals *)
                 List.iter
                   (S.assert_term solver_frames)
                   literals'_named;

                 (* Check for entailment *)
                 if S.check_sat solver_frames then
                   
                   (S.pop solver_frames;

                   (* Clause does not propagate *)
                    (CNF.add clause keep, fwd))

                 else

                   (* Get clause literals in unsat core *)
                   let clause'_core, clause'_rest = 

                     partition_core
                       solver_frames
                       name_to_literal
                       (Clause.of_literals literals')

                   in

                   (* Remove primes and negate literals *)
                   let clause_core =
                     Clause.map
                       (fun l -> 
                          (Term.negate (TransSys.bump_state (- 1) l)))
                       clause'_core
                   in

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
                   
                   S.pop solver_frames;

                   (* Clause was tightened? *)
                   if not (Clause.is_empty clause'_rest) then 
                     
                     (debug pdr
                       "Tightened clause@ %a to@ %a@ dropping@ %a"
                       Clause.pp_print_clause clause
                       Clause.pp_print_clause clause_core
                       Clause.pp_print_clause clause'_rest
                      in

                      S.push solver_frames;

                      S.assert_term solver_frames (Clause.to_term clause_core);
                      
                      (* Shortening the clause must not make the frame
                         unsatisfiable *)
                      assert (S.check_sat solver_frames);

                      S.assert_term 
                        solver_frames 
                        (Term.negate 
                           (TransSys.bump_state
                              1
                              (Clause.to_term clause_core)));

                      (* The shortened clause must propagate *)
                      assert (not (S.check_sat solver_frames));

                      S.pop solver_frames;

                      Stat.incr Stat.pdr_tightened_propagated_clauses;

                      (* Propagate shortened clause, keep original *)
                      (* (CNF.add clause keep, CNF.add clause_core fwd)) *)
                      (keep, CNF.add clause_core fwd))

                   else

                     (

                       (* Propagate unchanged clause *)
                       (keep, CNF.add clause fwd)))
              f'
              (CNF.empty, CNF.empty)

        in

        Stat.incr 
          ~by:(CNF.cardinal fwd) 
          Stat.pdr_fwd_propagated;

        Event.log `PDR Event.L_trace
          "Propagating %d clauses from F_%d to F_%d"
          (CNF.cardinal fwd)
          (succ (List.length accum))
          (succ (succ (List.length accum)));

        (* All clauses in R_i-1 \ R_i can be propagated to R_i, hence
           we have R_i-1 = R_i and terminate *)
        if CNF.cardinal keep = 0 then 

          (

            Event.log `PDR Event.L_trace
              "Fixpoint reached: F_%d and F_%d are equal"
              (succ (List.length accum))
              (succ (succ (List.length accum)));

            Stat.set 
              (succ (List.length accum))
              Stat.pdr_fwd_fixpoint;

            raise (Success (List.length frames))

          );

        (* Remove clauses of this frame from the context *)
        S.pop solver_frames;

        (* Propagate in next frame *)
        fwd_propagate_aux solvers transSys fwd (keep :: accum) tl

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
    transSys
    CNF.empty
    []
    (List.rev frames)
  

(* Check if the property is valid in the initial state and in the
   successor of the initial state, raise exception [Counterexample] if
   not *)
let bmc_checks solver_init transSys =

  (* Push new scope onto context of solver *)
  S.push solver_init;

  (debug smt 
      "Asserting negated property"
   in

   (* Assert negated property in the first state *)
   S.assert_term 
     solver_init 
     (Term.negate (TransSys.props_of_bound 0 transSys)));

  (* Check if the property is violated in the initial state *)
  if S.check_sat solver_init then raise Counterexample;

  (* Remove assertions for 0-step counterexample check *)
  S.pop solver_init;

  Event.log `PDR Event.L_info "All properties hold in the initial state.";

  (* Push new scope onto context of solver *)
  S.push solver_init;

  (debug smt 
      "Asserting negated property in the second state"
   in

   (* Assert negated property in the second state *)
   S.assert_term 
     solver_init 
     (Term.negate (TransSys.props_of_bound 1 transSys)));

  (debug smt 
      "Asserting transition relation"
   in

   (* Assert transition relation *)
   S.assert_term solver_init (TransSys.constr_of_bound 1 transSys));

  (debug smt 
      "Asserting invariants for second state"
   in

   (* Assert invariants for second state *)
   S.assert_term 
     solver_init
     (TransSys.invars_of_bound 1 transSys));

  (* Check if the property is violated in the second state *)
  if S.check_sat solver_init then raise Counterexample;

  (* Remove assertions for 1-step counterexample check *)
  S.pop solver_init;

  Event.log `PDR Event.L_info
    "All properties hold in the successor states of the initial state."


(* ********************************************************************** *)
(* Main loop and top-level function                                       *)
(* ********************************************************************** *)

(* Handle events from the queue and return the current k in the BMC process *)
let handle_events ((solver_init, solver_frames, _) as solvers) transSys bmc_k = 

   (* Receive all queued messages *)
   let messages = Event.recv () in

     List.fold_left 
       (function bmc_k -> function
        
         (* Invariant discovered by other module *)
         | Event.Invariant (_, inv) -> 
           
           (debug pdr
              "@[<hv>Received invariant@ @[<hv>%a@]@]"
              Term.pp_print_term inv 
            in
           
           (* Add invariant to the transition system *)
           TransSys.add_invariant transSys inv);
           
           (* Add prime to invariant *)
           let inv_1 = TransSys.bump_state 1 inv in

           (* Assert invariant in solver instance for initial state *)
           S.assert_term solver_init inv;
           S.assert_term solver_init inv_1;

           (* Assert invariant and primed invariant in solver instance for
              transition relation *)
           S.assert_term solver_frames inv;
           S.assert_term solver_frames inv_1;

           (* No new k in BMC *)
           bmc_k
           
         (* Pass new k in BMC *)
         | Event.BMCState (bmc_k', _) -> bmc_k'

         (* Property has been proved by other module 
            
            TODO: add as invariant and remove from properties to prove *)
         | Event.Proved (_, _, prop) -> bmc_k
           
         (* Property has been disproved by other module
          
            TODO: remove from properties to prove *)
         | Event.Disproved (_, _, prop) -> bmc_k
           
       )
       bmc_k
       messages


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
let rec pdr ((solver_init, solver_frames, _) as solvers) transSys bmc_k frames = 

  let pdr_k = succ (List.length frames) in

  Event.log `PDR Event.L_info "PDR main loop at k=%d" pdr_k;

  Event.progress `PDR pdr_k;

  Stat.set pdr_k Stat.pdr_k;

  Stat.update_time Stat.pdr_total_time; 

  (debug pdr 
     "Main loop, k=%d" 
     (succ (List.length frames))
   in

  (* Handle messages in the queue and return current k in BMC process *)
  let bmc_k' = handle_events solvers transSys bmc_k in

   debug pdr 
       "@[<v>Frames before forward propagation@,@[<hv>%a@]@]"
       pp_print_frames frames
   in

  (debug smt
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
      fwd_propagate solvers transSys frames 

    (* Fixed point reached *)
    with Success pdr_k -> 

      (* Must have checked for 0 and 1 step counterexamples *)
      if bmc_k' > 1 then raise (Success pdr_k) else

        (* Wait until BMC process has passed k=1 *)
        let rec wait_for_bmc bmc_k = 

          (* Handle events *)
          let bmc_k' = handle_events solvers transSys bmc_k in

          (* BMC has passed k=1? *)
          if bmc_k' > 1 then 

            (* Raise exception again *)
            raise (Success pdr_k)

          else

            (

              (* Delay *)
              minisleep 0.1;
              
              (* Wait *)
              wait_for_bmc bmc_k'
          
            )

        in

        (* Wait until BMC has passed k=1 *)
        wait_for_bmc bmc_k'

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
  let frames'' = strengthen solvers transSys frames' in

  Stat.record_time Stat.pdr_strengthen_time;

  Stat.set_int_list (frame_sizes frames'') Stat.pdr_frame_sizes;

  (* No reachable state violates the property, continue with the
       next k *)
  pdr solvers transSys bmc_k' frames''))


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
let main transSys =

  Stat.start_timer Stat.pdr_total_time;

  (* Determine logic for the SMT solver *)
  let logic = TransSys.get_logic transSys in

  (* Create new solver instance to reason about the initial state *)
  let solver_init = 
    S.new_solver ~produce_assignments:true ~produce_cores:true logic
  in

  (* Save solver instance for clean exit *)
  ref_solver_init := Some solver_init;

  (debug smt
      "Permanently asserting initial state constraint in solver instance"
   in

   (* Assert initial state constraint in solver instance *)
   S.assert_term solver_init (TransSys.init_of_bound 0 transSys));

  (* Get invariants of transition system *)
  let invars_1 = TransSys.invars_of_bound 1 transSys in

  (* Get invariants for current state *)
  let invars_0 = TransSys.invars_of_bound 0 transSys in

  (* Assert invariants for current state if not empty *)
  if not (invars_0 == Term.t_true) then 

    (debug smt 
        "Permanently asserting invariants in solver instance"
     in

     S.assert_term solver_init invars_0;

     S.assert_term solver_init invars_1);


  (* Create new solver instance to reason about counterexamples in
     frames *)
  let solver_frames = 
    S.new_solver ~produce_assignments:true ~produce_cores:true logic
  in

  (* Save solver instance for clean exit *)
  ref_solver_frames := Some solver_frames;

  (debug smt 
      "Permanently asserting property constraint in solver instance"
   in

   (* The property is implicit in every R_i *)      
   S.assert_term solver_frames (TransSys.props_of_bound 0 transSys));

  (debug smt 
      "Permanently asserting transition relation"
   in

   (* Assert transition relation from current frame *)
   S.assert_term solver_frames (TransSys.constr_of_bound 1 transSys));

  if not (invars_0 == Term.t_true) then 

    (

      (debug smt 
          "Permanently asserting unprimed invariants"
       in

       (* Assert invariants for current state *)
       S.assert_term 
         solver_frames
         invars_0);

      (debug smt
          "Permanently asserting invariants"
       in

       (* Assert invariants for next state *)
       S.assert_term 
         solver_frames
         invars_1)

    );

  (* Create new solver instance for all other queries (subsumption,
     invariance of blocking clauses) *)
  let solver_misc = 
    S.new_solver ~produce_assignments:true logic
  in

  (* Save solver instance for clean exit *)
  ref_solver_misc := Some solver_misc;

  (match Flags.pdr_inductive_assertions_file () with 

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

  (

    try 

      (* BMC module running in parallel? 

         If BMC is running in parallel, delegate check for zero and one
         step counterexamples to it. All results are tentative until BMC
         has shown that there are no such counterexamples. *)
      let bmc_init_k = 

        if List.mem `BMC (Flags.enable ()) then 

          (Event.log `PDR Event.L_info
             "Delegating check for zero and one step counterexamples \
              to BMC process.";

           (* BMC process starts at k=0 *)
           0

          )


      else

          (

            (* Do check for zero and one step counterexample in solver
               instance [solver_init] *)
            bmc_checks solver_init transSys;

            (* We have done checks for k=0 and k=1 *)
            2

          )

      in

      (debug smt 
          "Permanently asserting transition relation in solver_init"
       in
       
       (* Assert transition relation from current frame *)
       S.assert_term solver_init (TransSys.constr_of_bound 1 transSys));
      
      (* Run PDR procedure *)
      pdr (solver_init, solver_frames, solver_misc) transSys bmc_init_k [];

    with 

      (* All properties are valid *)
      | Success k -> 

        (

          List.iter (Event.proved `PDR (Some k)) transSys.TransSys.props
         
        )

      (* Some property is invalid *)
      | Counterexample -> 

        (
          
          List.iter 
            (function (p, _) -> Event.disproved `PDR None p) 
            transSys.TransSys.props

        )

  )


(*
;;


open Term.Abbrev;;

Debug.enable "smt" Format.std_formatter;;
Debug.enable "pdr" Format.std_formatter;;
Debug.enable "qe" Format.std_formatter;;
Debug.enable "extract" Format.std_formatter;;
Debug.enable "eval" Format.std_formatter;;
Debug.enable "termConv" Format.std_formatter;;
Debug.enable "lexer" Format.std_formatter;;


(* TODO: support uninterpreted constants in Eval
let u_n0 = UfSymbol.mk_uf_symbol "n0" [] (Type.mk_int ());;
let n0 = Term.mk_uf u_n0 [];;
*)

let n0 = ?%@4;;

let sv_c = StateVar.mk_state_var "c" (Type.mk_int ());;
let sv_n = StateVar.mk_state_var "n" (Type.mk_int ());;

let v_c'0 = Var.mk_state_var_instance sv_c (Lib.numeral_of_int 0);;
let v_c'1 = Var.mk_state_var_instance sv_c (Lib.numeral_of_int 1);;
let v_n'0 = Var.mk_state_var_instance sv_n (Lib.numeral_of_int 0);;
let v_n'1 = Var.mk_state_var_instance sv_n (Lib.numeral_of_int 1);;
let v = [sv_c; sv_n];;

let c'0 = Term.mk_var v_c'0;;
let c'1 = Term.mk_var v_c'1;;
let n'0 = Term.mk_var v_n'0;;
let n'1 = Term.mk_var v_n'1;;

let i = (c'0 =@ ?%@ 1) &@ (n'0 =@ n0);;

let t = 
  (n'1 =@ n'0) &@ 
    ((c'0 =@ n'0) =>@ (c'1 =@ ?%@ 1)) &@ 
    (!@(c'0 =@ n'0) =>@ (c'1 =@ (c'0 +@ ?%@ 1)));; 

let p = c'0 <=@ (n'0 +@ ?%@ 1);;

Debug.printf "pdr" "I: %a" Term.pp_print_term i;;
Debug.printf "pdr" "T: %a" Term.pp_print_term t;;
Debug.printf "pdr" "P: %a" Term.pp_print_term p;;

let z = { 
  TransSys.init = [i]; 
  TransSys.constr = [t]; 
  TransSys.trans = []; 
  TransSys.props = [("p", p)]; 
(*  TransSys.props = [("p1", n0 =@ n'0); ("p2", p)]; *)
  TransSys.props_valid = []; 
  TransSys.props_invalid = [] }
;;

main z
  
;; 

*)

(*
open Term.Abbrev;;
let l1 = ?%@ 0 <=@ ?%@ 1;;
let l2 = ?%@ 1 <=@ ?%@ 2;;
let l3 = ?%@ 0 <=@ ?%@ 2;;
let c1 = Clause.singleton l1;;
let c2 = Clause.singleton l2;;
let c3 = Clause.singleton l3;;
let c12 = Clause.union c1 c2;;
let c13 = Clause.union c1 c3;;
let c123 = Clause.union c12 c3;;
let s12 = CNF.singleton c12;;
let s123 = CNF.singleton c123;;
*)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
