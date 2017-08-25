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

(*
  Variable naming conventions:
  
  FRAMES

  In any list of frames, the frames are ordered by proximity to the current
  frame. Frames are by default difference-encoded lists of terms.

  fi - the current frame
  fj - the frame below the current frame
  frames_gt - all frames above the current frame
  frames_lt - all frames below the current frame
  
  frames_gte - fi::frames_gt
  frames_lte - fi::frames_lt

  frames_ltt - all frames below fj
  frame - the concatenation of frames_gte (removes difference encoding)
*)


module A = Actlit
module TermMap = Map.Make(Term)
  
(* Define exceptions to break out of loops *)
exception Success of Term.t
exception Failure
exception Error
exception Counterexample of Term.t list
exception InvariantViolation of int
exception ConcreteCounterexample of (Model.t * int)
    
(* Cleanup before exit *)
let on_exit _ = ()

(* ********************************************************************** *)
(* Utility functions for terms                                            *)
(* ********************************************************************** *)

(* extracts all atoms from a term *)
let atoms_of_term = Term.eval_t
  (fun subterm atom_lists ->
    if Term.is_atom (Term.construct subterm)
    then (Term.construct subterm)::(List.concat atom_lists)
    else List.concat atom_lists)
  
(* Removes duplicates from list of terms *)
let unique_terms term_list = (Term.TermSet.elements (Term.TermSet.of_list term_list))

(* Takes the given assignments from the sat solver and produces a list of terms *)
let get_term_list_from_term_values assignments = List.map
    (fun (term, value) ->
      if Term.bool_of_term value
      then term
      else Term.negate term)
    assignments   
  
(* ********************************************************************** *)
(* Abstracted variables                                                   *)
(* ********************************************************************** *)

(*
 * abvar_map is a map with terms as keys and abstract variables as values.
 * It is a bijection, and is therefore invertable
 *)
  
let absvarcounter = ref 0
  
(* For each predicate in new_predicates, it creates a new abstract variable.
   Output is the new map followed by a list of new abstract variables. *)
let update_abvar_map old_map new_predicates =

  (* Creates and returns a new abstract variable. Does NOT declare it. *)
  let mk_new_abvar term =
    
    (* First we need to extract the scope from term *)
    let abvar_scope = 
      let state_vars = Term.state_vars_of_term term in
      let usr_scope = StateVar.scope_of_state_var (StateVar.StateVarSet.choose state_vars) in
      (List.hd usr_scope)::["abv"]
    in

    (* give this abstract variable a unique name *)
    let abvar_name = Format.asprintf
      "abv%d"
      !absvarcounter
    in

    incr absvarcounter;
      
    (* create a new state variable (or use an existing one) to represent the abvar *)
    let abvar_statevar = StateVar.mk_state_var
      abvar_name
      abvar_scope
      Type.t_bool
    in

    (* we need to know the offset. Since abvars are used only for terms over one offset,
       we may safely assume that an arbitrary variable in the term is representative of the offset*)
    let abvar_offset =
      let vars = Term.vars_of_term term in
      Var.offset_of_state_var_instance (Var.VarSet.choose vars)
    in

    (* create an instance of the abvar at the given offset *)
    let abvar_instance = Var.mk_state_var_instance abvar_statevar abvar_offset in
    
    (* return the term consisting of the new var *)
    Term.mk_var abvar_instance
  in
    
  (* We only want new and unique predicates *)
  let new_predicates = List.filter
    (fun t ->  not (TermMap.mem t old_map))
    (unique_terms new_predicates)
  in
  
  (* new map from predicates to abvars *)
  let new_map = List.fold_left
    (fun acc p -> TermMap.add p (mk_new_abvar p) acc)
    old_map
    new_predicates
  in

  let new_abvars = List.map
    (fun t -> TermMap.find t new_map)
    new_predicates
  in

  Format.printf "@.Updated abvar_map with predicates. New map:@.";

  List.iter
    (fun (k,v) -> Format.printf "@.%a @.-----> MAPS TO %a@." Term.pp_print_term k Term.pp_print_term v)
    (TermMap.bindings new_map);
  
  new_map, new_abvars

(* declares given abstract variables at the given offset in solver.
   necessary for abstract path generation. *)
let declare_abstract_variables_at_offset solver abvars n = Var.declare_vars
  (SMTSolver.declare_fun solver)

  (* extracts all variables from the abvars *)
  (let set_of_variables = List.fold_left
     (fun acc term -> Var.VarSet.union acc (Term.vars_of_term term))
     Var.VarSet.empty
     abvars
   in
   
   List.map
     (fun v -> Var.set_offset_of_state_var_instance v (Numeral.of_int n))
     (Var.VarSet.elements set_of_variables))

(* generates hp, the list of equivalence terms between abvars and predicates *)
let get_hp abvar_map = List.map
  (fun (k,v) -> Term.mk_eq [k;v])
  (TermMap.bindings abvar_map)

(* inverts the given abvar map. It would work for other maps too, of course. *)
let invert abvar_map = List.fold_left
  (fun acc (k,v) -> TermMap.add v k acc)
  TermMap.empty
  (TermMap.bindings abvar_map)
  
let ic3ia solver input_sys aparam trans_sys init trans prop =

  let predicates = [init;(snd prop)] in  

  (* set containing all state variables in the problem *)
  let statevars = List.fold_left
    (fun acc p ->
      StateVar.StateVarSet.union (Term.state_vars_of_term p) acc)
    StateVar.StateVarSet.empty
    (trans::predicates)
  in

  (* list of all state variables as terms at offset 0 *)
  let variables = List.map
    (fun s -> Term.mk_var (Var.mk_state_var_instance s Numeral.zero))
    (StateVar.StateVarSet.elements statevars)
  in

  List.iter
    (Format.printf "@.variable: %a@." Term.pp_print_term)
    variables;
  (* ********************************************************************** *)
  (* Cloned variables                                                       *)
  (* ********************************************************************** *)
  
  (* Function to clone and declare all variables in given predicates and return a map *)
  let get_clone_map predicates =
    
    (* fold over statevars to construct map to new statevars *)
    let clone_map = StateVar.StateVarSet.fold
      (fun v acc ->
	
	(* Create a new state variable to correspond to v*)
	let new_statevar =
	  (StateVar.mk_state_var
	     ~is_input:(StateVar.is_input v)
	     ~is_const:(StateVar.is_const v)
	     ~for_inv_gen:(StateVar.for_inv_gen v)
	     (* The new name is the same as the old, but we will change the scope to *.cln.* *)
	     (StateVar.name_of_state_var v)
	     (List.hd (StateVar.scope_of_state_var v)::["cln"])
	     (StateVar.type_of_state_var v))
	in
	
	StateVar.StateVarMap.add v new_statevar acc)
      statevars
      StateVar.StateVarMap.empty
    in
    
    clone_map
  in
  
  (* Repeat for each term in predicates and in the transition function *)
  let clone_map = get_clone_map (trans::predicates) in

  (* Creates a clone of an uncloned term using provided map *)
  let clone_term term =
    let lookup term = StateVar.StateVarMap.find term clone_map in
    Term.map_state_vars lookup term
  in
  
  let declare_clone_variables_at_offset n =

    let set_of_variables_at_offset = List.map
      (fun sv ->
	let clone_sv = StateVar.StateVarMap.find sv clone_map in
	Var.mk_state_var_instance clone_sv (Numeral.of_int n))
      (StateVar.StateVarSet.elements statevars)
    in
    
    Var.declare_vars
      (SMTSolver.declare_fun solver)
      set_of_variables_at_offset
  in

  (* Initialize the clone variables *)
  declare_clone_variables_at_offset 0;
  declare_clone_variables_at_offset 1;  

  (* For declaring user variables at higher offsets *)
  let declare_variables_at_offset n =

    let set_of_variables_at_offset = List.map
      (fun sv ->
	Var.mk_state_var_instance sv (Numeral.of_int n))
      (StateVar.StateVarSet.elements statevars)
    in
    
    Var.declare_vars
      (SMTSolver.declare_fun solver)
      set_of_variables_at_offset;
  in
  
  (* Generates a term asserting the equality of an uncloned term and its clone *)
  let mk_clone_eq term =
    Term.mk_eq [term;clone_term term]
  in

  (* Gets the conjunction of equivalences between terms and their clones *)
  let get_eqP predicates =
    Term.mk_and (List.map mk_clone_eq predicates)
  in

  (* ********************************************************************** *)
  (* Abstracted variables                                                   *)
  (* ********************************************************************** *)

  let abvar_map, abvars = update_abvar_map TermMap.empty predicates in

  declare_abstract_variables_at_offset solver abvars 0;
  declare_abstract_variables_at_offset solver abvars 1;
  
  (* list of association terms between concrete and abstract variables *)
  let hp = get_hp abvar_map in

  (* abstracted terms *)
  let init' = TermMap.find init abvar_map in
  let prop' = TermMap.find (snd prop) abvar_map in

  let mk_and_assert_actlit trm =
    let act = A.fresh_actlit () in
    SMTSolver.declare_fun solver act;
    let acttrm = A.term_of_actlit act in
    let actimpl = Term.mk_implies [acttrm;trm] in
    SMTSolver.assert_term solver actimpl;
    acttrm
  in

  (* Check whether 'I ^ H |= 'P *)
  SMTSolver.check_sat_assuming_and_get_term_values
    solver
    
    (* SAT case ('P not entailed) *)
    (fun _ assignments ->
      Format.printf "@.Property invalid in initial state@.";

      let model = 
	SMTSolver.get_var_values
          solver
          (TransSys.get_state_var_bounds trans_sys)
          (TransSys.vars_of_bounds trans_sys Numeral.zero Numeral.zero)
      in
      
      raise (ConcreteCounterexample (model,0)))
    
    (* UNSAT case ('P entailed) *)
    (fun _ ->
      Format.printf "@.Property valid in initial state@.")

    (* Check satisfiability of 'I ^ H ^ !'P *)
    (List.map
       mk_and_assert_actlit
       ( hp @ init' :: [Term.negate prop']))

    (*  Check values of the things we fed in *)
    abvars;
  
  (* ********************************************************************** *)
  (* Utility                                                                *)
  (* ********************************************************************** *)

  (* Print frames for debugging *)
  let print_frames frames =
    let frames = List.rev frames in
    let framecounter = ref 0 in
    Format.printf "@.=====| FRAMES |=====@.";
    List.iter
      (fun f ->
	Format.printf "@.Frame #%d@." !framecounter;
	incr framecounter;
	List.iter
	  (fun t -> Format.printf "@. Term: %a@." Term.pp_print_term t)
	  f)
      frames;
    Format.printf "@.=====================@."
  in
    
  (* Checks whether clause is inductive relative to frame, where frame 
     has been converted from being difference encoded to including all clauses 
     of all frames sbove and including the current one
     
     If the clause is inductive, an empty list will be returned.
     
     If the clause is not inductive, a counterexample consisting of a list of 
     value assignments encoded as terms will be returned. *)
  
  let absrelind abvar_map frame clause =
    
    let abvars = List.map snd (TermMap.bindings abvar_map) in
    let predicates = List.map fst (TermMap.bindings abvar_map) in
    
    (* F ^ c ^ hp ^ eq ^ T(clone) ^ ~c' *)
    let terms_to_check =
      let eqP = get_eqP predicates in (* may need to allow updates to predicates*)
      let clone_trans = clone_term trans in
      let bump = Term.bump_state Numeral.one in
      let hp = Term.mk_and (get_hp abvar_map) in
      frame @
	[clone_trans;
	 clause;
	 hp;bump hp;
	 eqP;bump eqP;
	 bump (Term.negate clause)]
    in

    SMTSolver.check_sat_assuming_and_get_term_values
      solver

      (* SAT case - returns a list of terms that satisfies the predicate *)
      (fun _ assignments -> get_term_list_from_term_values assignments)

      (* UNSAT case - returns an empty list *)
      (fun _ -> [])
      
      (* F ^ c ^ hp ^ eq ^ T(clone) ^ ~c' *)
      (List.map mk_and_assert_actlit terms_to_check)

      abvars
  in
  
  (* Sometimes we don't need the counterexample from absrelind *)
  let isabsrelind abvar_map frame clause =

    let predicates = List.map
      fst
      (TermMap.bindings abvar_map)
    in
    
    (* F ^ c ^ hp ^ eq ^ T(clone) ^ ~c' *)
    let terms_to_check =
      let eqP = get_eqP predicates in (* may need to allow updates to predicates*)
      let clone_trans = clone_term trans in
      let bump = Term.bump_state Numeral.one in
      let hp = Term.mk_and (get_hp abvar_map) in
      frame @
	[clone_trans;
	 clause;
	 hp;bump hp;
	 eqP;bump eqP;
	 bump (Term.negate clause)]
    in
    
    not (SMTSolver.check_sat_assuming_tf
	   solver      
	   (List.map mk_and_assert_actlit terms_to_check))
  in


  (* does the clause contradict the frame? *)
  let isSatisfiable abvar_map frame clause = 

    (* F ^ hp ^ c *)
    let terms_to_check =
      let hp = Term.mk_and (get_hp abvar_map) in
      clause :: hp :: frame
    in

    SMTSolver.check_sat_assuming_tf
      solver
      (List.map mk_and_assert_actlit terms_to_check)
      
  in

  (* does the frame imply the clause? *)
  let isEntailed abvar_map frame clause =
    (* F ^ hp ^ ~c *)
    let terms_to_check =
      let hp = Term.mk_and (get_hp abvar_map) in
      (Term.negate clause) :: hp :: frame
    in

    not (SMTSolver.check_sat_assuming_tf
	   solver
	   (List.map mk_and_assert_actlit terms_to_check))
      
  in
  
  (* is the clause redundant given the frame? *)
  let notentailed frame clause =
    SMTSolver.check_sat_assuming_tf
      solver
      (List.map
	 mk_and_assert_actlit
	 ((Term.negate clause)::frame))
  in

  (* returns frames where redundant clauses are removed *)
  let consolidate frames_lte =

    let rec filter_redundant_clauses frames_gt frames_lte =

      (* removes clauses that are entailed by the rest of the frame *)
      let rec filter_clauses checked remaining =

	match remaining with

	(* nothing left to filter, so return the clauses that were not entailed *)
	| [] -> checked

	(* check whether the head is entailed; add to checked if it is *)
	| c :: remaining' ->
	   if notentailed
	     (List.concat ( checked :: remaining' :: frames_gt ))
	     c
	   then filter_clauses (c::checked) remaining'
	   else filter_clauses checked remaining'
      in
      
      match frames_lte with

      (* Lowest frame reached; return *)
      | [] -> []

      (* filter this frame first, then filter lower frames *)
      | fi :: frames_lt ->

	 (* consolidate this frame *)
	 let fi' = filter_clauses [] fi in

	 (* consolidate frames below*)
	 let frames_lt' = filter_redundant_clauses (fi'::frames_gt) frames_lt in

	 (* return modified list of frames*)
	 fi'::frames_lt'	 
	 
    in

    filter_redundant_clauses [] frames_lte

  in  

  (* asserts that all invariants hold *)
  let checkInvariants abvar_map frames_lte = 
    
    (* invariant 1: f0 ^ hp |= I *)
    let i1 =
      let f0 = List.concat frames_lte in
      let hp = Term.mk_and (get_hp abvar_map) in
      
      (* f0 ^ hp ^ ~I *)
      let sat_terms = Term.negate init' :: hp :: f0 in
      
      (* invariant holds if this is not satisfiable *)
      not (SMTSolver.check_sat_assuming_tf
	     solver      
	     (List.map mk_and_assert_actlit sat_terms))
    in

    (* invariant 2: fi |= f(i+1) for all i < k 
       this is built into the difference-encoded frames, but we'll test it anyway *)
    
    let i2 =
      
      (* checks whether fa |= fb *)
      let check fa fb = 
	
	let fb = Term.mk_and fb in
	
	(* fa ^ ~ fb *)
	let sat_term = Term.negate fb :: fa in

	(* entailment if this is not satisfiable *)
	not (SMTSolver.check_sat_assuming_tf
	       solver      
	       (List.map mk_and_assert_actlit sat_term))
      in

      let rec testI2 frames_gte frames_lt =
	match frames_lt with
	(* nothing to check at the bottom *)
	| [] -> true
	   
	| fj :: frames_ltt ->
	   let fa = List.concat (fj::frames_gte) in
	   let fb = List.concat frames_gte in
	   (check fa fb && (testI2 (fj::frames_gte) frames_ltt))
      in

      match frames_lte with
      | [] -> true
      | fi :: frames_lt -> testI2 [fi] frames_lt

    in

    (* invariant 3: fi ^ T ^ hp ^ hp' |= f(i+1)' for all i < k *)

    let i3 =

      (* defines abstract transition relation*)
      let abv_trans =
	let hp = Term.mk_and (get_hp abvar_map) in
	let hp' = Term.bump_state Numeral.one hp in
	Term.mk_and [trans;hp;hp']
      in
      
      (* checks whether fa ^ T ^ hp ^ hp' |= fb *)
      let check fa fb = 

	let fb = Term.bump_state Numeral.one (Term.mk_and fb) in
	
	(* fa ^ T ^ hp ^ hp' ^ ~ fb' *)
	let sat_term = Term.negate fb :: abv_trans :: fa in

	(* entailment if this is not satisfiable *)
	not (SMTSolver.check_sat_assuming_tf
	       solver      
	       (List.map mk_and_assert_actlit sat_term))
      in
      
      let rec testI3 frames_gte frames_lt =
	match frames_lt with
	(* nothing to check at the bottom *)
	| [] -> true
	   
	| fj :: frames_ltt ->
	   let fa = List.concat (fj::frames_gte) in
	   let fb = List.concat frames_gte in
	   (check fa fb && (testI3 (fj::frames_gte) frames_ltt))
      in

      testI3 [List.hd frames_lte] (List.tl frames_lte)
    in

    (* invariant 4: fi ^ hp |= P for all i < k *)

    let i4 = 

      (* defines abstract transition relation*)
      let hp = Term.mk_and (get_hp abvar_map) in
      
      (* checks whether fa ^ hp |= P *)
      let check fa = 

	(* fa ^ hp ^ ~P *)
	let sat_term = Term.negate prop' :: hp :: fa in

	(* entailment if this is not satisfiable *)
	not (SMTSolver.check_sat_assuming_tf
	       solver      
	       (List.map mk_and_assert_actlit sat_term))
      in
      
      let rec testI4 frames_gte frames_lt =
	match frames_lt with
	(* nothing to check at the bottom *)
	| [] -> true
	   
	| fj :: frames_ltt ->
	   let fa = List.concat (fj::frames_gte) in
	   (check fa && (testI4 (fj::frames_gte) frames_ltt))
      in

      testI4 [List.hd frames_lte] (List.tl frames_lte)
    in    

  (* now report if one of these invariants is false*)

    if not i1 then raise (InvariantViolation 1);
    if not i2 then raise (InvariantViolation 2);
    if not i3 then raise (InvariantViolation 3);
    if not i4 then raise (InvariantViolation 4)
      
  in

  (* ********************************************************************** *)
  (* Simulate                                                               *)
  (* ********************************************************************** *)

  (* Function which takes a term and returns a list of copies (not to be 
     confused with clones) where each is offset by a different amount between 
     0 and k *)
  let copy_and_bump_term k trm =
    let rec rec_cnb = function
      | 0 -> [trm]
      | i -> (Term.bump_state (Numeral.of_int i) trm)::(rec_cnb (i-1))
    in
    rec_cnb k
  in

  (* Takes as input an abstract path and determines whether it can be 
     concretized *)
  let simulate abstract_path abvar_map =
    let k = List.length abstract_path - 1 in

    let variables_on_path =
      (List.concat
	 (List.map
	    (copy_and_bump_term k)
	    variables))
    in
    
    let term_list = 
      abstract_path
      @(copy_and_bump_term (k-1) trans)
      @(List.concat (List.map (copy_and_bump_term k) (get_hp abvar_map)))
    in

    (* check satisfiability of abstract path and return concrete path or nothing *)
    SMTSolver.check_sat_assuming_and_get_term_values
      solver

      (* SAT case - returns the term assignments on the path *)
      (fun _ assignments ->

	let model = 
	SMTSolver.get_var_values
          solver
          (TransSys.get_state_var_bounds trans_sys)
          (TransSys.vars_of_bounds trans_sys Numeral.zero (Numeral.of_int k))
	in
	
	Format.printf "@.Model: %a@." Model.pp_print_model model;
	
	Some model)

      (* UNSAT case - returns an empty list *)
      (fun _ -> None)
      
      (List.map mk_and_assert_actlit term_list)
      
      variables_on_path
      
  in

  (* Generates interpolants. Abstract path must be unbumped in ascending order of offset.*)
  let generate_interpolants abvar_map abstract_path =
    let interpolizers = 

      (* Converts the abvar map into its inverse. Justified because we know that it is
	 a bijective map by construction.*)
      let rev_abvar_map = List.fold_left
  	(fun acc (key,value) -> TermMap.add value key acc)
  	TermMap.empty
	(TermMap.bindings abvar_map)
      in

      (* Replaces all abstract variables in trm with their concrete atomic forms *)
      let concretize_term trm = Term.map
	(fun _ t ->
	  if TermMap.mem t rev_abvar_map
	  then TermMap.find t rev_abvar_map
	  else t)
	trm
	
      in      
      
      (* Creates the sequence of formulas that will be used to generate interpolants. *)
      List.mapi
      	(fun i s ->
      	  match i with
      	  | 0 -> concretize_term s
      	  | n ->
      	     Term.mk_and [
      	       Term.bump_state (Numeral.of_int (n-1)) trans;
      	       Term.bump_state (Numeral.of_int n) (concretize_term s)])
      	abstract_path
      
      (* List.mapi *)
      (* 	(fun i s -> *)
      (* 	  match i with *)
      (* 	  | k when k = List.length abstract_path - 1 -> *)
      (* 	     Term.bump_state (Numeral.of_int k) (concretize_term s) *)
      (* 	  | n -> *)
      (* 	     Term.mk_and [ *)
      (* 	       Term.bump_state (Numeral.of_int n) trans; *)
      (* 	       Term.bump_state (Numeral.of_int n) (concretize_term s)]) *)
      (* 	abstract_path *)
    in

    List.iter
      (fun t -> Format.printf "@.Interpolizer: %a@." Term.pp_print_term t)
      interpolizers;
    
    SMTSolver.push solver;
	  
    let names = List.map
      (fun t -> SMTExpr.ArgString
	(SMTSolver.assert_named_term_wr
           solver
           t))
      interpolizers
    in
    
    if SMTSolver.check_sat
      solver
    then
      raise Error
    else
      let interpolants =
	SMTSolver.get_interpolants
    	  solver
    	  names
      in

      SMTSolver.pop solver;

      (* let interpolants = List.map *)
      (* 	(Term.bump_state (Numeral.of_int (-1))) *)
      (* 	interpolants *)
      (* in *)
      
      Format.printf "@. Printing interpolants @.";
      List.iter
	(fun t -> Format.printf "@.interpolant: %a@." Term.pp_print_term t)
	interpolants;

      interpolants
  in
  
  (* ********************************************************************** *)
  (* Propagate                                                              *)
  (* ********************************************************************** *)
  
  (* Partition clauses into clauses to keep (those that are not
     relatively inductive) and those to propagate (those that
     are relatively inductive *)
  let partition_clauses abvar_map frame clauses =

    let rec partition keep prop undecided =
      match undecided with
      (* if there are still clauses to sort, sort them *)
      | c :: undecided' ->

	 (* check whether clause is inductive relative to frame *)
	 if isabsrelind abvar_map frame c
	 (* It is relatively inductive, so we should propagate it *)
	 then partition keep (c::prop) undecided'
	 (* It is not relatively inductive, so we should keep it *)
	 else partition (c::keep) prop undecided'

      (* if all clauses are sorted, we are done *)
	   
      | [] -> keep, prop
    in

    partition [] [] clauses

  in  
    
  (* Note: with difference encoding, have access to current frame and all frames above.*)
  
  (* Recursively propagates inductive clauses through the list.
     Returns a list of frames *)
  let rec propagate abvar_map frames_gt frames_lte =
    match frames_lte with
    (* When there are at least two successive frames, first recurse on the
       second and then propagate terms from the second to the first  *)
    | fi::fj::frames_ltt ->

       (* recursively propagate at the previous frame *)
       (match propagate abvar_map (fi::frames_gt) (fj::frames_ltt) with
	  
       (* find clauses that propagate and propagate them *)
       | fj'::frames_ltt' ->

	  (* split fj' into clauses to keep and to propagate*)
	  let keep, prop = partition_clauses
	    abvar_map
	    (List.concat (fj'::fi::frames_gt))
	    fj'
	  in

	  List.iter
	    (fun c ->
	      if (isabsrelind abvar_map (List.concat (fj'::fi::frames_gt)) c)
	      then
		(Format.printf
		  "@.Expected %a to not be relatively inductive@."
		  Term.pp_print_term
		  c;
		 raise Failure))
	    keep;
	  
	  Format.printf "@.Propagating frame %d to frame %d.@." (List.length frames_ltt') (List.length (fj'::frames_ltt'));
	  
	  Format.printf "@.  Keeping clauses:@.";
	  List.iter
	    (Format.printf "@.    %a@." Term.pp_print_term)
	    keep;
	  
	  Format.printf "@.  Propagating clauses:@.";
	  List.iter
	    (Format.printf "@.    %a@." Term.pp_print_term)
	    prop;
	    
	  (* check for fixed point *)
	  if List.length keep = 0 then
	    (Format.printf "@.Propagating all clauses from frame %d; fixed point reached. Printing inductive invariant:@." (List.length frames_ltt');
	     List.iter
	       (Format.printf "@. - i.i. term: %a@." Term.pp_print_term)
	       (unique_terms (prop@fi));

	     Format.printf "@.Abvar mapping:@.";
	     
	     List.iter
	       (fun (k,v) -> Format.printf "@.%a @.-----> MAPS TO %a@." Term.pp_print_term k Term.pp_print_term v)
	       (TermMap.bindings abvar_map);
	     

	     (* package the invariant - list of predicates preserved from one frame to the next - as conjunction *)
	     let invariant =
	       let inverse_abvar_map = invert abvar_map in
	       
	       Term.mk_and
		 (List.map
		    (Term.map
		       (fun _ subterm ->
			 if TermMap.mem subterm inverse_abvar_map
			 then TermMap.find subterm inverse_abvar_map
			 else subterm))
		    fi)
	     in
	    	     
	     (* raise with invariant consisting of list of predicates that were preserved from one frame to the next *)
	     raise (Success invariant));
	  
	  (unique_terms (prop @ fi)) :: keep :: frames_ltt'
	    
       | _ ->
	  Format.printf "@.Unreachable state in <propagate>@.";
	  raise Error )

    (* otherwise don't do anything*)
    | frame -> frame
  in
  
  (* ********************************************************************** *)
  (* Block                                                                  *)
  (* ********************************************************************** *)

  (* removes uneeded blocking clauses. May not return anything if no clause is needed
     such as due to recblocking in a lower frame *)
  let get_generalized_blocking_clause abvar_map bad_cube frames_gte frames_lt =
    
    (* Retrieve the lowest frame for satisfiability testing *)
    let f0 = List.concat (frames_gte @ frames_lt) in
    
    (* Generate list of literals that would each block bad_cube and are consistent 
       with the bottom frame and are not entailed by the bottom frame*)
    
    let candidate_literals = List.map
      Term.negate
      (Term.node_args_of_term bad_cube)
    in

    if (not (isSatisfiable abvar_map f0 (Term.mk_or candidate_literals)))
    then
      (Format.printf "@.Blocking clause not satisfiable@.";
       raise Failure);
    
    (* Include in generalized blocking clause only the literals that propagate 
       together relative to current frame *)    
    let rec generalize confirmed candidates =
      
      match confirmed, candidates with
      (* if there are no candidates or confirmed, return none *)
      | [],[] -> None

      (* if there is only one literal left and none of the others have been confirmed, just use the last one*)
      | [], c::[] -> Some c

      (* while there are still candidates, check whether they are necessary *)
      | _, c :: candidates' ->

	 (* the blocking clause without candidate c *)
	 let clause = Term.mk_or (candidates' @ confirmed) in

	 (* discard candidates that are not needed for the clause to be inductive or satisfiable or entailed*)
	 if ((isabsrelind abvar_map (List.concat frames_gte) clause)
	     (* && *)
	     (*   (isSatisfiable abvar_map f0 clause) *)
	     &&
	       (* =TODO= this is supposed to fix unsound examples - make sure it does not break things  *)
	       (isEntailed abvar_map f0 clause))
	 then generalize confirmed candidates'
	 else generalize (c::confirmed) candidates'

      (* once we have confirmed or discarded all candidates, return the blocking clause*)
      | _, [] -> Some (Term.mk_or confirmed)
    in

    generalize [] candidate_literals
  in	
  
  (* Returns list of frames leq the current frame 
     cex_path is a list with the most recent bad cube at the head
     it can serve as the path to a counterexample *)
  
  let rec recblock abvar_map cex_path_gte frames_gte frames_lt =

    let bad_cube = List.hd cex_path_gte in
    
    (* The current frame will be needed *)
    let fi = List.hd frames_gte in
    
    match frames_lt with
    (* If there are no frames below, we cannot block the cube, so we need to check the counterexample *)
    | [] -> raise (Counterexample cex_path_gte)
       
    (* If there are frames below, check whether there are any models where the blocking clause
       does not propagate *)
    | fj::frames_ltt ->

       (* Check whether the blocking clause is inductive relative to previous frame *)
       ( match absrelind
	   abvar_map
	   (List.concat (fj::frames_gte))
	   (Term.negate bad_cube)
	 with
	   
	 (* It is - we can add a generalization of it to the frame *)
	 | [] ->
	    Format.printf "@.Blocking clause (recblock) is inductive relative to frame %d@." (List.length frames_ltt);
	   (match get_generalized_blocking_clause
	       abvar_map
	       bad_cube
	       (fj::frames_gte)
	       frames_ltt
	    with
	   (* if a generalized clause was returned, add it to the current frame *)
	    | Some g ->
	       Format.printf "@. Cube to block = %a@." Term.pp_print_term bad_cube;
	      Format.printf "@. Generalized blocking clause = %a@." Term.pp_print_term g;
	     
	      (g::fi) :: frames_lt

	    (* should not be reachable *)
	    | None ->
	       Format.printf "@.Generalized blocking clause returned None @.";
	      raise Error)
		
	 (* It isn't - we'd better block the counterexample and try again *)    
	 | cti ->
	    let cex = Term.mk_and cti in
	    
	    Format.printf "@.Blocking clause (recblock) not inductive relative to frame %d; counterexample found@." (List.length frames_ltt);
	    Format.printf "@.Blocking clause = %a@." Term.pp_print_term (Term.negate bad_cube);
	    Format.printf "@.Counterexample = %a@." Term.pp_print_term cex;
	    
	    let frames_lt' = recblock
	      abvar_map
	      (cex::cex_path_gte)
	      (fj::frames_gte)
	      frames_ltt
	    in

	    recblock
	      abvar_map
	      cex_path_gte
	      frames_gte
	      frames_lt' );
  in

  (* Attempts to block all bad states. Returns the updated list of frames, followed by
     an updated abvar map and an updated list of predicates*)
  let rec block abvar_map frames_lte =
    
    match frames_lte with

    (* List of frames in descending order *)
    | fk :: frames_lt ->

       let abvars = List.map snd (TermMap.bindings abvar_map) in
       
      (* Fk ^ H ^ ~P' *)
       let terms_to_check = fk @ (get_hp abvar_map) @ [Term.negate prop'] in
       
       SMTSolver.check_sat_assuming_and_get_term_values
	 solver
	 
	(* SAT case - extract a cube and recblock it *)
	 (fun _ assignments ->

	   (* we want to add clauses so that this cube cannot occur *)
	   let bad_cube = Term.mk_and (get_term_list_from_term_values assignments) in

	   Format.printf "@.Beginning block of bad cube: %a@." Term.pp_print_term bad_cube;
	   
	  (* modify frames below to prevent the bad cube *)
	   let abvar_map', frames_lte' =
	     try abvar_map, (recblock abvar_map [bad_cube] [fk] frames_lt ) with

	    (* If recursive blocking fails, check to see if counterexample is spurious*)
	     | Counterexample cex_path ->
		Format.printf "@.Lowest frame reached (recblock) - this means failure@.";

	       (* Can we find a concrete path consistent with the counterexample? *)
	       (match simulate
		   (List.mapi
		      (fun i t -> Term.bump_state (Numeral.of_int i) t)
		      cex_path)
		   abvar_map;
		with
		  
		(* if we cannot find a path, do nothing. *)
		| None -> Format.printf "@.Counterexample is spurious.@."
		   
		(* if counterexample is concretizable, we are done. *)
		| Some cex_model -> raise (ConcreteCounterexample (cex_model,(List.length cex_path - 1))));
	       
	       (* Generate the interpolants from the counterexample and unbump them *)
	       let interpolants = List.mapi
		 (fun i t -> Term.bump_state (Numeral.of_int (-i)) t)
		 (generate_interpolants abvar_map cex_path)
	       in
	       
	       (* Filter out interpolants that are just 'true' or 'false' *)
	       let nontrivial_interpolants = List.filter
		 (fun t -> ((not (Term.equal t Term.t_true)) && (not (Term.equal t Term.t_false))))
		 interpolants
	       in

	      (* extract all atomic formulae from the interpolants for use as predicates*)
	       let atoms_of_interpolants = List.concat
		 (List.map
		    atoms_of_term
		    nontrivial_interpolants)
	       in

	       (* filter out atoms that are already predicates *)
	       let predicates = List.map
		 snd
		 (TermMap.bindings abvar_map)
	       in

	       
	       let novel_atoms = Term.TermSet.elements
		 (Term.TermSet.diff
		    (Term.TermSet.of_list atoms_of_interpolants)
		    (Term.TermSet.of_list predicates))
	       in

	       (* This ought not to happen *)
	       if List.length novel_atoms > 0
	       then Format.printf "@.Generated %d novel predicates from interpolants.@." (List.length novel_atoms)
	       else
		 (Format.printf "@.No new predicates generated!@.";
		  raise Error);
	       
	       (* Update the abvar map with abvars for new predicates *)
	       let abvar_map',new_abvars = update_abvar_map
		 abvar_map
		 novel_atoms
	       in
	       
	      (* declare the new abvars for every level up to the current one *)
	       List.iter
		 (declare_abstract_variables_at_offset solver new_abvars)
		 (List.mapi (fun i _ -> i) frames_lte);
	       
	       (*Update abvar map*)
	       abvar_map', frames_lte
	   in
	   
	   (* Let's try blocking again with the modified frames *)
	   block abvar_map' frames_lte')
	 
	 (* UNSAT case - don't need to do anything *)
	 (fun _ ->
	   Format.printf "@.Nothing found that needs blocking (block)@.";
	   abvar_map, frames_lte)
	 
	 (* CHECK SAT | Fk ^ H ^ ~'P *)
	 (List.map mk_and_assert_actlit terms_to_check)
	 
	 abvars
	 
    (* Block is always called at k > 0, so this is unreachable*)
    | _ ->
       Format.printf "@.Unreachable state in <block>@.";
      raise Error
	
  in
  
  (* ********************************************************************** *)
  (* Program Loop                                                           *)
  (* ********************************************************************** *)
  
  let rec ic3ia' abvar_map frames =
    
    (* (\* check invariants *\) *)
    (* checkInvariants abvar_map frames; *)
    
    (* eliminate redundant clauses *)
    Format.printf "@...........Consolidating@.";
    let frames = consolidate frames in
    
    (* Add a new frame and propagate forward the changes *)
    Format.printf "@...........Propagating@.";
    let frames = propagate
      abvar_map
      []
      ([]::frames)
    in
    print_frames frames;

    let k = List.length frames - 1 in

    (* get list of abvars to declare them in next frame  *)
    let abvars = List.map snd (TermMap.bindings abvar_map) in

    (* When we propagate frames forward, we will also declare all our concrete 
       variables at those offsets for use in simulation *)    
    if (List.length frames > 2) then
      (declare_abstract_variables_at_offset solver abvars k;
       declare_variables_at_offset k;
       declare_clone_variables_at_offset k);
    
    (* Block bad states and try to simulate paths to safety violation when you fail *)
    Format.printf "@...........Blocking@.";
    let abvar_map, frames = block
      abvar_map
      frames
    in
    print_frames frames;

    ic3ia' abvar_map frames
  in

  ic3ia' abvar_map [[init']]
  
(* ====================================================================== *)
(* Main                                                                   *)
(* ====================================================================== *)

let main input_sys aparam trans_sys =
  
  let logic = TransSys.get_logic trans_sys in

  let solver =
    SMTSolver.create_instance
      ~produce_assignments:true
      ~produce_cores:true
      ~produce_interpolants:true
      logic
      `Z3_SMTLIB
  in

  (* Declares uninterpreted function symbols *)
  TransSys.define_and_declare_of_bounds
    trans_sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    (Numeral.zero)
    (Numeral.of_int 1);

  (* Returns a term representing the initiation condition *)
  let init = TransSys.init_of_bound None trans_sys Numeral.zero in
  let trans = TransSys.trans_of_bound None trans_sys Numeral.one in
  (* Given a list of properties, we will run IC3ia for each one seperately.*)
  (* note that each property is given as a pair, where the first member is an identifying string. *)
  let props = TransSys.props_list_of_bound trans_sys Numeral.zero in
  
  List.iter
    (fun prop ->
      try ic3ia
	    solver
	    input_sys
	    aparam
	    trans_sys
	    init
	    trans
	    prop
      with

      (* if ic3ia succeeds, broadcast a certificate from the inductive clause *)
      | Success invariant ->
	 let cert = 1, Term.mk_and [invariant;snd prop] in
	 
	 Event.prop_status
	   (Property.PropInvariant cert)
	   input_sys
	   aparam
	   trans_sys
	   (fst prop)

      | ConcreteCounterexample (cex_model,k) ->

	 let path = Model.path_from_model
	   (TransSys.state_vars trans_sys)
	   cex_model
	   (Numeral.of_int k)
	 in
	 
	 let list = Model.path_to_list path in
	 
	 Event.prop_status
	   (Property.PropFalse list)
	   input_sys
	   aparam
	   trans_sys
	   (fst prop))
	   
    props
    
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End:
*)
