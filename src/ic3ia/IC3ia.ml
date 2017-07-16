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
   Frames may be difference encoded. Variables referring to difference
  encoded frames will be prefixed by d (dframe), while those representing
  the full body of a frame will simply be referred to as frame

  lt,geq,gt, etc. will be used to indicate a list of frames relative
  to the current frame. For example, dframe-lt would be a list of all
  frames with indices less than the current frame, excluding the current
  frame. The order of frames in such a list will always have those closest
  to the current frame at the head of the list.
*)


module A = Actlit
module TermMap = Map.Make(Term)
  
(* Define exceptions to break out of loops *)
exception Success of Term.t list
exception Failure
exception Error
exception Counterexample of Term.t list

  
(* Cleanup before exit *)
let on_exit _ = ()

(* ********************************************************************** *)
(* Utility functions for terms                                            *)
(* ********************************************************************** *)
  
let atoms_of_term term =
  Term.eval_t
    (fun subterm atom_lists ->
      if Term.is_atom (Term.construct subterm)
      then (Term.construct subterm)::(List.concat atom_lists)
      else List.concat atom_lists)
    term

(* Removes duplicates from list of terms *)
let unique_terms term_list =
  (Term.TermSet.elements (Term.TermSet.of_list term_list))
    
(* ********************************************************************** *)
(* Abstracted variables                                                   *)
(* ********************************************************************** *)

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

    (* We need to give this abstract variable a unique name *)
    let abvar_name =
      Format.asprintf "abv%d" !absvarcounter
    in
    incr absvarcounter;
      
    (* We will create a new state variable (or use an existing one) to represent the abvar *)
    let abvar_statevar =
      StateVar.mk_state_var
	abvar_name
	abvar_scope
	Type.t_bool
    in

    (* We also need to know the offset. Since abvars are used only for terms over one offset,
       we may safely assume that an arbitrary variable in the term is representative of the offset*)
    let abvar_offset =
      let vars = Term.vars_of_term term in
      Var.offset_of_state_var_instance (Var.VarSet.choose vars)
    in

    (* Now create an instance of the abvar at the given offset *)
    
    let abvar_instance = Var.mk_state_var_instance abvar_statevar abvar_offset in
    
    (* Return the term consisting of the new var *)
    Term.mk_var abvar_instance
  in

  (*  We only want new and unique predicates *)
  let new_predicates = List.filter
    (fun t -> not (TermMap.mem t old_map))
    (Term.TermSet.elements (Term.TermSet.of_list new_predicates))
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

let declare_abstract_variables_at_offset solver abvars n =
  Var.declare_vars
    (SMTSolver.declare_fun solver)
    (let set_of_variables =
       List.fold_left
	 (fun acc term -> Var.VarSet.union acc (Term.vars_of_term term))
	 Var.VarSet.empty
	 abvars
     in

     let list_of_variables = Var.VarSet.elements set_of_variables in

     List.map
       (fun v -> Var.set_offset_of_state_var_instance v (Numeral.of_int n))
       list_of_variables)

let get_hp abvar_map =
  List.map
    (fun (k,v) -> Term.mk_eq [k;v])
    (TermMap.bindings abvar_map)
    
let ic3ia solver trans_sys init trans prop =

  let predicates = [init;prop] in  
  
  (* ********************************************************************** *)
  (* Cloned variables                                                       *)
  (* ********************************************************************** *)
  
  (* Creates a clone of an uncloned term using provided map *)
  let clone_term map term =
    let lookup term = StateVar.StateVarMap.find term map in
    Term.map_state_vars lookup term
  in
  
  (* Function to clone and declare all variables in given predicates and return a map *)
  let get_clone_map predicates =
    
    (* Get set containing all state variables in predicates *)
    let statevars =
      List.fold_left
	(fun acc p ->
	  StateVar.StateVarSet.union (Term.state_vars_of_term p) acc)
	StateVar.StateVarSet.empty
	predicates
    in
    
    (* fold over statevars to construct map to new statevars *)
    let clone_map = 
      StateVar.StateVarSet.fold
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

    let set_of_variables = 
      List.fold_left
	(fun acc term -> Var.VarSet.union acc (Term.vars_of_term term))
	Var.VarSet.empty
	(List.map (clone_term clone_map) (predicates))
    in
    
    Var.declare_constant_vars
      (SMTSolver.declare_fun solver)
      (Var.VarSet.elements (Var.VarSet.filter Var.is_const_state_var set_of_variables));
    
    Var.declare_vars
      (SMTSolver.declare_fun solver)
      (Var.VarSet.elements (Var.VarSet.filter Var.is_state_var_instance set_of_variables));
    
    clone_map
  in
  
  (* Repeat for each term in predicates and in the transition function *)
  let clone_map = get_clone_map (trans::predicates) in
  let clone_term = clone_term clone_map in

  let declare_clone_variables_at_offset n =
    let clone_vars =
      let set_of_variables = 
	List.fold_left
	  (fun acc term -> Var.VarSet.union acc (Term.vars_of_term term))
	  Var.VarSet.empty
	  (List.map clone_term predicates)
      in
      Var.VarSet.elements set_of_variables
    in

    let offset_clone_vars =
      List.map
	(fun v -> Var.set_offset_of_state_var_instance v (Numeral.of_int n))
	clone_vars
    in

    (* QUESTION: Do we need to declare offset constant vars as well? *)
    Var.declare_vars
      (SMTSolver.declare_fun solver)
      offset_clone_vars;
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

  (* Traverse the term and replace where appropriate with abstract variables *)  
  (* let convert_to_abstract_term term = *)
  (*   Term.map *)
  (*     (fun _ subterm -> if TermMap.mem subterm abvar_map then TermMap.find subterm abvar_map else subterm) *)
  (*     term *)
  (* in *)

  declare_abstract_variables_at_offset solver abvars 0;
  declare_abstract_variables_at_offset solver abvars 1;
  
  (* list of association terms between concrete and abstract variables *)
  let hp = get_hp abvar_map in

  (* abstracted terms *)
  let init' = TermMap.find init abvar_map in
  let prop' = TermMap.find prop abvar_map in

  let mk_and_assert_actlit trm =
    let act = A.fresh_actlit () in
    SMTSolver.declare_fun solver act;
    let acttrm = A.term_of_actlit act in
    let actimpl = Term.mk_implies [acttrm;trm] in
    SMTSolver.assert_term solver actimpl;
    acttrm
  in

  (* Takes the given assignments and produces a list of terms *)
  let get_term_list_from_term_values assignments =
    List.map
      (fun (term, value) ->
	if
	  Term.bool_of_term value
	then
	  term
	else
	  Term.negate term)
      assignments
  in
  
  (* Check whether 'I ^ H |= 'P *)
  SMTSolver.check_sat_assuming_and_get_term_values
    solver
    
    (* SAT case ('P not entailed) *)
    (fun _ assignments ->
      Format.printf "@.Property invalid in initial state@.";
      (*Format.printf "@.Values for model:@.";
      List.iter	
	(fun (term, assignment) -> (Format.printf "@.%a %a@." Term.pp_print_term term Term.pp_print_term assignment) )
	assignments;*)
      raise Failure)
    
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

  (* Checks whether the clause is consistent with the frame *)
  
  let isconsistent abvar_map frame clause = 

    (* F ^ hp ^ c *)
    let terms_to_check =
      let hp = Term.mk_and (get_hp abvar_map) in
      clause :: hp :: frame
    in
    
    SMTSolver.check_sat_assuming_tf
      solver
      (List.map mk_and_assert_actlit terms_to_check)

  in

  (* Checks whether current frame entails clause, i.e. does clause tell us anything new? *)
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
	    
	   
	   
  (* removes uneeded blocking clauses. May not return anything if no clause is needed
     such as due to recblocking in a lower frame *)
  let get_generalized_blocking_clause abvar_map bad_cube frames_gte frames_lt =

    (* Retrieve the lowest frame *)
    let f0 = List.concat (frames_gte @ frames_lt) in
    
    (* Generate list of literals that would each block bad_cube and are consistent 
       with the bottom frame and are not entailed by the bottom frame*)
    let candidate_literals = List.filter
      (isconsistent abvar_map f0)
      (List.map Term.negate (Term.node_args_of_term bad_cube))
    in

  (* Include in generalized blocking clause only the literals that propagate 
     together relative to current frame *)
    
    let rec generalize confirmed candidates =
      
      match confirmed, candidates with
      (* if there are no candidates or confirmed, return none *)
      | [],[] -> None
      (* if there is only one literal left and the rest have been confirmed, just use the last one*)
      | [], c::[] -> Some c

      (* while there are still candidates, check whether they are necessary *)
      | _, c :: candidates' ->
	 
	 if isabsrelind
	   abvar_map
	   (List.concat frames_gte)
	   (Term.mk_or (candidates' @ confirmed))

	 (* discard candidates that are not needed for the clause to be inductive*)
	 then generalize confirmed candidates'
	 else generalize (c::confirmed) candidates'

      (* once we have confirmed or discarded all candidates, return the blocking clause*)
      | _, [] -> Some (Term.mk_or confirmed)
    in

    generalize [] candidate_literals
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
    
    let term_list = 
      abstract_path
      @(copy_and_bump_term (k-1) trans)
      @(List.concat (List.map (copy_and_bump_term k) (get_hp abvar_map)))
    in

    (* Check satisfiability of F ^ c ^ hp ^ eq ^ T(clone) ^ !c' *)
    SMTSolver.check_sat_assuming_tf
      solver
      (List.map mk_and_assert_actlit term_list);	
  in

  (* Generates interpolants. Abstract path must be unbumped in ascending order of offset.*)
  let generate_interpolants abvar_map abstract_path =
    let interpolizers = 

      (* Converts the abvar map into its inverse. Justified because we know that it is
	 a bijective map by construction.*)
      let rev_abvar_map =
	List.fold_left
  	  (fun acc (key,value) -> TermMap.add value key acc)
  	  TermMap.empty
	  (TermMap.bindings abvar_map)
      in

      (* Replaces all abstract variables in trm with their concrete atomic forms *)
      let concretize_term trm =
	
	Term.map
	  (fun _ t ->
	    (* Format.printf "@.debug - %a@." Term.pp_print_term t ; *)
	    if TermMap.mem t rev_abvar_map
	    then TermMap.find t rev_abvar_map
	    else t)
	  trm
	   
      in      
      
      (* Creates the sequence of formulas that will be used to generate interpolants.*)
      List.mapi
	(fun i s ->
	  match i with
	  | 0 -> concretize_term s
	  | n ->
	     Term.mk_and [
	       Term.bump_state (Numeral.of_int (n-1)) trans;
	       Term.bump_state (Numeral.of_int n) (concretize_term s)])
	abstract_path
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
	     (* return invariant consisting of list of predicates that were preserved from one frame to the next *)
	     
	     raise (Success fi));
	  
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
	       
	   (* if no clause was returned, we must have recblocked it already. 
	      Therefore propagate changes from lower frames but avoid success exception. *)
	   | None -> propagate
	      abvar_map
	      (List.tl frames_gte)
	      (fi::frames_lt))
	     
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
       
      (* Fk ^ H ^ ~'P *)
       let terms_to_check = fk @ (get_hp abvar_map) @ [Term.negate prop'] in
       
       SMTSolver.check_sat_assuming_and_get_term_values
	 solver
	 
	(* SAT case - extract a cube and recblock it *)
	 (fun _ assignments ->
	   
	  (* we want to add clauses so that this cube cannot occur *)
	   let bad_cube = Term.mk_and (get_term_list_from_term_values assignments) in

	  (* modify frames below to prevent the bad cube *)
	   let abvar_map', frames_lte' =
	     try abvar_map, (recblock abvar_map [bad_cube] [fk] frames_lt ) with

	    (* If recursive blocking fails, check to see if counterexample is spurious*)
	     | Counterexample cex_path ->
		Format.printf "@.Lowest frame reached (recblock) - this means failure@.";

	      (* If counterexample is concretizable then we are done *)
	       if
		 simulate
		   (List.mapi
		      (fun i t -> Term.bump_state (Numeral.of_int i) t)
		      cex_path)
		   abvar_map;
	       then
		 (Format.printf "@.Concretizable counterexample found.@.";
		  raise Failure);

	      (* Generate the interpolants from the counterexample and unbump them *)
	       let interpolants = List.mapi
		 (fun i t -> Term.bump_state (Numeral.of_int (-i)) t)
		 (generate_interpolants abvar_map cex_path)
	       in
	       
	      (* Filter out interpolants that are just 'true'
		 TODO: Raise error if interpolants are 'false' *)
	       let nontrivial_interpolants = List.filter
		 (fun t -> not (Term.equal t Term.t_true))
		 interpolants
	       in

	      (* extract all atomic formulae from the interpolants for use as predicates*)
	       let atoms_of_interpolants = List.concat
		 (List.map
		    atoms_of_term
		    nontrivial_interpolants)
	       in
	       
	      (* Update the abvar map with abvars for new predicates *)
	       let abvar_map',new_abvars = update_abvar_map
		 abvar_map
		 atoms_of_interpolants
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
      (TransSys.define_and_declare_of_bounds
	 trans_sys
	 (SMTSolver.define_fun solver)
	 (SMTSolver.declare_fun solver)
	 (SMTSolver.declare_sort solver)
	 (Numeral.of_int k)
	 (Numeral.of_int k);
       declare_abstract_variables_at_offset solver abvars k;
       declare_clone_variables_at_offset k);
    
    (* Block bad states and try to simulate paths to safety violation when you fail *)
    Format.printf "@...........Blocking@.";
    let abvar_map, frames =block
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
  let props = List.map
    snd
    (TransSys.props_list_of_bound trans_sys Numeral.zero)
  in 
  
  List.iter
    (fun prop -> ic3ia solver trans_sys init trans prop)
    props
    
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End:
*)
