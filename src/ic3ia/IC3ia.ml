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
exception Success
exception Failure
exception Error
  
(* Cleanup before exit *)
let on_exit _ = ()

(* Checks whether given clause is inductive relative to the frame *)
(* let absRelInd solver frame trans_sys clause associations = *)
    
let ic3ia solver trans_sys init trans prop =

  let predicates = [init;prop] in  
  let absvarcounter = ref 0 in

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
    Term.mk_and (List.map (fun t -> mk_clone_eq t) predicates)
  in

  (* Assert the cloned transition function*)
  SMTSolver.assert_term solver (clone_term trans);
  Format.printf "CLONED TRANSITION SYSTEM:@.%a@." Term.pp_print_term (clone_term trans);

  (* ********************************************************************** *)
  (* Abstracted variables                                                   *)
  (* ********************************************************************** *)

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
    
  (* Extracts a map from boolean atoms to abstract variables given a list of predicates *)
  let get_abvar_map predicates =

    let atoms_of_term term =
      Term.eval_t
	(fun subterm atom_lists ->
	  if
	    Term.is_atom (Term.construct subterm)
	  then
	    (Term.construct subterm)::(List.concat atom_lists)
	  else
	    List.concat atom_lists)
	term
    in
    
    let all_atoms =
	(* accumulate all atoms of the predicates *)
      (List.fold_left 
	 (fun acc t ->
	   (atoms_of_term t) @ acc)
	 []
	 predicates)
    in
    
    let all_unique_atoms =
      Term.TermSet.elements (Term.TermSet.of_list all_atoms)
    in
    
     (* Return a map from terms to their abstract variables *)
    List.fold_left
      (fun acc atom ->
	TermMap.add atom (mk_new_abvar atom) acc)
      TermMap.empty
      all_unique_atoms
  in

  let abvar_map = get_abvar_map predicates in

  (* Traverse the term and replace where appropriate with abstract variables *)  
  let convert_to_abstract_term term =
    Term.map
      (fun _ subterm -> if TermMap.mem subterm abvar_map then TermMap.find subterm abvar_map else subterm)
      term
  in

  (* list of all abstract variables *)
  let abvars =
    List.map
      (fun (_,abv) -> abv)
      (TermMap.bindings abvar_map)
  in

  let declare_abstract_variables_at_offset n =
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
  in

  declare_abstract_variables_at_offset 0;
  declare_abstract_variables_at_offset 1;
  
  (* list of association terms between concrete and abstract variables *)
  let hp =
    List.map
      (fun (con,abv) -> Term.mk_eq [abv;con])
      (TermMap.bindings abvar_map)
  in

  (* abstracted terms *)
  let init' = convert_to_abstract_term init in
  let prop' = convert_to_abstract_term prop in

  Format.printf "@.ABSTRACT VARIABLES:";
  List.iter
    (fun trm -> Format.printf "@.%a@." Term.pp_print_term trm)
    abvars;

  Format.printf "@.ASSOCIATIONS:";
  List.iter
    (fun trm -> Format.printf "@.%a@." Term.pp_print_term trm)
    hp;

  Format.printf "@.PREDICATES:";
  List.iter
    (fun trm -> Format.printf "@.%a@." Term.pp_print_term trm)
    [init';prop'];

  Format.printf "@.CLONED PREDICATES:";
  List.iter
    (fun trm -> Format.printf "@.%a@." Term.pp_print_term (mk_clone_eq trm))
    [init;prop];

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
	  Term.mk_not term)
      assignments
  in
  
  (* TODO: Should return counterexample *)


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
       (fun trm -> mk_and_assert_actlit trm)
       ( hp @ init' :: [Term.mk_not prop']))

    (*  Check values of the things we fed in *)
    abvars;
  (* TODO: Write utility function to handle SAT checking *)

  (* For extracting a clause from the term values given by check_sat_assuming_and_get_term_values
     Note that the clause is the negation of the term values *)
  
  (* PAPER LINE 3*)
  (* Initialize frames *)
  (* Question: Do we need to include tinit in the initial states?*)
  let frames = [[];[init']] in

  (* ********************************************************************** *)
  (* Utility                                                                *)
  (* ********************************************************************** *)

  (* Print frames for debugging *)
  let print_frames frames =
    let frames = List.rev frames in
    let framecounter = ref 0 in
    List.iter
      (fun f ->
	Format.printf "@.Frame #%d@." !framecounter;
	incr framecounter;
	List.iter
	  (fun t -> Format.printf "@. Term: %a@." Term.pp_print_term t)
	  f)
      frames
  in
    
  (* Checks whether clause is inductive relative to frame, where frame 
     has been converted from being difference encoded to including all clauses 
     of all frames sbove and including the current one
     
     If the clause is inductive, an empty list will be returned.

     If the clause is not inductive, a counterexample consisting of a list of 
     value assignments encoded as terms will be returned. *)
  
  let absRelInd frame clause =
    SMTSolver.check_sat_assuming_and_get_term_values
      solver

      (* SAT case - returns a list of terms that satisfies the predicate *)
      (fun _ assignments ->
	let cti' = get_term_list_from_term_values assignments in
	cti')
	  

      (* UNSAT case - returns an empty list *)
      (fun _ -> [])
      
      (* Check satisfiability of F ^ c ^ hp ^ eq ^ T(clone) ^ !c' *)
      (List.map
	 (fun trm -> mk_and_assert_actlit trm)
	 (let eqP = get_eqP predicates in (* may need to allow updates to predicates*)
	  let bump = Term.bump_state Numeral.one in
	  let hp = Term.mk_and hp in
	  frame @
	    [clause;
	     hp;
	     bump hp;
	     eqP;
	     bump eqP;
	     (Term.negate (bump clause))]))
      abvars
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
  let simulate abstract_path =
    let k = List.length abstract_path - 1 in
    
    let term_list = 
      abstract_path
      @(copy_and_bump_term (k-1) trans)
      @(List.concat (List.map (copy_and_bump_term k) hp))
    (*      @[Term.bump_state (Numeral.of_int k) (Term.negate prop)]*)
    in

    SMTSolver.check_sat_assuming
      solver
      
      (* SAT case - returns a list of terms that satisfies the predicate *)
      (fun _ -> Format.printf "@.Abstract path was concretizable@.")
      
      
      (* UNSAT case - returns an empty list *)
      (fun _ -> Format.printf "@.Abstract path could not be concretized - spurious counterexample@.")
      
      (* Check satisfiability of F ^ c ^ hp ^ eq ^ T(clone) ^ !c' *)
      (List.map
	 (fun trm -> mk_and_assert_actlit trm)
	 term_list);	
  in
  

  
  (* ********************************************************************** *)
  (* Block                                                                  *)
  (* ********************************************************************** *)

  (* Returns list of frames leq the current frame 
     cex_path is a list with the most recent bad cube at the head
     it can serve as the path to a counterexample
  *)
  let rec recblock cex_path frames_geq frames_lt =

    let bad_cube = List.hd cex_path in
    
    (* First, create a clause that negates the bad cube (which itself is encoded as a list *)
    let blocking_clause =
      Term.mk_or
	(List.map
	   (fun t -> Term.negate t)
	   bad_cube)
    in
    
    (* The current frame will be needed *)
    let fi = List.hd frames_geq in

    let make_blocking_clause cti =
      Term.mk_or
	(List.map
	   (fun t -> Term.negate t)
	   cti)
    in

    
    (* Takes as input a non-difference encoded frame bad cube (list of terms) and creates a blocking clause while
       removing terms unnecessary to block the bad cube.
       To be used after un-generalized clause has been made absrelind. *)
    let generalize_blocking_clause frame bad_cube =
      (* Determines which terms are needed to block the bad set of terms (second input) 
	 Returns a blocking clause. *)
      let rec generalize confirmed = function
	(* No terms left to confirm, so just return a blocking clause made from the confirmed terms*)
	| [] -> make_blocking_clause confirmed
	(* Check if blocking clause without head is absrelind; remove head if it is *)
	| hd::tl -> match absRelInd frame (make_blocking_clause (tl@confirmed)) with
	  (* Clearly the head is not needed, so remove it *)
	  | [] -> generalize confirmed tl
	  (* We need the head; confirm it *)
	  | _ -> generalize (hd::confirmed) tl
      in
      generalize [] bad_cube
    in
    
	   
    match frames_lt with
    (* If there are no frames below, we cannot block the cube, and have failed. *)
    | [] ->
       Format.printf "@.Lowest frame reached (recblock) - this means failure@.";
      Format.printf "@.Counterexample:@.";
      List.iteri
	(fun i t -> Format.printf "@.CTI term: %a@." Term.pp_print_term (Term.bump_state (Numeral.of_int i) t))
	(List.map (fun t -> Term.mk_and t) cex_path);
      simulate
	(List.mapi
	   (fun i t -> Term.bump_state (Numeral.of_int i) t)
	   (List.map (fun t -> Term.mk_and t) cex_path));
       raise Failure (*We probably should provide some info on the counterexample here, or else handle concretization in this function *)

    (* fj is the frame right below the current frame, the (i-1)th frame *)
    | fj::fb ->

       Format.printf "@.Frames above: %d@." (List.length (fj::frames_geq));
       (* Check whether the blocking clause is relatively inductive *)
       ( match absRelInd (List.concat (fj::frames_geq)) blocking_clause with
	 
       (* No counterexample, so it is relatively inductive and we can add it to the current frame 
	    TODO: generalize the blocking clause *)
       | [] ->
	 Format.printf "@.Blocking clause (recblock) is inductive relative to frame %d@." (List.length fb);
	  (* Format.printf "@.New Generalization of %a:@." Term.pp_print_term (make_blocking_clause bad_cube); *)
	 let g = generalize_blocking_clause (List.concat (fj::frames_geq)) bad_cube in

	 
	 Format.printf "@. Cube to block = %a@." Term.pp_print_term (Term.mk_and bad_cube);
	 Format.printf "@. Generalized blocking clause = %a@." Term.pp_print_term g;
	 print_frames ((g::fi)::frames_lt);
	 
	 (g::fi)::frames_lt
	  
       (* Uh-oh - we'd better block the counterexample and try again*)
	  
       | cti ->
	  Format.printf "@.Blocking clause (recblock) not inductive relative to frame %d; counterexample found@." (List.length fb);
	 Format.printf "@.Cube to block = %a@." Term.pp_print_term (Term.mk_and bad_cube);
	 Format.printf "@.Blocking clause = %a@." Term.pp_print_term blocking_clause;
	 Format.printf "@.Counterexample = %a@." Term.pp_print_term (Term.mk_and cti);
	 let frames_lt' = recblock (cti::cex_path) (fj::frames_geq) fb in
	 recblock cex_path frames_geq frames_lt'); (* block cti *) (* what if bad_cube = cti? *)
  in

  let rec block = function
    | [] -> raise Error (* Actually, this should not happen. Should raise some other error *)
    | fk :: frames_below ->
       (* Check if Fk ^ H |= 'P, recblock counterexamples *)
       SMTSolver.check_sat_assuming_and_get_term_values
	 solver
	 
	 (* SAT case - extract a cube and recblock it *)
	 (fun _ assignments ->
	   (* print_frames (fk::frames_below); *)

	   (* Format.printf "@.Extracted a cube (block), will now try to recblock it"; *)

	   (* Represent cube as a list of terms *)
	   let bad_cube = get_term_list_from_term_values assignments in
	   Format.printf "@.We found a bad cube while blocking frame %d. Better recblock it. Cube: %a@."
	     (List.length frames_below)
	     Term.pp_print_term (Term.mk_and bad_cube);
	   (* Modify frames below to prevent the bad cube  *)
	   let frames' = recblock [bad_cube] [fk] frames_below in

	   (* TODO: Handle counterexamples (failure case), concretizing when needed*)
	   (* Let's try blocking again with the modified frames *)
	   block frames')
	 
	 (* UNSAT case - don't need to do anything, so just continue with unmodified frames *)
	 (fun _ ->
	   Format.printf "@.Nothing found that needs blocking (block)@.";
	   fk::frames_below)

	 (List.map
	    (fun trm -> mk_and_assert_actlit trm)
	    ( fk @ hp @ [Term.negate prop']))

	 abvars
  in
  
  (* ********************************************************************** *)
  (* Propagate                                                              *)
  (* ********************************************************************** *)

  (* partitions clauses into clauses to keep and clauses to propagate based
     on whether they are absrelind or not*)
  let partition_absrelind clauses frame_nd =
    Format.printf "@.Partitioning the following clauses:@.";
    (List.iter
       (fun t -> Format.printf "@.Clause %a@." Term.pp_print_term t)
       clauses);
    
    let rec partition maybe_prop keep =
      Format.printf "@.--recursively partitioning %d clauses@." (List.length maybe_prop + List.length keep);
      SMTSolver.check_sat_assuming_and_get_term_values
	solver
	
	  (* SAT case - any clause that is false should not remain a
	     candidate for propagation. Recurse on what remains. *)
	(fun _ assignments ->
	  let maybe_prop_pair, keep_pair =
	    (List.partition
	       (fun (term, value) -> Term.bool_of_term value)
	       assignments)
	  in
	  
	  let unzip_and_unbump = List.map (fun p -> Term.bump_state (Numeral.of_int (-1)) (fst p)) in
	  
	  partition
	    (unzip_and_unbump maybe_prop_pair)
	    ((unzip_and_unbump keep_pair)@keep))	 
	
	  (* UNSAT case - all clauses propagate and we are done filtering! *)
	(fun _ ->
	  Format.printf "@.Keeping clauses:@.";
	  List.iter
	    (fun t -> Format.printf "@.Clause %a@." Term.pp_print_term t)
	    keep;
	  
	  Format.printf "@.Propagating clauses:@.";
	  List.iter
	    (fun t -> Format.printf "@.Clause %a@." Term.pp_print_term t)
	    maybe_prop;
	    (* Format.printf "@.UNSAT - we are done@."; *)
	  (keep, maybe_prop))
	
	  (* Check satisfiability of F ^ c ^ hp ^ eq ^ T(clone) ^ !c' *)
	(List.map
	   (fun trm -> mk_and_assert_actlit trm)
	   (let eqP = get_eqP predicates in (* may need to allow updates to predicates*)
	    let bump = Term.bump_state Numeral.one in
	    let hp = Term.mk_and hp in
	    let clause_conj = Term.mk_and maybe_prop in
	    frame_nd @
		[clause_conj;
		 hp;
		 bump hp;
		 eqP;
		 bump eqP;
		 (Term.mk_not (bump clause_conj))]))
	
	  (* We care about the values of terms in maybe_prop' *)
	(List.map (Term.bump_state Numeral.one) maybe_prop)
    in
    partition clauses []
  in	
  
  (* Note: with difference encoding, have access to current frame and all frames above.*)
  
  (* Recursively propagates inductive clauses through the list.
     frames_gt is given in ascending order, with fk last*)
  let rec propagate frames_gt = function
    (* When there are at least two successive frames, first recurse on the
       second and then propagate terms from the second to the first  *)
    | fi::fj::frames_lt ->
       (* Format.printf "@.Entering partition@."; *)
       (match propagate (fi::frames_gt) (fj::frames_lt) with
       (* We have reached a fixed point *)
       | []::_ ->
	  (* Format.printf "@.Fixed point@."; *)
	  raise Success
       (* Else, find clauses that propagate and propagate them *)
       | fj'::frames_lt' ->
	  (* Format.printf "@.Partitioning@."; *)
	  (* split fj' into clauses to keep and to propagate*)
	  let keep, prop = partition_absrelind fj' (List.concat (fi::frames_gt)) in
	  
	  (prop@fi)::(keep)::frames_lt'
       | [] -> raise Error ) (* Should be an unreachable state; need to raise a different error *)
    (* otherwise don't do anything*)
    | frame -> frame
  in
    
  (* ********************************************************************** *)
  (* Program Loop                                                           *)
  (* ********************************************************************** *)
  
  let rec ic3ia' frames =
    let k = List.length frames - 1 in

    (* Block bad states and try to simulate paths to safety violation when you fail *)
    Format.printf "@.Blocking@.";
    let frames = block frames in
    print_frames frames;

    (* Propagate forward the changes *)
    Format.printf "@.Propagating@.";
    let frames = propagate [] ([]::frames) in
    print_frames frames;

    (* When we propagate frames forward, we will also declare all our concrete 
       variables at those offsets for use in simulation *)
    if (List.length frames > 2) then
      (TransSys.define_and_declare_of_bounds
	 trans_sys
	 (SMTSolver.define_fun solver)
	 (SMTSolver.declare_fun solver)
	 (SMTSolver.declare_sort solver)
	 (Numeral.of_int (k + 1))
	 (Numeral.of_int (k + 1));
       declare_abstract_variables_at_offset (k+1);
       declare_clone_variables_at_offset (k+1));
    
    ic3ia' frames
  in

  ic3ia' frames
  (*try ic3ia' frames with
  | Success -> Format.printf "@.Property invariant"
  | Failure -> Format.printf "@.Property not invariant"
  | _ -> ()
  *)
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
    Numeral.zero
    (Numeral.of_int 1);

  List.iter
    (fun v -> Format.printf "Trans init':@.%a@." Var.pp_print_var v)
    (TransSys.init_formals trans_sys);
  
    Format.printf "TRANS SYSTEM:%a@." TransSys.pp_print_trans_sys trans_sys;
  (*TODO: Need to modify so that this extracts abstract variables from subsystems too.
    Currently, it only considers terms from the top node.
  *)
  (* Returns a term representing the initiation condition *)
  let init = TransSys.init_of_bound None trans_sys Numeral.zero in
  let trans = TransSys.trans_of_bound None trans_sys Numeral.one in
  (* Given a list of properties, we will run IC3ia for each one seperately.*)
  let props = List.map
    (fun (s,t) -> t)
    (TransSys.props_list_of_bound trans_sys Numeral.zero)
  in 

  Format.printf "TRANSITION SYSTEM:@.%a@." Term.pp_print_term trans;
  
  List.iter
    (fun prop -> ic3ia solver trans_sys init trans prop)
    props;
  
  ()

    
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End:
*)
