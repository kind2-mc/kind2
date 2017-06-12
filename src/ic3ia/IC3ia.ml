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

module A = Actlit
module TermMap = Map.Make(Term)
  
(* Define exceptions to break out of loops *)
exception Success
exception Failure
  
(* Cleanup before exit *)
let on_exit _ = ()

(* Checks whether given clause is inductive relative to the frame *)
(* let absRelInd solver frame trans_sys clause associations = *)
    
let ic3ia solver init trans prop =

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
  
      (*
    
    (*********************************************************)
    
    (* use the counter to create an unused name *)
    let symbol_name = Format.asprintf "_abvar_%d" !absvarcounter in
    let uf_symbol = (UfSymbol.mk_uf_symbol symbol_name [] Type.t_bool) in
    incr absvarcounter;
    
    (* declare the new symbol in the solver *)
    SMTSolver.declare_fun solver uf_symbol;
    
    (* Return the term consisting of the new symbol *)
    Term.mk_uf uf_symbol []
	in*)
  
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

  (* Declare all abstract variables in the solver *)
  Var.declare_vars
    (SMTSolver.declare_fun solver)
    (let set_of_variables = 
       List.fold_left
	 (fun acc term -> Var.VarSet.union acc (Term.vars_of_term term))
	 Var.VarSet.empty
	 abvars
     in

     let list_of_variables = Var.VarSet.elements set_of_variables in

     let bumped_list_of_variables =
       List.map
	 (fun v -> Var.bump_offset_of_state_var_instance v Numeral.one)
	 list_of_variables
     in

     list_of_variables @ bumped_list_of_variables);
  
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
  let absRelInd frame clause =
    SMTSolver.check_sat_assuming_and_get_term_values
      solver

      (* SAT case - returns a list of terms that satisfies the predicate *)
      (fun _ assignments ->
	Format.printf "@.Clause is not inductive relative to frame; counterexample found@.";
	get_term_list_from_term_values assignments)
    

      (* UNSAT case - returns an empty list *)
      (fun _ ->
	Format.printf "@.Clause is inductive relative to frame@.";
	[])
      
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
	     (Term.mk_not (bump clause))]))
      abvars
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
  let frames = [[init']] in
  
  let rec recblock bad_cube frames_below =
    (* First, create a clause that negates the bad cube (which itself is encoded as a list *)
    let blocking_clause =
      Term.mk_or
	(List.map
	   (fun t -> Term.negate t)
	   bad_cube)
    in
    
    match frames_below with
    (* If there are no frames below, we cannot block the cube, and have failed. *)
    | [] -> raise Failure (*We probably should provide some info on the counterexample here, or else handle concretization in this function *)
       
    | fi::fb -> 
       (* Check whether the blocking clause is relatively inductive *)
       (match absRelInd fi blocking_clause with
	 
       (* No counterexample, so it is relatively inductive and we can add it to the current frame 
	  TODO: generalize the blocking clause *)
       | [] -> (blocking_clause::fi)::fb
	  
       (* Uh-oh - we'd better block the counterexample and try again*)
	  
       | cti -> recblock bad_cube (fi::(recblock cti fb));(* block cti *)
       )
  in

  (* ********************************************************************** *)
  (* Block                                                                  *)
  (* ********************************************************************** *)
  
  let rec block = function
    | [] -> raise Failure (* Actually, this should not happen. Should raise some other error *)
    | fk :: frames_below ->
       (* Check if Fk ^ H |= 'P, recblock counterexamples *)
       SMTSolver.check_sat_assuming_and_get_term_values
	 solver
	 
	 (* SAT case - extract a cube and recblock it *)
	 (fun _ assignments ->

	   (* Represent cube as a list of terms *)
	   let bad_cube = get_term_list_from_term_values assignments in
	   
	   (* Modify frames below to prevent the bad cube  *)
	   let fb = recblock bad_cube frames_below in

	   (* TODO: Handle counterexamples (failure case), concretizing when needed*)
	   (* Let's try blocking again with the modified frames *)
	   block (fk::fb))
	 
	 (* UNSAT case - don't need to do anything, so just continue with unmodified frames *)
	 (fun _ -> fk::frames_below)

	 (List.map
	    (fun trm -> mk_and_assert_actlit trm)
	    (fk @ hp @ [Term.mk_not prop']))

	 abvars
  in
  
  (* ********************************************************************** *)
  (* Propagate                                                              *)
  (* ********************************************************************** *)
  
  let propagate frames =
    frames
  in
  
  let rec ic3ia' frames =
    let frames = block frames in
    List.iter
      (Format.printf "Frame";
       List.iter
	 (Format.printf "@.%a@." Term.pp_print_term))
      frames;
    let frames = propagate frames in
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
      logic
      (Flags.Smt.solver ())
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
    (fun prop -> ic3ia solver init trans prop)
    props;
  
  ()

    
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End:
*)
