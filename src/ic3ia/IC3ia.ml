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

  (* CLONE VARIABLES *)
  
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
	  (* Define function that appends * to a string *)
	  let appclone prefix = String.concat "" [prefix;"*"] in	

	  (* Crete a new state variable to correspond to v*)
	  let new_statevar =
	    (StateVar.mk_state_var
	       ~is_input:(StateVar.is_input v)
	       ~is_const:(StateVar.is_const v)
	       ~for_inv_gen:(StateVar.for_inv_gen v)
	       (appclone (StateVar.name_of_state_var v))
	       (List.map appclone (StateVar.scope_of_state_var v))
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
  
  (* ABSTRACT VARIABLES *)

  (* Creates, declares, and returns a new abstract variable *)
  let mk_new_abvar term =
    
    (* use the counter to create an unused name *)
    let symbol_name = Format.asprintf "_abvar_%d" !absvarcounter in
    let uf_symbol = (UfSymbol.mk_uf_symbol symbol_name [] Type.t_bool) in
    incr absvarcounter;
    
    (* declare the new symbol in the solver *)
    SMTSolver.declare_fun solver uf_symbol;
    
    (* Return the term consisting of the new symbol *)
    Term.mk_uf uf_symbol []
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

  (* TODO: Should return counterexample *)
  let absRelInd frame clause =
    SMTSolver.check_sat_assuming
      solver

      (* SAT case *)
      (fun _ -> Format.printf "@.Clause is not inductive relative to frame; counterexample found@.")

      (* UNSAT case *)
      (fun _ -> Format.printf "@.Clause is inductive relative to frame@.")
      
      (* Check satisfiability of F ^ c ^ hp ^ eq ^ T(clone) ^ !c' *)
      (List.map
	 (fun trm -> mk_and_assert_actlit trm)
	 (let eqP = get_eqP predicates in
	  let bump = Term.bump_state Numeral.one in
	  let hp = Term.mk_and hp in
	  [frame;
	   clause;
	   hp;
	   bump hp;
	   eqP;
	   bump eqP;
	   (Term.mk_not (bump clause))]))
  in
  
  (* Check whether 'I ^ H |= 'P *)
  SMTSolver.check_sat_assuming
    solver

    (* SAT case ('P not entailed) *)
    (fun _ ->
      Format.printf "@.Property invalid in initial state@.";
      raise Failure)
    
    (* UNSAT case ('P entailed) *)
    (fun _ ->
      Format.printf "@.Property valid in initial state@.")

    (* Check satisfiability of 'I ^ H ^ !'P *)
    (List.map
       (fun trm -> mk_and_assert_actlit trm)
       ( hp @ init' :: [Term.mk_not prop']));
  (* TODO: Write utility function to handle SAT checking *)
  
  (* PAPER LINE 3*)
  (* Initialize frames *)
  (* Question: Do we need to include tinit in the initial states?*)
  let frames = [[init']] in
  
  let rec recblock cube_to_block frames_below =
    match frames_below with
    (* If there are no frames below, we cannot block the cube, and have failed. *)
    | [] -> raise Failure
       
    | fi::tail_frames ->
       (* Check whether absrelind F_i-1 T, ~cube_to_block is satisfiable *)
       (* If it is, extract a cube c and try to block c at i-1, then call this function again on cube_to_block, frames_below *)
       (* If it isn't, generalize ~cube_to_block to g and add g to the frames, then return TRUE *)
       true
  in

  let block = function
    | [] -> raise Failure (* Actually, this should not happen. Should raise some other error *)
    | fk :: tail_frames ->
       (match
	   (* Check if Fk ^ H |= 'P, recblock counterexamples *)
	   SMTSolver.check_sat_assuming solver
	     
	     (* SAT case ('P not entailed) *)
	     (fun _ ->
	       Format.printf "@.Property not entailed by current frame; counterexample found@.";
	       raise Failure)
	     
	     (* UNSAT case ('P entailed) *)
	     (fun _ ->
	       Format.printf "@.Property entailed by current state@.")
	     
	     (* Check satisfiability of 'Fk ^ H ^ !'P *)
	     (List.map
		(fun trm -> mk_and_assert_actlit trm)
		(fk @ hp @ [Term.mk_not prop']));
	with
	| _ -> [])
  in
  
  let propagate frames = frames in
  
  let rec ic3ia' frames =
    absRelInd init' (Term.mk_not init');
    let frames = block frames in
    let frames = propagate frames in
    ic3ia' frames
  in
  
  try ic3ia' frames with
  | Success -> Format.printf "@.Property invariant"
  | Failure -> Format.printf "@.Property not invariant"
  | _ -> ()
      
let main input_sys aparam trans_sys =
  
  let logic = TransSys.get_logic trans_sys in
  
  let solver =
    SMTSolver.create_instance
      ~produce_assignments:true
      ~produce_cores:true
      logic
      (Flags.Smt.solver ())
  in

  (* Question: does this assert the transition system? Because we only want the cloned transition system.*)
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
