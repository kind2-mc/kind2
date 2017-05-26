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
  let conevarcounter = ref 0 in

  (* Function to clone all variables in given predicates and return a map *)
  let get_clone_map predicates =
    let clone_map = ref StateVar.StateVarMap.empty in
    List.iter
      (fun p ->
	
	(* Get set containing all state variables in predicate p *)
	let statevars = Term.state_vars_of_term p in

	(* Define function that appends _clone to a string *)
	let appclone prefix = String.concat "" [prefix;"_clone"] in

	(* Iterate over statevars, cloning each uncloned variable and adding it to clone_map*)
	StateVar.StateVarSet.iter
	  (fun v ->
	    if not (StateVar.StateVarMap.mem v !clone_map)
	    then

	      (* Create new state variable as clone of input*)
	      let new_statevar =
		(StateVar.mk_state_var
		      ~is_input:(StateVar.is_input v)
		      ~is_const:(StateVar.is_const v)
		      ~for_inv_gen:(StateVar.for_inv_gen v)
		      (appclone (StateVar.name_of_state_var v))
		      (List.map appclone (StateVar.scope_of_state_var v))
		      (StateVar.type_of_state_var v))
	      in
	      
	      clone_map := StateVar.StateVarMap.add v new_statevar !clone_map)
	  
	  statevars)

      (* Repeat for each term in predicates *)
      predicates;

    !clone_map
  in

  (* Creates a clone of an uncloned term *)
  let clone_term term state_var_map =
    let lookup term = StateVar.StateVarMap.find term state_var_map in
    Term.map_state_vars lookup term
  in

  (* Generates a term asserting the equality of an uncloned term and its clone *)
  let mk_clone_eq term state_var_map =
    Term.mk_eq [term;clone_term term state_var_map]
  in
  
  let clone_map = get_clone_map predicates in


  
  (* Extracts a map from boolean atoms to abstract variables given a list of predicates *)
  let get_abvar_map predicates =

    (* Mutable map from atoms to abstract variables *)
    let abvar_map = ref TermMap.empty in
    
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

    (* Traverse the term and map each unmapped boolean atom to an abstract variable *)
    let extract_from_term term =
      Term.map
	(fun _ subterm ->
    	  if
    	    Term.is_atom subterm && not (TermMap.mem subterm !abvar_map)
    	  then
    	    abvar_map := TermMap.add subterm (mk_new_abvar subterm) !abvar_map;
    	  subterm)
	term;
      ()
    in

    (* Extract abstract variables from each predicate *)
    List.iter
      extract_from_term
      predicates;
    
    !abvar_map
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
  
  let mk_and_assert_actlit trm =
    let act = A.fresh_actlit () in
    SMTSolver.declare_fun solver act;
    let acttrm = A.term_of_actlit act in
    let actimpl = Term.mk_implies [acttrm;trm] in
    SMTSolver.assert_term solver actimpl;
    acttrm
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
    | [] -> raise Failure
    | _ -> raise Success
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
  let trans = [] in
  (* Given a list of properties, we will run IC3ia for each one seperately.*)
  let props = List.map
    (fun (s,t) -> t)
    (TransSys.props_list_of_bound trans_sys Numeral.zero)
  in 
  
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
