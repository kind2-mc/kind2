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
module AbvMap = Map.Make(Term)

(* Define exceptions to break out of loops *)
exception Success
exception Failure
  
(* Cleanup before exit *)
let on_exit _ = ()

(* Checks whether given clause is inductive relative to the frame *)
(* let absRelInd solver frame trans_sys clause associations = *)
  

let ic3ia solver init trans prop =
  
  let absvarcounter = ref 0 in
  let conevarcounter = ref 0 in

  (* Maps terms to abstract variables *)
  let abvar_map = ref AbvMap.empty in
  
  (* Function to convert a term to a tuple consisting of:
     1. A list of abstract variables
     2. A list of associations between abstract and concrete variables
     3. The abstracted term
  *)
  (* TODO: check if an atom has already been abstracted, and reuse the previously created abstract variable if it has. Use maps for this.*)
  let getAbstractions term =

    (* Use mutable lists that will be populated while traversing the term tree*)
    let abvars = ref [] in
    let abascs = ref [] in
    
    (* Utility function to create new abstract variables, generate an association term, and return the abstracted variable *)
    let mk_new_abvar term =
      (* use the counter to create an unused name *)
      let symbol_name = Format.asprintf "_abvar_%d" !absvarcounter in
      let uf_symbol = (UfSymbol.mk_uf_symbol symbol_name [] Type.t_bool) in
      incr absvarcounter;
      
      (* declare the new symbol in the solver *)
      SMTSolver.declare_fun solver uf_symbol;
      
      (* add the new abstract variable and its association term to our lists  *)
      let abvar = Term.mk_uf uf_symbol [] in 
      abvars := abvar::(!abvars);
      let abasc = Term.mk_eq [abvar;term] in
      abascs := abasc::(!abascs);

      abvar
    in
    
    (* Traverse the term and map each boolean atom to an abstract variable (or use existing mapping)  *)
    Term.map
      (* The first input is the number of let bindings above. I'm not going to worry about this for now. Possible error source *)
      (fun _ subterm ->
	if
	  Term.is_atom subterm && not (AbvMap.mem subterm !abvar_map)
	then
	  (abvar_map := AbvMap.add subterm (mk_new_abvar subterm) !abvar_map;
	   subterm)
	else
	  subterm)
      term;
    
    (* Traverse the term and replace where appropriate with abstract variables *)
    let abterm =
      Term.map
	(* The first input is the number of let bindings above. I'm not going to worry about this for now. Possible error source *)
	(fun _ subterm -> if Term.is_atom subterm then (AbvMap.find subterm !abvar_map) else subterm)
	term
    in
    
    !abvars,!abascs,abterm
  in
    
  let ainit,hinit,tinit = getAbstractions init in
  let aprop,hprop,tprop = getAbstractions prop in

  let hp = hinit @ hprop in

  (* code for cloning a term (putting a bar over it). returns the cloned term *)
  (* idea: maintain a mapping from vars to their cloned versions. When you see a var in the mapping,
     just replace it with its clone. Otherwise, create a fresh statevar and var and add them to the mapping.
  *)
  (* let clone_term term = *)
  (*   let clone_or_lookup var = *)
  (* in  *)

  
  let mk_and_assert_actlit trm =
    let act = A.fresh_actlit () in
    SMTSolver.declare_fun solver act;
    let acttrm = A.term_of_actlit act in
    let actimpl = Term.mk_implies [acttrm;trm] in
    SMTSolver.assert_term solver actimpl;
    acttrm
  in

  (*Print for debugging*)
  Format.printf "ABSTRACT VARS OF INIT:";
  List.iter
    (fun trm -> Format.printf "@.%a@." Term.pp_print_term trm)
    (ainit @ hinit);

  Format.printf "ABSTRACT VARS OF PROP:";
  List.iter
    (fun trm -> Format.printf "@.%a@." Term.pp_print_term trm)
    (aprop @ hprop);
  
  Format.printf "ABSTRACTED INIT TERM':@.%a@." Term.pp_print_term tinit;
  Format.printf "ABSTRACTED PROP TERM':@.%a@." Term.pp_print_term tprop;
  (* PAPER LINE 2*)
  
  (* Check whether 'I ^ H |= 'P *)
  SMTSolver.check_sat_assuming
    solver

    (* SAT case ('P not entailed) *)
    (fun _ ->
      Format.printf "Property invalid in initial state@.";
      raise Failure)
    
    (* UNSAT case ('P entailed) *)
    (fun _ ->
      Format.printf "Property valid in initial state@.")

    (* Check satisfiability of 'I ^ H ^ !'P *)
    (List.map
       (fun trm -> mk_and_assert_actlit trm)
       ( hp @ tinit :: [Term.mk_not tprop]));
  (* TODO: Write utility function to handle SAT checking *)
  
  (* PAPER LINE 3*)
  (* Initialize frames *)
  (* Question: Do we need to include tinit in the initial states?*)
  let frames = [[tinit]] in

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
	       Format.printf "Property not entailed by current frame; counterexample found@.";
	       raise Failure)
	     
	     (* UNSAT case ('P entailed) *)
	     (fun _ ->
	       Format.printf "Property entailed by current state@.")
	     
	     (* Check satisfiability of 'Fk ^ H ^ !'P *)
	     (List.map
		(fun trm -> mk_and_assert_actlit trm)
		(fk @ hp @ [Term.mk_not tprop]));
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
  | Success -> Format.printf "Property invariant"
  | Failure -> Format.printf "Property not invariant"
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
    Numeral.zero (Numeral.of_int 1);
  
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
  (* Print abstract variables and associations for initial states *)
  
  let tst,eqs = getAbstractVars t in
  
  Format.printf "INIT':@.%a@." Term.pp_print_term t;

  List.iter
    (fun trm -> Format.printf "INIT':@.%a@." Term.pp_print_term trm)
    tst;
  
  List.iter
    (fun trm -> Format.printf "INIT':@.%a@." Term.pp_print_term trm)
    eqs
  *)
    
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End:
*)
