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

(* Cleanup before exit *)
let on_exit _ = ()


let ic3ia solver init trans prop =

  let absvarcounter = ref 0 in
  
  (* Function to abstract the variables in a term
     Output is a tuple
     First value of tuple is a list of fresh abstract variables
     Second value of tuple is a list of association terms (eq) relating those abstract variables to concrete terms
  *)
  (* QUESTION: Do we also need to reconstruct the term, but with abstract variables replacing concrete ones?*)

  (* Function to convert a term to a tuple consisting of:
     1. A list of abstract variables
     2. A list of associations between abstract and concrete variables
     3. The abstracted term
  *)
  let rec getAbstractions term =

    (* Use mutable lists that will be populated while traversing the term tree*)
    let abvars = ref [] in
    let abascs = ref [] in

    (* Utility function to create new abstract variables, generate an association term, and return the abstracted variable *)
    let mk_new_abvar term =
      (* use the counter to create an unused name *)
      let symbol_name = Format.asprintf "__ic3ia_absvar_%d" !absvarcounter in
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

    let abterm =
      (* Traverse the term and replace where appropriate with abstract variables *)
      Term.map
	(* The first input is the number of let bindings above. I'm not going to worry about this for now. Possible error source *)
	(fun _ subterm -> if Term.is_atom subterm then mk_new_abvar subterm else subterm)
	term
    in
    !abvars,!abascs,abterm
  in
    
  (* let rec getAbstractVars term = *)
  (*   (\* Create or retrieve uninterpreted constant *\) *)
  (*   (\* Task: need to reconstruct formula as well*\) *)
  (*   let mk_new_absvar () = *)
  (*     let symbol_name = Format.asprintf "__ic3ia_absvar_%d" !absvarcounter in *)
  (*     let uf_symbol = (UfSymbol.mk_uf_symbol symbol_name [] Type.t_bool) in *)

  (*     (\* declare the new symbol in the solver *\) *)
  (*     SMTSolver.declare_fun solver uf_symbol; *)
  (*     incr absvarcounter; *)
  (*     (Term.mk_uf uf_symbol []) *)
  (*   in *)
    
  (*   match Term.destruct term with *)
  (*   (\* variables like x,y,z. Assume this is boolean. Todo: raise error if not boolean *\) *)
  (*   | Term.T.Var _ -> *)
  (*      let newabsvar = mk_new_absvar () in *)
  (*      [newabsvar],[Term.mk_eq [newabsvar;term],Term.T.mk_term newabsvar *)
       
  (*   (\* symbols like +, >, & *\) *)
  (*   | Term.T.App (s,l) -> *)
  (*      (match Symbol.node_of_symbol s with *)

  (*      (\* NOTE: Likely error source for unusual inputs, due to lack of consideration of other cases. *\) *)
	 
  (*      (\* comparison operator -> create new variable *\) *)
  (*      | `EQ (\* QUESTION: Is it a problem that EQ can be a boolean operator as well?*\) *)
  (*      | `LEQ *)
  (*      | `GEQ *)
  (*      | `LT *)
  (*      | `GT -> *)
  (* 	  let newabsvar = mk_new_absvar () in *)
  (* 	  [newabsvar],[Term.mk_eq [newabsvar;term]],Term.T.mk_term newabsvar *)
	    
  (*      (\* boolean operator -> recurse *\) *)
  (*      | `NOT *)
  (*      | `IMPLIES *)
  (*      | `AND *)
  (*      | `OR *)
  (*      | `XOR -> *)
  (* 	  List.fold_left *)
  (* 	    ( fun acc sub -> *)
  (* 	      let absvars,terms = getAbstractVars sub in *)
  (* 	      match acc with *)
  (* 	      | (avs,trms,node) -> avs@absvars,trms@terms, *)
  (* 	    ) *)
  (* 	    ([],[]) *)
  (* 	    l *)
	    
  (*      (\* Something else -> empty list (QUESTION: should we have an error here?) *\) *)
  (*      | node -> [],[],node) *)
	 
  (*   (\* Constants and special information do not get abstract variables *\) *)
  (*   | node -> [],[],node *)
  (* in *)
  (* (\* end getAbstractVars  *\) *)

  let ainit,hinit,tinit = getAbstractions init in
  let aprop,hprop,tprop = getAbstractions prop in

  (* let mk_and_assert_actlit trm = *)
  (*   let act = A.fresh_actlit () in *)
  (*   SMTSolver.declare_fun solver act; *)
  (*   let acttrm = A.term_of_actlit act in *)
  (*   let actimpl = Term.mk_implies [acttrm;trm] in *)
  (*   SMTSolver.assert_term solver actimpl; *)
  (*   acttrm *)
  (* in *)
  
  (* Check whether 'I ^ H |= 'P *)
  (* SMTSolver.check_sat_assuming *)
  (*   solver *)
  (*   (fun _ -> Format.printf "Invalid") (\*SAT*\) *)
  (*   (fun _ -> Format.printf "Valid") (\*UNSAT*\) *)
  (*   (ainit @ hinit @ aprop @ hprop @ tinit :: [Term.mk_not tprop]); *)

  (*Print for debugging*)
  List.iter
    (fun trm -> Format.printf "INITABSVARS':@.%a@." Term.pp_print_term trm)
    (ainit@hinit);
  
  List.iter
    (fun trm -> Format.printf "PROPABSVARS':@.%a@." Term.pp_print_term trm)
    (aprop@hprop);
  
  Format.printf "INITABSVARS':@.%a@." Term.pp_print_term tinit;
  
  ()

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
  
(*  Format.printf "%a@." TransSys.pp_print_trans_sys trans_sys;
*)
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
    props
  
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
