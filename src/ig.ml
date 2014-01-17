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

open Tree
open PdrUtil
open Lib


(* Solver for SMTLIB 2.0, used in z3. *)
module MySolver2 = SMTSolver.Make (SMTLIBSolver)

(* Solver for SMTLIB 1.2, used in iZ3. *)
module MySolver1 = SMTSolver.Make (SMTLIB1Solver)

(* Instantiate the term to the bound *)
let term_of_bound i term = 
  Term.mk_let 
    [("__i", Term.mk_num_of_int i)] 
    term


(* Instantiate the initial state constraint to the bound *)
let init_of_bound i z = 
  List.map (term_of_bound i) z.TransSys.init


(* Instantiate the properties to the bound *)
let props_of_bound i z = 
  (List.map (term_of_bound i) (List.map snd z.TransSys.props))
    

(* Instantiate the global constraint to the bound *)
let constr_of_bound i z = 
  List.map (term_of_bound i) z.TransSys.constr


(* Call with lift_formula f z.TransSys.state_index *)
let lift_formula f idx = 
  let lift_formula' idx sym args =
    match sym with 
      | (`UF _ as s) -> Term.mk_app (Term.mk_symbol s) [idx]
      | _ -> 
        match args with
          | [] -> Term.mk_const (Term.mk_symbol sym)
          | _ -> Term.mk_app (Term.mk_symbol sym) args 
  in 
  Term.fold (lift_formula' idx) f


(* Using iz3 to generate the interplants for the list of formula f_list,
   and if it is satisfiable, it will generate an empty list.
   The result will be put into the last argument, t_list.*)
let generate_interpolants (f_list: Term.term list) (interpolants: Term.term list ref) : unit =  
  let iZ3_config = 
      { SMTLIB1Solver.solver_cmd = 
          [| "/home/chris/iz3-3.3pre2/bin/iz3";
             "-f" |];
        SMTLIB1Solver.debug_channel = Some Pervasives.stdout; } 
  in

  (* Set library path to where libfoci and libiz3 are *)
  Unix.putenv "LD_LIBRARY_PATH" "/home/chris/lib"; 
  (* Unix.putenv "LD_LIBRARY_PATH" "/space/ruoyzhang/lib"; *)

  let iSolver =     
      MySolver1.create_instance 
	~produce_assignments:true
	iZ3_config
	`QF_UFLIA
  in
  
  (* Declare all uninterpreted symbols in the solver *)
  ignore (TermConv.declare_smt_symbols (MySolver1.declare_fun iSolver));
  
  (* Assert all the formulas in the k-reachable formula list *)
  List.iter 
  (fun x ->
    ignore (MySolver1.assert_expr iSolver (TermConv.smtexpr_of_term x));
  )
  f_list;
  
  Format.printf "Lanching iZ3...@.";
  (match MySolver1.check_sat iSolver with 

    (* Result is unsatisfiable *)
    | SMTExpr.Unsat -> 
  	Format.printf "UNSAT@.";
	(* Get additional output from solver

	   The first line will be "interpolant:", then one interpolant
	   between each two asserted formulas, i.e. one formula less
	   than the number of asserts. The command does not matter in
	   the SMTLIB1 interface *)
	let response, sexprs =
	  MySolver1.execute_custom_command iSolver "dummy" [] (List.length f_list)
	in
	
	(* Drop the first line on output, which is just
	   "interpolant:", and convert S-expressions to SMT
	   expressions *)
	let interpolant_smtexprs = 
	  List.map 
	    SMTExpr.expr_of_string_sexpr 
	    (List.tl sexprs) in

      Format.printf "The interpolants are: @." ;
      Format.printf "@[<v>%a@]@." (pp_print_list SMTExpr.pp_print_expr "") interpolant_smtexprs;

      (* Convert SMT expressions to terms *)
      Format.printf "Trying to Convert SMT expressions to terms: @." ;
      interpolants := List.map TermConv.mk_of_smtexpr interpolant_smtexprs;
      Format.printf "The interpolants are: @." ;
      Format.printf "@[<v>%a@]@." (pp_print_list Term.pp_print_term "") !interpolants
	
    (* Result is satisfiable *)
    | SMTExpr.Sat -> 
      
      Format.printf 
	"Problem is satisfiable, no interpolants@." 

    (* Result is unknown *)
    | SMTExpr.Unknown -> 
      
      Format.printf 
	"Satisfiability of problem is unknown, no interpolants@." 

    (* Result is something else, most likely an error *)
    | SMTExpr.Response r -> 

      Format.printf 
	"SMT solver responded %a@."
	SMTExpr.pp_print_response r 

  );   
  
  (* Delete instance to get rid of temporary file *)
  MySolver1.delete_instance iSolver


(* Generate a list of the transition functions, up to state k. The list will be
   empty if k = 0. The result will be put into the last argument, t_list. *)
let rec generate_k_transition_list (ts: TransSys.t) (k: int) (t_list: Term.term list ref) : unit =
  if( k > 0 )
  then(
    let tran = 
      let tran_list = (constr_of_bound k ts) in
      (match tran_list with
      | [] -> Term.mk_true ()
      | [f] -> f
      | _ -> Prop.tland tran_list
      ) 
    in
    
    t_list := List.append [tran] !t_list;
    generate_k_transition_list ts (k - 1) t_list
  )
  else()


(* Generate a list of formulas which represents a k reachable property. It means that 
   from initial states, after k step of transition relations, the property holds. 
   The result will be put into the last argument, t_list. *)
let generate_k_reachable_formula_list (ts: TransSys.t) (k: int) (t_list: Term.term list ref) : unit =
  let init = 
    let init_list = (init_of_bound 0 ts) in
    (match init_list with
    | [] -> Term.mk_true ()
    | [f] -> f
    | _ -> Prop.tland init_list
    ) 
  in
  
  let prop = 
    let prop_list = (props_of_bound k ts) in
    (match prop_list with
    | [] -> Term.mk_true ()
    | [f] -> f
    | _ -> Prop.tland prop_list
    )
  in
  
  let k_transition_list = ref [] in
  generate_k_transition_list ts k k_transition_list;
  t_list := List.append (List.append [init] !k_transition_list) [Term.mk_not prop]
  

(* Check if a formula is an invariant. If it is an invariant,
   1) It should holds on the initial state.
   2) Given it holds on one state, it should continue to hold
      in the next state. *)
let check_invariant (ts: TransSys.t) (inv: Term.term) : bool =
  Format.printf "Checking invariant of:@\n@[<hv>%a@]@." Term.pp_print_term inv;

  let init = 
    let init_list = (init_of_bound 0 ts) in
    (match init_list with
    | [] -> Term.mk_true ()
    | [f] -> f
    | _ -> Prop.tland init_list
    ) 
  in

  let tran = 
    let tran_list = (constr_of_bound 1 ts) in
    (match tran_list with
    | [] -> Term.mk_true ()
    | [f] -> f
    | _ -> Prop.tland tran_list
    ) 
  in

  let inv0 = (term_of_bound 0 inv) in

  let inv1 = (term_of_bound 1 inv) in

  let smtlib_solver_config = 
      { SMTLIBSolver.solver_cmd = 
          [| "/home/chris/z3/bin/external/z3";
             "-smt2"; 
             "-in" |];
	SMTLIBSolver.debug_channel = Some Pervasives.stdout } in

  let solver = Solver.init_solver smtlib_solver_config in

  (
  match check_entailment solver init inv0 with
    | CeX _ -> 
      MySolver2.delete_instance solver; 
      false

    | Valid -> 
    (
    match check_entailment solver (Prop.tand inv0 tran) inv1 with
      | CeX _ -> 
        MySolver2.delete_instance solver; 
	false

      | Valid ->
        MySolver2.delete_instance solver; 
	true
    )
  )

let rec generate_invariant_start_with_k (ts: TransSys.t) (k: int) : Term.term =
  let k_reachable_formula_list = ref [] in
  let interpolants = ref [] in
  let lifted_interpolants = ref [] in

  generate_k_reachable_formula_list ts k k_reachable_formula_list;
  generate_interpolants !k_reachable_formula_list interpolants;
  if ((List.length !interpolants) != 0)
  then (
    lifted_interpolants := (List.map (fun x -> lift_formula x ts.TransSys.state_index) !interpolants);

    (
    try (
      let inv = List.find (fun x -> check_invariant ts x) !lifted_interpolants in
      Format.printf "Invariants found in the %i step@." k; inv
      )
    with Not_found -> generate_invariant_start_with_k ts (k + 1)
    )

    (*
    List.iter (fun x -> 
                 if (check_invariant ts x)
                 then (Format.printf "Invariants found in the %i step@." k; find := true; inv := x) 
                 else ()) 
    !lifted_interpolants;
    
    if (!find = true)
    then (!inv)
    else (generate_invariant_start_with_k ts (k + 1))
    *)
  )
  else (
    Format.printf "The  property doesn't hold in the %i step, exiting@." k;
    (Term.mk_false ())
  )

let rec generate_invariant (ts: TransSys.t) : Term.term =
  generate_invariant_start_with_k ts 0

let main filename =
  let ts = OldParser.of_file filename in
  TransSys.pp_print_trans_sys Format.std_formatter ts;
  Format.printf "Start to generate invariant.@.";
  
  let inv = generate_invariant ts in
  Format.printf "The invariant is:@\n@[<hv>%a@]@." Term.pp_print_term inv;
  ()

let test = main Sys.argv.(1);;


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
