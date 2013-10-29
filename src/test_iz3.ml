open Lib

(* Use SMTLIB1 solver *)
module MySolver = SMTSolver.Make (SMTLIB1Solver)


(* Testing interpolant generation with iZ3 *)
let test () = 

  (* Configuration of SMTLIB solver

     Use -f option to flatten all let expressions, since syntax for
     lets in SMTLIB 1.2 is different and we want to parse it with our
     SMTLIB 2 parser *)
  let smtlib_solver_config = 
    { SMTLIB1Solver.solver_cmd = "/home/chris/iz3-3.3pre2/bin/iz3 -f";
      SMTLIB1Solver.debug_channel = Some Pervasives.stdout; } 
  in
  
  (* Set library path to where libfoci and libiz3 are *)
  Unix.putenv "LD_LIBRARY_PATH" "/home/chris/lib";
  
  (* Create instance of the solver, all flags are ignored *)
  let solver = 
    MySolver.create_instance 
      smtlib_solver_config
      `QF_UFLIA
  in

  (* Make uninterpreted integer constant x *)
  let s_x = Term.mk_uf_symbol "x" [] Type.Int in

  (* Make uninterpreted integer constant y *)
  let s_y = Term.mk_uf_symbol "y" [] Type.Int in

  (* Make uninterpreted constant x *)
  let t_x = Term.mk_uf s_x [] in

  (* Make uninterpreted constant y *)
  let t_y = Term.mk_uf s_y [] in

  (* Make integer numeral 0 *)
  let t_0 = Term.mk_num 0 in
  
  (* First formula: (< x 0) *)
  let f1 = Term.mk_lt [t_x; t_0] in

  (* Second formula: (> y 0) *)
  let f2 = Term.mk_gt [t_y; t_0] in

  (* Third formula: (= x y) *)
  let f3 = Term.mk_eq [t_x; t_y] in
  
  (* Declare all uninterpreted symbols in the solver *)
  ignore (Term.declare_smt_symbols (MySolver.declare_fun solver));
  
  (* Assert first formula, this will always succeed in SMTLIB1 *)
  ignore (MySolver.assert_expr solver (Term.smtexpr_of_term f1));

  (* Assert second formula, this will always succeed in SMTLIB1 *)
  ignore (MySolver.assert_expr solver (Term.smtexpr_of_term f2));

  (* Assert third formula, this will always succeed in SMTLIB1 *)
  ignore (MySolver.assert_expr solver (Term.smtexpr_of_term f3));
  
  (* Check result of solver: interpolants only generated for
     unsatisfiable formulas *)
  (match MySolver.check_sat solver with 

    (* Result is unsatisfiable *)
    | SMTExpr.Unsat -> 

      (* The interpolants returned by the solver *)
      let interpolants = 

	(* Get additional output from solver

	   The first line will be "interpolant:", then one interpolant
	   between each two asserted formulas, i.e. one formula less
	   than the number of asserts. The command does not matter in
	   the SMTLIB1 interface *)
	let response, sexprs =
	  MySolver.execute_custom_command solver "dummy" [] 3
	in
	
	(* Drop the first line on output, which is just
	   "interpolant:", and convert S-expressions to SMT
	   expressions *)
	let interpolant_smtexprs = 
	  List.map 
	    SMTExpr.expr_of_string_sexpr 
	    (List.tl sexprs) in

	(* Convert SMT expressions to terms *)
	List.map Term.mk_of_smtexpr interpolant_smtexprs

      in
      
      (* Print list of interpolant terms *)
      Format.printf 
	"@[<v>%a@]@." 
	(pp_print_list Term.pp_print_term "")
	interpolants
	
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
  MySolver.delete_instance solver

;;

test ()

