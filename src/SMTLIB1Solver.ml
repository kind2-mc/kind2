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

open Lib
open SMTExpr


(* ********************************************************************* *)
(* Types                                                                 *)
(* ********************************************************************* *)

(* Configuration *)
type config = 
    { solver_cmd : string array;    (* Command line arguments for the
                                       solver *)
    }
      
(* Solver instance *)
type t = 
    { solver_config : config;           (* Configuration of the solver
                                           instance *)
      solver_executable : string;       (* Name of the executable of
                                           the solver *)
      solver_args : string array;       (* Arguments to the solver *)
      solver_file_name : string;        (* Name of input file for solver *)
      solver_file : Unix.file_descr;    (* File descriptor of solver's
                                           input file *)
      mutable solver_pid : int option;          (* PID of solver *)

      mutable solver_stdin : Unix.file_descr option;  (* File
                                                         descriptor of
                                                         solver's
                                                         standard
                                                         input *)
      mutable solver_lexbuf : Lexing.lexbuf option;  (* Lexing buffer
                                                        for solver's
                                                        standard
                                                        output *)
      mutable solver_stdout : Unix.file_descr option;  (* File
                                                          descriptor
                                                          of solver's
                                                          standard
                                                          output *)

      mutable solver_stderr : Unix.file_descr option;  (* File
                                                          descriptor
                                                          of solver's
                                                          standard
                                                          error *)
    }


(* ********************************************************************* *)
(* Helper functions to execute commands                                  *)
(* ********************************************************************* *)


(* Read an S-expression from the solver output *)
let expr_of_solver_lexbuf = function

  | { solver_lexbuf = Some lexbuf } ->
    
    (* Parse S-expression and return *)
    SExprParser.sexp SExprLexer.main lexbuf 
      
  | _ -> failwith "Solver is not running"


(* Parse the solver response to an input file *)
let get_run_response solver _ = 
  
  (* Return response *)
  check_sat_response_of_sexpr (expr_of_solver_lexbuf solver)


(* Get n S-expressions from the solver *)
let rec get_custom_command_result solver accum = function 

  (* Terminate recursion and return result *)
  | i when i <= 0 -> List.rev accum

  (* Get one S-expression and recurse to get remaining results *)
  | i -> 

    get_custom_command_result 
      solver
      ((expr_of_solver_lexbuf solver) :: accum) 
      (pred i)


(* Parse the solver response to a custom command *)
let get_custom_command_response num_res solver timeout = 

  (* Get remaining results *)
  let result = get_custom_command_result solver [] num_res in

  (* Return response and result *)
  (Success, result) 
        

(* Send the command to the solver input file *)
let append_input { solver_file = solver_file } command  = 
  
  (* Get an output channel to write to solver's input file *)
  let solver_file_ch = Unix.out_channel_of_descr solver_file in

  (* Get a pretty-printing formatter writing to solver's input file *)
  let solver_file_formatter = 
    Format.formatter_of_out_channel solver_file_ch 
  in

  (* Send command to solver *)
  Format.pp_print_string solver_file_formatter command;

  (* Print newline and flush formatter *)
  Format.pp_print_newline solver_file_formatter ()


(* Send the command to the solver instance *)
let run_solver 
    solver
    parse_response 
    pp_print_response 
    timeout = 
  
  (* Create pipes for input, output and error output *)
  let solver_stdin_in, solver_stdin_out = Unix.pipe () in
  let solver_stdout_in, solver_stdout_out = Unix.pipe () in 
  let solver_stderr_in, solver_stderr_out = Unix.pipe () in 

  (* Create solver process *)
  let solver_pid = 
    Unix.create_process 
      solver.solver_executable 
      solver.solver_args 
      solver_stdin_in
      solver_stdout_out
      solver_stderr_out
  in
  
  (* Close our end of the pipe which has been duplicated by the
     process *)
  Unix.close solver_stdin_in;
  Unix.close solver_stdout_out; 
  Unix.close solver_stderr_out; 

  let solver_stdout = Unix.in_channel_of_descr solver_stdout_in in

  let lexbuf = Lexing.from_channel solver_stdout in

  solver.solver_pid <- Some solver_pid;
  solver.solver_stdin <- Some solver_stdin_out; 
  solver.solver_lexbuf <- Some lexbuf; 
  solver.solver_stdout <- Some solver_stdout_in; 
  solver.solver_stderr <- Some solver_stderr_in; 

  (* Wait for response without timeout *)
  let res = parse_response solver timeout in

  (* Return response *)
  res



(* ********************************************************************* *)
(* Commands                                                              *)
(* ********************************************************************* *)


(* Declare a new uninterpreted sort symbol *)
let declare_sort solver sort arity = 

  (* SMTLIB 1.2 only accepts sorts without parameters *)
  if arity = 0 then 

    (* The command to be executed *)
    let cmd = Format.sprintf "@[<hv 1>:extrasorts ((%s))@]" sort in

    (* Send command to the solver without timeout *)
    append_input solver cmd;

    (* SMTLIB 1.2 commands are not interactive and always succeed *)
    SMTExpr.Success

  else

    (* SMTLIB 1.2 does not support sorts with parameters *)
    SMTExpr.Unsupported


(* Define a sort symbol as an abbreviation for a sort expression *)
let define_sort solver sort args expr = 

  (* SMTLIB 1.2 does not support sorts definitions *)
  SMTExpr.Unsupported


(* Declare a new function symbol *)
let declare_fun solver fun_symbol arg_sorts res_sort = 

  let cmd = 
    Format.sprintf 
      "@[<hv 1>:extrafuns ((%s %s %s))@]" 
      fun_symbol
      (string_of_t 
         (pp_print_list Format.pp_print_string " ") 
         (List.map string_of_sort arg_sorts))
      (string_of_sort res_sort)
  in

  (* Send command to the solver without timeout *)
  append_input solver cmd;

  (* SMTLIB 1.2 commands are not interactive and always succeed *)
  SMTExpr.Success


(* Define a new function symbol as an abbreviation for an expression *)
let define_fun solver fun_symbol arg_sorts res_sort defn = 

  (* SMTLIB 1.2 does not support function definitions *)
  SMTExpr.Unsupported


(* Assert the expression *)
let assert_expr solver expr = 

  let cmd = 
    Format.sprintf 
      "@[<hv 1>:formula@ %s@]" 
      (string_of_expr expr) in
  
  (* Send command to the solver without timeout *)
  append_input solver cmd;

  (* SMTLIB 1.2 commands are not interactive and always succeed *)
  SMTExpr.Success

    
(* Push a number of empty assertion sets to the stack *)
let push solver scopes = 

  (* SMTLIB 1.2 does not support scopes *)
  SMTExpr.Unsupported


(* Pop a number of assertion sets from the stack *)
let pop solver scopes  = 

  (* SMTLIB 1.2 does not support scopes *)
  SMTExpr.Unsupported


(* Check satisfiability of the asserted expressions *)
let check_sat solver = 

  (* Close parentheses around benchmark *)
  let cmd = Format.sprintf ")" in

  (* Send command to the solver without timeout *)
  append_input solver cmd;

  (* Run solver on commands *)
  run_solver 
    solver 
    get_run_response 
    pp_print_check_sat_response 
    0

  
(* Get values of expressions in the model *)
let get_value solver expr_list = 

  (* SMTLIB 1.2 does not support models *)
  SMTExpr.Unsupported, []


(* Execute a get-value command and return the response *)
let execute_custom_command solver _ args num_res = 

  get_custom_command_response num_res solver 0


(* Execute a custom command and return the response *)
let execute_custom_check_sat_command solver cmd = 

  (* SMTLIB 1.2 does not support custom commands *)
  SMTExpr.Response SMTExpr.Unsupported


(* ********************************************************************* *)
(* Creating and deleting solver instances                                *)
(* ********************************************************************* *)


(* Create an instance of the solver *)
let create_instance 
    ?(produce_assignments = false)
    ?(produce_models = false) 
    ?(produce_proofs = false) 
    ?(produce_cores = false)     
    ({ solver_cmd = solver_cmd } as config)
    logic =

(*
  (* Split command line into arguments 

     TODO: Don't use the glib function but do lexing in OCaml *)
  let solver_args_in = Util_glib.shell_parse_argv command in

  (* Name of executable is first argument 
*)

     TODO: expand ~ *)
  let solver_executable = solver_cmd.(0) in

  (* Create a temporary file and read its name *)
  let in_ch = Unix.open_process_in "/bin/mktemp" in

  (* Name of temporary file *)
  let temp_file_name = 

    try
      
      (* Read name of temp file from output of command *)
      input_line in_ch
        
    (* Command produced no output *)
    with End_of_file ->
      
      (* Raise error *)
      failwith "Could not create a temporary file for solver"

  in

  (* Open temporary file for writing *)
  let solver_file = Unix.openfile temp_file_name [Unix.O_WRONLY] 0o640 in

  (* Append the name of the temporary file to solver arguments *)
  let solver_cmd = Array.append solver_cmd [| temp_file_name |] in

  (* Create the solver instance *)
  let solver =
    { solver_config = config;
      solver_executable = solver_executable;
      solver_args = solver_cmd;
      solver_file_name = temp_file_name; 
      solver_file = solver_file;
      solver_pid = None;
      solver_stdin = None;
      solver_lexbuf = None;
      solver_stdout = None;
      solver_stderr = None }
  in

  (* Set logic *)
  append_input
    solver 
    (Format.sprintf 
       "(benchmark none@\n:status unknown@\n:logic %s@\n" 
       (string_of_logic logic));
  
  (* Return solver instance *)
  solver

    

(* Delete the solver instance by sending the exit command and wait for
   the solver process to exit *)
let delete_instance = function
  | { solver_file_name = solver_file_name;
      solver_pid = Some solver_pid;
      solver_stdin = Some solver_stdin ;
      solver_stdout = Some solver_stdout;
      solver_stderr = Some solver_stderr } ->
    
    (* Wait for process to terminate *)
    let _, process_status = Unix.waitpid [] solver_pid in
    
    (
      
      (* Check termination status of solver *)
      match process_status with

        (* Exit with code *)
        | Unix.WEXITED c -> 
          Format.eprintf "Solver exited with code %d@." c
            
        (* Killed by signal *)
        | Unix.WSIGNALED s -> 
          Format.eprintf "Solver killed with signal %d@." s
            
        (* Stopped by signal *)
        | Unix.WSTOPPED s -> 
          Format.eprintf "Solver stopped by signal %d@." s

    );

    (* Close file descriptors of solver *)
    Unix.close solver_stdin;
    Unix.close solver_stdout;
    Unix.close solver_stderr;

    (* Delete temporary file *)
    Unix.unlink solver_file_name

  | _ -> failwith "Solver is not running" 
   
(* ********************************************************************* *)
(* Toplevel testing code                                                 *)
(* ********************************************************************* *)

(*

(* Testing interpolant generation with iZ3 *)
let test () = 

  (* Configuration of SMTLIB solver

     Use -f option to flatten all let expressions, since syntax for
     lets in SMTLIB 1.2 is different and we want to parse it with our
     SMTLIB 2 parser *)
  let smtlib_solver_config = 
    { solver_cmd = "/home/chris/iz3-3.3pre2/bin/iz3 -f";
      debug_channel = Some Pervasives.stdout; } 
  in
  
  (* Set library path to where libfoci and libiz3 are *)
  Unix.putenv "LD_LIBRARY_PATH" "/home/chris/lib";
  
  (* Create instance of the solver, all flags are ignored *)
  let solver = 
    create_instance 
      smtlib_solver_config
      `QF_UFLIA
  in

  (* Make uninterpreted integer constant x *)
  let s_x = UfSymbol.mk_uf_symbol "x" [] Type.Int in

  (* Make uninterpreted integer constant y *)
  let s_y = UfSymbol.mk_uf_symbol "y" [] Type.Int in

  (* Make uninterpreted constant x *)
  let t_x = Term.mk_uf s_x [] in

  (* Make uninterpreted constant y *)
  let t_y = Term.mk_uf s_y [] in

  (* Make integer numeral 0 *)
  let t_0 = Term.mk_num_of_int 0 in
  
  (* First formula: (< x 0) *)
  let f1 = Term.mk_lt [t_x; t_0] in

  (* Second formula: (> y 0) *)
  let f2 = Term.mk_gt [t_y; t_0] in

  (* Third formula: (= x y) *)
  let f3 = Term.mk_eq [t_x; t_y] in
  
  (* Declare all uninterpreted symbols in the solver *)
  ignore (TermConv.declare_smt_symbols (declare_fun solver));
  
  (* Assert first formula, this will always succeed in SMTLIB1 *)
  ignore (assert_expr solver (TermConv.smtexpr_of_term f1));

  (* Assert second formula, this will always succeed in SMTLIB1 *)
  ignore (assert_expr solver (TermConv.smtexpr_of_term f2));

  (* Assert third formula, this will always succeed in SMTLIB1 *)
  ignore (assert_expr solver (TermConv.smtexpr_of_term f3));
  
  (* Check result of solver: interpolants only generated for
     unsatisfiable formulas *)
  (match check_sat solver with 

    (* Result is unsatisfiable *)
    | Unsat -> 

      (* The interpolants returned by the solver *)
      let interpolants = 

        (* Get additional output from solver

           The first line will be "interpolant:", then one interpolant
           between each two asserted formulas, i.e. one formula less
           than the number of asserts. The command does not matter in
           the SMTLIB1 interface *)
        let response, sexprs =
          execute_custom_command solver "dummy" [] 3
        in
        
        (* Drop the first line on output, which is just
           "interpolant:", and convert S-expressions to SMT
           expressions *)
        let interpolant_smtexprs = 
          List.map 
            SMTExpr.expr_of_string_sexpr 
            (List.tl sexprs) in

        (* Convert SMT expressions to terms *)
        List.map TermConv.mk_of_smtexpr interpolant_smtexprs

      in
      
      (* Print list of interpolant terms *)
      Format.printf 
        "@[<v>%a@]@." 
        (pp_print_list Term.pp_print_term "")
        interpolants
        
    (* Result is satisfiable *)
    | Sat -> 
      
      Format.printf 
        "Problem is satisfiable, no interpolants@." 

    (* Result is unknown *)
    | Unknown -> 
      
      Format.printf 
        "Satisfiability of problem is unknown, no interpolants@." 

    (* Result is something else, most likely an error *)
    | Response r -> 

      Format.printf 
        "SMT solver responded %a@."
        SMTExpr.pp_print_response r 

  );   
  
  (* Delete instance to get rid of temporary file *)
  delete_instance solver

;;

test ()
*)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
