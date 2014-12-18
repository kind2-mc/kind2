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

type any_response =
  | NoResp
  | Resp of response
  | CheckSatResp of check_sat_response
  | GetValueResp of (response * (SMTExpr.t * SMTExpr.t) list)
  | GetUnsatCoreResp of (response * (string list))
  | CustomResp of (response * (HStringSExpr.t list))
  | Comment of string 

type command_type =
  | NoRespCmd
  | Cmd
  | CheckSatCmd
  | GetValueCmd
  | GetUnsatCoreCmd
  | CustomCmd of int

(* Configuration *)
type config =
    { solver_cmd : string array;    (* Command line arguments for the
                                       solver *)
      
    }
      
(* Solver instance *)
type t = 
    { solver_config : config;           (* Configuration of the solver
                                           instance *)
      solver_pid : int;                 (* PID of the solver process *)
      solver_stdin : Unix.file_descr;   (* File descriptor of solver's stdin *)
      solver_lexbuf : Lexing.lexbuf;    (* Lexing buffer on solver's
                                           stdout *)
      solver_stdout : Unix.file_descr;  (* File descriptor of solver's
                                           stdout *)
      solver_stderr : Unix.file_descr;  (* File descriptor of solver's
                                           stderr *)
      solver_trace_cmd : string -> unit;
      (* Tracing function for commands *)
      
      solver_trace_res : any_response -> unit;
      (* Tracing function for responses *)
    }



(* ********************************************************************* *)
(* Configurations                                                        *)
(* ********************************************************************* *)


(* Configuration for Z3 *)
let smtlibsolver_config_z3 () = 

  (* Path and name of Z3 executable *)
  let z3_bin = Flags.z3_bin () in

  { solver_cmd = [| z3_bin; "-smt2"; "-in" |] }


(* Configuration for CVC4 *)
let smtlibsolver_config_cvc4 () = 

  (* Path and name of CVC4 executable *)
  let cvc4_bin = Flags.cvc4_bin () in

  if Flags.pdr_tighten_to_unsat_core () then 

    (* Use unsat core option *)
    { solver_cmd = 
        [| cvc4_bin; 
           "--lang"; "smt2";
           "--rewrite-divk";
           "--tear-down-incremental" |] }

  else

    (* Omit unsat core option for version older than 1.5 *)
    { solver_cmd = 
        [| cvc4_bin; 
           "--lang"; "smt2";
           "--rewrite-divk";
           "--incremental" |] }


(* Configuration for MathSAT5 *)
let smtlibsolver_config_mathsat5 () = 

  (* Path and name of MathSAT5 executable *)
  let mathsat5_bin = Flags.mathsat5_bin () in
  
  { solver_cmd = [| mathsat5_bin; "-input=smt2" |] }


(* Configuration for Yices *)
let smtlibsolver_config_yices () = 

  (* Path and name of Yices executable *)
  let yices_bin = Flags.yices_bin () in

  { solver_cmd = [| yices_bin; "--incremental" |] }


(* Configuration for current SMT solver *)
let config_of_flags () = match Flags.smtsolver () with 
  | `Z3_SMTLIB -> smtlibsolver_config_z3 ()
  | `CVC4_SMTLIB -> smtlibsolver_config_cvc4 ()
  | `MathSat5_SMTLIB -> smtlibsolver_config_mathsat5 ()
  | `Yices_SMTLIB -> smtlibsolver_config_yices ()
  | _ -> 
    (* (Event.log `INVMAN L_fatal "Not using an SMTLIB solver"); *)
    failwith "SMTLIBSolver.config_of_flags"
    

(* Command to limit check-sat in Z3 to run for the given numer of ms
   at most *)
let z3_check_sat_limited_cmd ms = 
  Format.sprintf "(check-sat-using (try-for smt %d))" ms


(* Command to limit check-sat in CVC4 to run for the given numer of ms
   at most *)
let cvc4_check_sat_limited_cmd _ = 
  failwith "check-sat with timeout not implemented for CVC4"


(* Command to limit check-sat in MathSAT5 to run for the given numer of ms
   at most *)
let mathsat5_check_sat_limited_cmd _ = 
  failwith "check-sat with timeout not implemented for MathSAT5"


(* Command to limit check-sat in Yices to run for the given numer of ms
   at most *)
let yices_check_sat_limited_cmd _ = 
  failwith "check-sat with timeout not implemented for Yices"


(* Command to limit check-sat to run for the given numer of ms at most *)
let check_sat_limited_cmd ms = match Flags.smtsolver () with 
  | `Z3_SMTLIB -> z3_check_sat_limited_cmd ms
  | `CVC4_SMTLIB -> cvc4_check_sat_limited_cmd ms
  | `MathSat5_SMTLIB -> mathsat5_check_sat_limited_cmd ms
  | `Yices_SMTLIB -> yices_check_sat_limited_cmd ms
  | _ -> 
    (* (Event.log `INVMAN L_fatal "Not using an SMTLIB solver"); *)
    failwith "SMTLIBSolver.check_sat_limited_cmd"


(* Indicates whether the solver supports the check-sat-assuming
   command. *)
let check_sat_assuming_supported () = match Flags.smtsolver () with 
  | `Z3_SMTLIB -> true
  | `CVC4_SMTLIB -> false
  | `MathSat5_SMTLIB -> false
  | `Yices_SMTLIB -> false
  | _ -> 
    (* (Event.log `INVMAN L_fatal "Not using an SMTLIB solver"); *)
    failwith "SMTLIBSolver.check_sat_assuming_cmd"


let z3_check_sat_assumptions_cmd assumptions = 
  Format.asprintf 
    "(check-sat %a)"
    (pp_print_list pp_print_expr "@ ")
    assumptions

let cvc4_check_sat_assumptions_cmd _ = 
  failwith "check-sat with assumptions not implemented for CVC4"

let mathsat5_check_sat_assumptions_cmd assumptions = 
  Format.asprintf 
    "(check-sat-assumptions (%a))"
    (pp_print_list pp_print_expr "@ ")
    assumptions

let yices_check_sat_assumptions_cmd _ = 
  failwith "check-sat with assumptions not implemented for Yices"


(* Command to run check-sat with given assumptions *)
let check_sat_assumptions_cmd assumptions = match Flags.smtsolver () with 
  | `Z3_SMTLIB -> z3_check_sat_assumptions_cmd assumptions
  | `CVC4_SMTLIB -> cvc4_check_sat_assumptions_cmd assumptions
  | `MathSat5_SMTLIB -> mathsat5_check_sat_assumptions_cmd assumptions
  | `Yices_SMTLIB -> yices_check_sat_assumptions_cmd assumptions
  | _ -> 
    (* (Event.log `INVMAN Event.L_fatal "Not using an SMTLIB solver"); *)
    failwith "SMTLIBSolver.check_sat_limited_cmd"


(* ********************************************************************* *)
(* Helper functions to execute commands                                  *)
(* ********************************************************************* *)


(* Read an S-expression from the solver output *)
let expr_of_solver_lexbuf { solver_lexbuf = lexbuf } = 

  (* Parse S-expression and return *)
  SExprParser.sexp SExprLexer.main lexbuf 
  

(* Parse the solver response to a command *)
let get_command_response solver timeout = 

  (* Return response *)
  response_of_sexpr (expr_of_solver_lexbuf solver)


(* Parse the solver response to a check-sat command *)
let get_check_sat_response solver timeout = 

  (* Return response *)
  check_sat_response_of_sexpr (expr_of_solver_lexbuf solver)


(* Parse the solver response to a get-value command *)
let get_get_value_response solver timeout = 

  (* Return response *)
  get_value_response_of_sexpr (expr_of_solver_lexbuf solver)
      

(* Parse the solver response to a get-unsat-core command *)
let get_get_unsat_core_response solver timeout = 

  (* Return response *)
  get_unsat_core_response_of_sexpr (expr_of_solver_lexbuf solver)
      

(* Get n S-expressions from the solver *)
let rec get_custom_command_result solver accum = function 

  (* Terminate recursion and return result *)
  | i when i <= 0 -> List.rev accum

  (* Get one S-expression and recurse to get remaining results *)
  | i -> 

    get_custom_command_result 
      solver
      (expr_of_solver_lexbuf solver :: accum) 
      (pred i)


(* Parse the solver response to a custom command *)
let get_custom_command_response num_res solver timeout = 

  (* Get response from solver *)
  let response = expr_of_solver_lexbuf solver in

  (* Get result only upon success *)
  match get_custom_command_response_of_sexpr response with 

    (* First line of reply is success status *)
    | Success -> 

      (* Get remaining results *)
      let result = get_custom_command_result solver [] num_res in

      (* Return response and result *)
      (Success, result) 
        
    (* First line of reply is neither error nor success *)
    | NoResponse -> 

      (* Use already consumed first result and get remaining results *)
      let result = 
        response :: get_custom_command_result solver [] (pred num_res) 
      in
      
      (* Return success and result *)
      (Success, result) 
        
    (* First line of reply is error or unsupported *)
    | (Error _ as r) 
    | (Unsupported as r) -> 

      (* Return response and empty result *)
      (r, []) 


let get_any_response solver timeout = function
  | NoRespCmd -> NoResp
  | Cmd -> Resp (get_command_response solver timeout)
  | CheckSatCmd -> CheckSatResp (get_check_sat_response solver timeout)
  | GetValueCmd -> GetValueResp (get_get_value_response solver timeout)
  | GetUnsatCoreCmd ->
     GetUnsatCoreResp (get_get_unsat_core_response solver timeout)
  | CustomCmd num_res ->
     CustomResp (get_custom_command_response num_res solver timeout)


let pp_print_any_response ppf = function
  | NoResp -> ()
  | Resp res -> SMTExpr.pp_print_response ppf res
  | CheckSatResp res -> SMTExpr.pp_print_check_sat_response ppf res
  | GetValueResp res -> SMTExpr.pp_print_get_value_response ppf res
  | GetUnsatCoreResp (r, c) ->
     Format.fprintf ppf "%a@,(@[<hv 1>%a@])"
             SMTExpr.pp_print_response r
             (pp_print_list Format.pp_print_string "@ ") c
  | CustomResp (r, e) ->
     Format.fprintf ppf "%a@,(@[<hv 1>%a@])" 
             SMTExpr.pp_print_response r
             (pp_print_list HStringSExpr.pp_print_sexpr "@ ") e  
  | Comment s -> 
    
    (* Use newline function of Format module instead of \n in string,
       necessary to preserve comment character at beginning of line *)
    let rec aux p = 
      try 
        let newline_pos = String.index_from s p '\n' in
        Format.pp_print_string 
          ppf
          (String.sub s p (newline_pos - p));
        Format.pp_print_newline ppf ();
        aux (newline_pos + 1)
      with Not_found -> 
        Format.pp_print_string 
          ppf
          (String.sub s p (String.length s - p))
    in

    aux 0 

        

(* Send the command to the solver instance *)
let send_command 
    ({ solver_stdin = solver_stdin; } as solver)
    cmd_type
    command 
    timeout = 

  (* Get an output channel to write to solver's stdin *)
  let solver_stdin_ch = Unix.out_channel_of_descr solver_stdin in

  (* Get a pretty-printing formatter writing to solver's stdin *)
  let solver_stdin_formatter = 
    Format.formatter_of_out_channel solver_stdin_ch 
  in

  (* Send command to solver *)
  Format.pp_print_string solver_stdin_formatter command;

  (* Print newline and flush formatter *)
  Format.pp_print_newline solver_stdin_formatter ();

  (* Wait for response without timeout *)
  let res = get_any_response solver timeout cmd_type in

  (* Return response *)
  res

(* Samme as above but additionnaly trace the commands and responses *)
let send_command_and_trace solver cmd_type command timeout = 

  (* Trace the command *)
  solver.solver_trace_cmd command;

  (* Send the command to the solver and get the response *)
  let res = send_command solver cmd_type command timeout in

  (* Trace the response of the solver *)
  solver.solver_trace_res res;

  res

(* Execute a command and return the response *)
let execute_command solver command timeout = 

  match send_command_and_trace solver Cmd command timeout with
  | Resp res -> res
  | _ -> assert false

(* Execute a command without logging in the trace and return the response *)
let execute_command_no_trace solver command timeout = 

  match send_command solver Cmd command timeout with
  | Resp res -> res
  | _ -> assert false

  
(* Execute a command and do not parse a response *)
let execute_command_no_response solver command timeout = 

  match send_command_and_trace solver NoRespCmd command timeout with
  | NoResp -> NoResponse
  | _ -> assert false


(* Execute a check-sat command and return the response *)
let execute_check_sat_command solver command timeout = 

  match send_command_and_trace solver CheckSatCmd command timeout with
  | CheckSatResp res -> res
  | _ -> assert false


(* Execute a get-value command and return the response *)
let execute_get_value_command solver command timeout = 

  match send_command_and_trace solver GetValueCmd command timeout with
  | GetValueResp res -> res
  | _ -> assert false


(* Execute a get-unsat-core command and return the response *)
let execute_get_unsat_core_command solver command timeout = 

  match send_command_and_trace solver GetUnsatCoreCmd command timeout with
  | GetUnsatCoreResp res -> res
  | _ -> assert false


(* Execute a custom command and return the response *)
let execute_custom_command' solver command timeout num_res = 

  match send_command_and_trace solver (CustomCmd num_res) command timeout with
  | CustomResp res -> res
  | _ -> assert false  


(* ********************************************************************* *)
(* Commands                                                              *)
(* ********************************************************************* *)


(* Declare a new function symbol *)
let declare_fun solver fun_symbol arg_sorts res_sort = 

  let cmd = 
    Format.sprintf 
      "@[<hv 1>(declare-fun@ %s@ @[<hv 1>%s@]@ %s)@]" 
      fun_symbol
      (paren_string_of_string_list (List.map string_of_sort arg_sorts))
      (string_of_sort res_sort)
  in

  (* Send command to the solver without timeout *)
  execute_command solver cmd 0


(* Define a new function symbol as an abbreviation for an expression *)
let define_fun solver fun_symbol arg_vars res_sort defn = 

  let cmd =
    Format.asprintf
      "@[<hv 1>(define-fun@ %s@ @[<hv 1>(%a)@]@ %s@ %a)@]" 
      fun_symbol
      (pp_print_list
         (fun ppf var -> 
          Format.fprintf ppf "(%s %s)" 
                         (Var.string_of_var var)
                         (string_of_sort (Var.type_of_var var)))
         "@ ")
      arg_vars
      (string_of_sort res_sort)
      pp_print_expr defn
  in

  (* Send command to the solver without timeout *)
  execute_command solver cmd 0


(* Assert the expression *)
let assert_expr solver expr = 

  let cmd = 
    Format.sprintf
      "@[<hv 1>(assert@ @[<hv>%s@])@]" 
      (string_of_expr expr) in
  
  (* Send command to the solver without timeout *)
  execute_command solver cmd 0

    
(* Push a number of empty assertion sets to the stack *)
let push solver scopes = 

  let cmd = Format.sprintf "@[<hv 1>(push@ %d)@]" scopes in

  (* Send command to the solver without timeout *)
  execute_command solver cmd 0


(* Pop a number of assertion sets from the stack *)
let pop solver scopes  = 

  let cmd = Format.sprintf "@[<hv 1>(pop@ %d)@]" scopes in

  (* Send command to the solver without timeout *)
  execute_command solver cmd 0


(* Check satisfiability of the asserted expressions *)
let check_sat ?(timeout = 0) solver = 

  let cmd = match timeout with 
    | i when i <= 0 -> Format.sprintf "@[<hv 1>(check-sat)@]"
    | _ -> check_sat_limited_cmd timeout
  in

  (* Send command to the solver without timeout *)
  execute_check_sat_command solver cmd 0


(* Check satisfiability of the asserted expressions *)
let check_sat_assuming solver exprs =
  (* Retrieving command from solver info. *)
  let command = match Flags.smtsolver () with 
    | `Z3_SMTLIB -> "check-sat"
    | `CVC4_SMTLIB -> failwith "CVC4 does not support check_sat_assuming."
    | `MathSat5_SMTLIB -> failwith "MathSat5 does not support check_sat_assuming."
    | `Yices_SMTLIB -> failwith "Yices does not support check_sat_assuming."
    | _ -> 
       (* (Event.log `INVMAN L_fatal "Not using an SMTLIB solver"); *)
       failwith "SMTLIBSolver.check_sat_assuming"
  in

  (* Building the complete command. *)
  let cmd =
    exprs
    |> List.fold_left
         ( fun s e -> 
           Format.sprintf "%s %s" s (string_of_expr e) )
         command
    |> Format.sprintf "(%s)"
  in

  (* Send command to the solver without timeout *)
  execute_check_sat_command solver cmd 0


(* Check satisfiability of the asserted expressions under the given
   assumptions *)
let check_sat_assumptions solver assumptions = 

  (* Create command per solver *)
  let cmd = check_sat_assumptions_cmd assumptions in

  (* Send command to the solver without timeout *)
  execute_check_sat_command solver cmd 0


(* Get values of expressions in the model *)
let get_value solver expr_list = 

  (* The command to send to the solver *)
  let cmd = 
    Format.asprintf
      "@[<hv 1>(get-value@ @[<hv 1>(%a)@])@]" 
      (pp_print_list pp_print_expr "@ ") expr_list;
  in

  (* Send command to the solver without timeout *)
  execute_get_value_command solver cmd 0


(* Get an unsatisfiable core *)
let get_unsat_core solver = 

  (* The command to send to the solver *)
  let cmd = 
    Format.sprintf "@[<hv 1>(get-unsat-core)@]"
  in

  (* Send command to the solver without timeout *)
  execute_get_unsat_core_command solver cmd 0


(* Execute a custom command and return the response *)
let execute_custom_command solver cmd args num_res = 

  (* The command to send to the solver *)
  let cmd = 
    if args = [] then 
      Format.sprintf 
        "@[<hv 1>(%s)@]" 
        cmd
    else
      Format.sprintf 
        "@[<hv 1>(%s@ %s)@]" 
        cmd
        (string_of_t (pp_print_list pp_print_custom_arg " ") args)
  in

  (* Send command to the solver without timeout *)
  execute_custom_command' solver cmd 0 num_res 


(* Execute a custom command and return the response *)
let execute_custom_check_sat_command cmd solver = 

  (* Send command to the solver without timeout *)
  execute_check_sat_command solver cmd 0


(* ********************************************************************* *)
(* Solver commands tracing                                               *)
(* ********************************************************************* *)

(* Formatter writing to SMT trace file *)
let create_trace_ppf id = 

  (* Tracing of SMT commands enabled? *)
  if Flags.smt_trace () then 
    
    (* Name of SMT trace file *)
    let trace_filename = 
      Filename.concat
        (Flags.smt_trace_dir ())
        (Format.sprintf "%s.%s.%d.smt2" 
                        (Filename.basename (Flags.input_file ()))
                        (suffix_of_kind_module (Event.get_module ()))
                        id)
    in
    
    try
      
      (* Open file for output, may fail *)
      let trace_oc = open_out trace_filename in
      
      Event.log L_debug
                "Tracing output of SMT solver instace to %s"
                trace_filename;

      (* Return formatter *)
      Some (Format.formatter_of_out_channel trace_oc)
           
    (* Silently fail *)
    with Sys_error e -> 

      Event.log L_debug
                "Failed to open trace file for SMT solver %s"
                e;
      
      None 
        
  else

    (* Do not trace SMT commands *)
    None 

(* Tracing of commands *)
let trace_cmd solver_ppf cmd = match solver_ppf with
  | Some ppf -> Format.fprintf ppf "%s@." cmd
  | None -> ()

(* Tracing of responses *)
let trace_res solver_ppf res = match solver_ppf with
  | Some ppf ->
     let fmt_out_fun = Format.pp_get_formatter_out_functions ppf () in

     let reset_ppf ppf = 
       Format.fprintf ppf "@?";
       Format.pp_set_formatter_out_functions ppf fmt_out_fun;
       Format.fprintf ppf "@.";
       Format.fprintf ppf "@\n"
     in

     Format.fprintf ppf "@?";

     Format.pp_set_formatter_out_functions 
       ppf 
       { fmt_out_fun with 
         Format.out_newline = 
           fun () -> fmt_out_fun.Format.out_string "\n;; " 0 4  };

     Format.kfprintf reset_ppf ppf ";; %a" pp_print_any_response res

  | None -> ()


(* Output a comment into the trace *)
let trace_comment solver comment = 
  solver.solver_trace_res (Comment comment)


(* ********************************************************************* *)
(* Creating and deleting solver instances                                *)
(* ********************************************************************* *)


(* Create an instance of the solver *)
let create_instance
    ?produce_assignments
    ?produce_models
    ?produce_proofs
    ?produce_cores
    logic
    id =

  (* Get autoconfigured configuration *)
  let ({ solver_cmd = solver_cmd } as config) = config_of_flags () in

  (* Name of executable is first argument 

     TODO: expand ~ *)
  let solver_executable = solver_cmd.(0) in

  (* Create pipes for input, output and error output *)
  let solver_stdin_in, solver_stdin_out = Unix.pipe () in
  let solver_stdout_in, solver_stdout_out = Unix.pipe () in 
  let solver_stderr_in, solver_stderr_out = Unix.pipe () in 

  (* Create solver process *)
  let solver_pid = 
    Unix.create_process 
      solver_executable 
      solver_cmd 
      solver_stdin_in
      solver_stdout_out
      solver_stderr_out
  in

  (* Close our end of the pipe which has been duplicated by the
     process *)
  Unix.close solver_stdin_in;
  Unix.close solver_stdout_out; 
  Unix.close solver_stderr_out; 

  (* Get an output channel to read from solver's stdout *)
  let solver_stdout_ch = Unix.in_channel_of_descr solver_stdout_in in

  (* Create a lexing buffer on solver's stdout *)
  let solver_lexbuf = Lexing.from_channel solver_stdout_ch in

  (* Create trace functions *)
  let trace_ppf = create_trace_ppf id in
  (* TODO change params to erase pretty printing -- Format.pp_set_margin ppf *)
  let ftrace_cmd = trace_cmd trace_ppf in
  let ftrace_res = trace_res trace_ppf in
  
  (* Create the solver instance *)
  let solver =
    { solver_config = config;
      solver_pid = solver_pid;
      solver_stdin = solver_stdin_out; 
      solver_lexbuf = solver_lexbuf; 
      solver_stdout = solver_stdout_in; 
      solver_stderr = solver_stderr_in;
      solver_trace_cmd = ftrace_cmd;
      solver_trace_res = ftrace_res; }
  in

  (* Print success after commands, default is false per SMTLIB
     specification *)
  (match 
     let cmd = "(set-option :print-success true)" in
     (debug smt "%s" cmd in
      execute_command solver cmd 0)
   with 
     | Success -> () 
     | _ -> raise (Failure ("Cannot set option print-success")));

  (* Interactive mode not needed for MathSAT5 *)
  (match Flags.smtsolver () with 
    | `Z3_SMTLIB ->

      (* Run in interactive mode *)
      (match 
         let cmd = "(set-option :interactive-mode true)" in
         (debug smt "%s" cmd in
          execute_command_no_trace solver cmd 0)
       with 
         | Success -> () 
         | _ -> raise (Failure ("Cannot set option interactive-mode")))

    | _ -> ()

  );

  (* Produce assignments to be queried with get-values, default is
     false per SMTLIB specification *)
  (match Flags.smtsolver () with 
    | `Yices_SMTLIB -> ()
    | _ -> 

      (match produce_models with
        | None -> ()
        | Some o ->
          (match 
             let cmd =
               Format.sprintf "(set-option :produce-models %B)" o 
             in
             (debug smt "%s" cmd in
              execute_command solver cmd 0)
           with 
             | Success -> () 
             | _ -> raise (Failure ("Cannot set option produce-models")))));

  (* Produce assignments to be queried with get-values, default is
     false per SMTLIB specification *)
  (match Flags.smtsolver () with 
    | `Yices_SMTLIB -> ()
    | _ -> 

      (match produce_assignments with
        | None -> ()
        | Some o ->
          (match 
             let cmd =
               Format.sprintf "(set-option :produce-assignments %B)" o 
             in
             (debug smt "%s" cmd in
              execute_command solver cmd 0)
           with 
             | Success -> () 
             | _ -> raise
                      (Failure ("Cannot set option produce-assignments")))));

  (* Produce unsatisfiable cores, default is false per SMTLIB
     specification *)
  (match Flags.smtsolver () with 
    | `Yices_SMTLIB -> ()
    | _ -> 
      (match produce_cores with
        | None -> ()
        | Some o ->
          (match 
             let cmd =
               Format.sprintf "(set-option :produce-unsat-cores %B)" o in
             (debug smt "%s" cmd in
              execute_command solver cmd 0)
           with 
             | Success -> () 
             | _ -> 
               raise
                 (Failure ("Cannot set option produce-unsat-cores")))));
      
  (* Set logic *)
  (match logic with 
    | `detect -> () 
    | _ -> 
      (match
         let cmd = Format.sprintf "(set-logic %s)" (string_of_logic logic) in
         (debug smt "%s" cmd in
          execute_command solver cmd 0)
       with 
         | Success -> () 
         | _ -> 
           raise 
             (Failure 
                ("Cannot set logic " ^ (string_of_logic logic)))));

  (* Return solver instance *)
  solver

    

(* Delete the solver instance by sending the exit command and wait for
   the solver process to exit *)
let delete_instance 
    ({ solver_pid = solver_pid ;
       solver_stdin = solver_stdin ;
       solver_stdout = solver_stdout;
       solver_stderr = solver_stderr } as solver) =

  (* Execute exit command, do not parse response

     If we are interrupted while waiting for a solver response, the
     response to (exit) will be the response to the previous
     command. Hence, ignore these stale respones on the output
     channel *)

  let _ = execute_command_no_response solver "(exit)" 0 in

  (* Wait for process to terminate *)
  let _, process_status = Unix.waitpid [] solver_pid in

  (
    
    (* Check termination status of solver *)
    match process_status with

      (* Exit with code *)
      | Unix.WEXITED c -> 
        (debug smt "Solver exited with code %d" c end)
          
      (* Killed by signal *)
      | Unix.WSIGNALED s -> 
        (debug smt "Solver killed with signal %d" s end)
          
      (* Stopped by signal *)
      | Unix.WSTOPPED s -> 
        (debug smt "Solver stopped by signal %d" s end)

  );

  (* Close file descriptors of solver *)
  Unix.close solver_stdin;
  Unix.close solver_stdout;
  Unix.close solver_stderr

   
(* ********************************************************************* *)
(* Toplevel testing code                                                 *)
(* ********************************************************************* *)

(*

let pp_print_expr_pair ppf (s, t) = 
  pp_print_expr ppf s;
  Format.pp_print_space ppf ();
  pp_print_expr ppf t


let test () = 

  let config = 
    { solver_cmd = "/home/chris/z3/bin/external/z3 -smt2 -in -v:5"; 
      debug_channel = Some Pervasives.stdout }
  in

  let solver = 
    create_instance 
      config
      ~produce_models:true
      `QF_LIA
  in

  ignore (declare_fun solver "a" [] (sort_expr_of_sort INT));
  
  ignore (declare_fun solver "a" [] (sort_expr_of_sort INT));

  let e1 = Tree.L (`UF "a") in
  let e2 = Tree.N (`EQ, [e1; Tree.L (`NUMERAL (numeral_of_int 1))]) in

  let res = assert_expr solver e2 in 
  Format.printf ";; %a@." pp_print_response res;

  let res = check_sat solver in 
  Format.printf ";; %a@." pp_print_check_sat_response res;

  (match get_value solver [e1; e2] with 
    | Success, v -> 
      Format.printf 
        "%a@." 
        (pp_print_list pp_print_expr_pair " ") 
        v
    | r, _ -> 
      Format.printf ";; %a@." pp_print_response r
  );

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
