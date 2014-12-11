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
module Conv = SMTExpr.Yices
open Conv

(* ********************************************************************* *)
(* Types                                                                 *)
(* ********************************************************************* *)

(* Map of sexprs to store models *)
module SMTExprMap = Map.Make(Term)
       
type any_response =
  | NoResp
  | Resp of response
  | CheckSatResp of check_sat_response
  | GetValueResp of (response * (SMTExpr.t * SMTExpr.t) list)
  | GetUnsatCoreResp of (response * (string list))
  | CustomResp of (response * (HStringSExpr.t list))

type command_type =
  | NoRespCmd
  | Cmd
  | CheckSatCmd
  | GetValueCmd
  | GetUnsatCoreCmd
  | CustomCmd of int

type yices_state =
  | YNone
  | YError
  | YUnsat of YicesResponse.yices_id list
  | YModel of SMTExpr.t SMTExprMap.t

                   
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

      mutable solver_state : yices_state;
      (* Used to record response to last command from which to extract values or
         unsat cores. *)

      mutable solver_last_id : YicesResponse.yices_id;
      (* Yices identifier that was last asserted. Remember to reset this to 0
         when restarting the solver or deleting the instance. *)

      solver_id_names : (YicesResponse.yices_id, int) Hashtbl.t;
      (* Associates yices assertion ids to smtlib names of named formulas *)

      solver_push_stack : YicesResponse.yices_id Stack.t;
      (* The internal push stack of assertions identiers. This should be
         cleared on deletion or resets. *)
    }



(* ********************************************************************* *)
(* Configurations                                                        *)
(* ********************************************************************* *)

(* Configuration for Yices *)

let config_yices () = 

  (* Path and name of Z3 executable *)
  let yices_bin = Flags.yices_bin () in

  { solver_cmd = [| yices_bin |] }


(* Configuration for current SMT solver *)
let config_of_flags () = config_yices ()


(* Command to limit check-sat to run for the given numer of ms at most *)
let check_sat_limited_cmd ms =
    (* (Event.log `INVMAN L_fatal "Not using an SMTLIB solver"); *)
    failwith "Yices.check_sat_limited_cmd"


(* Indicates whether the solver supports the check-sat-assuming
   command. *)
let check_sat_assuming_supported () = true


(* Command to run check-sat with given assumptions *)
let check_sat_assumptions_cmd assumptions =
  failwith "check-sat with assumptions not implemented for Yices"


let next_id solver =
  solver.solver_last_id
  |> YicesResponse.int_of_yices_id
  |> succ
  |> YicesResponse.yices_id_of_int  


let name_of_yices_id solver id =
  let n = Hashtbl.find solver.solver_id_names id in
  "t"^(string_of_int n)
       
    


let register_unsat_core solver uc =
  (* Get the corresponding SMTLIB names *)
  solver.solver_state <- YUnsat uc


let register_model solver model =
  let m =
    List.fold_left
      (fun acc (e, v) ->
       let e_smte = Conv.expr_of_string_sexpr e in
       let v_smte = Conv.expr_of_string_sexpr v in
       (* Format.eprintf "in model (= %a %a)@." *)
       (*                pp_print_expr e_smte *)
       (*                pp_print_expr v_smte; *)
       SMTExprMap.add e_smte v_smte acc)
      SMTExprMap.empty model in
  solver.solver_state <- YModel m

(* ********************************************************************* *)
(* Helper functions to execute commands                                  *)
(* ********************************************************************* *)

(* Default values for types (used to compensate for yices' incomplete models) *)
let default_type_term =
  let open Type in
  let open Term in
  function
  (* Default boolean: false *)
  | Bool -> mk_bool false
  (* Default integer: 0 *)
  | Int -> mk_num Numeral.zero
  (* Take the first value of the range as its default *)
  | IntRange (i, _) -> mk_num i
  (* Default real: 0.0 *)
  | Real -> mk_dec Decimal.zero
  (* Take first constructor of scalar type as its default *)
  | Scalar (_, c::_) ->
     mk_const (Symbol.mk_symbol (`UF (UfSymbol.uf_symbol_of_string c)))
  (* Take the bitvector 00000000...0 as default *)
  | BV n -> mk_bv (Lib.bitvector_of_string (String.make n '0'))
  (* We shouldn't ask default value for a whole array *)
  | Array _ -> failwith "No defaut value for arrays"
  | Scalar (_, []) -> failwith "No defaut value for empty scalars"

(* Default SMTExpr.t value for a type *)
let default_of_type ty =
  ty
  |> Type.node_of_type
  |> default_type_term
  |> Conv.smtexpr_of_term
    

(* Read the answer returned by yices *)                   
let parse_yices_output { solver_lexbuf = lexbuf } =
  (* Parse yices response and return *)
  (* Format.eprintf "parsing <%s>" lexbuf.Lexing.lex_buffer; *)
  YicesParser.resp YicesLexer.token lexbuf


(* Parse the solver response to a command *)
let get_command_response solver timeout = 

  (* Return response *)
  match parse_yices_output solver with
    
  | YicesResponse.YSuccess ->
     Success
    
  | YicesResponse.YNoResp ->
     NoResponse (* or success maybe *)

  | YicesResponse.YError msg ->
     solver.solver_state <- YError;
     Error msg
     
  | _ ->
     failwith "Yices returned an unexpected response"


(* Parse the solver response to a check-sat command *)
let get_check_sat_response solver timeout = 

  (* Return response *)
  match parse_yices_output solver with
    
  | YicesResponse.YRespSat model ->
     register_model solver model;
     Sat
       
  | YicesResponse.YRespUnknown model ->
     register_model solver model;
     Unknown
       
  | YicesResponse.YRespUnsat uc ->
     register_unsat_core solver uc;
     Unsat

  | YicesResponse.YSuccess ->
     Response Success

  | YicesResponse.YNoResp ->
     Response NoResponse

  | YicesResponse.YError msg ->
     solver.solver_state <- YError;
     Response (Error msg)


(* Get n S-expressions from the solver *)
let rec get_custom_command_result solver accum i =
  failwith "Yices get_custom_command_result not implemented"


(* Parse the solver response to a custom command *)
let get_custom_command_response num_res solver timeout = 
  failwith "Yices get_custom_command_response not implemented"



let get_any_response solver timeout = function
  | NoRespCmd -> NoResp
  | Cmd -> Resp (get_command_response solver timeout)
  | CheckSatCmd -> CheckSatResp (get_check_sat_response solver timeout)
  | CustomCmd num_res ->
     CustomResp (get_custom_command_response num_res solver timeout)
  | GetUnsatCoreCmd | GetValueCmd -> assert false


let pp_print_any_response ppf = function
  | NoResp -> ()
  | Resp res -> pp_print_response ppf res
  | CheckSatResp res -> pp_print_check_sat_response ppf res
  | GetValueResp res -> pp_print_get_value_response ppf res
  | GetUnsatCoreResp (r, c) ->
     Format.fprintf ppf "%a@,(@[<hv 1>%a@])"
             pp_print_response r
             (pp_print_list Format.pp_print_string "@ ") c
  | CustomResp (r, e) ->
     Format.fprintf ppf "%a@,(@[<hv 1>%a@])" 
             pp_print_response r
             (pp_print_list HStringSExpr.pp_print_sexpr "@ ") e  


(* Send the command to the solver instance *)
let send_command 
      ({ solver_stdin = solver_stdin; } as solver)
      ~wait
      cmd_type
      command 
      timeout = 

  (* Get an output channel to write to solver's stdin *)
  let solver_stdin_ch = Unix.out_channel_of_descr solver_stdin in

  (* Get a pretty-printing formatter writing to solver's stdin *)
  let solver_stdin_formatter = 
    Format.formatter_of_out_channel solver_stdin_ch 
  in

  (* Add the success marker if we need to parse the response *)
  let cmd =
    if wait then
      Format.sprintf "%s\n(echo \"%s\\n\")" command YicesResponse.success
    else command
  in
  
  (* Send command to solver *)
  Format.pp_print_string solver_stdin_formatter cmd;

  (* Print newline and flush formatter *)
  Format.pp_print_newline solver_stdin_formatter ();

  (* Wait for response without timeout *)
  if wait then get_any_response solver timeout cmd_type
  else Resp Success


(* Samme as above but additionnaly trace the commands and responses *)
let send_command_and_trace ~wait solver cmd_type command timeout = 

  (* Trace the command *)
  solver.solver_trace_cmd command;

  (* Send the command to the solver and get the response *)
  let res = send_command ~wait solver cmd_type command timeout in

  (* Trace the response of the solver *)
  solver.solver_trace_res res;

  res

(* Execute a command and return the response *)
let execute_command solver command timeout = 

  match send_command_and_trace ~wait:true solver Cmd command timeout with
  | Resp res -> res
  | _ -> assert false

(* Execute a command without logging in the trace and return the response *)
let execute_command_no_trace solver command timeout = 

  match send_command ~wait:true solver Cmd command timeout with
  | Resp res -> res
  | _ -> assert false

  
(* Execute a command and do not parse a response *)
let execute_command_no_response solver command timeout = 

  match send_command_and_trace ~wait:false solver NoRespCmd command timeout with
  | NoResp | Resp Success -> Success
  | _ -> assert false


(* Execute a check-sat command and return the response *)
let execute_check_sat_command solver command timeout = 

  match send_command_and_trace ~wait:true solver CheckSatCmd command timeout with
  | CheckSatResp res -> res
  | _ -> assert false


(* Execute a custom command and return the response *)
let execute_custom_command' solver command timeout num_res = 

  match
    send_command_and_trace ~wait:true
       solver (CustomCmd num_res) command timeout with
  | CustomResp res -> res
  | _ -> assert false  


(* ********************************************************************* *)
(* Helper functions for printing commands                                *)
(* ********************************************************************* *)

(* Print function type *)
let pp_print_function_type ppf (arg_sorts, res_sort) =
  
  match arg_sorts with
  (* Not an arrow type (constant symbol) *)
  | [] -> Format.fprintf ppf "%s" (string_of_sort res_sort)

  (* Arrow type *)
  | _ ->  Format.fprintf ppf "@[<hv 1>(-> @[%a@]@ %s)@]"
                         (pp_print_list Format.pp_print_string "@ ")
                           (List.map string_of_sort arg_sorts)
                         (string_of_sort res_sort)



(* Print one binding, i.e. variable with type annotation *)
let pp_print_binding ppf var =
  Format.fprintf ppf "%s :: %s"
                 (Var.string_of_var var)
                 (string_of_sort (Var.type_of_var var))


(* Print a list of bindings, i.e. variables with their type *)
let pp_print_bindings ppf vars =
  match vars with
  (* Bindings cannot be empty *)
  | [] -> assert false
  | _ ->
     Format.fprintf ppf "(@[<hv 1>%a@])"
                    (pp_print_list pp_print_binding "@ ") vars

(* Print lambda expression *)
let pp_print_lambda ppf (arg_vars, defn)  =
  Format.fprintf ppf "(lambda@ @[<hv 1>%a@]@ %a)"
                 pp_print_bindings arg_vars
                 pp_print_expr defn


(* ********************************************************************* *)
(* Commands                                                              *)
(* ********************************************************************* *)

(* Declare a new function symbol *)
let declare_fun solver fun_symbol arg_sorts res_sort = 

  let cmd = 
    Format.asprintf 
      "@[<hv 1>(define@ %s ::@ @[<hv 1>%a@])@]"
      fun_symbol pp_print_function_type (arg_sorts, res_sort)
  in

  (* Send command to the solver without timeout *)
  execute_command solver cmd 0


(* Define a new function symbol as an abbreviation for an expression *)
let define_fun solver fun_symbol arg_vars res_sort defn =

  (* Get type of arguments *)
  let arg_sorts = List.map Var.type_of_var arg_vars in
  
  let cmd =
    Format.asprintf
      "@[<hv 1>(define@ %s ::@ @[<hv 1>%a@]@ @[<hv 1>%a@])@]" 
      fun_symbol
      pp_print_function_type (arg_sorts, res_sort)
      pp_print_lambda (arg_vars, defn)
  in

  (* Send command to the solver without timeout *)
  execute_command solver cmd 0


(* Assert the expression *)
let assert_expr solver expr = 

  (* Take the next id *)
  let id = next_id solver in
  
  let t = Conv.term_of_smtexpr expr in
  let t', name_info =
    if Term.is_named t then
      (* Open the named term and map the yices id to the name *)
      begin
        let name = Term.name_of_named t in
        Hashtbl.add solver.solver_id_names id name; 
        Term.term_of_named t,
        Format.asprintf "[id: %a, name: t%d]"
                       YicesResponse.pp_print_yices_id id name
      end
    else t, Format.asprintf "[id: %a]" YicesResponse.pp_print_yices_id id in
  let expr = Conv.smtexpr_of_term t' in
  

  let cmd = 
    Format.asprintf
      "@[<hv 1>(assert+@ @[<hv>%s@])@]\n;; %s" 
      (string_of_expr expr)
      name_info
  in
  
  (* Send command to the solver without timeout *)
  let res = execute_command solver cmd 0 in

  (* Register the new asserted id once the solver has asserted it
     and update state to indicate context has been modified *)
  solver.solver_last_id <- id;
  solver.solver_state <- YNone;
  
  (* Return result of command *)
  res


(* Retract an assertion from the context of Yices *)
let retract solver id =

  let cmd = Format.asprintf
              "@[<hv 1>(retract %a)@]"
              YicesResponse.pp_print_yices_id id
  in

  (* Send command to the solver without timeout *)
  ignore(execute_command solver cmd 0)

  

(* Push one empty assertion to the stack *)
let push_1 solver =
  let cmd = Format.sprintf "@[<hv 1>(push)@]" in

  (* Send command to the solver without timeout *)
  execute_command solver cmd 0
  

(* Push a number of empty assertion sets to the stack *)
let rec push solver = function
  | 0 -> Success
  | 1 -> push_1 solver
  | n when n > 0 ->
     (match push_1 solver with
      | Success | NoResponse -> ()
      | _ -> failwith "Could not push");
     push solver (pred 1)
  | _ -> assert false


(* Pop one empty assertion to the stack *)
let pop_1 solver =
  let cmd = Format.sprintf "@[<hv 1>(pop)@]" in

  (* Send command to the solver without timeout *)
  execute_command solver cmd 0
  

(* Pop a number of empty assertion sets to the stack *)
let rec pop solver = function
  | 0 -> Success
  | 1 -> pop_1 solver
  | n when n > 0 -> 
     (match pop_1 solver with
      | Success | NoResponse -> ()
      | _ -> failwith "Could not pop");
     pop solver (pred 1)
  | _ -> assert false


(* Same as before but more efficient *)
let fast_push_1 solver =
  Stack.push solver.solver_last_id solver.solver_push_stack

let rec fast_push solver = function
  | 0 -> ()
  | 1 -> fast_push_1 solver
  | n when n > 0 -> fast_push_1 solver; fast_push solver (pred 1)
  | _ -> assert false

(* Get last element of multiple pops *)
let rec popn_stack_ids s = function
  | 1 -> Stack.pop s
  | n when n > 0 ->
     ignore (Stack.pop s); popn_stack_ids s (pred n)
  | _ -> assert false
                   
let fast_pop solver = function
  | 0 -> ()
  | n when n > 0 ->
     (try
         let id = popn_stack_ids solver.solver_push_stack n in
         for i = YicesResponse.int_of_yices_id solver.solver_last_id
             downto YicesResponse.int_of_yices_id id + 1 do
           retract solver (YicesResponse.yices_id_of_int i)
         done
       with Stack.Empty -> failwith "Yices stack empty: cannot pop")
  | _ -> failwith "Yices: cannot pop negative number of times"
                                  


(* Check satisfiability of the asserted expressions *)
let check_sat ?(timeout = 0) solver = 

  let cmd = match timeout with 
    | i when i <= 0 -> Format.sprintf "@[<hv 1>(check)\n@]"
    | _ -> check_sat_limited_cmd timeout
  in

  (* Send command to the solver without timeout *)
  execute_check_sat_command solver cmd 0


(* Check satisfiability of the asserted expressions *)
let check_sat_assuming solver exprs =

  (* We use retract feature of Yices to keep internal context *)
  fast_push solver 1;
  let res =
    List.fold_left (fun acc expr -> assert_expr solver expr) NoResponse exprs
  in
  match res with
  | Error _ | Unsupported -> Response res
  | Success
  | NoResponse ->
     let res = check_sat ~timeout:0 solver in
     (* Remove assumed expressions from context while keeping state *)
     fast_pop solver 1;
     res


(* Get values of expressions in the model *)
let get_value solver expr_list = 

  (* get-value is not supported by Yices so we simulate the command by looking
     up values in the registered model of the solver state *)
  
  (* The fake SMTLIB command  *)
  let cmd = 
    Format.asprintf
      "@[<hv 1>(get-value@ @[<hv 1>(%a)@])@]" 
      (pp_print_list pp_print_expr "@ ") expr_list;
  in

  (* Trace the fake command but comment it *)
  solver.solver_trace_cmd (";; "^cmd);

  match solver.solver_state with
  | YModel model ->

     let smt_expr_values =
       List.fold_left
         (fun acc e ->
          let v =
            try SMTExprMap.find e model
            with Not_found ->
              (* If the variable is not found in the model, use the default
                 value for its type *)
              default_of_type (Var.type_of_var (Conv.var_of_smtexpr e))
          in
          (e, v) :: acc) [] expr_list
     in

     (* construct the response with the desired values *)
     let res = Success, smt_expr_values in
       
     (* Trace the response of the solver *)
     solver.solver_trace_res (GetValueResp res);

     (* return the computed values *)
     res

  | _ -> failwith "Yices: No model to compute get-values"


(* Get an unsatisfiable core *)
let get_unsat_core solver = 

  (* get-unsat-core is not supported by Yices so we simulate the command by
     looking up names in the registered unsat core of the solver state *)

  (* The fake SMTLIB command  *)
  let cmd = 
    Format.sprintf "@[<hv 1>(get-unsat-core)@]"
  in
  
  (* Trace the fake command but comment it *)
  solver.solver_trace_cmd (";; "^cmd);

  match solver.solver_state with
  | YUnsat uc ->

     (* Get the names for the unsat core ids *)
     let uc_names =
       List.fold_left (fun acc id ->
                 try name_of_yices_id solver id :: acc
                 with Not_found ->
                    (* This means that this assertion was not originally named
                       so we're not interrested in its appearing in the
                       unsat core. Ignore it. *)
                   acc) [] uc in

     let res = Success, uc_names in
     
     (* Trace the response of the solver *)
     solver.solver_trace_res (GetUnsatCoreResp res);

     (* return the computed values *)
     res

  | _ -> failwith "Yices: No unsat core to return"


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
(* Creating and deleting solver instances                                *)
(* ********************************************************************* *)


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
        (Format.sprintf "%s.%s.%d.ys" 
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
let trace_cmd = function
  | Some ppf -> fun cmd -> Format.fprintf ppf "%s@." cmd
  | None -> fun _ -> ()

(* Tracing of responses *)
let trace_res = function
  | Some ppf ->
     let fmt_out_fun = Format.pp_get_formatter_out_functions ppf () in

     let reset_ppf ppf = 
       Format.fprintf ppf "@?";
       Format.pp_set_formatter_out_functions ppf fmt_out_fun;
       Format.fprintf ppf "@.";
       Format.fprintf ppf "@\n"
     in

     Format.pp_set_formatter_out_functions 
       ppf 
       { fmt_out_fun with 
         Format.out_newline = 
           fun () -> fmt_out_fun.Format.out_string "\n;; " 0 4  };

     fun res ->
     Format.kfprintf reset_ppf ppf ";; %a" pp_print_any_response res

  | None -> fun _ -> ()


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
      solver_trace_res = ftrace_res;
      solver_state = YNone;
      solver_last_id = YicesResponse.yices_id_of_int 0;
      solver_id_names = Hashtbl.create 19;
      solver_push_stack = Stack.create ();
    }
  in

  (* Produce assignments to be queried with get-values, default is
     false per SMTLIB specification *)
  
  let evidence =
    (match produce_cores with Some o -> o | None -> false) ||
    (match produce_assignments with Some o -> o | None -> false) ||
    (match produce_models with Some o -> o | None -> false) in
  
  (match 
      let cmd =
        Format.sprintf "(set-evidence! %B)" evidence
      in
      (debug smt "%s" cmd in
       execute_command solver cmd 0)
    with 
    | Success | NoResponse -> () 
    | _ -> raise (Failure ("Cannot set option evidence")));

  (* Set logic *)
  (match logic with 
    | `LIA | `LRA -> 
      (match
         let cmd = "(set-arith-only! true)" in
         (debug smt "%s" cmd in
          execute_command solver cmd 0)
       with 
         | Success | NoResponse -> () 
         | _ -> 
           raise 
             (Failure 
                ("Cannot set logic " ^ (string_of_logic logic))))
  
    | `detect | _ -> () );

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

  ignore (execute_command_no_response solver "(exit)" 0);

  (* Reset internal state of yices *)
  solver.solver_last_id <- YicesResponse.yices_id_of_int 0;
  solver.solver_state <- YNone;
  Hashtbl.clear solver.solver_id_names;
  Stack.clear solver.solver_push_stack;
  
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
