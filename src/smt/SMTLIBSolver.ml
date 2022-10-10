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

open Lib
open SolverResponse

(* ********************************************************************* *)
(* Types                                                                 *)
(* ********************************************************************* *)

type _ command_type =
  | NoRespCmd : no_response command_type
  | Cmd : decl_response command_type
  | CheckSatCmd : check_sat_response command_type
  | GetValueCmd : get_value_response command_type
  | GetModelCmd : get_model_response command_type
  | GetUnsatCoreCmd : get_unsat_core_response command_type
  | CustomCmd : int -> custom_response command_type


let s_timeout = HString.mk_hstring "timeout"
let s_success = HString.mk_hstring "success"
let s_unsupported = HString.mk_hstring "unsupported"
let s_error = HString.mk_hstring "error"
let s_sat = HString.mk_hstring "sat"
let s_unsat = HString.mk_hstring "unsat"
let s_unknown = HString.mk_hstring "unknown"
let s_model = HString.mk_hstring "model"

module type SMTLIBSolverDriver = sig
  include SolverDriver.S

  val s_define_fun : HString.t
  
  val expr_of_string_sexpr : HStringSExpr.t -> Term.t

  val expr_or_lambda_of_string_sexpr : HStringSExpr.t -> (HString.t * Model.value)

end


module Make (Driver : SMTLIBSolverDriver) : SolverSig.S = struct
  
  open Driver
  module Conv = SMTExpr.Converter(Driver)
  open Conv 
    
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

      solver_trace_res : response -> unit;
      (* Tracing function for responses *)

      solver_trace_coms : string -> unit;
      (* Tracing function for outputing comments *)
    }

    
  (***** TODO from smtexpr : inline this later on *****)

  let response_error e = match e with
    | HStringSExpr.Atom s when s == s_timeout -> `Timeout
    | e -> 
      raise 
        (Failure 
           ("Invalid solver response " ^ HStringSExpr.string_of_sexpr e))

  (* Return a solver response of an S-expression *)
  let response_of_sexpr : HStringSExpr.t -> decl_response = function 

    (* Successful command *)
    | HStringSExpr.Atom s when s == s_success -> `Success 

    (* Unsupported command *)
    | HStringSExpr.Atom s when s == s_unsupported -> `Unsupported

    (* Error *)
    | HStringSExpr.List 
        [HStringSExpr.Atom s; HStringSExpr.Atom e ] when s == s_error -> 
      `Error (HString.string_of_hstring e)

    (* Invalid response *)
    | e -> response_error e

  
  (* Return a solver response to a check-sat command of an S-expression *)
  let check_sat_response_of_sexpr = function 

    | HStringSExpr.Atom s when s == s_sat -> `Sat
    | HStringSExpr.Atom s when s == s_unsat -> `Unsat
    | HStringSExpr.Atom s when s == s_unknown -> `Unknown
    (* | r -> Response (response_of_sexpr r) *)
    | e -> response_error e

  (* Helper function to return a solver response to a get-value command
     as expression pairs *)
  let rec get_value_response_of_sexpr' accum = function 
    | [] -> `Values (List.rev accum)
    | HStringSExpr.List [ e; v ] :: tl -> 

      Debug.smtexpr
        "get_value_response_of_sexpr: %a is %a"
        HStringSExpr.pp_print_sexpr e
        HStringSExpr.pp_print_sexpr v; 

       let accum =
         try
           ((expr_of_string_sexpr e :> SMTExpr.t), 
            (expr_of_string_sexpr v :> SMTExpr.t)) :: 
           accum
         with Failure _ -> accum in
       
       get_value_response_of_sexpr' accum tl

    (* Hack for cvc5's (- 1).0 expressions *)
    | HStringSExpr.List [ e; v; HStringSExpr.Atom d ] :: tl 
      when d == HString.mk_hstring ".0" ->

      get_value_response_of_sexpr' 
        accum
        (HStringSExpr.List [ e; v ] :: tl)

    | e :: _ -> 

      Debug.smtexpr
        "get_value_response_of_sexpr: %a"
        HStringSExpr.pp_print_sexpr e;

      invalid_arg "get_value_response_of_sexpr"


  (* Helper function to return a solver response to a get-model command
     as expression pairs *)
  let rec get_model_response_of_sexpr' accum = function 

    | [] -> `Model accum

    | e :: tl -> 

      Debug.smtexpr
        "get_model_response_of_sexpr: %a" HStringSExpr.pp_print_sexpr e;

      try

        (* Get name of variable and its assignment *)
        let s, t_or_l = expr_or_lambda_of_string_sexpr e in

        (* Get uninterpreted function symbol by name *)
        let u =
          UfSymbol.uf_symbol_of_string (HString.string_of_hstring s) 
        in

        (* Continue with next model assignment *)
        get_model_response_of_sexpr' ((u, t_or_l) :: accum) tl

      (* No symbol of that name

         May happen if named terms have been asserted *)
      with Not_found ->

        (* Continue with next model assignment *)
        get_model_response_of_sexpr' accum tl



  (* Return a solver response to a get-value command as expression pairs *)
  let get_value_response_of_sexpr = function 

    (* Solver returned error message 

       Must match for error first, because we may get (error "xxx") or
       ((x 1)) which are both lists *)
    | HStringSExpr.List 
        [HStringSExpr.Atom s; 
         HStringSExpr.Atom e ] when s == s_error -> 
      `Error (HString.string_of_hstring e)

    (* Solver returned a list not starting with an error atom  *)
    | HStringSExpr.List l -> get_value_response_of_sexpr' [] l

    (* Solver returned other response *)
    | e -> response_error e



  let s_declare_datatypes = HString.mk_hstring "declare-datatypes"
  let s__compress_equal_mod_input () =
    HString.mk_hstring (Compress.function_symbol_name ())


  let ignore_model_item = function
      
    (* (declare-datatype ...) *)
    | HStringSExpr.List (HStringSExpr.Atom s :: _)
      when s == s_declare_datatypes -> true

    (* (define-fun __compress_equal_mod_input ...) *)
    | HStringSExpr.List (HStringSExpr.Atom s :: HStringSExpr.Atom c :: _)
      when s == s_define_fun && c == s__compress_equal_mod_input () -> true 
  
    | _ -> false

  
  (* Return a solver response to a get-value command as expression pairs *)
  let get_model_response_of_sexpr = function 

    (* Solver returned error message 

       Must match for error first, because we may get (error "xxx") or
       ((x 1)) which are both lists *)
    | HStringSExpr.List 
        [HStringSExpr.Atom s; 
         HStringSExpr.Atom e ] when s == s_error -> 
      `Error (HString.string_of_hstring e)

    (* Solver returned a list starting with model (e.g. z3 4.8.9 and below) *)
    | HStringSExpr.List 
        (HStringSExpr.Atom s :: l) when s == s_model -> 

      (* remove useless declarations/definitions from the model *)
      List.filter (fun d -> not (ignore_model_item d)) l
      |> get_model_response_of_sexpr' []

    (* Solver returned a list not starting with an error or model atom *)
    | HStringSExpr.List l ->

      (* remove useless declarations/definitions from the model *)
      List.filter (fun d -> not (ignore_model_item d)) l
      |> get_model_response_of_sexpr' []

    (* Solver returned other response *)
    | e -> response_error e


  (* Return a solver response to a get-unsat-core command as list of strings *)
  let get_unsat_core_response_of_sexpr = function 

    (* Solver returned error message Must match for error first *)
    | HStringSExpr.List 
        [HStringSExpr.Atom s; HStringSExpr.Atom e ]
      when s == s_error -> 
      `Error (HString.string_of_hstring e)

    (* Solver returned a list not starting with an error atom *)
    | HStringSExpr.List l -> 

      (* Convert list of atoms to list of strings *)
      `Unsat_core
        (List.map
           (function 
             | HStringSExpr.Atom n -> (HString.string_of_hstring n)
             | _ -> invalid_arg "get_unsat_core_response_of_sexpr")
           l)

    (* Solver returned other response *)
    | e -> response_error e


  (* Return a solver response to a custom command *)
  let get_custom_command_response_of_sexpr = function 

    (* Solver returned error message 

       Must match for error first, because we may get (error "xxx") or
       ((x 1)) which are both lists *)
    | HStringSExpr.List 
        [HStringSExpr.Atom s; HStringSExpr.Atom e ] 
      when s == s_error -> 
      `Error (HString.string_of_hstring e)

    (* Solver returned success message *)
    | HStringSExpr.Atom s when s == s_success -> `Success 

    | _ -> `NoResponse



  (* ********************************************************************* *)
  (* Helper functions to execute commands                                  *)
  (* ********************************************************************* *)


  (* Read an S-expression from the solver output *)
  let expr_of_solver_lexbuf { solver_lexbuf = lexbuf } = 

    (* Parse S-expression and return *)
    SExprParser.sexp SExprLexer.main lexbuf 


  (* Parse the solver response to a command *)
  let [@ocaml.warning "-27"] get_command_response solver timeout = 

    (* Return response *)
    response_of_sexpr (expr_of_solver_lexbuf solver)


  (* Parse the solver response to a check-sat command *)
  let [@ocaml.warning "-27"] get_check_sat_response solver timeout = 

    (* Return response *)
    check_sat_response_of_sexpr (expr_of_solver_lexbuf solver)


  (* Parse the solver response to a get-value command *)
  let [@ocaml.warning "-27"] get_get_value_response solver timeout = 

    (* Return response *)
    get_value_response_of_sexpr (expr_of_solver_lexbuf solver)


  (* Parse the solver response to a get-model command *)
  let [@ocaml.warning "-27"] get_get_model_response solver timeout = 

    (* Return response *)
    get_model_response_of_sexpr (expr_of_solver_lexbuf solver)


  (* Parse the solver response to a get-unsat-core command *)
  let [@ocaml.warning "-27"] get_get_unsat_core_response solver timeout = 

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
  let [@ocaml.warning "-27"] get_custom_command_response num_res solver timeout = 

    (* Get response from solver *)
    let response = expr_of_solver_lexbuf solver in

    (* Get result only upon success *)
    match get_custom_command_response_of_sexpr response with 

    (* First line of reply is success status *)
    | `Success -> 

      (* Get remaining results *)
      let result = get_custom_command_result solver [] num_res in

      (* Return response and result *)
      `Custom result 

    (* First line of reply is neither error nor success *)
    | `NoResponse -> 

      (* Use already consumed first result and get remaining results *)
      let result = 
        response :: get_custom_command_result solver [] (pred num_res) 
      in

      (* Return success and result *)
      `Custom result

    (* First line of reply is error or unsupported *)
    | `Error _ as r ->

      (* Return response and empty result *)
      r


  let get_any_response : type r. t -> int -> r command_type -> r =
    fun solver timeout -> function
      | NoRespCmd -> `NoResponse
      | Cmd -> get_command_response solver timeout
      | CheckSatCmd -> get_check_sat_response solver timeout
      | GetValueCmd -> get_get_value_response solver timeout
      | GetModelCmd -> get_get_model_response solver timeout
      | GetUnsatCoreCmd -> get_get_unsat_core_response solver timeout
      | CustomCmd num_res -> get_custom_command_response num_res solver timeout


  (* Send the command to the solver instance *)
  let send_command
      cmd_type
      ({ solver_stdin; solver_stderr } as solver)
      command 
      timeout = 

    let err_p1 = Unix.((fstat solver_stderr).st_size) in
    
    try

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

    with e ->
      let err_p2 = Unix.((fstat solver_stderr).st_size) in
      let len = err_p2 - err_p1 in
      (* Was something written to stderr? *)
      if len <> 0 then begin
        let buf = Bytes.create err_p2 in
        Unix.read solver_stderr buf 0 err_p2 |> ignore;
        let err_msg = Bytes.sub_string buf err_p1 len in
        (* Show solver error message *)
        (* KEvent.log L_fatal "@[<v>Solver error message:@ %s@]" err_msg; *)
        failwith ("Solver error: "^err_msg)
      end

      (* Otherwise propagate error *)
      else raise e
      (*
      else (
      let buf = Bytes.create 512 in
      let len = ref (Unix.read solver_stderr buf 0 512) in
      while (!len > 0) do
        Format.printf "%s" (Bytes.sub_string buf 0 !len);
        len := (Unix.read solver_stderr buf 0 512)
      done;
      solver.solver_trace_coms "__EXCEPTION__";
      raise e)
      *)


  (* Samme as above but additionnaly trace the commands and responses *)
  let send_command_and_trace =
    fun cmd_type solver command timeout -> 

    (* Trace the command *)
    solver.solver_trace_cmd command;

    (* Send the command to the solver and get the response *)
    let res = send_command cmd_type solver command timeout in

    (* Trace the response of the solver *)
    solver.solver_trace_res (res :> response);

    res

  (* Execute a command and return the response *)
  let execute_command = send_command_and_trace Cmd

  (* Execute a command and do not parse a response *)
  let execute_command_no_response = send_command_and_trace NoRespCmd

  (* Execute a check-sat command and return the response *)
  let execute_check_sat_command = send_command_and_trace CheckSatCmd

  (* Execute a get-value command and return the response *)
  let execute_get_value_command = send_command_and_trace GetValueCmd

  (* Execute a get-model command and return the response *)
  let execute_get_model_command = send_command_and_trace GetModelCmd

  (* Execute a get-unsat-core command and return the response *)
  let execute_get_unsat_core_command = send_command_and_trace GetUnsatCoreCmd

  (* Execute a custom command and return the response *)
  let execute_custom_command' solver command timeout num_res = 
    send_command_and_trace (CustomCmd num_res) solver command timeout


  (* ********************************************************************* *)
  (* Commands                                                              *)
  (* ********************************************************************* *)

  (* Declare a new sort symbol *)
  let declare_sort solver sort = match Type.node_of_type sort with
    | Type.Abstr _ ->

      let cmd =
        Format.sprintf "@[<hv 1>(declare-sort@ %s 0)@]"
          (string_of_sort sort)
      in

      (* Send command to the solver without timeout *)
      execute_command solver cmd 0

    (* | Type.Enum (name, l) -> *)
    (*   let s = match name with Some n -> n | None -> (string_of_sort sort) in *)
    (*   let cmd = *)
    (*     Format.asprintf "@[<hv 1>(declare-datatypes ()@ ((%s %a)))@]" *)
    (*       s *)
    (*       (pp_print_list (fun ppf -> Format.fprintf ppf "(%s)") " ") l *)
    (*   in *)

    (*   (\* Send command to the solver without timeout *\) *)
    (*   execute_command solver cmd 0 *)


    | _ -> failwith "Only declare uninterpreted sorts."


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


  (* Assert-soft the expression *)
  let assert_soft_expr solver expr weight =

    let cmd =
      Format.sprintf
        "@[<hv 1>(assert-soft@ @[<hv>%s@] :weight %d)@]"
        (string_of_expr expr) weight in

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


  let check_sat_assuming_supported = Driver.check_sat_assuming_supported

  (* Check satisfiability of the asserted expressions *)
  let check_sat_assuming solver exprs =
    (* Retrieving command from solver info. *)
    let command = check_sat_assuming_cmd () in
    
    (* Building the complete command. *)
    let cmd =
      Format.asprintf "(%s (%a))"
        command
        (pp_print_list Format.pp_print_string " ")
        (List.map string_of_expr exprs)
    in

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


  (* Get values of expressions in the model *)
  let get_model solver () = 

    (* The command to send to the solver *)
    let cmd = Format.sprintf "@[<hv 1>(get-model)@]" in

    (* Send command to the solver without timeout *)
    execute_get_model_command solver cmd 0

  (* Get an unsatisfiable core *)
  let get_unsat_core solver =
    let cmd = Format.sprintf "@[<hv 1>(get-unsat-core)@]" in

    (* Send command to the solver without timeout *)
    execute_get_unsat_core_command solver cmd 0

  (* Get an unsatisfiable subset of assumptions *)
  let get_unsat_assumptions solver =

    (* The command to send to the solver *)
    let cmd =
      if Flags.Smt.check_sat_assume () then
        Format.sprintf "@[<hv 1>(get-unsat-assumptions)@]"
      else
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
    if Flags.Smt.trace () then (

      (* Create root dir if needed. *)
      Flags.output_dir () |> mk_dir ;
      (* Create smt_trace dir if needed. *)
      let tdir = Flags.Smt.trace_dir () in
      mk_dir tdir ;
      (* Create smt_trace subdir if needed. *)
      let tdir = Filename.concat tdir (Flags.Smt.trace_subdir ()) in
      mk_dir tdir ;

      (* Name of SMT trace file *)
      let trace_filename = 
        Filename.concat
          tdir
          (Format.sprintf "%s.%s.%d.%s" 
             (Filename.basename (Flags.input_file ()))
             (short_name_of_kind_module (KEvent.get_module ()))
             id
             trace_extension
          )
      in

      try

        (* Open file for output, may fail *)
        let trace_oc = open_out trace_filename in

        KEvent.log L_debug
          "Tracing output of SMT solver instance to %s"
          trace_filename;

        (* Return formatter *)
        Some (Format.formatter_of_out_channel trace_oc)

      (* Silently fail *)
      with Sys_error e -> 

        KEvent.log L_debug
          "Failed to open trace file for SMT solver %s"
          e;

        None 

    )
    else

      (* Do not trace SMT commands *)
      None 

  (* Set the formatter to print commented and return a function to reset the
   printing of the formatter *)
  let set_commented_formatter ppf =
    let fmt_out_fun = Format.pp_get_formatter_out_functions ppf () in

    let reset_ppf ppf = 
      Format.fprintf ppf "@?";
      Format.pp_set_formatter_out_functions ppf fmt_out_fun;
      Format.fprintf ppf "@.@.";
    in

    let op, cl = comment_delims in

    let out_newline () =
      fmt_out_fun.Format.out_string " " 0 1;
      fmt_out_fun.Format.out_string cl 0 (String.length cl);
      fmt_out_fun.Format.out_string "\n" 0 1;
      fmt_out_fun.Format.out_string op 0 (String.length op);
      fmt_out_fun.Format.out_string " " 0 1
    in

    let out_flush n =
      fmt_out_fun.Format.out_string (" "^cl) 0 (1 + String.length cl); 
      fmt_out_fun.Format.out_flush n
    in


    (* Apply [f] to each line in [s] starting at postion [p] for [n]
       characters. Lines can be separated by any of "\n", "\r", "\n\r"
       or "\r\n" *)
    let rec iter_line f g s p i n =
      
      (* Terminate when no more characters left *)
      if n = 0 then ()

      (* Apply [f] at the end of the string *)
      else if i >= n then f s p n else

        (* Check next character, and following only if within range *)
        match s.[p+i], (if i+1 < n then Some s.[p+i+1] else None) with
            
          (* Two character line break *)
          | '\n', Some '\r'  
          | '\r', Some '\n' ->
            
            (* Apply [f] to line, then [g], skip over line break and
               continue *)
            f s p i;
            g ();
            iter_line f g s (p+i+2) 0 (n-i-2)
              
          (* One character line break *)
          | '\n', _
          | '\r', _ ->

            (* Apply [f] to line, skip over line break and continue *)
            f s p i;
            g ();
            iter_line f g s (p+i+1) 0 (n-i-1)

          (* Not a line break: continue *)
          | _, _ -> iter_line f g s p (i+1) n
    in

    let out_string s p n =
      iter_line
        fmt_out_fun.Format.out_string
        out_newline
        s
        p
        0
        n
    in
    
    Format.pp_set_formatter_out_functions 
      ppf 
      { fmt_out_fun with
        Format.out_newline = out_newline;
        Format.out_flush = out_flush;
        Format.out_string = out_string;
      };

    reset_ppf

  (* Tracing of commands *)
  let trace_cmd solver_ppf cmd = match solver_ppf with
    | Some ppf -> Format.fprintf ppf "%s@." cmd
    | None -> ()

  (* Tracing of responses *)
  let trace_res solver_ppf res = match solver_ppf with
    | Some ppf ->
      let op, _ = comment_delims in
      let reset_ppf = set_commented_formatter ppf in
      Format.kfprintf reset_ppf ppf "%s %a" op pp_print_response res
    | None -> ()

  (* Tracing of comments *)
  let trace_coms solver_ppf com = match solver_ppf with
    | Some ppf ->
      let op, _ = comment_delims in
      let reset_ppf = set_commented_formatter ppf in
      Format.kfprintf reset_ppf ppf "%s %s" op com
    | None -> ()


  (* ********************************************************************* *)
  (* Creating and deleting solver instances                                *)
  (* ********************************************************************* *)


  (* Create an instance of the solver *)
  let create_instance
      ?(timeout=0)
      ?(produce_assignments=false)
      ?(produce_proofs=false)
      ?(produce_unsat_cores=false)
      ?(produce_unsat_assumptions=false)
      ?(minimize_cores=false)
      ?(produce_interpolants=false)
      logic
      id =
    
    (* Get autoconfigured configuration *)
    let solver_cmd  = 
      Driver.cmd_line
        logic
        timeout
        produce_assignments
        produce_proofs
        produce_unsat_cores
        produce_unsat_assumptions
        minimize_cores
        produce_interpolants
    in
    let config = { solver_cmd = solver_cmd } in
    
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
    let ftrace_coms = trace_coms trace_ppf in
    
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
        solver_trace_coms = ftrace_coms; }
    in
    
    let header_logic =
      let s = string_of_logic logic in
      (* if s = "" then [] else *)
      [Format.sprintf "(set-logic %s)" s]
    in

    let header_farray =
      if not (Flags.Arrays.smt ()) && TermLib.logic_allow_arrays logic then
        [
          (* Sort declaration for uninterpreted arrays *)
          "(declare-sort FArray 2)";
        ]
      else [] in

    let define_bv2int =
      match logic with 
      | `Inferred l -> if TermLib.FeatureSet.mem BV l && TermLib.FeatureSet.mem IA l then true else false
      | _ -> false
    in
    
    let header_bv2int =
      [ "(define-fun int8_to_int ((x (_ BitVec 8))) Int (ite (bvsle x (_ bv0 8)) (- (bv2nat (bvneg x))) (bv2nat x)))" ;
        "(define-fun int16_to_int ((x (_ BitVec 16))) Int (ite (bvsle x (_ bv0 16)) (- (bv2nat (bvneg x))) (bv2nat x)))" ; 
        "(define-fun int32_to_int ((x (_ BitVec 32))) Int (ite (bvsle x (_ bv0 32)) (- (bv2nat (bvneg x))) (bv2nat x)))" ;
        "(define-fun int64_to_int ((x (_ BitVec 64))) Int (ite (bvsle x (_ bv0 64)) (- (bv2nat (bvneg x))) (bv2nat x)))" ; ]
    in
    
    let headers =
      "(set-option :print-success true)" ::
      (headers minimize_cores) @
      (if produce_assignments then
        (*["(set-option :produce-assignments true)"] else []) @*)
        (* The command get-model is used instead of get-assignment,
          thus we should use the option produce-models instead of produce-assignments *)
        ["(set-option :produce-models true)"] else []) @
      (if produce_unsat_cores ||
          (produce_unsat_assumptions && not (Flags.Smt.check_sat_assume ()))
       then ["(set-option :produce-unsat-cores true)"]
       else []) @
      (if produce_unsat_assumptions && Flags.Smt.check_sat_assume ()
       then ["(set-option :produce-unsat-assumptions true)"]
       else []) @
      header_logic @
      header_farray @
      (if define_bv2int then header_bv2int else [])
    in
    
    (* Add interpolation option only if true *)
    let headers = 
      if produce_interpolants then
        headers @ 
        [Format.sprintf "(set-option :produce-interpolants %B)" produce_interpolants]
      else
        
        headers 
    in
    
    (* Print specific headers specifications *)
    List.iter (fun cmd ->
        Debug.smt "%s" cmd;
        match execute_command solver cmd 0 with 
          | `Success -> () 
          | _ -> raise (Failure ("Failed to add header: "^cmd))
    ) headers;

    (* Print prelude *)
    List.iter (fun cmd ->
        Debug.smt "%s" cmd;
        match execute_command solver cmd 0 with 
          | `Success -> () 
          | _ -> raise (Failure ("Failed to add prelude command: "^cmd))
     ) prelude;


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

    begin
      try ignore(execute_command_no_response solver "(exit)" 0)
      with Signal s when s = Sys.sigpipe ->
        KEvent.log L_warn
          "[Warning] Got broken pipe when trying to exit %s instance PID %d.\
          It may be due to a timeout."
          solver.solver_config.solver_cmd.(0) solver_pid
    end;

    (* Check if solver instance has exited, wait 10ms, count down and
       kill process eventually *)
    let rec wait_and_kill time_to_kill = 

      (* Have we waited long enough? *)
      if time_to_kill <= 0 then

        (

          (* Send SIGKILL to process *)
          Unix.kill solver_pid Sys.sigkill;

          (* Return exit code *)
          Unix.waitpid [] solver_pid |> snd

        )

      else

        (

          (* Wait 10ms *)
          minisleep 0.01;

          (* Check return status *)
          match Unix.waitpid [Unix.WNOHANG] solver_pid with

          (* Process has not exited yet? Wait one more time *)
          | 0, _ -> wait_and_kill (pred time_to_kill)

          (* Return exit code *)
          | _, process_status -> process_status

        )
    in
        
    (* Wait 10*10ms for process to terminate *)
    let process_status = wait_and_kill 10 in

    (

      (* Check termination status of solver *)
      match process_status with

      (* Exit with code *)
      | Unix.WEXITED c -> 
        Debug.smt "Solver exited with code %d" c;

      (* Killed by signal *)
      | Unix.WSIGNALED s -> 
        Debug.smt "Solver killed with signal %d" s;

      (* Stopped by signal *)
      | Unix.WSTOPPED s -> 
        Debug.smt "Solver stopped by signal %d" s;

    );

    (* Close file descriptors of solver *)
    Unix.close solver_stdin;
    Unix.close solver_stdout;
    Unix.close solver_stderr


  (* Output a comment into the trace *)
  let trace_comment solver comment = 
    solver.solver_trace_coms comment

    



  module Create (P : SolverSig.Params) : SolverSig.Inst = struct

    module Conv = Conv
    
    let solver = create_instance
        ~timeout:P.timeout
        ~produce_assignments:P.produce_assignments
        ~produce_unsat_cores:P.produce_unsat_cores
        ~produce_unsat_assumptions:P.produce_unsat_assumptions
        ~minimize_cores:P.minimize_cores
        ~produce_proofs:P.produce_proofs
        ~produce_interpolants:P.produce_interpolants
        P.logic P.id

    let delete_instance () = delete_instance solver


    let declare_sort = declare_sort solver
    let declare_fun = declare_fun solver
    let define_fun = define_fun solver
    let assert_expr = assert_expr solver
    let assert_soft_expr = assert_soft_expr solver

    let push = push solver
    let pop = pop solver
    let check_sat ?(timeout = 0) () = check_sat ~timeout solver
    let check_sat_assuming = check_sat_assuming solver

    let check_sat_assuming_supported = check_sat_assuming_supported
    let get_value = get_value solver
    let get_model = get_model solver
    let get_unsat_core () = get_unsat_core solver
    let get_unsat_assumptions () = get_unsat_assumptions solver

    let execute_custom_command = execute_custom_command solver
    let execute_custom_check_sat_command cmd = execute_custom_check_sat_command cmd solver
    let trace_comment = trace_comment solver
    
  end


end



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
