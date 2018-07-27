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

open YicesDriver
include YicesDriver
module Conv = SMTExpr.Converter(YicesDriver)
open Conv 

open SolverResponse


(* ********************************************************************* *)
(* Types                                                                 *)
(* ********************************************************************* *)

(* Map of sexprs to store models *)
module SMTExprMap = Map.Make(Term)



type _ command_type =
  | NoRespCmd : no_response command_type
  | Cmd : decl_response command_type
  | CheckSatCmd : check_sat_response command_type
  | GetValueCmd : get_value_response command_type
  | GetUnsatCoreCmd : get_unsat_core_response command_type
  | CustomCmd : int -> custom_response command_type


type yices_state =
  | YNone
  | YError
  | YUnsat of YicesResponse.yices_id list
  | YModel of SMTExpr.t SMTExprMap.t

                   
(* Configuration *)
type config =
    { solver_cmd : string array;    (* Command line arguments for the
                                       solver *)
      solver_arith_only : bool;
    }

(* Solver instance *)
type t = 
  { solver_config : config;           (* Configuration of the solver
                                         instance *)
    solver_pid : int;                 (* PID of the solver process *)
    solver_stdin : Unix.file_descr;   (* File descriptor of solver's stdin *)
    solver_lexbuf : Lexing.lexbuf;    (* Lexing buffer on solver's stdout *)
    solver_errlexbuf : Lexing.lexbuf; (* Lexing buffer on solver's stderr *)
    solver_stdout : Unix.file_descr;  (* File descriptor of solver's stdout *)
    solver_stderr : Unix.file_descr;  (* File descriptor of solver's stderr *)
    solver_trace_cmd : ?commented:bool -> string -> unit;
    (* Tracing function for commands *)

    solver_trace_res : response -> unit;
    (* Tracing function for responses *)

    solver_trace_coms : string -> unit;
    (* Tracing function for outputing comments *)

    mutable solver_state : yices_state;
    (* Used to record response to last command from which to extract values or
       unsat cores. *)

    mutable solver_last_id : YicesResponse.yices_id;
    (* Yices identifier that was last asserted. Remember to reset this to 0
       when restarting the solver or deleting the instance. *)

    solver_id_names : (YicesResponse.yices_id, string) Hashtbl.t;
    (* Associates yices assertion ids to smtlib names of named formulas *)

    solver_push_stack : YicesResponse.yices_id Stack.t;
    (* The internal push stack of assertions identiers. This should be
       cleared on deletion or resets. *)
  }

 
(* Conversions for SMTLIB *)
let smtlib_string_sexpr_conv = 

  GenericSMTLIBDriver.
    ({ s_let = HString.mk_hstring "let";
       s_forall = HString.mk_hstring "forall";
       s_exists = HString.mk_hstring "exists";
       s_div = HString.mk_hstring "/";
       s_minus = HString.mk_hstring "-";
       prime_symbol = None;
       s_define_fun = HString.mk_hstring "define-fun";
       s_declare_fun = HString.mk_hstring "declare-fun";
       const_of_atom = GenericSMTLIBDriver.const_of_smtlib_atom;
       symbol_of_atom = GenericSMTLIBDriver.symbol_of_smtlib_atom;
       type_of_sexpr = GenericSMTLIBDriver.type_of_smtlib_sexpr;
       expr_of_string_sexpr = gen_expr_of_string_sexpr';
       expr_or_lambda_of_string_sexpr = gen_expr_or_lambda_of_string_sexpr' } )
 

let rec yices_expr_of_string_sexpr = function

  (* An list with a list as first element, can be a multidimentional array *)
  | HStringSExpr.List [(HStringSExpr.List _ as ar); arg] ->

    let ar_t = yices_expr_of_string_sexpr ar in
    let arg_t = yices_expr_of_string_sexpr arg in
    Term.mk_select ar_t arg_t

  | sexpr ->
    GenericSMTLIBDriver.gen_expr_of_string_sexpr smtlib_string_sexpr_conv sexpr


let yices_lambda_of_string_sexpr = 
  GenericSMTLIBDriver.gen_expr_or_lambda_of_string_sexpr
    smtlib_string_sexpr_conv


let next_id solver =
  solver.solver_last_id
  |> YicesResponse.int_of_yices_id
  |> succ
  |> YicesResponse.yices_id_of_int  


let name_of_yices_id solver id =
  Hashtbl.find solver.solver_id_names id
       
    


let register_unsat_core solver uc =
  (* Get the corresponding SMTLIB names *)
  solver.solver_state <- YUnsat uc


    
let register_model solver model =
  (* Drop auxiliary variables *)
  let model =
    List.filter (fun (e, _) ->
        match e with
        | HStringSExpr.Atom x ->
          (try HString.sub x 0 4 <> "aux:"
           with Invalid_argument _ -> true)
        | _ -> true
      ) model
  in
  let m =
    List.fold_left
      (fun acc (e, v) ->
         let e_smte = yices_expr_of_string_sexpr e in
         let v_smte = yices_expr_of_string_sexpr v in

         (* Convert to real if it should be *)
         let v_smte =
           if Term.is_numeral v_smte &&
              Type.is_real (Term.type_of_term e_smte)
           then
             v_smte
             |> Term.numeral_of_term
             |> Numeral.to_big_int
             |> Decimal.of_big_int
             |> Term.mk_dec
           else v_smte
         in
         
         (* assert (Term.type_of_term e_smte = Term.type_of_term v_smte); *)
         SMTExprMap.add e_smte v_smte acc)
      SMTExprMap.empty model in
  solver.solver_state <- YModel m



(* ********************************************************************* *)
(* Helper functions to execute commands                                  *)
(* ********************************************************************* *)
    

(* Read the answer returned by yices *)                   
let parse_yices_output { solver_lexbuf = lexbuf } =
  (* Parse yices response and return *)
  (* Format.eprintf "parsing <%s>@." lexbuf.Lexing.lex_buffer; *)
  YicesParser.resp YicesLexer.token lexbuf


(* Read the error messge returned by yices *)
let get_yices_errmsg { solver_errlexbuf = errlb } =
  (* Wrong *)
  let yemsg = YicesParser.error_msg YicesLexer.error_msg errlb in
  Lexing.flush_input errlb;
  yemsg
  

  
(* Parse the solver response to a command *)
let get_command_response solver timeout = 

  (* Return response *)
  match parse_yices_output solver with
    
  | YicesResponse.YSuccess ->
     `Success
    
  | YicesResponse.YNoResp ->
     `NoResponse (* or success maybe *)

  | YicesResponse.YError ->
     solver.solver_state <- YError;
     `Error (get_yices_errmsg solver)
     
  | _ ->
     failwith "Yices returned an unexpected response"


(* Parse the solver response to a check-sat command *)
let get_check_sat_response solver timeout = 

  (* Return response *)
  match parse_yices_output solver with
    
  | YicesResponse.YRespSat model ->
     register_model solver model;
     `Sat
       
  | YicesResponse.YRespUnknown model ->
     register_model solver model;
     `Unknown
       
  | YicesResponse.YRespUnsat uc ->
     register_unsat_core solver uc;
     `Unsat
     
  | YicesResponse.YError ->
     solver.solver_state <- YError;
     `Error (get_yices_errmsg solver)
       
  | _ ->
     failwith "Yices returned an unexpected response"


(* Get n S-expressions from the solver *)
let rec get_custom_command_result solver accum i =
  (* Return response *)
  match parse_yices_output solver with
  
  | YicesResponse.YCustom r ->
    `Custom [HStringSExpr.Atom (HString.mk_hstring r)]

  | YicesResponse.YError ->
     solver.solver_state <- YError;
     `Error (get_yices_errmsg solver)

  | _ ->
    failwith "Yices get_custom_command_result got unexpected answer"


(* Parse the solver response to a custom command *)
let get_custom_command_response num_res solver timeout = 
(* Return response *)
  match parse_yices_output solver with
  
  | YicesResponse.YCustom r ->
    `Custom [HStringSExpr.Atom (HString.mk_hstring r)]

  | YicesResponse.YError ->
     solver.solver_state <- YError;
     `Error (get_yices_errmsg solver)

  | _ ->
    failwith "Yices get_custom_command_response got unexpected answer"
  


let get_any_response : type r. t -> int -> r command_type -> r =
  fun solver timeout -> function
    | NoRespCmd -> `NoResponse
    | Cmd -> get_command_response solver timeout
    | CheckSatCmd -> get_check_sat_response solver timeout
    | CustomCmd num_res -> get_custom_command_response num_res solver timeout
    | GetUnsatCoreCmd -> assert false
    | GetValueCmd -> assert false


(* Send the command to the solver instance *)
let send_command 
      cmd_type
      ({ solver_stdin = solver_stdin; } as solver)
      command 
      timeout = 

  (* Get an output channel to write to solver's stdin *)
  let solver_stdin_ch = Unix.out_channel_of_descr solver_stdin in

  (* Get a pretty-printing formatter writing to solver's stdin *)
  let solver_stdin_formatter = 
    Format.formatter_of_out_channel solver_stdin_ch 
  in

  (* Add the success marker *)
  let cmd =
    Format.sprintf "%s\n(echo \"%s\\n\")" command YicesResponse.success
  in
  
  (* Send command to solver *)
  Format.pp_print_string solver_stdin_formatter cmd;

  (* Print newline and flush formatter *)
  Format.pp_print_newline solver_stdin_formatter ();

  (* Wait for response without timeout *)
  get_any_response solver timeout cmd_type
    

let send_command_async 
      cmd_type
      { solver_stdin = solver_stdin }
      command 
      timeout = 

  (* Get an output channel to write to solver's stdin *)
  let solver_stdin_ch = Unix.out_channel_of_descr solver_stdin in

  (* Get a pretty-printing formatter writing to solver's stdin *)
  let solver_stdin_formatter = 
    Format.formatter_of_out_channel solver_stdin_ch 
  in

  let cmd = command in
  
  (* Send command to solver *)
  Format.pp_print_string solver_stdin_formatter cmd;

  (* Print newline and flush formatter *)
  Format.pp_print_newline solver_stdin_formatter ()
  (* don't wait *)



(* Samme as above but additionnaly trace the co mmands and responses *)
let send_command_and_trace =
  fun cmd_type solver command timeout -> 

    (* Trace the command *)
    solver.solver_trace_cmd command;

    (* Send the command to the solver and get the response *)
    let res = send_command cmd_type solver command timeout in

    (* Trace the response of the solver *)
    solver.solver_trace_res (res :> response);

    res


let send_command_and_trace_async =
  fun cmd_type solver command timeout -> 

    (* Trace the command *)
    solver.solver_trace_cmd command;

    (* Send the command to the solver and do not wait for the response *)
    send_command_async cmd_type solver command timeout
      

(* Execute a command and return the response *)
let execute_command = send_command_and_trace Cmd

(* Execute a command without logging in the trace and return the response *)
let execute_command_no_trace = send_command_async Cmd

(* Execute a command and do not parse a response *)
let execute_command_no_response = send_command_and_trace NoRespCmd

(* Execute a check-sat command and return the response *)
let execute_check_sat_command = send_command_and_trace CheckSatCmd

(* Execute a custom command and return the response *)
let execute_custom_command' solver command timeout num_res = 
  send_command_and_trace (CustomCmd num_res) solver command timeout


(* ********************************************************************* *)
(* Helper functions for printing commands                                *)
(* ********************************************************************* *)

(* Set the formatter to print commented and return a function to reset the
   printing of the formatter *)
let set_commented_formatter ppf =
  let fmt_out_fun = Format.pp_get_formatter_out_functions ppf () in

  let reset_ppf ppf = 
    Format.fprintf ppf "@?";
    Format.pp_set_formatter_out_functions ppf fmt_out_fun;
    Format.fprintf ppf "@.";
    Format.fprintf ppf "@\n"
  in

  let op, cl = comment_delims in

  Format.pp_set_formatter_out_functions 
    ppf 
    { fmt_out_fun with 
      Format.out_newline = (fun () ->
          fmt_out_fun.Format.out_string
            (" "^cl^"\n"^op^" ")
            0 (3 + String.length op + String.length cl ));
      Format.out_flush = (fun n ->
          fmt_out_fun.Format.out_string (" "^cl) 0 (1 + String.length cl);
          fmt_out_fun.Format.out_flush n
        );
    };

  reset_ppf


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

(* Returns true if the symbol is in the combination of SAT U equality U linear
   aritmetic *)
let ensure_symbol_qf_lira s =
  match Symbol.node_of_symbol s with
  | `TRUE
  | `FALSE
  | `NOT
  | `IMPLIES
  | `AND
  | `OR
  | `XOR
  | `EQ
  | `DISTINCT
  | `ITE
  | `NUMERAL _
  | `DECIMAL _
  | `MINUS
  | `PLUS
  | `TIMES
  | `DIV
  | `LEQ
  | `LT
  | `GEQ
  | `GT
  | `TO_REAL
  | `TO_INT
  | `TO_INT8
  | `TO_INT16
  | `TO_INT32
  | `TO_INT64
  | `IS_INT
  | `UF _
    -> ()

  (* | `UF f when UfSymbol.arg_type_of_uf_symbol f = [] -> () *)

  | `BV _ 
  | `INTDIV
  | `DIVISIBLE _
  | `MOD
  | `ABS
(*
  | `CONCAT
  | `EXTRACT _
  | `BVNOT
  | `BVNEG
  | `BVAND
  | `BVOR
  | `BVADD
  | `BVMUL
  | `BVDIV
  | `BVUREM
  | `BVSHL
  | `BVLSHR
  | `BVULT
*)
  | `SELECT _
  | `STORE ->
    
    let msg = Format.sprintf "Yices was run with set-arith-only, but the \
                              symbol %s is not interpreted correctly in this \
                              mode. Run Kind 2 with --smt_logic none instead."
        (Symbol.string_of_symbol s)
    in
    KEvent.log L_error "%s" msg;
    failwith msg



let rec ensure_lambda_qf_lira l =
  let open Term.T in
  match node_of_lambda l with
  | L (_, t) -> ensure_term_qf_lira t
  
and ensure_term_qf_lira t =
  let open Term.T in
  match node_of_t t with
  | FreeVar _ | BoundVar _ -> ()
  | Leaf s -> ensure_symbol_qf_lira s
  | Node (s, a) ->
    ensure_symbol_qf_lira s;
    List.iter ensure_term_qf_lira a
  | Let (lam, a) ->
    ensure_lambda_qf_lira lam;
    List.iter ensure_term_qf_lira a
  | Exists lam | Forall lam -> ensure_lambda_qf_lira lam
  | Annot (t, _) -> ensure_term_qf_lira t

let fail_when_arith solver t =
  if solver.solver_config.solver_arith_only then ensure_term_qf_lira t


let fail_symbol_when_arith solver s =
  if solver.solver_config.solver_arith_only then ensure_symbol_qf_lira s    

let fail_declare_when_arith solver f arg_sorts res_sort =
    if solver.solver_config.solver_arith_only && arg_sorts <> [] then
    let msg = Format.asprintf "Yices was run with set-arith-only, but the \
                               symbol %s has type %a."
        f pp_print_function_type (arg_sorts, res_sort) in
    KEvent.log L_error "%s" msg;
    failwith msg

    

(* ********************************************************************* *)
(* Commands                                                              *)
(* ********************************************************************* *)


(* Declare a new sort symbol *)
let declare_sort solver sort = match Type.node_of_type sort with
  | Type.Abstr _ ->

    let cmd =
      Format.sprintf "@[<hv 1>(define-type@ %s)@]"
        (string_of_sort sort)
    in

    (* Send command to the solver without timeout *)
    execute_command solver cmd 0

  (* | Type.Enum (name, l) -> *)
  (*   let s = match name with Some n -> n | None -> (string_of_sort sort) in *)
  (*   let cmd = *)
  (*     Format.asprintf "@[<hv 1>(define-type@ %s@ (scalar %a))@]" *)
  (*       s *)
  (*       (pp_print_list Format.pp_print_string " ") l *)
  (*   in *)

  (*   (\* Send command to the solver without timeout *\) *)
  (*   execute_command solver cmd 0 *)


  | _ -> failwith "Only declare uninterpreted and enumerated sorts."


(* Declare a new function symbol *)
let declare_fun solver fun_symbol arg_sorts res_sort = 

  fail_declare_when_arith solver fun_symbol arg_sorts res_sort;

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

  fail_when_arith solver expr;
  
  let t = expr in
  let t', name_info =
    if Term.is_named t then
      (* Open the named term and forget the name *)
      begin
        let name = "t"^(string_of_int (Term.name_of_named t)) in
        Term.term_of_named t,
        Format.asprintf "[name removed: %s]" name
      end
    else t, "" in
  let expr = Conv.smtexpr_of_term t' in
  

  let cmd = 
    Format.asprintf
      "@[<hv 1>(assert@ @[<hv>%s@])@]\n;; %s" 
      (string_of_expr expr)
      name_info
  in
  
  (* Send command to the solver without timeout *)
  let res = execute_command solver cmd 0 in

  (* Update state to indicate context has been modified *)
  solver.solver_state <- YNone;
  
  (* Return result of command *)
  res


(* Assert a removable expression, costly *)
let assert_removable_expr ?id solver expr = 

  fail_when_arith solver expr;
  
  (* Take the next id if none is given *)
  let id = match id with None -> next_id solver | Some id -> id in
  
  let t = expr in (* Conv.term_of_smtexpr expr in *)
  let t', name_info =
    if Term.is_named t then
      (* Open the named term and map the yices id to the name *)
      begin
        let name = "t"^(string_of_int (Term.name_of_named t)) in
        Hashtbl.add solver.solver_id_names id name; 
        Term.term_of_named t,
        Format.asprintf "[id: %a, name: %s]"
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
  | 0 -> `Success
  | 1 -> push_1 solver
  | n when n > 0 ->
     (match push_1 solver with
      | `Success | `NoResponse -> ()
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
  | 0 -> `Success
  | 1 -> pop_1 solver
  | n when n > 0 -> 
     (match pop_1 solver with
      | `Success | `NoResponse -> ()
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
                                  
(* let push s d = *)
(*   fast_push s d; *)
(*   `Success *)

(* let pop s d = *)
(*   fast_pop s d; *)
(*   `Success *)


(* Check satisfiability of the asserted expressions *)
let check_sat ?(timeout = 0) solver = 

  let cmd = match timeout with 
    | i when i <= 0 -> Format.sprintf "@[<hv 1>(check)\n@]"
    | _ -> check_sat_limited_cmd timeout
  in

  (* Send command to the solver without timeout *)
  execute_check_sat_command solver cmd 0


(* ********************************************************************* *)
(* Default values                                                        *)
(* ********************************************************************* *)


(* Default SMTExpr.t value for a type *)
let default_of_type t =
  TermLib.default_of_type t |> Conv.smtexpr_of_term


(* Check satisfiability of the asserted expressions *)
let check_sat_assuming solver exprs =

  (* We use retract feature of Yices to keep internal context *)
  fast_push solver 1;
  let res = List.fold_left (fun acc expr ->
      match Term.destruct expr with
        | Term.T.App (s, []) | Term.T.Const s when Symbol.is_uf s ->
          (* Register name of litterals for unsat core *)
          let name = 
            s |> Symbol.uf_of_symbol |> UfSymbol.string_of_uf_symbol in
          let id = next_id solver in
          Hashtbl.add solver.solver_id_names id name; 
          assert_removable_expr ~id solver expr

        | _ -> assert_removable_expr solver expr

    ) `NoResponse exprs
  in
  (match res with
   | `Error _  | `Unsupported ->
     failwith "Yices: check-sat assumed failed while assuming"
   | _ -> ());
  let res = check_sat ~timeout:0 solver in
  (* Remove assumed expressions from context while keeping state *)
  fast_pop solver 1;
  res



let model_of_yices_model model =

  let vars_assign = Var.VarHashtbl.create (SMTExprMap.cardinal model) in

  (* Construct an assignment of state variables found in the model *)
  SMTExprMap.iter
    (fun e v ->
       try
         let t = Conv.var_term_of_smtexpr e in

         if Term.is_free_var t then

           Var.VarHashtbl.add vars_assign 
             (Term.free_var_of_term t)
             (Model.Term (Conv.term_of_smtexpr v))

         else begin
           assert (Term.is_select t);
           (* The term is an array, we construct a map to represent its
              model. Here we just add one component of the map, mapping the
              arguments of the array access to the value v *)

           let var, args_t = Term.indexes_and_var_of_select t in
           let args = List.map
               (fun x -> Numeral.to_int (Term.numeral_of_term x)) args_t in

           let vt = Conv.term_of_smtexpr v in

           let map_var = match Var.VarHashtbl.find vars_assign var with
             | Model.Map m -> m
             | _ -> assert false
             | exception Not_found -> Model.MIL.empty in
           let map_var = Model.MIL.add args vt map_var in

           Var.VarHashtbl.add vars_assign var (Model.Map map_var)
         end
       (* Ignore expressions that are not state variables *)
       with Invalid_argument _ -> ()
    ) 
    model;

  vars_assign



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
  solver.solver_trace_cmd ~commented:true cmd;

  match solver.solver_state with
    | YModel model ->

      let vars_assign = model_of_yices_model model in

      let smt_expr_values =
        List.fold_left
          (fun acc e ->
             let v =
               try 
                 SMTExprMap.find e model
               with Not_found ->

                 (* If the variable is not found in the model, use the default
                     value for its type *)
                 try
                   default_of_type
                     (Term.type_of_term (Conv.var_term_of_smtexpr e))
                 with Invalid_argument _ ->
                   (* If the expression e is not a state variable, we evaluate it
                      in the assignment of the model *)
                   (* Format.eprintf "eval : %a@." Conv.pp_print_expr e; *)
                   let ve =
                     Eval.eval_term [] vars_assign (Conv.term_of_smtexpr e) in
                   Eval.term_of_value ve
             in
             (e, v) :: acc
          ) [] expr_list
      in


      (* List.iter (fun (e, v) -> *)
      (*     assert(not (Term.equal e v)) ) smt_expr_values; *)

      (* construct the response with the desired values *)
      let res = `Values (List.rev smt_expr_values) in

      (* Trace the response of the solver *)
      solver.solver_trace_res res;

      (* return the computed values *)
      res

    | _ -> failwith "Yices: No model to compute get-values"


let get_model solver = 

  (* get-value is not supported by Yices so we simulate the command by looking
     up values in the registered model of the solver state *)

  (* The fake SMTLIB command  *)
  let cmd =
    Format.asprintf
      "@[<hv 1>(get-model)@]" 
  in

  (* Trace the fake command but comment it *)
  solver.solver_trace_cmd ~commented:true cmd;

  match solver.solver_state with
    | YModel model ->

      let m =
        Var.VarHashtbl.fold (fun var value acc ->
            (Var.unrolled_uf_of_state_var_instance var, value) :: acc)
          (model_of_yices_model model) [] in
      
      `Model m

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
  solver.solver_trace_cmd ~commented:true cmd;

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

     let res = `Unsat_core uc_names in
     
     (* Trace the response of the solver *)
     solver.solver_trace_res res;

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

  (* add custom start marker *)
  let cmd = Format.sprintf "(echo \"%s\\n\")@ %s" YicesResponse.custom cmd in
    
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
  if Flags.Smt.trace () then 

    let tdir = Flags.Smt.trace_dir () in
    (* Create root dir if needed. *)
    Flags.output_dir () |> mk_dir ;
    (* Create smt_trace dir if needed. *)
    mk_dir tdir ;

    (* Name of SMT trace file *)
    let trace_filename = 
      Filename.concat
        tdir
        (Format.sprintf "%s.%s.%d.ys" 
                        (Filename.basename (Flags.input_file ()))
                        (short_name_of_kind_module (KEvent.get_module ()))
                        id)
    in
    
    try
      
      (* Open file for output, may fail *)
      let trace_oc = open_out trace_filename in
      
      KEvent.log L_debug
        "Tracing output of SMT solver instace to %s" trace_filename;

      (* Return formatter *)
      Some (Format.formatter_of_out_channel trace_oc)
           
    (* Silently fail *)
    with Sys_error e -> 

      KEvent.log L_debug "Failed to open trace file for SMT solver %s" e;
      
      None 
        
  else

    (* Do not trace SMT commands *)
    None 

(* Tracing of commands *)
let trace_cmd ppf ?(commented=false) =
  match ppf with
  | Some ppf ->
    fun cmd ->
      let op, cl = comment_delims in
      let cmd = 
        if commented then
          op^" "^(Str.global_replace (Str.regexp_string "\n")
                    (" "^cl^"\n"^op^" ") cmd)
        else cmd
      in
      Format.fprintf ppf "%s@." cmd
  | None -> fun _ -> ()

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


(* Create an instance of the solver *)
let create_instance
    ?produce_assignments
    ?produce_proofs
    ?produce_cores
    logic
    id =


  let arith_only =
    let open TermLib in
    let open TermLib.FeatureSet in
    match logic with
    | `Inferred l -> subset l (of_list [IA; RA; LA])
    | `SMTLogic ("QF_LIA" | "QF_LRA" | "QF_LIRA") -> true
    | _ -> false
  in
  
  
  (* Get autoconfigured configuration *)
  let solver_cmd  = 
    YicesDriver.cmd_line
      logic
      produce_assignments
      produce_proofs
      produce_cores
      false
  in

  let config = { solver_cmd = solver_cmd; solver_arith_only = arith_only } in
  
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

  (* Get an output channel to read from solver's stdout *)
  let solver_stderr_ch = Unix.in_channel_of_descr solver_stderr_in in

  (* Create a lexing buffer on solver's stdout *)
  let solver_errlexbuf = Lexing.from_channel solver_stderr_ch in

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
      solver_errlexbuf = solver_errlexbuf;
      solver_stdout = solver_stdout_in; 
      solver_stderr = solver_stderr_in;
      solver_trace_cmd = ftrace_cmd;
      solver_trace_res = ftrace_res;
      solver_trace_coms = ftrace_coms;
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
    (match produce_assignments with Some o -> o | None -> false)
  in

  let header_logic solver =
    if solver.solver_config.solver_arith_only then
      ["(set-arith-only! true)"]
    else [] in
    
  
  let headers =
    (Format.sprintf "(set-evidence! %B)" evidence) ::
    (header_logic solver) @
    (headers ())
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
      KEvent.log L_fatal
        "[Warning] Got broken pipe when trying to exit %s instance PID %d."
        solver.solver_config.solver_cmd.(0) solver_pid
  end;

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
      ~produce_assignments:P.produce_assignments
      ~produce_cores:P.produce_cores
      ~produce_proofs:P.produce_proofs
      P.logic P.id

  let delete_instance () = delete_instance solver


  let declare_sort = declare_sort solver
  let declare_fun = declare_fun solver
  let define_fun = define_fun solver
  let assert_expr = assert_removable_expr solver

  let push = push solver
  let pop = pop solver
  let check_sat ?(timeout = 0) () = check_sat ~timeout solver
  let check_sat_assuming = check_sat_assuming solver

  let check_sat_assuming_supported = check_sat_assuming_supported
  let get_value = get_value solver
  let get_model () = get_model solver
  let get_unsat_core () = get_unsat_core solver


  let execute_custom_command = execute_custom_command solver
  let execute_custom_check_sat_command cmd =
    execute_custom_check_sat_command cmd solver
  let trace_comment = trace_comment solver



end

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
