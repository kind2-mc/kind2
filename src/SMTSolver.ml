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


let gentag =
  let r = ref 0 in
  fun () -> incr r; !r



(* Input signature for the Make functor *)
module type Solver =
sig 

  type t

  val create_instance : 
    ?produce_assignments:bool -> 
    ?produce_models:bool -> 
    ?produce_proofs:bool -> 
    ?produce_cores:bool -> 
    SMTExpr.logic -> 
    t

  val delete_instance : t -> unit

  val declare_fun : t -> string -> SMTExpr.sort list -> SMTExpr.sort -> SMTExpr.response

  val define_fun : t -> string -> SMTExpr.var list -> SMTExpr.sort -> SMTExpr.t -> SMTExpr.response

  val assert_expr : t -> SMTExpr.t -> SMTExpr.response

  val push : t -> int -> SMTExpr.response 

  val pop : t -> int -> SMTExpr.response 

  val check_sat : ?timeout:int -> t -> SMTExpr.check_sat_response

  val check_sat_assuming : ?timeout:int -> t -> SMTExpr.t list -> SMTExpr.check_sat_response

  val get_value : t -> SMTExpr.t list -> SMTExpr.response * (SMTExpr.t * SMTExpr.t) list

  val get_unsat_core : t -> SMTExpr.response * string list

  val execute_custom_command : t -> string -> SMTExpr.custom_arg list -> int -> SMTExpr.response * HStringSExpr.t list

  val execute_custom_check_sat_command : string -> t -> SMTExpr.check_sat_response

end

let smtsolver_module () = match Flags.smtsolver () with 

  | `Z3_SMTLIB
  | `CVC4_SMTLIB
  | `MathSat5_SMTLIB
  | `Yices_SMTLIB -> (module SMTLIBSolver : Solver)

  | `detect -> raise (Invalid_argument "smtsolver_module")


(* Output signature of the Make functor *)
module type S =
sig

  type solver_t 

  type t

  val create_instance : 
    ?produce_assignments:bool -> 
    ?produce_models:bool -> 
    ?produce_proofs:bool -> 
    ?produce_cores:bool -> 
    SMTExpr.logic -> 
    t

  val delete_instance : t -> unit

  val declare_fun : t -> string -> SMTExpr.sort list -> SMTExpr.sort -> SMTExpr.response

  val define_fun : t -> string -> SMTExpr.var list -> SMTExpr.sort -> SMTExpr.t -> SMTExpr.response

  val assert_expr : t -> SMTExpr.t -> SMTExpr.response

  val push : t -> int -> SMTExpr.response 

  val pop : t -> int -> SMTExpr.response 

  val check_sat : ?timeout:int -> t -> SMTExpr.check_sat_response

  val check_sat_assuming : ?timeout:int -> t -> SMTExpr.t list -> SMTExpr.check_sat_response

  val get_value : t -> SMTExpr.t list -> SMTExpr.response * (SMTExpr.t * SMTExpr.t) list

  val get_unsat_core : t -> SMTExpr.response * string list

  val execute_custom_command : t -> string -> SMTExpr.custom_arg list -> int -> SMTExpr.response * HStringSExpr.t list

  val execute_custom_check_sat_command : string -> t -> SMTExpr.check_sat_response

end

(* Functor to create a generic SMT solver *)
module Make (S : Solver) : S with type solver_t = S.t = 
struct
  
  type solver_t = S.t

  type t = 
      { solver : solver_t; 
        id : int;
        trace_ppf : Format.formatter option }

  type attr = [ `NAME of string ]

  type expr = SMTExpr.t

  type sort

  let trace_cmd = function 
    | Some ppf -> (function fmt -> Format.fprintf ppf (fmt ^^ "@."))
    | None -> Format.ifprintf Format.std_formatter 

  let trace_res = function 
    | Some ppf -> 
      (function fmt -> 

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

        Format.kfprintf reset_ppf ppf (";; " ^^ fmt)

      )
    | None -> Format.ifprintf Format.std_formatter 

  let create_instance 
      ?produce_assignments
      ?produce_models
      ?produce_proofs
      ?produce_cores
      l = 
    
    let id = gentag () in

    (* Formatter writing to SMT trace file *)
    let trace_ppf = 

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
            
    in

    let pp_if_some fmt ppf = function
      | None -> ()
      | Some v -> Format.fprintf ppf fmt v
    in
    
    trace_cmd trace_ppf
      "@[<v>@[<hv 1>(set-option@ :print-success@ true)@]@,%a%a%a%a%t@]"
      (pp_if_some
         "@[<hv 1>(set-option@ :produce-assignments@ %B)@]@,") 
      produce_assignments
      (pp_if_some
         "@[<hv 1>(set-option@ :produce-models@ %B)@]@,")
      produce_models 
      (pp_if_some
        "@[<hv 1>(set-option@ :produce-proofs@ %B)@]@,")
      produce_proofs
      (pp_if_some
         "@[<hv 1>(set-option@ :produce-unsat-cores@ %B)@]@,")
      produce_cores
      (function ppf -> 
        match l with
          | `detect -> ()
          | _ -> 
            Format.fprintf ppf
              "@[<hv 1>(set-logic@ %a)@]" 
              SMTExpr.pp_print_logic l);

  let s = 
    S.create_instance 
      ?produce_assignments 
      ?produce_models
      ?produce_proofs
      ?produce_cores
      l 
  in

  { solver = s;
    id = id;
    trace_ppf = trace_ppf } 

  let delete_instance { solver = s; trace_ppf } = 

    trace_cmd trace_ppf
      "@[<hv 1>(exit)@]";
    
    S.delete_instance s


  let declare_fun { solver = s; trace_ppf } f a r = 

    trace_cmd trace_ppf
      "@[<hv 1>(declare-fun@ %s@ @[<hv 1>(%a)@]@ %a)@]" 
      f
      (pp_print_list SMTExpr.pp_print_sort "@ ") a
      SMTExpr.pp_print_sort r;

    let res = S.declare_fun s f a r in

    trace_res trace_ppf
      "%a" 
      SMTExpr.pp_print_response res;

    res


  let define_fun { solver = s; trace_ppf } f a r d = 

    trace_cmd trace_ppf
      "@[<hv 1>(define-fun@ %s@ @[<hv 1>(%a)@]@ %a@ %a)@]" 
      f
      (pp_print_list
         (fun ppf var -> 
            Format.fprintf ppf "(%a %a)" 
              Var.pp_print_var var
              SMTExpr.pp_print_sort (Var.type_of_var var))
         "@ ")
      a
      SMTExpr.pp_print_sort r
      SMTExpr.pp_print_expr d;

    let res = S.define_fun s f a r d in

    trace_res trace_ppf
      "%a" 
      SMTExpr.pp_print_response res;

    res


  let assert_expr { solver = s; trace_ppf } e = 
    
    trace_cmd trace_ppf "@[<hv 1>(assert@ @[<hv>%a@])@]" 
      SMTExpr.pp_print_expr e;
    
    let res = S.assert_expr s e in

    trace_res trace_ppf
      "%a" 
      SMTExpr.pp_print_response res;

    res

  let push { solver = s; trace_ppf } i = 

    trace_cmd trace_ppf "@[<hv 1>(push@ %i)@]" i;
    
    let res = S.push s i in

    trace_res trace_ppf
      "%a" 
      SMTExpr.pp_print_response res;

    res


  let pop { solver = s; trace_ppf } i = 
    
    trace_cmd trace_ppf "@[<hv 1>(pop@ %i)@]" i;
    
    let res = S.pop s i in
 
    trace_res trace_ppf
      "%a" 
      SMTExpr.pp_print_response res;

    res


  let check_sat ?(timeout = 0) { solver = s; trace_ppf } = 

    trace_cmd trace_ppf "@[<hv 1>(check-sat)@]";

    Stat.start_timer Stat.smt_check_sat_time;

    let res = S.check_sat ~timeout s in

    Stat.record_time Stat.smt_check_sat_time;

    trace_res trace_ppf
      "%a" 
      SMTExpr.pp_print_check_sat_response res;

    res


  let check_sat_assuming ?(timeout = 0) { solver = s; trace_ppf } exprs = 

    trace_cmd trace_ppf
      "@[<hv 1>(check-sat %a)@]"
      (pp_print_list SMTExpr.pp_print_expr "@ ") exprs;

    Stat.start_timer Stat.smt_check_sat_time;

    let res = S.check_sat_assuming ~timeout s exprs in

    Stat.record_time Stat.smt_check_sat_time;

    trace_res trace_ppf
      "%a" 
      SMTExpr.pp_print_check_sat_response res;

    res


  let get_value { solver = s; trace_ppf } e = 
    
    trace_cmd trace_ppf 
      "@[<hv 1>(get-value@ @[<hv 1>(%a)@])@]" 
      (pp_print_list SMTExpr.pp_print_expr "@ ") e;

    Stat.start_timer Stat.smt_get_value_time;

    let res = S.get_value s e in

    Stat.record_time Stat.smt_get_value_time;

    trace_res trace_ppf
      "%a" 
      SMTExpr.pp_print_get_value_response res;

    res


  let get_unsat_core { solver = s; trace_ppf } = 
    
    trace_cmd trace_ppf 
      "@[<hv 1>(get-unsat-core)@]";

    let (r, c) as res = S.get_unsat_core s in

    trace_res trace_ppf
      "%a@,(@[<hv 1>%a@])" 
      SMTExpr.pp_print_response r
      (pp_print_list Format.pp_print_string "@ ") c;

    res


  let execute_custom_command { solver = s; trace_ppf } c a r = 
    
    trace_cmd trace_ppf
      "@[<hv 1>(%s%t)@]" 
      c 
      (function ppf -> 
        if a = [] then () else 
          Format.fprintf 
            ppf 
            "@ %a" 
            (pp_print_list SMTExpr.pp_print_custom_arg "@ ") a);
    
    let (r, e) as res = S.execute_custom_command s c a r in

    trace_res trace_ppf
      "%a@,(@[<hv 1>%a@])" 
      SMTExpr.pp_print_response r
      (pp_print_list HStringSExpr.pp_print_sexpr "@ ") e;

    res

  let execute_custom_check_sat_command c { solver = s; trace_ppf } = 
    
    trace_cmd trace_ppf "@[<hv 1>(%s)@]" c; 
    
    let res = S.execute_custom_check_sat_command c s in

    trace_res trace_ppf
      "%a" 
      SMTExpr.pp_print_check_sat_response res;

    res


end

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
