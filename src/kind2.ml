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
open TermLib.Signals

module Refiner = Refiner
module Log = Log
module BMC = Base
module IND = Step
module PDR = PDR
module InvGenTS = InvGenGraph.TwoState
module InvGenOS = InvGenGraph.OneState
module TestGen = Testgen

let dbl_sep_line_warn () =
  Event.log
    L_info
    "|========================================|"

let sgl_sep_line_warn () =
  Event.log
    L_info
    "   -----------------------------------   "

(* Prints the final statistics of the analysis. *)
let print_final_statistics sys =

  (* Printing header. *)
  Event.log
    L_info
    "@[<v>%a@,Final statistics:@]"
    pp_print_hline () ;

  (* Printing stats for each module. *)
  Event.all_stats ()
  |> List.iter
       ( fun (mdl, stat) ->
         Event.log_stat mdl L_info stat ) ;

  (* Printing result for the properties of the top level. *)
  TransSys.get_prop_status_all sys
  |> Event.log_prop_status L_fatal


let print_hashcons_stats () =

  let pp_print_hashcons_stat ppf (l, c, t, s, m, g) =

    Format.fprintf
      ppf
      "Number of buckets: %d@,\
       Number of entries in table: %d@,\
       Sum of sizes of buckets: %d@,\
       Size of smallest bucket: %d@,\
       Median bucket size: %d@,\
       Size of greatest bucket: %d@,"
      l
      c
      t
      s
      m
      g

  in

  Event.log L_info
    "@[<hv>Hashconsing for state variables:@,%a@]"
    pp_print_hashcons_stat (StateVar.stats ());

  Event.log L_info
    "@[<hv>Hashconsing for variables:@,%a@]"
    pp_print_hashcons_stat (Var.stats ());

  Event.log L_info
    "@[<hv>Hashconsing for terms:@,%a@]"
    pp_print_hashcons_stat (Term.stats ());

  Event.log L_info
    "@[<hv>Hashconsing for symbols:@,%a@]"
    pp_print_hashcons_stat (Symbol.stats ())

(* Actually exits with an exit code. *)
let exit_of_status status =

  (* Close tags in XML output. *)
  Event.terminate_log () ;

  (* Exit with status. *)
  exit status


(* Check which SMT solver is available. *)
let check_smtsolver () =

  (* SMT solver from command-line. *)
  match Flags.smtsolver () with

    (* User chose Z3. *)
    | `Z3_SMTLIB ->

       let z3_exec =
         try
           (* Check if Z3 is on the path. *)
           Flags.z3_bin () |> find_on_path
         with
         | Not_found ->
            (* Fail if not. *)
            Event.log 
              L_fatal 
              "Z3 executable %s not found."
              (Flags.z3_bin ()) ;

            exit 2
       in

       Event.log
         L_info "Using Z3 executable %s." z3_exec

    (* User chose CVC4. *)
    | `CVC4_SMTLIB -> 

       let cvc4_exec = 
         try
           (* Check if CVC4 is on the path. *)
           Flags.cvc4_bin () |> find_on_path
         with 
         | Not_found -> 
            (* Fail if not. *)
            Event.log
              L_fatal
              "CVC4 executable %s not found."
              (Flags.cvc4_bin ()) ;

            exit 2
       in

       Event.log
         L_info
         "Using CVC4 executable %s."
         cvc4_exec

    (* User chose MathSat5. *)
    | `MathSat5_SMTLIB ->

       let mathsat5_exec =
         try
           (* Check if MathSat5 is on the path. *)
           Flags.mathsat5_bin () |> find_on_path
         with
         | Not_found ->
            (* Fail if not. *)
            Event.log
              L_fatal
              "MathSat5 executable %s not found."
              (Flags.mathsat5_bin ()) ;

            exit 2
       in

       Event.log
         L_info
         "Using MathSat5 executable %s." 
         mathsat5_exec


    (* User chose Yices. *)
    | `Yices_native -> 

       let yices_exec =
         try
           (* Check if MathSat5 is on the path *)
           Flags.yices_bin () |> find_on_path
         with
         | Not_found ->
            (* Fail if not. *)
            Event.log
              L_fatal
              "Yices executable %s not found."
              (Flags.yices_bin ()) ;

            exit 2
       in

       Event.log
         L_info
         "Using Yices executable %s." 
         yices_exec


    (* User chose Yices2. *)
    | `Yices_SMTLIB ->

       (* Not supported, failing. *)
       Event.log
         L_fatal
         "Yices2 is not supported at the moment." ;

       exit 2

    (*    let yices_exec = *)
    (*      try *)
    (*        (\* Check if MathSat5 is on the path. *\) *)
    (*        Flags.yices2smt2_bin () |> find_on_path *)
    (*      with *)
    (*      | Not_found -> *)
    (*         (\* Fail if not. *\) *)
    (*         Event.log *)
    (*           L_fatal *)
    (*           "Yices2 SMT2 executable %s not found." *)
    (*           (Flags.yices2smt2_bin ()) ; *)

    (*         exit 2 *)
    (*    in *)

    (*    Event.log *)
    (*      L_info *)
    (*      "Using Yices2 SMT2 executable %s."  *)
    (*      yices_exec *)


    (* User did not choose SMT solver. *)
    | `detect ->

       try

         let z3_exec =
           (* Check if z3 is on the path. *)
           Flags.z3_bin () |> find_on_path
         in

         Event.log
           L_info "Using Z3 executable %s." z3_exec ;

         (* Z3 is on path? *)
         Flags.set_smtsolver
           `Z3_SMTLIB
           z3_exec

      with Not_found ->

        try 

          let cvc4_exec =
            (* Check if cvc4 is on the path. *)
            Flags.cvc4_bin () |> find_on_path
          in

          Event.log
            L_info
            "Using CVC4 executable %s." 
            cvc4_exec;

          (* CVC4 is on path? *)
          Flags.set_smtsolver 
            `CVC4_SMTLIB
            cvc4_exec

        with Not_found ->

          try

            let mathsat5_exec =
              (* Check if mathsat is on the path. *)
              Flags.mathsat5_bin () |> find_on_path
            in

            Event.log
              L_info
              "Using MatSat5 executable %s." 
              mathsat5_exec ;

            (* MathSat5 is on path? *)
            Flags.set_smtsolver 
              `MathSat5_SMTLIB
              mathsat5_exec

          with Not_found -> 

            try 

              let yices_exec =
                (* Check if yices is on the path. *)
                Flags.yices_bin () |> find_on_path
              in

              Event.log
                L_info
                "Using Yices executable %s." 
                yices_exec;

              (* Yices is on path? *)
              Flags.set_smtsolver
                `Yices_SMTLIB
                yices_exec
                
            with Not_found ->
              
              Event.log L_fatal "No SMT Solver found." ;
              
              exit 2

(* Refines an [abstraction], returns [None] if it is pointless / not
   possible to refine further, and [Some abstraction'] otherwise. *)
let refine_further = Refiner.refine

let reset_props sys =
  TransSys.reset_non_valid_props_to_unknown sys

let reset_invariants sys =
  TransSys.reset_invariants sys

let lift_valids sys =
  TransSys.lift_valid_properties sys

let clean_up_sys sys =
  reset_props sys ;
  reset_invariants sys
  (* lift_valids sys *)

(* Prints final things. *)
let print_final_things sys log =

  if Flags.modular () || Flags.compositional () then (
    dbl_sep_line_warn () ;
    Event.log L_warn "Analysis breakdown:" ;

    Event.log
      L_warn
      "%a"
      Log.pp_print_log log
  ) else (
    sgl_sep_line_warn () ;
    print_final_statistics sys
  )

let launch_analysis sys log msg_setup =
  (* Set timeout if necessary. *)
  set_timeout_from_flag () ;
  match
    Analysis.run sys log msg_setup (Flags.enable ())
  with
  | Analysis.Ok
  | Analysis.Timeout ->
    (* No error, we can keep going. *)
    ()
  | Analysis.Error(status) ->
     (* Error, we must stop there. *)
     print_final_things sys log ;
     (* Exiting with corresponding status. *)
     exit status

let rec launch_compositional sys log msg_setup =

  sgl_sep_line_warn () ;

  Event.log_run_start L_warn sys ;

  (* Registering abstraction sublog in log. *)
  Log.add_abstraction_sublog log sys ;

  (* Resetting
     - non valid properties to unknown
     - invariants of the system to empty list
     and lifting valid properties from subsystems. *)
  clean_up_sys sys ;

  (* Launching. *)
  launch_analysis sys log msg_setup ;

  Event.log_run_stop L_warn sys ;

  minisleep 0.3 ;

  sgl_sep_line_warn () ;

  (* Looking at analysis outcome, deciding what to do next. *)
  if TransSys.all_props_actually_proved sys then (
    (* All properties were found valid, we're done. *)

    Event.log
      L_warn
      "Proved all properties for %a, done."
      TransSys.pp_print_trans_sys_name sys ;

  ) else (
    (* Some properties could not be proved, notifying user. *)

    Event.log
      L_warn
      "@[<v>\
       Could not prove all properties for %a:@ \
       %a@ \
       with@   \
       abstracted subsystem(s): [%a]@   \
       concrete   subsystem(s): [%a]@]"
      TransSys.pp_print_trans_sys_name sys
      (pp_print_list
         ( fun ppf (name, status) ->
           Format.fprintf
             ppf
             "    %s - %a"
             name
             TransSys.pp_print_prop_status_pt status )
         "@ ")
      ( TransSys.get_prop_status_all sys
        |> List.filter
             ( function
               | (_, TransSys.PropInvariant) -> false
               | _ -> true ) )
      Refiner.pp_print_abstracted sys
      Refiner.pp_print_concrete sys ;

    (* Can we refine the abstraction? *)
    match refine_further sys with

    (* No. *)
    | None ->
      Event.log
        L_warn
        "Can't refine %a further, done."
        TransSys.pp_print_trans_sys_name sys ;

    (* Yes we can. *)
    | Some nu_abs ->
       (* Notifying user. *)
       Event.log
        L_warn
        "Refining abstraction." ;
       (* Looping. *)
       launch_compositional sys log msg_setup

  )

let choose_compositional sys log msg_setup =

  if Flags.compositional () then (
    (* Building abstraction. *)
    Refiner.set_first_abstraction sys ;
    (* Launching compositional analysis. *)
    launch_compositional sys log msg_setup

  ) else (
    (* No abstraction. *)
    Refiner.set_no_abstraction sys ;
    (* Registering empty abstraction. *)
    Log.add_abstraction_sublog log sys ;
    (* Notifying user. *)
    (* sgl_sep_line_warn () ;
    Event.log
      L_warn
      "Analyzing system %a."
      TransSys.pp_print_trans_sys_name sys ; *)
    (* Launching normal analysis. *)
    launch_analysis sys log msg_setup
  )
    

let launch_modular systems log msg_setup =

  (* Loops over the systems to analyze. *)
  let rec loop = function

    (* No more systems to analyze. *)
    | [] -> ()

    (* Let's do this. *)
    | sys :: sys_tail ->

        Event.log_system_start L_warn sys ;

       (* Resetting
          - non valid properties to unknown
          - invariants of the system to empty list
          and lifting valid properties from subsystems. *)
       clean_up_sys sys ;

       ( if TransSys.get_prop_status_all sys = [] then
         (* Nothing to prove, skipping. *)
         Event.log
           L_warn
           "No property to prove for system %a."
           TransSys.pp_print_trans_sys_name sys

         else if TransSys.all_props_actually_proved sys then
           (* Everything is already proved, skipping. *)
           Event.log
             L_warn
             "All properties of system %a are already valid."
             TransSys.pp_print_trans_sys_name sys

         else
           (* Launching compositional or not. *)
           choose_compositional sys log msg_setup
       ) ;

       Event.log_system_stop L_warn sys ;

       (* Looping. *)
       loop sys_tail
  in

  (* Running on systems. *)
  loop systems



(* Launches the top level (potentially modular) analysis. *)
let launch sys msg_setup =

  sgl_sep_line_warn () ;
  Event.log_analysis_briefing L_warn sys ;

  (* Launching analysis, getting log back. *)
  let log, status =
    if Flags.modular () then (

      (* Getting all systems bottom up. *)
      let all_sys =
        TransSys.get_all_subsystems sys
      in
      (* Creating log. *)
      let log = Log.mk_log all_sys in

      (* Launching modular mode. *)
      launch_modular all_sys log msg_setup ;

      log, Analysis.status_of_exn Exit

    ) else (

      (* Creating log. *)
      let log = Log.mk_log [sys] in

      (* Launching normal mode. *)
      choose_compositional sys log msg_setup ;

      log, Analysis.status_of_exn Exit
    )
  in

  print_final_things sys log ;

  (* print_hashcons_stats () ; *)

  exit_of_status status


(* Sets everything up before launching top level analysis. *)
let setup_and_run sys =

  (* Warn if list of properties is empty. *)
  if ( TransSys.props_list_of_bound
         sys
         Numeral.zero ) = []
  then
    Event.log
      L_warn "No properties to prove." ;

  (* Which modules are enabled? *)
  ( match Flags.enable () with

    (* No modules enabled, error. *)
    | [] -> 
       Event.log
         L_fatal "Need at least one process enabled"

    (* Only running the interpreter. *)
    | [p] when p = `Interpreter ->
      Event.log
        L_warn
        "Running interpreter as a single process.";

      (* Set module currently running. *)
      Event.set_module p ;

      let exit_interpreter exn =
        (* Ignore SIGALRM from now on *)
        ignore_sigalrm () ;

        (* Cleanup before exiting. *)
        Interpreter.on_exit (Some sys) ;
        (* Terminate event log. *)
        Event.terminate_log () ;
        (* Exiting normally. *)
        Analysis.status_of_exn Exit
        |> exit 
      in

      ( try
          (* Run interpreter. *)
          Interpreter.main
            (Flags.interpreter_input_file ())
            sys ;
          (* Clean things and exit. *)
          exit_interpreter Exit
        with
        | e ->
           exit_interpreter e |> ignore ;
           raise e )

    (* Run some modules in parallel. *)
    | modules ->
      Event.log
        L_info
        "@[<hov>Running %a.@]"
        (pp_print_list pp_print_kind_module ",@ ")
        modules ;

      Event.log
        L_info
        "@[<v>Creating message setup.@]" ;

      (* Creating message setup. *)
      let msg_setup = Event.setup () in

      Event.log
        L_trace
        "Messaging initialized in supervisor." ;

      (* Initialize messaging for invariant manager, obtain a
         background thread with no workers. *)
      Event.run_im
        msg_setup [] Analysis.panic_exit ;

      (* Launching. *)
      launch sys msg_setup )
       

(* Entry point. *)
let main () =

  (* Parse command-line flags. *)
  Flags.parse_argv ();

  (* At least one debug section enabled? *)
  if Flags.debug () = [] then

    (* Initialize debug output when no debug section enabled. *)
    Debug.initialize ()

  else (

    (* Formatter to write debug output to. *)
    let debug_formatter =
      match Flags.debug_log () with

      (* Write to stdout by default. *)
      | None -> Format.std_formatter

      (* Open channel to given file and create formatter on channel. *)
      | Some f ->
         ( try open_out f with
           | Sys_error _ -> failwith "Could not open debug logfile." )
         |> Format.formatter_of_out_channel

    in

    (* Enable each requested debug section and write to formatter. *)
    Flags.debug ()
    |> List.iter 
         ( fun s ->
           Debug.enable s debug_formatter ) ;

  );

  (* Set log format to XML if requested .*)
  if Flags.log_format_xml () then
    Event.set_log_format_xml () ;

  (* No output at all? *)
  if not (Flags.log_level () = L_off) then (

    (* Temporarily set log level to info and output logo. *)
    set_log_level L_info ;
    Event.log L_info "%a" pp_print_banner ()

  );

  (* Set log level. *)
  set_log_level (Flags.log_level ()) ;

  (* Record backtraces on log levels debug and higher. *)
  if output_on_level L_debug then
    Printexc.record_backtrace true ;

  (* Check and set SMT solver. *)
  check_smtsolver () ;

  (* Must not use vtalrm signal, this is used internally by the OCaml
     Threads module. *)

  (* Set sigalrm to raise an exception by default. *)
  set_sigalrm_exn () ;

  (* Raise exception on CTRL+C. *)
  catch_break true ;

  (* Install generic signal handler for SIGINT. *)
  set_sigint () ;

  (* Install generic signal handler for SIGTERM. *)
  set_sigterm () ;

  (* Install generic signal handler for SIGQUIT. *)
  set_sigquit () ;

  (* Set timeout from timeout flag. *)
  set_timeout_from_flag () ;

  Stat.start_timer Stat.total_time ;

  try

    (* Temporarily setting module to parsing. *)
    Event.set_module `Parser ;

    Event.log
      L_info
      "Parsing input file %s."
      (Flags.input_file ()) ;

    (* Parse file into two-state transition system. *)
    let trans_sys =
      ( match Flags.input_format () with

        | `Lustre ->
           LustreInput.of_file
             (Flags.enable () = [`Interpreter])
             (Flags.input_file ())

        | `Native -> (

          (* Some (NativeInput.of_file (Flags.input_file ())) *)

          Event.log
            L_fatal
            "Native input deactivated while \
             refactoring transition system." ;
          
          assert false

        )

        | `Horn ->
           (* Horn.of_file (Flags.input_file ()) *)
           assert false )
    in

    (* Output the transition system. *)
    ( debug
        parse
        "%a"
        TransSys.pp_print_trans_sys trans_sys
      end ) ;

    (* Set module to supervisor. *)
    Event.set_module `Supervisor ;

    (* setup_and_run trans_sys *)

    Testgen.main trans_sys

    (* if Flags.modular () then ( *)
    (*   let all_systems = *)
    (*     TransSys.get_all_subsystems (get !trans_sys) *)
    (*   in *)
    (*   log_ref := Some (Log.mk_log all_systems) ; *)
    (*   launch_modular_analysis (get !trans_sys) *)
    (* ) else ( *)
    (*   log_ref := Some (Log.mk_log [get !trans_sys]) ; *)
    (*   launch_analysis true (get !trans_sys) *)
    (* ) *)

  with

  | e ->
     (* There should not be anything left to clean it this level. *)
     Event.log
       L_error
       "Exception caught at top level." ;

     exit (Analysis.status_of_exn e)

;;

main ()



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
