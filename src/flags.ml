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

(* Workflow: see [flags.mli]. *)

(* Raised on unknown flag. Stores the unknown flag. *)
exception UnknownFlag of string
(* Raised on bad argument for existing flag. Stores an explanation, the flag
and the description of the flag. *)
exception BadArg of string * (string * Arg.spec * (Format.formatter -> unit))


(* Strings recognized as the bool value [true]. *)
let true_strings = [ "true" ; "on" ; "t" ]
(* Strings recognized as the bool value [false]. *)
let false_strings = [ "false" ; "off" ; "f" ]

(* Bool formatter. *)
let fmt_bool fmt b =
  Format.fprintf fmt "%s" (if b then "true" else "false")

(* Parses a bool and sets a reference. *)
let bool_arg reference = Arg.Bool (fun b -> reference := b)


(* Prints a flag [(flag, spec, desc)]. *)
let fmt_flag fmt (flag, spec, desc) =
  Format.fprintf
    fmt
    "@[<v>%t@[<v>%t@]@]"
    (fun fmt -> match spec with
      | Arg.Unit _ | Arg.Set _ | Arg.Clear _ ->
        Format.fprintf fmt "\x1b[1m%-10s\x1b[0m " flag
      | Arg.Bool _ ->
        Format.fprintf fmt "\x1b[1m%s <bool>\x1b[0m@   " flag
      | Arg.String _ | Arg.Set_string _ ->
        Format.fprintf fmt "\x1b[1m%s <string>\x1b[0m@   " flag
      | Arg.Int _ | Arg.Set_int _ ->
        Format.fprintf fmt "\x1b[1m%s <int>\x1b[0m@   " flag
      | Arg.Float _ | Arg.Set_float _ ->
        Format.fprintf fmt "\x1b[1m%s <float>\x1b[0m@   " flag
      | _ ->
        failwith "Unsupported Arg.spec (Tuple, Symbol, or Rest)."
    )
    desc

(* Prints all the flags in the input list, given a triples of the flag,
its spec, and its description. *)
let print_flags =
  Format.printf "@[<v>%a@]" (pp_print_list fmt_flag "@ ")


module Make_Spec (_:sig end) = struct
  (* All the flag specification of this module. *)
  let all_specs = ref []
  let format_specs = ref []
  let add_specs specs = all_specs := List.rev_append specs !all_specs
  let add_spec flag parse desc = all_specs := (flag, parse, desc) :: !all_specs
  let add_format_spec flag parse desc =
    add_spec flag parse desc; format_specs := (flag, parse, desc) :: !format_specs

  (* Returns all the flag specification of this module. *)
  let all_specs () = !all_specs
  let format_specs () = !format_specs
end

(* Signature of modules for flags. *)
module type FlagModule = sig
  (* Identifier of the module. *)
  val id: string
  (* Short description of the module. *)
  val desc: string
  (* Explanation of the module. *)
  val fmt_explain: Format.formatter -> unit
  (* Specifications of all the flags in the module. *)
  val all_specs: unit -> (
    string * Arg.spec * (Format.formatter -> unit)
  ) list
end



(* Options related to the underlying SMT solver. *)
module Smt = struct

  include Make_Spec (struct end)
  
  (* Identifier of the module. *)
  let id = "smt"
  (* Short description of the module. *)
  let desc = "SMT solver flags"
  (* Explanation of the module. *)
  let fmt_explain fmt =
    Format.fprintf fmt "@[<v>\
      SMT solvers are the tools Kind 2 relies on to verify systems. Flags@ \
      in this module control which solver Kind 2 uses, the path to the@ \
      binary, and tweak how Kind 2 interacts with the solver at runtime.\
    @]"

  (* Active SMT solver. *)
  type solver = [
    | `MathSAT_SMTLIB
    | `Boolector_SMTLIB
    | `Z3_SMTLIB
    | `CVC4_SMTLIB
    | `Yices_SMTLIB
    | `Yices_native
    | `detect
  ]
  let solver_of_string = function
    | "MathSAT" ->  `MathSAT_SMTLIB
    | "Boolector" -> `Boolector_SMTLIB
    | "Z3" -> `Z3_SMTLIB
    | "CVC4" -> `CVC4_SMTLIB
    | "Yices2" -> `Yices_SMTLIB
    | "Yices" -> `Yices_native
    | _ -> Arg.Bad "Bad value for --smt_solver" |> raise
  let string_of_solver = function
    | `MathSAT_SMTLIB -> "MathSAT"
    | `Boolector_SMTLIB -> "Boolector"
    | `Z3_SMTLIB -> "Z3"
    | `CVC4_SMTLIB -> "CVC4"
    | `Yices_SMTLIB -> "Yices2"
    | `Yices_native -> "Yices"
    | `detect -> "detect"
  let solver_values = "Z3, CVC4, Yices, Yices2, Boolector, MathSAT"
  let solver_default = `detect
  let solver = ref solver_default
  let _ = add_spec
    "--smt_solver"
    (Arg.String (fun str -> solver := solver_of_string str))
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          where <string> can be %s@ \
          Set the main SMT solver@ \
          Default: %s\
        @]"
        solver_values
        (string_of_solver solver_default)
    )
  let set_solver s = solver := s
  let solver () = !solver

  type qe_solver = [
    | `Z3_SMTLIB
    | `CVC4_SMTLIB
    | `detect
  ]
  let qe_solver_of_string = function
    | "Z3" -> `Z3_SMTLIB
    | "CVC4" -> `CVC4_SMTLIB
    | _ -> Arg.Bad "Bad value for --smt_qe_solver" |> raise
  let string_of_qe_solver = function
    | `Z3_SMTLIB -> "Z3"
    | `CVC4_SMTLIB -> "CVC4"
    | `detect -> "detect"
  let qe_solver_values = "Z3, CVC4"
  let qe_solver_default = `detect
  let qe_solver = ref qe_solver_default
  let _ = add_spec
    "--smt_qe_solver"
    (Arg.String (fun str -> qe_solver := qe_solver_of_string str))
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          where <string> can be %s@ \
          Set the SMT solver used for quantifier elimination@ \
          Default: %s\
        @]"
        qe_solver_values
        (string_of_qe_solver qe_solver_default)
    )
  let set_qe_solver s = qe_solver := s
  let qe_solver () = !qe_solver

  (* Active SMT logic. *)
  type logic = [
    `None | `detect | `Logic of string
  ]
  let logic_values = [
    `None ; `detect ; `Logic ("\"logic\"")
  ]
  let logic_of_string = function
    | "none" | "None" -> `None
    | "detect" | "Detect" -> `detect
    | s -> `Logic s
  let string_of_logic = function
    | `None -> "none"
    | `detect -> "detect"
    | `Logic s -> s
  let logic_default = `detect
  let logic = ref logic_default
  let _ = add_spec
    "--smt_logic"
    (Arg.String (fun str -> logic := logic_of_string str))
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          where <string> is none, detect, or a legal SMT-LIB logic@ \
          Select logic for SMT solvers@ \
          \"none\" for no logic@ \
          \"detect\" to detect with the input system@ \
          Other SMT-LIB logics will be passed to the solver@ \
          Default: %s\
        @]"
        (string_of_logic logic_default)
    )

  let set_logic l = logic := l
    
  let detect_logic_if_none () =
    if !logic = `None then logic := `detect
          
  let logic () = !logic

  (* Activates check-sat with assumptions when supported. *)
  let check_sat_assume_default = true
  let check_sat_assume = ref check_sat_assume_default
  let _ = add_spec
    "--check_sat_assume"
    (bool_arg check_sat_assume)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Use check-sat-assuming, or simulate with push/pop@ \
          when false@ \
          Default: %a\
        @]"
      fmt_bool check_sat_assume_default
    )
  let set_check_sat_assume b = check_sat_assume := b
  let check_sat_assume () = !check_sat_assume

  (* Use short name for variables at SMT level. *)
  let short_names_default = true
  let short_names = ref short_names_default
  let _ = add_spec
    "--smt_short_names"
    (bool_arg short_names)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Send short variables names to SMT solver, send full names if false@ \
          Default: %a\
        @]"
      fmt_bool short_names_default
    )
  let set_short_names b = short_names := b
  let short_names () = !short_names


  (* MathSAT binary. *)
  let mathsat_bin_default = "mathsat"
  let mathsat_bin = ref mathsat_bin_default
  let _ = add_spec
    "--mathsat_bin"
    (Arg.Set_string mathsat_bin)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Executable of MathSAT solver@ Default: \"%s\"@]"
        mathsat_bin_default
    )
  let set_mathsat_bin str = mathsat_bin := str
  let mathsat_bin () = !mathsat_bin

  (* Boolector binary. *)
  let boolector_bin_default = "boolector"
  let boolector_bin = ref boolector_bin_default
  let _ = add_spec
    "--boolector_bin"
    (Arg.Set_string boolector_bin)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Executable of Boolector solver@ Default: \"%s\"@]"
        boolector_bin_default
    )
  let set_boolector_bin str = boolector_bin := str
  let boolector_bin () = !boolector_bin

  (* Z3 binary. *)
  let z3_bin_default = "z3"
  let z3_bin = ref z3_bin_default
  let _ = add_spec
    "--z3_bin"
    (Arg.Set_string z3_bin)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Executable of Z3 solver@ Default: \"%s\"@]"
        z3_bin_default
    )
  let set_z3_bin str = z3_bin := str
  let z3_bin () = ! z3_bin

  let z3_qe_light = ref false
  let set_z3_qe_light b = z3_qe_light := b
  let z3_qe_light () = !z3_qe_light

  (* CVC4 binary. *)
  let cvc4_bin_default = "cvc4"
  let cvc4_bin = ref cvc4_bin_default
  let _ = add_spec
    "--cvc4_bin"
    (Arg.Set_string cvc4_bin)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Executable of CVC4 solver@ Default: \"%s\"@]"
        cvc4_bin_default
    )
  let set_cvc4_bin str = cvc4_bin := str
  let cvc4_bin () = !cvc4_bin

  let cvc4_rewrite_divk = ref true
  let set_cvc4_rewrite_divk b = cvc4_rewrite_divk := b
  let cvc4_rewrite_divk () = !cvc4_rewrite_divk

  let cvc4_bv_consts_in_binary = ref true
  let set_cvc4_bv_consts_in_binary b = cvc4_bv_consts_in_binary := b
  let cvc4_bv_consts_in_binary () = !cvc4_bv_consts_in_binary

  (* Yices binary. *)
  let yices_bin_default = "yices"
  let yices_bin = ref yices_bin_default
  let _ = add_spec
    "--yices_bin"
    (Arg.Set_string yices_bin)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Executable of Yices solver@ Default: \"%s\"@]"
        yices_bin_default
    )
  let set_yices_bin str = yices_bin := str
  let yices_bin () = !yices_bin

  (* Yices 2 binary. *)
  let yices2smt2_bin_default = "yices-smt2"
  let yices2smt2_bin = ref yices2smt2_bin_default
  let _ = add_spec
    "--yices2_bin"
    (Arg.Set_string yices2smt2_bin)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Executable of Yices2 SMT2 solver@ Default: \"%s\"@]"
        yices2smt2_bin_default
    )
  let set_yices2smt2_bin str = yices2smt2_bin := str
  let yices2smt2_bin () = !yices2smt2_bin

  let yices2_smt2models = ref false
  let set_yices2_smt2models b = yices2_smt2models := b
  let yices2_smt2models () = !yices2_smt2models

  (* Activates logging of SMT interactions. *)
  let trace_default = false
  let trace = ref trace_default
  let _ = add_spec
    "--smt_trace"
    (Arg.Set trace)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Write all SMT commands to files@]"
    )
  let set_trace b = trace := b
  let trace () = !trace

  (* Folder to log the SMT traces into. *)
  let trace_dir = ref "."
  let set_trace_dir s =
    trace_dir := Filename.concat s "smt_trace"
  let trace_dir () = !trace_dir



  let find_solver ~fail name bin =
    (* Check if solver execdutable is on the path *)
    try find_on_path bin with
    | Not_found when fail ->
      Log.log L_fatal "@[<v>%s executable %s not found.@]" name bin;
      exit 2

  
  (* Check which SMT solver is available *)
  let check_smtsolver () = match solver () with
    (* User chose MathSAT *)
    | `MathSAT_SMTLIB ->
      find_solver ~fail:true "MathSAT" (mathsat_bin ()) |> ignore
    (* User chose Boolector *)
    | `Boolector_SMTLIB ->
      find_solver ~fail:true "Boolector" (boolector_bin ()) |> ignore
    (* User chose Z3 *)
    | `Z3_SMTLIB ->
      find_solver ~fail:true "Z3" (z3_bin ()) |> ignore
    (* User chose CVC4 *)
    | `CVC4_SMTLIB ->
      find_solver ~fail:true "CVC4" (cvc4_bin ()) |> ignore
    (* User chose Yices *)
    | `Yices_native ->
      find_solver ~fail:true "Yices" (yices_bin ()) |> ignore
    (* User chose Yices2 *)
    | `Yices_SMTLIB ->
      find_solver ~fail:true "Yices2 SMT2" (yices2smt2_bin ()) |> ignore
    (* User did not choose SMT solver *)
    | `detect ->
      try
        let exec = find_solver ~fail:false "Z3" (z3_bin ()) in
        set_solver `Z3_SMTLIB;
        set_z3_bin exec;
      with Not_found ->
      try
        let exec = find_solver ~fail:false "Yices2 SMT2" (yices2smt2_bin ()) in
        set_solver `Yices_SMTLIB;
        set_yices2smt2_bin exec;
      with Not_found ->
      try
        let exec = find_solver ~fail:false "CVC4" (cvc4_bin ()) in
        set_solver `CVC4_SMTLIB;
        set_cvc4_bin exec;
      with Not_found ->
      try
        let exec = find_solver ~fail:false "Yices" (yices_bin ()) in
        set_solver `Yices_native;
        set_yices_bin exec;
      with Not_found ->
      try
        let exec = find_solver ~fail:false "Boolector" (boolector_bin ()) in
        set_solver `Boolector_SMTLIB;
        set_boolector_bin exec;
      with Not_found ->
      try
        let exec = find_solver ~fail:false "MathSAT" (mathsat_bin ()) in
        set_solver `MathSAT_SMTLIB;
        set_mathsat_bin exec;
      with Not_found ->
        Log.log L_fatal "No SMT Solver found.";

        exit 2

  let check_qe_solver () = match qe_solver () with
    (* User chose Z3 *)
    | `Z3_SMTLIB -> (
      match solver () with
      | `Z3_SMTLIB -> ()
      | _ -> find_solver ~fail:true "Z3" (z3_bin ()) |> ignore
    )
    (* User chose CVC4 *)
    | `CVC4_SMTLIB -> (
      match solver () with
      | `CVC4_SMTLIB -> ()
      | _ -> find_solver ~fail:true "CVC4" (cvc4_bin ()) |> ignore
    )
    | `detect ->
      match solver () with
      | `Z3_SMTLIB -> set_qe_solver `Z3_SMTLIB;
      | _ ->
        try
          let exec = find_solver ~fail:false "Z3" (z3_bin ()) in
          set_qe_solver `Z3_SMTLIB;
          set_z3_bin exec;
        with Not_found ->
        match solver () with
        | `CVC4_SMTLIB -> set_qe_solver `CVC4_SMTLIB;
        | _ ->
          try
            let exec = find_solver ~fail:false "CVC4" (cvc4_bin ()) in
            set_qe_solver `CVC4_SMTLIB;
            set_cvc4_bin exec;
          with Not_found -> () (* Ẃe keep `detect to know no qe solver was found *)
end




(* BMC and k-induction flags. *)
module BmcKind = struct

  include Make_Spec (struct end)

  (* Identifier of the module. *)
  let id = "ind"
  (* Short description of the module. *)
  let desc = "BMC / K-induction flags"
  (* Explanation of the module. *)
  let fmt_explain fmt =
    Format.fprintf fmt "@[<v>\
      K-induction is the primary verification technique in Kind 2. It@ \
      consists of two processes:@ \
      > bounded model checking (BMC) explores the reachable states of the\
      @   system looking for a falsification of one of the properties.@ \
      > the (k-inductive) step tries to prove that from `k` succeeding states\
      @   verifying the properties, it not possible to reach a state violating\
      @   any of them. If this holds, then if BMC proved these properties to\
      @   hold in the `k` first states, then by (k-)induction the properties\
      @   hold.@ \
      Internally many techniques such as path compression, multi-property,@ \
      etc. are used to improve the basic scheme described above.@ \
      Flags in this module deal with the behavior of BMC and step.\
    @]"

  let max_default = 0
  let max = ref max_default
  let _ = add_spec
    "--unroll_max"
    (Arg.Set_int max)
    (fun fmt ->
      Format.fprintf fmt
      "@[<v>\
        Maximal number of iterations for BMC and k-induction@ \
        Default: %d (unlimited: 0)\
      @]"
      max_default
    )
  let max () = !max

  let check_unroll_default = true
  let check_unroll = ref check_unroll_default
  let _ = add_spec
    "--bmc_check_unroll"
    (bool_arg check_unroll)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Check that the unrolling alone is satisfiable@ \
          Default: %a\
        @]"
        fmt_bool check_unroll_default
    )
  let check_unroll () = !check_unroll

  let print_cex_default = false
  let print_cex = ref print_cex_default
  let _ = add_spec
    "--ind_print_cex"
    (bool_arg print_cex)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Print counterexamples to induction@ Default: %a@]"
        fmt_bool print_cex_default
    )
  let print_cex () = !print_cex

  let compress_default = true
  let compress = ref compress_default
  let _ = add_spec
    "--ind_compress"
    (bool_arg compress)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Compress inductive counterexamples@ Default: %a@]"
        fmt_bool compress_default
    )

  let disable_compress () = compress := false
  
  let compress () = !compress

  let compress_equal_default = true
  let compress_equal = ref compress_equal_default
  let _ = add_spec
    "--ind_compress_equal"
    (bool_arg compress_equal)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Compress inductive counterexamples for states equal modulo inputs@ \
          Default: %a\
        @]"
        fmt_bool compress_equal_default
    )
  let compress_equal () = !compress_equal

  let compress_same_succ_default = false
  let compress_same_succ = ref compress_same_succ_default
  let _ = add_spec
    "--ind_compress_same_succ"
    (bool_arg compress_same_succ)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Compress inductive counterexamples for states with same successors@ \
          Default: %a\
        @]"
        fmt_bool compress_same_succ_default
    )
  let compress_same_succ () = !compress_same_succ

  let compress_same_pred_default = false
  let compress_same_pred = ref compress_same_pred_default
  let _ = add_spec
    "--ind_compress_same_pred"
    (bool_arg compress_same_pred)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Compress inductive counterexamples for states with same predecessors@ \
          Default: %a\
        @]"
        fmt_bool compress_same_pred_default
    )
  let compress_same_pred () = !compress_same_pred

  let lazy_invariants_default = false
  let lazy_invariants = ref lazy_invariants_default
  let _ = add_spec
    "--ind_lazy_invariants"
    (bool_arg lazy_invariants)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Asserts invariants lazily@ Default: %a@]"
        fmt_bool lazy_invariants_default
    )
  let lazy_invariants () = !lazy_invariants

end



(* IC3 flags. *)
module IC3 = struct

  include Make_Spec (struct end)

  (* Identifier of the module. *)
  let id = "ic3"
  (* Short description of the module. *)
  let desc = "IC3 flags"
  (* Explanation of the module. *)
  let fmt_explain fmt =
    Format.fprintf fmt "@[<v>\
      IC3 (a.k.a. PDR) is a relatively recent technique that tries to prove@ \
      a property by contructing an inductive invariant that implies it.@ \
      The IC3 engine in Kind 2 performs quantifier elimination which has its@ \
      own flags (see module \"qe\").\
    @]"

  let check_inductive_default = true
  let check_inductive = ref check_inductive_default
  let _ = add_spec
    "--ic3_check_inductive"
    (bool_arg check_inductive)
    (fun fmt ->
    Format.fprintf fmt
      "@[<v>Check inductiveness of blocking clauses@ Default: %a@]"
      fmt_bool check_inductive_default
    )
  let check_inductive () = !check_inductive

  let print_to_file_default = None
  let print_to_file = ref print_to_file_default
  let _ = add_spec
    "--ic3_print_to_file"
    (Arg.String (fun str -> print_to_file := Some str))
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          where <string> is a file path in an existing directory.@ \
          Output file for blocking clauses@ \
          Default: stdout\
        @]"
    )
  let print_to_file () = !print_to_file

  let inductively_generalize_default = 1
  let inductively_generalize = ref inductively_generalize_default
  let _ = add_spec
    "--ic3_inductively_generalize"
    (Arg.Set_int inductively_generalize)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Inductively generalize blocking clauses before forward propagation@ \
          0 = none@ \
          1 = normal IG@ \
          2 = IG with ordering@ \
          Default: %s\
        @]"
        (string_of_int inductively_generalize_default)
    )
  let inductively_generalize () = !inductively_generalize

  let block_in_future_default = true
  let block_in_future = ref block_in_future_default
  let _ = add_spec
    "--ic3_block_in_future"
    (bool_arg block_in_future)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Block counterexample in future frames@ Default: %a@]"
        fmt_bool block_in_future_default
    )
  let block_in_future () = !block_in_future

  let block_in_future_first_default = true
  let block_in_future_first = ref block_in_future_first_default
  let _ = add_spec
    "--ic3_block_in_future_first"
    (bool_arg block_in_future_first)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Block counterexample in future frames first before returning to@ \
          frame@ \
          Default: %a\
        @]"
        fmt_bool block_in_future_first_default
    )
  let block_in_future_first () = !block_in_future_first

  let fwd_prop_non_gen_default = true
  let fwd_prop_non_gen = ref fwd_prop_non_gen_default
  let _ = add_spec
    "--ic3_fwd_prop_non_gen"
    (bool_arg fwd_prop_non_gen)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Also propagate clauses before generalization@ Default: %a@]"
        fmt_bool fwd_prop_non_gen_default
    )
  let fwd_prop_non_gen () = !fwd_prop_non_gen

  let fwd_prop_ind_gen_default = true
  let fwd_prop_ind_gen = ref fwd_prop_ind_gen_default
  let _ = add_spec
    "--ic3_fwd_prop_ind_gen"
    (bool_arg fwd_prop_ind_gen)
    (fun fmt ->
      Format.fprintf fmt
      "@[<v>\
        Inductively generalize all clauses after forward propagation@ \
        Default: %a\
      @]"
      fmt_bool fwd_prop_ind_gen_default
    )
  let fwd_prop_ind_gen () = !fwd_prop_ind_gen

  let fwd_prop_subsume_default = true
  let fwd_prop_subsume = ref fwd_prop_subsume_default
  let _ = add_spec
    "--ic3_fwd_prop_subsume"
    (bool_arg fwd_prop_subsume)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Subsumption in forward propagation@ Default: %a@]"
        fmt_bool fwd_prop_subsume_default
    )
  let fwd_prop_subsume () = !fwd_prop_subsume

  let use_invgen_default = true
  let use_invgen = ref use_invgen_default
  let _ = add_spec
    "--ic3_use_invgen"
    (bool_arg use_invgen)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Use invariants from invariant generators@ Default: %a@]"
        fmt_bool use_invgen_default
    )
  let use_invgen () = !use_invgen

  type abstr = [ `None | `IA ]
  let abstr_of_string = function
    | "None" -> `None
    | "IA" -> `IA
    | _ -> raise (Arg.Bad "Bad value for --ic3_abstr")
  let string_of_abstr = function
    | `IA -> "IA"
    | `None -> "None"
  let abstr_values = [
    `None ; `IA
  ] |> List.map string_of_abstr |> String.concat ", "
  let abstr_default = `None
  let abstr = ref abstr_default
  let _ = add_spec
    "--ic3_abstr"
    (Arg.String (fun str -> abstr := abstr_of_string str))
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          where <string> can be %s@ \
          Choose method of abstraction in IC3@ \
          Default: %s\
        @]"
        abstr_values (string_of_abstr abstr_default)
    )
  let abstr () = !abstr

end


(* Quantifier elimination module. *)
module QE = struct

  include Make_Spec (struct end)

  (* Identifier of the module. *)
  let id = "qe"
  (* Short description of the module. *)
  let desc = "quantifier elimination flags"
  (* Explanation of the module. *)
  let fmt_explain fmt =
    Format.fprintf fmt "@[<v>\
      Quantifier elimination (QE) is a technique that, given some variables@ \
      `v_1`, ..., `v_n` and a quantifier-free formula `f`, returns a@ \
      quantifier-free formula equivalent to `(exists (v_1, ..., v_n) f)`.@ \
      The QE method implemented in Kind 2 supports integer arithmetic,@ \
      but not real or machine integer arithmetic. If the solver used is@ \
      Z3 or CVC4 then the solver's QE will be used instead of the internal@ \
      one for systems with real or machine integer variables.@ \
      IC3 (module \"ic3\") is the only Kind 2 technique that uses QE.\
    @]"

  type qe_method = [
    `Precise | `Impl | `Impl2 | `Cooper
  ]
  let qe_method_of_string = function
    | "precise" -> `Precise
    | "impl" -> `Impl
    | "impl2" -> `Impl2
    | "cooper" -> `Cooper
    | _ -> raise (Arg.Bad "Bad value for --qe_method")
  let string_of_qe_method = function
    | `Precise -> "precise"
    | `Impl -> "impl"
    | `Impl2 -> "impl2"
    | `Cooper -> "cooper"
  let qe_method_values = [
    `Precise ; `Impl ; `Impl2 ; `Cooper
  ] |> List.map string_of_qe_method |> String.concat ", "
  let qe_method_default = `Cooper
  let qe_method = ref qe_method_default
  let _ = add_spec
    "--qe_method"
    (Arg.String (fun str -> qe_method := qe_method_of_string str))
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          where <string> can be %s@ \
          Choose quantifier elimination method@ \
          Default: %s\
        @]"
        qe_method_values (string_of_qe_method qe_method_default)
    )
  let set_qe_method q = qe_method := q
  let qe_method () = !qe_method

  type extract = [ `First | `Vars ]
  let extract_of_string = function
    | "first" -> `First
    | "vars" -> `Vars
    | _ -> raise (Arg.Bad "Bad value for --qe_extract")
  let string_of_extract = function
    | `First -> "first"
    | `Vars -> "vars"
  let extract_values = [
    `First ; `Vars
  ] |> List.map string_of_extract |> String.concat ", "
  let extract_default = `First
  let extract = ref extract_default
  let _ = add_spec
    "--qe_extract"
    (Arg.String (fun str -> extract := extract_of_string str))
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          where <string> can be %s@ \
          Heuristics for extraction of implicant@ \
          Default: %s\
        @]"
        extract_values (string_of_extract extract_default)
    )
  let extract () = !extract

  let ae_val_use_ctx_default = true
  let ae_val_use_ctx = ref ae_val_use_ctx_default
  let _ = add_spec
    "--ae_val_use_ctx"
    (bool_arg ae_val_use_ctx)
    (fun fmt ->
      Format.fprintf fmt
      "@[<v>\
        Use context (premises) in ae_val procedure@ \
        Default: %a\
      @]"
      fmt_bool ae_val_use_ctx_default
    )
  let ae_val_use_ctx () = !ae_val_use_ctx

  let order_var_by_elim_default = false
  let order_var_by_elim = ref order_var_by_elim_default
  let _ = add_spec
    "--order_var_by_elim"
    (bool_arg order_var_by_elim)
    (fun fmt ->
      Format.fprintf fmt
      "@[<v>\
        Order variables in polynomials by order of elimination@ \
        Default: %a\
      @]"
      fmt_bool order_var_by_elim_default
    )
  let order_var_by_elim () = !order_var_by_elim

  let general_lbound_default = false
  let general_lbound = ref general_lbound_default
  let _ = add_spec
    "--general_lbound"
    (bool_arg general_lbound)
    (fun fmt ->
      Format.fprintf fmt
      "@[<v>\
        Choose lower bounds containing variables@ \
        Default: %a\
      @]"
      fmt_bool general_lbound_default
    )
  let general_lbound () = !general_lbound
end




(* Contracts flags. *)
module Contracts = struct

  include Make_Spec (struct end)

  (* Identifier of the module. *)
  let id = "contracts"
  (* Short description of the module. *)
  let desc = "contract and compositional verification flags"
  (* Explanation of the module. *)
  let fmt_explain fmt =
    Format.fprintf fmt "@[<v>\
      Kind 2 extends Lustre with a syntax for assume-guarantee-like@ \
      contracts. The syntax and semantics of contracts are described in@ \
      Kind 2 documentation.@ \
      Contracts allow to perform compositional verification, where sub-nodes@ \
      with a contract are abstracted away by their specification. Also, the@ \
      test generation technique (see module \"testgen\") relies on contracts@ \
      to generate the testcases.\
    @]"

  let compositional_default = false
  let compositional = ref compositional_default
  let _ = add_spec
    "--compositional"
    (bool_arg compositional)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Abstract subnodes with a contract@ Default: %a@]"
        fmt_bool compositional_default
    )
  let compositional () = !compositional

  let translate_default = None
  let translate = ref translate_default
  let _ = add_spec
    "--translate_contracts"
    ( Arg.String (fun str -> translate := Some str) )
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Translates a contracts in assertions / properties (experimental)@ \
          Default: %t@]"
        (fun fmt ->
          Format.fprintf fmt "%s" (
            match translate_default with
            | None -> "off"
            | Some f -> f
          )
        )
    )
  let translate_contracts () = !translate

  let check_modes_default = true
  let check_modes = ref check_modes_default
  let _ = add_spec
    "--check_modes"
    (bool_arg check_modes)
    (fun fmt ->
      Format.fprintf fmt
      "@[<v>\
        Checks the modes of a contracts are exhaustive@ \
        Default: %a\
      @]"
      fmt_bool check_modes_default
    )
  let check_modes () = !check_modes

  let check_implem_default = true
  let check_implem = ref check_implem_default
  let _ = add_spec
    "--check_implem"
    (bool_arg check_implem)
    (fun fmt ->
      Format.fprintf fmt
      "@[<v>\
        Checks the implementation of nodes@ \
        Default: %a\
      @]"
      fmt_bool check_implem_default
    )
  let check_implem () = !check_implem

  let contract_gen_default = false
  let contract_gen = ref contract_gen_default
  let _ = add_spec
    "--contract_gen"
    (bool_arg contract_gen)
    (fun fmt ->
      Format.fprintf fmt
      "@[<v>\
        Uses invariant generation to infer contracts for a lustre system.@ \
        Providing contracts, properties and assertion helps but is not@ \
        mandatory. Contracts will be written to the folder specified by@ \
        --output_dir.@ \
        (Kind 2 will actually try to use invariants logged in previous runs@ \
        automatically, even if they are not explicitely imported.)@ \
        See also --contract_gen_depth and --contract_gen_fine_grain.@ \
        Default: %a\
      @]"
      fmt_bool contract_gen_default
    )
  let contract_gen () = !contract_gen

  let contract_gen_depth_default = 7
  let contract_gen_depth = ref contract_gen_depth_default
  let _ = add_spec
    "--contract_gen_depth"
    (Arg.Int (fun n -> contract_gen_depth := n))
    (fun fmt ->
      Format.fprintf fmt
      "@[<v>\
        Controls the depth of exploration used to generate contracts.@ \
        Note that invariant generation is expected to go faster as it@ \
        unrolls (explores) the system.@ \
        Default: %d\
      @]"
      contract_gen_depth_default
    )
  let contract_gen_depth () = !contract_gen_depth


  let assumption_gen_default = false
  let assumption_gen = ref assumption_gen_default
  let _ = add_spec
    "--assumption_gen"
    (bool_arg assumption_gen)
    (fun fmt ->
      Format.fprintf fmt
      "@[<v>\
        For each falsified property, it looks for an assumption@ \
        that blocks all possible violations of the property.@ \
        Default: %a\
      @]"
      fmt_bool assumption_gen_default
    )
  let assumption_gen () = !assumption_gen

  let assump_include_outputs_default = true
  let assump_include_outputs = ref assump_include_outputs_default
  let _ = add_spec
    "--outputs_in_assumption"
    (bool_arg assump_include_outputs)
    (fun fmt ->
      Format.fprintf fmt
      "@[<v>\
        Generated assumptions may include references@ \
        to previous values of output streams.@ \
        Default: %a\
      @]"
      fmt_bool assump_include_outputs_default
    )
  let assump_include_outputs () = !assump_include_outputs


  let refinement_default = true
  let refinement = ref refinement_default
  let _ = add_spec
    "--refinement"
    (bool_arg refinement)
    (fun fmt ->
      Format.fprintf fmt
      "@[<v>\
        (De)activates refinement in compositional reasoning@ \
        Default: %a\
      @]"
      fmt_bool refinement_default
    )
  let refinement () = !refinement

end


(* Contracts flags. *)
module Certif = struct

  include Make_Spec (struct end)

  (* Identifier of the module. *)
  let id = "certif"
  (* Short description of the module. *)
  let desc = "Certification and proof production flags"
  (* Explanation of the module. *)
  let fmt_explain fmt =
    Format.fprintf fmt "@[<v>\
      Kind 2 generates (intermediate) certificates in the SMT-LIB 2 format and@ \
      produces proofs in the LFSC format.\
    @]"

  (* All the flag specification of this module. *)
  let all_specs = ref []
  let add_specs specs = all_specs := List.rev_append specs !all_specs
  let add_spec flag parse desc = all_specs := (flag, parse, desc) :: !all_specs

  (* Returns all the flag specification of this module. *)
  let all_specs () = !all_specs

  let certif_default = false
  let certif = ref certif_default
  let _ = add_spec
    "--certif"
    (Arg.Bool (fun b -> certif := b;
                if b then begin
                  Smt.set_short_names false;
                  BmcKind.disable_compress ();
                end))
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Produce SMT-LIB 2 certificates.@ Default: %a@]"
        fmt_bool certif_default
    )

  let proof_default = false
  let proof = ref proof_default
  let _ = add_spec
    "--proof"
    (Arg.Bool (fun b -> proof := b;
                if b then begin
                  certif := true;
                  Smt.set_short_names false;
                  Smt.detect_logic_if_none ();
                  BmcKind.disable_compress ();
                end))
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Produce LFSC proofs.@ Default: %a@]"
        fmt_bool proof_default
    )

  let certif () = !certif
  let proof () = !proof

  let abstr_default = false
  let abstr = ref abstr_default
  let _ = add_spec
    "--certif_abstr"
    (bool_arg abstr)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Use absrtact type indexes in certificates and proofs .@ Default: %a@]"
        fmt_bool abstr_default
    )
  let abstr () = !abstr

  let log_trust_default = false
  let log_trust = ref log_trust_default
  let _ = add_spec
    "--log_trust"
    (bool_arg log_trust)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Log trusted parts of the proof in a separate file \
         for users to fill.@ Default: %a@]"
        fmt_bool log_trust_default
    )
  let log_trust () = !log_trust

  type mink = [ `No | `Fwd | `Bwd | `Dicho | `FrontierDicho | `Auto]
  let mink_values = [ `No; `Fwd; `Bwd; `Dicho; `FrontierDicho; `Auto]
  let mink_of_string = function
    | "no" -> `No
    | "fwd" -> `Fwd
    | "bwd" -> `Bwd
    | "dicho" -> `Dicho
    | "frontierdicho" -> `FrontierDicho
    | "auto" -> `Auto
    | _ -> raise (Arg.Bad "Bad value for --certif_mink")
  let string_of_mink = function
    | `No -> "no"
    | `Fwd -> "fwd"
    | `Bwd -> "bwd"
    | `Dicho -> "dicho"
    | `FrontierDicho -> "frontierdicho"
    | `Auto -> "auto"
  let mink_default = `Auto
  let mink = ref mink_default
  let _ = add_spec
    "--certif_mink"
    (Arg.String (fun str -> mink := mink_of_string str))
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          where <string> is no, fwd, bwd, dicho, frontierdicho or auto.@ \
          Select strategy for minimizing k of certificates@ \
          \"no\" for no minimization@ \
          \"fwd\" for a search starting at 1 up to k@ \
          \"bwd\" for a search starting at k and going down to 1@ \
          \"dicho\" for a binary search of the minimum k@ \
          \"frontierdicho\" tries the frontier k/k-1 then employs the dicho stractegy@ \
          \"auto\" to heuristically select the best strategy among the previous ones (default)\
        @]"
    )
  let mink () = !mink


  type mininvs = [ `Easy | `Medium | `MediumOnly | `Hard | `HardOnly ]
  let mininvs_values = [ `Easy; `Medium; `MediumOnly; `Hard; `HardOnly ]
  let mininvs_of_string = function
    | "easy" -> `Easy
    | "medium" -> `Medium
    | "mediumonly" -> `MediumOnly
    | "hard" -> `Hard
    | "hardonly" -> `HardOnly
    | _ -> raise (Arg.Bad "Bad value for --certif_mininvs")
  let string_of_mininvs = function
    | `Easy -> "easy"
    | `Medium -> "medium"
    | `MediumOnly -> "mediumonly"
    | `Hard -> "hard"
    | `HardOnly -> "hardonly"
  let mininvs_default = `Medium
  let mininvs = ref mininvs_default
  let _ = add_spec
    "--certif_mininvs"
    (Arg.String (fun str -> mininvs := mininvs_of_string str))
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          where <string> is easy, medium, mediumonly, hard, hardonly.@ \
          Select strategy for minimizing the invariants of certificates@ \
          \"easy\" to only do unsat-core based trimming@ \
          \"medium\" does easy + coarse couter-example based minimization (default)@ \
          \"mediumonly\" does only coarse couter-example based minimization@ \
          \"hard\" does easy + cherry-pick invariants based on couter-examples@ \
          \"hardonly\" only cherry-picks invariants based on couter-examples\
        @]"
    )
  let mininvs () = !mininvs


  (* JKIND binary. *)
  let jkind_bin_default = "jkind"
  let jkind_bin = ref jkind_bin_default
  let _ = add_spec
      "--jkind_bin"
      (Arg.Set_string jkind_bin)
      (fun fmt ->
         Format.fprintf fmt
           "@[<v>Executable of JKind for frontend certificates.@ \
            Default: \"%s\"@]"
           jkind_bin_default
      )
  let jkind_bin () = ! jkind_bin


  let only_user_candidates_default = false
  let only_user_candidates = ref only_user_candidates_default
  let _ = add_spec
    "--only_user_candidates"
    (bool_arg only_user_candidates)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Only use user provided candidates for invariants.@ \
         Default: %a@]"
        fmt_bool only_user_candidates_default
    )
  let only_user_candidates () = !only_user_candidates

end

(* Inductive Validity Cores flags. *)
module IVC = struct

  include Make_Spec (struct end)

  (* Identifier of the module. *)
  let id = "ivc"
  (* Short description of the module. *)
  let desc = "Inductive Validity Cores generation flags"
  (* Explanation of the module. *)
  let fmt_explain fmt =
    Format.fprintf fmt "@[<v>\
      Kind 2 generates a minimal inductive validity core,@ \
      that is a minimal subset of the model elements sufficient to prove the properties.\
    @]"

  (* All the flag specification of this module. *)
  let all_specs = ref []
  let add_specs specs = all_specs := List.rev_append specs !all_specs
  let add_spec flag parse desc = all_specs := (flag, parse, desc) :: !all_specs

  (* Returns all the flag specification of this module. *)
  let all_specs () = !all_specs

  let compute_ivc_default = false
  let compute_ivc = ref compute_ivc_default
  let _ = add_spec
    "--ivc"
    (bool_arg compute_ivc)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Enable inductive validity core generation@ \
          Default: %a\
        "
        fmt_bool compute_ivc_default
    )
  let compute_ivc () = !compute_ivc

  type ivc_element =
    [ `NODE_CALL | `CONTRACT_ITEM | `EQUATION | `ASSERTION | `ANNOTATIONS ]
  let ivc_element_of_string = function
    | "node_calls" -> `NODE_CALL
    | "contracts" -> `CONTRACT_ITEM
    | "equations" -> `EQUATION
    | "assertions" -> `ASSERTION
    | "annotations" -> `ANNOTATIONS
    | unexpected -> Arg.Bad (
      Format.sprintf "Unexpected value \"%s\" for flag --ivc_category" unexpected
    ) |> raise
  let ivc_category_default_init = []
  let ivc_category_default_after =
    [`NODE_CALL ; `CONTRACT_ITEM ; `EQUATION ; `ASSERTION ]
  let ivc_category = ref ivc_category_default_init
  let finalize_ivc_elements () =
    (* If [enabled] is unchanged, set it do default after init. *)
    if !ivc_category = ivc_category_default_init then (
      ivc_category := ivc_category_default_after
    )
  let _ = add_spec
    "--ivc_category"
    (Arg.String
      (fun str ->
        let elt = ivc_element_of_string str in
        if List.mem elt !ivc_category |> not
        then ivc_category := elt :: !ivc_category
      )
    )
    (fun fmt ->
      Format.fprintf fmt
        "\
          where <string> can be 'node_calls', 'contracts', 'equations', 'assertions' or 'annotations'@ \
          Minimize only a specific category of elements, repeat option to minimize multiple categories@ \
          Default: minimize all categories of elements\
        "
    )
  let ivc_category () = !ivc_category


  let ivc_all_default = false
  let ivc_all = ref ivc_all_default
  let _ = add_spec
    "--ivc_all"
    (bool_arg ivc_all)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Compute all the Minimal Inductive Validity Cores.@ \
          Default: %a\
        "
        fmt_bool ivc_all_default
    )
  let ivc_all () = !ivc_all


  let ivc_approximate_default = true
  let ivc_approximate = ref ivc_approximate_default
  let _ = add_spec
    "--ivc_approximate"
    (bool_arg ivc_approximate)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Compute an approximation (superset) of a MIVC.@ \
          Ignored if --ivc_all is true.@ \
          Default: %a\
        "
        fmt_bool ivc_approximate_default
    )
  let ivc_approximate () = !ivc_approximate


  let ivc_smallest_first_default = false
  let ivc_smallest_first = ref ivc_smallest_first_default
  let _ = add_spec
    "--ivc_smallest_first"
    (bool_arg ivc_smallest_first)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Compute a smallest IVC first.@ \
          If --ivc_all is false, the computed IVC will be a smallest one.@ \
          Default: %a\
        "
        fmt_bool ivc_smallest_first_default
    )
  let ivc_smallest_first () = !ivc_smallest_first


  let ivc_only_main_node_default = false
  let ivc_only_main_node = ref ivc_only_main_node_default
  let _ = add_spec
    "--ivc_only_main_node"
    (bool_arg ivc_only_main_node)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Only elements of the main node are considered in the computation@ \
          Default: %a\
        "
        fmt_bool ivc_only_main_node_default
    )
  let ivc_only_main_node () = !ivc_only_main_node


  (*let ivc_per_property_default = true
  let ivc_per_property = ref ivc_per_property_default
  let _ = add_spec
    "--ivc_per_property"
    (bool_arg ivc_per_property)
    (fun fmt ->
      Format.fprintf fmt
        "\
          If true, IVCs will be computed for each property separately@ \
          Default: %a\
        "
        fmt_bool ivc_per_property_default
    )
  let ivc_per_property () = !ivc_per_property*)
  let ivc_per_property () = false


  let ivc_must_set_default = false
  let ivc_must_set = ref ivc_must_set_default
  let _ = add_spec
    "--ivc_must_set"
    (bool_arg ivc_must_set)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Compute the MUST set in addition to the IVCs@ \
          Default: %a\
        "
        fmt_bool ivc_must_set_default
    )
  let ivc_must_set () = !ivc_must_set


  let print_ivc_default = true
  let print_ivc = ref print_ivc_default
  let _ = add_spec
    "--print_ivc"
    (bool_arg print_ivc)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Print the inductive validity core computed@ \
          Default: %a\
        "
        fmt_bool print_ivc_default
    )
  let print_ivc () = !print_ivc


  let print_ivc_compl_default = false
  let print_ivc_compl = ref print_ivc_compl_default
  let _ = add_spec
    "--print_ivc_complement"
    (bool_arg print_ivc_compl)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Print the complement of the inductive validity core computed@ \
          (= the elements that were not necessary to prove the properties)@ \
          Default: %a\
        "
        fmt_bool print_ivc_compl_default
    )
  let print_ivc_compl () = !print_ivc_compl


  type minimize_mode = [ `DO_NOT_MINIMIZE | `VALID_LUSTRE | `CONCISE ]

  let mm_of_string = function
    | "no" -> `DO_NOT_MINIMIZE
    | "valid_lustre" -> `VALID_LUSTRE
    | "concise" -> `CONCISE
    | _ -> raise (Arg.Bad "Bad value for --minimize_program")

  let minimize_program_default = `DO_NOT_MINIMIZE
  let minimize_program = ref minimize_program_default
  let _ = add_spec
    "--minimize_program"
    (Arg.String (fun str -> minimize_program := mm_of_string str))
    (fun fmt ->
      Format.fprintf fmt
        "\
          Minimize the source Lustre program according to the inductive validity core(s) computed@ \
          \"no\" to disable this feature (default)@ \
          \"valid_lustre\" to replace useless expressions by a valid node call@ \
          \"concise\" to replace useless expressions by a '_'\
        "
    )
  let minimize_program () = !minimize_program

  let minimized_program_dir_default = ""
  let minimized_program_dir = ref minimized_program_dir_default
  let _ = add_spec
      "--ivc_output_dir"
      (Arg.Set_string minimized_program_dir)
      (fun fmt ->
         Format.fprintf fmt
           "Output directory for the minimized programs@ \
            Default: <INPUT_FILENAME>"
      )
  let minimized_program_dir () = !minimized_program_dir


  let ivc_precomputed_mcs_default = 0
  let ivc_precomputed_mcs = ref ivc_precomputed_mcs_default
  let _ = add_spec
    "--ivc_precomputed_mcs"
    (Arg.Set_int ivc_precomputed_mcs)
    (fun fmt ->
      Format.fprintf fmt
        "\
          When computing all MIVCs,@ \
          set a cardinality upper bound for the precomputed MCSs@ \
          (helps prune space of candidates).@ \
          Default: %n\
        "
        ivc_precomputed_mcs_default
    )
  let ivc_precomputed_mcs () = !ivc_precomputed_mcs


  let ivc_uc_timeout_default = 0
  let ivc_uc_timeout = ref ivc_uc_timeout_default
  let _ = add_spec
    "--ivc_uc_timeout"
    (Arg.Set_int ivc_uc_timeout)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Set a timeout for each unsat core check sent to the solver.@ \
          Set to 0 to disable timeout.@ \
          Default: %n\
        "
        ivc_uc_timeout_default
    )
  let ivc_uc_timeout () = !ivc_uc_timeout


  let ivc_disable_must_opt_default = false
  let ivc_disable_must_opt = ref ivc_disable_must_opt_default
  let _ = add_spec
    "--ivc_disable_must_opt"
    (bool_arg ivc_disable_must_opt)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Disable the must-set optimisation.@ \
          This setting is ignored if --ivc_must_set is true.@ \
          Default: %a\
        "
        fmt_bool ivc_disable_must_opt_default
    )
  let ivc_disable_must_opt () = !ivc_disable_must_opt
  (*let ivc_disable_must_opt () = false*)

end

(* Minimal Cut Sets flags. *)
module MCS = struct

  include Make_Spec (struct end)

  (* Identifier of the module. *)
  let id = "mcs"
  (* Short description of the module. *)
  let desc = "Minimal Cut Sets generation flags"
  (* Explanation of the module. *)
  let fmt_explain fmt =
    Format.fprintf fmt "@[<v>\
      Kind 2 generates a minimal cut set,@ \
      that is a minimal subset of the model elements@ \
      whose no satisfaction leads to the violation of a property.\
    @]"

  (* All the flag specification of this module. *)
  let all_specs = ref []
  let add_specs specs = all_specs := List.rev_append specs !all_specs
  let add_spec flag parse desc = all_specs := (flag, parse, desc) :: !all_specs

  (* Returns all the flag specification of this module. *)
  let all_specs () = !all_specs

  (*let compute_mcs_default = false
  let compute_mcs = ref compute_mcs_default
  let _ = add_spec
    "--mcs"
    (bool_arg compute_mcs)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Compute a minimal cut set@ \
          Default: %a\
        "
        fmt_bool compute_mcs_default
    )
  let compute_mcs () = !compute_mcs*)
  let compute_mcs () = false

  type mcs_element =
    [ `NODE_CALL | `CONTRACT_ITEM | `EQUATION | `ASSERTION | `ANNOTATIONS ]
  let mcs_element_of_string = function
    | "node_calls" -> `NODE_CALL
    | "contracts" -> `CONTRACT_ITEM
    | "equations" -> `EQUATION
    | "assertions" -> `ASSERTION
    | "annotations" -> `ANNOTATIONS
    | unexpected -> Arg.Bad (
      Format.sprintf "Unexpected value \"%s\" for flag --mcs_category" unexpected
    ) |> raise
  let mcs_category_default_init = []
  let mcs_category_default_after = [`ANNOTATIONS]
  let mcs_category = ref mcs_category_default_init
  let finalize_mcs_elements () =
    (* If [enabled] is unchanged, set it do default after init. *)
    if !mcs_category = mcs_category_default_init then (
      mcs_category := mcs_category_default_after
    )
  let _ = add_spec
    "--mcs_category"
    (Arg.String
      (fun str ->
        let elt = mcs_element_of_string str in
        if List.mem elt !mcs_category |> not
        then mcs_category := elt :: !mcs_category
      )
    )
    (fun fmt ->
      Format.fprintf fmt
        "\
          where <string> can be 'node_calls', 'contracts', 'equations', 'assertions' or 'annotations'@ \
          Consider only a specific category of elements, repeat option to consider multiple categories@ \
          Default: annotations\
        "
    )
  let mcs_category () = !mcs_category


  let mcs_only_main_node_default = false
  let mcs_only_main_node = ref mcs_only_main_node_default
  let _ = add_spec
    "--mcs_only_main_node"
    (bool_arg mcs_only_main_node)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Only elements of the main node are considered in the computation@ \
          Default: %a\
        "
        fmt_bool mcs_only_main_node_default
    )
  let mcs_only_main_node () = !mcs_only_main_node


  let mcs_all_default = false
  let mcs_all = ref mcs_all_default
  let _ = add_spec
    "--mcs_all"
    (bool_arg mcs_all)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Specify whether all the Minimal Cut Sets must be computed or just one@ \
          Default: %a\
        "
        fmt_bool mcs_all_default
    )
  let mcs_all () = !mcs_all

  let mcs_approximate_default = true
  let mcs_approximate = ref mcs_approximate_default
  let _ = add_spec
    "--mcs_approximate"
    (bool_arg mcs_approximate)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Compute an approximation of a MCS.@ \
          Ignored if --mcs_all is true.@ \
          Default: %a\
        "
        fmt_bool mcs_approximate_default
    )
  let mcs_approximate () = !mcs_approximate

  let mcs_max_cardinality_default = -1
  let mcs_max_cardinality = ref mcs_max_cardinality_default
  let _ = add_spec
    "--mcs_max_cardinality"
    (Arg.Set_int mcs_max_cardinality)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Only search for MCSs of cardinality lower or equal to this parameter.@ \
          If -1, all MCSs will be considered.@ \
          Default: %i\
        "
        mcs_max_cardinality_default
    )
  let mcs_max_cardinality () = !mcs_max_cardinality


  let print_mcs_default = true
  let print_mcs = ref print_mcs_default
  let _ = add_spec
    "--print_mcs"
    (bool_arg print_mcs)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Print the minimal cut set computed@ \
          Default: %a\
        "
        fmt_bool print_mcs_default
    )
  let print_mcs () = !print_mcs


  let print_mcs_compl_default = false
  let print_mcs_compl = ref print_mcs_compl_default
  let _ = add_spec
    "--print_mcs_complement"
    (bool_arg print_mcs_compl)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Print the complement of the minimal cut set computed@ \
          (this is equivalent to computing a Maximal Unsafe Abstraction)@ \
          Default: %a\
        "
        fmt_bool print_mcs_compl_default
    )
  let print_mcs_compl () = !print_mcs_compl


  let print_mcs_legacy_default = false
  let print_mcs_legacy = ref print_mcs_legacy_default
  let _ = add_spec
    "--print_mcs_legacy"
    (bool_arg print_mcs_legacy)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Print the minimal cut set using the legacy format@ \
          Default: %a\
        "
        fmt_bool print_mcs_legacy_default
    )
  let print_mcs_legacy () = !print_mcs_legacy


  let print_mcs_counterexample_default = false
  let print_mcs_counterexample = ref print_mcs_counterexample_default
  let _ = add_spec
    "--print_mcs_counterexample"
    (bool_arg print_mcs_counterexample)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Print a counterexample for each MCS found@ \
          (ignored if --print_mcs_legacy is true)@ \
          Default: %a\
        "
        fmt_bool print_mcs_counterexample_default
    )
  let print_mcs_counterexample () = !print_mcs_counterexample


  let mcs_per_property_default = true
  let mcs_per_property = ref mcs_per_property_default
  let _ = add_spec
    "--mcs_per_property"
    (bool_arg mcs_per_property)
    (fun fmt ->
      Format.fprintf fmt
        "\
          If true, MCSs will be computed for each property separately@ \
          Default: %a\
        "
        fmt_bool mcs_per_property_default
    )
  let mcs_per_property () = !mcs_per_property

end

(* Arrays flags. *)
module Arrays = struct

  include Make_Spec (struct end)

  (* Identifier of the module. *)
  let id = "arrays"
  (* Short description of the module. *)
  let desc = "arrays flags"
  (* Explanation of the module. *)
  let fmt_explain fmt =
    Format.fprintf fmt "@[<v>\
      Kind 2 extends Lustre with a syntax for recursive whole arrays@ \
      definitions. The syntax and semantics are described in@ \
      Kind 2 documentation.\
    @]"

  (* All the flag specification of this module. *)
  let all_specs = ref []
  let add_specs specs = all_specs := !all_specs @ specs
  let add_spec flag parse desc = all_specs := (flag, parse, desc) :: !all_specs

  (* Returns all the flag specification of this module. *)
  let all_specs () = !all_specs

  let smt_default = false
  let smt = ref smt_default
  let _ = add_spec
    "--smt_arrays"
    (bool_arg smt)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Use the builtin theory of arrays in solvers.@ Default: %a@]"
        fmt_bool smt_default
    )
  let smt () = !smt

  let inline_default = true
  let inline = ref inline_default
  let _ = add_spec
    "--inline_arrays"
    (bool_arg inline)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Inline arrays whose bound is statically known.@ Default: %a@]"
        fmt_bool inline_default
    )
  let inline () = !inline

  let recdef_default = false
  let recdef = ref recdef_default

  let recdef_action b =
    recdef := b;
    match Smt.solver () with
    | `CVC4_SMTLIB -> ()
    | _ ->
      raise (Arg.Bad 
               "Recursive encoding of arrays can only be used with CVC4. \
                Use the flag --smtsolver CVC4")  

  let _ = add_spec
    "--arrays_rec"
    (Arg.Bool recdef_action)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Define recurvsive functions for arrays (only if previously@ \
         selected CVC4 as the SMT solver).@ Default: %a@]"
        fmt_bool recdef_default
    )
  let recdef () = !recdef

  
  let var_size_default = false
  let var_size = ref var_size_default
  let _ = add_spec
    "--var_array_size"
    (bool_arg var_size)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Allow variable arrays size (Dangerous).@ Default: %a@]"
        fmt_bool var_size_default
    )
  let var_size () = !var_size

end


(* Testgen flags. *)
module Testgen = struct

  include Make_Spec (struct end)

  (* Identifier of the module. *)
  let id = "test"
  (* Short description of the module. *)
  let desc = "test generation flags"
  (* Explanation of the module. *)
  let fmt_explain fmt =
    Format.fprintf fmt "@[<v>\
      Test generation uses the contract (see module \"contract\") attached@ \
      to a node to explore the behavior of a node. For each behavior, a@ \
      trace of inputs triggering it is generated and logged as a testcase in@ \
      CSV.\
    @]"

  let active_default = false
  let active = ref active_default
  let _ = add_spec
    "--testgen"
    (bool_arg active)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Activates test generation for systems proved correct@ \
          Default: %a\
        @]"
        fmt_bool active_default
    )
  let active () = !active

  let graph_only_default = false
  let graph_only = ref graph_only_default
  let _ = add_spec
    "--testgen_graph_only"
    (bool_arg graph_only)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Only draw the graph of reachable modes, do not log testcases.@ \
          Default: %a\
        @]"
        fmt_bool graph_only_default
    )
  let graph_only () = !graph_only

  let len_default = 5
  let len = ref len_default
  let _ = add_spec
    "--testgen_len"
    (Arg.Set_int len)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Maximimum length for test generation@ \
          Default: %d\
        @]"
        len_default
    )
  let len () = !len

end


(* Invgen flags. *)
module Invgen = struct

  include Make_Spec (struct end)

  (* Identifier of the module. *)
  let id = "invgen"
  (* Short description of the module. *)
  let desc = "invariant generation flags"
  (* Explanation of the module. *)
  let fmt_explain fmt =
    Format.fprintf fmt "@[<v>\
      Invariant generation attempts to discover invariants of the form@ \
      `<expr> => <expr>` using expressions mined from the initial and@ \
      transition predicates of the system. The candidates invariants@ \
      considered are selected by an incremental exploration of the reachable@ \
      states.\
    @]"

  let prune_trivial_default = true
  let prune_trivial = ref prune_trivial_default
  let _ = add_spec
    "--invgen_prune_trivial"
    (bool_arg prune_trivial)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Invariant generation will only communicate invariants not implied@ \
          by the transition relation@ \
          Default: %a\
        @]"
        fmt_bool prune_trivial_default
    )
  let prune_trivial () = !prune_trivial

  let max_depth_default = None
  let max_depth = ref max_depth_default
  let _ = add_spec
    "--invgen_max_depth"
    (Arg.Int (fun n -> max_depth := Some n))
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Maximal depth for graph-based invariant generation techniques.@ \
          Default: none\
        @]"
    )
  let set_max_depth n = max_depth := n
  let max_depth () = !max_depth

  let max_succ_default = 1
  let max_succ = ref max_succ_default
  let _ = add_spec
    "--invgen_max_succ"
    (Arg.Int (fun b -> max_succ := b))
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Maximal number of successive iterations for subsystems@ \
          Default: %d\
        @]"
        max_succ_default
    )
  let max_succ () = !max_succ

  let lift_candidates_default = false
  let lift_candidates = ref lift_candidates_default
  let _ = add_spec
    "--invgen_lift_candidates"
    (bool_arg lift_candidates)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Invariant generation will instantiate candidates from sub-nodes@ \
          Default: %a\
        @]"
        fmt_bool lift_candidates_default
    )
  let lift_candidates () = !lift_candidates

  let top_only_default = false
  let top_only = ref top_only_default
  let _ = add_spec
    "--invgen_top_only"
    (bool_arg top_only)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Only generate invariants for the top level@ \
          Default: %a\
        @]"
        fmt_bool top_only_default
    )
  let top_only () = !top_only

  let all_out_default = false
  let all_out = ref all_out_default
  let _ = add_spec
    "--invgen_all_out"
    (bool_arg all_out)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Forces invariant generation to consider a huge number of candidates@ \
          Slower, but more likely to succeed.@ \
          Default: %a\
        @]"
        fmt_bool all_out_default
    )
  let all_out () = !all_out

  let mine_trans_default = true
  let mine_trans = ref mine_trans_default
  let _ = add_spec
    "--invgen_mine_trans"
    (bool_arg mine_trans)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Invariant generation will extract candidate terms from the@ \
          transition predicate@ \
          Default: %a\
        @]"
        fmt_bool mine_trans_default
    )
  let mine_trans () = !mine_trans

  let two_state_default = true
  let two_state = ref two_state_default
  let _ = add_spec
    "--invgen_two_state"
    (bool_arg two_state)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Run invariant generion in two state mode\
          Default: %b\
        @]" two_state_default
    )
  let two_state () = !two_state

  let bool_eq_only_default = false
  let bool_eq_only = ref bool_eq_only_default
  let _ = add_spec
    "--invgen_bool_eq_only"
    (bool_arg bool_eq_only)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Forces bool invgen to look for equalities only\
          Default: %b\
        @]" bool_eq_only_default
    )
  let bool_eq_only () = !bool_eq_only

  let arith_eq_only_default = false
  let arith_eq_only = ref arith_eq_only_default
  let _ = add_spec
    "--invgen_arith_eq_only"
    (bool_arg arith_eq_only)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Forces arith invgen to look for equalities only\
          Default: %b\
        @]" arith_eq_only_default
    )
  let arith_eq_only () = !arith_eq_only

  let renice_default = 0
  let renice = ref renice_default
  let _ = add_spec
    "--invgen_renice"
    (Arg.Set_int renice)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Renice invariant generation process. Give a positive argument to@ \
          lower priority\
        @]"
    )
  let renice () = !renice
end


(* C2I flags. *)
module C2I = struct

  include Make_Spec (struct end)

  (* Identifier of the module. *)
  let id = "c2i"
  (* Short description of the module. *)
  let desc = "C2I flags"
  (* Explanation of the module. *)
  let fmt_explain fmt =
    Format.fprintf fmt "@[<v>\
      C2I is an invariant generation technique based on machine-learning.@ \
      The Kind 2 implementation is still experimental and is inactive by@ \
      default.\
    @]"

  let dnf_size_default = 3
  let dnf_size = ref dnf_size_default
  let _ = add_spec
    "--c2i_dnf"
    (Arg.Set_int dnf_size)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Number of disjuncts in the DNF constructed by C2I@ \
          Default %d\
        @]"
        dnf_size_default
    )
  let dnf_size () = !dnf_size

  let int_cube_size_default = 3
  let int_cube_size = ref int_cube_size_default
  let _ = add_spec
    "--c2i_int_cubes"
    (Arg.Set_int int_cube_size)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Number of int cubes in the DNF constructed by C2I@ \
          Default %d\
        @]"
        int_cube_size_default
    )
  let int_cube_size () = !int_cube_size

  let real_cube_size_default = 3
  let real_cube_size = ref real_cube_size_default
  let _ = add_spec
    "--c2i_real_cubes"
    (Arg.Set_int real_cube_size)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Number of real cubes in the DNF constructed by C2I@ \
          Default %d\
        @]"
        real_cube_size_default
    )
  let real_cube_size () = !real_cube_size

  let modes_default = true
  let modes = ref modes_default
  let _ = add_spec
    "--c2i_modes"
    (bool_arg modes)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Activates mode subcandidates. Subsumes \"c2i_dnf_size\"@ \
          Default %a\
        @]"
        fmt_bool modes_default
    )
  let modes () = !modes
end


(* Interpreter flags. *)
module Interpreter = struct

  include Make_Spec (struct end)

  (* Identifier of the module. *)
  let id = "interpreter"
  (* Short description of the module. *)
  let desc = "interpreter flags"
  (* Explanation of the module. *)
  let fmt_explain fmt =
    Format.fprintf fmt "@[<v>\
      The interpreter is a special mode where Kind 2 reads inputs from a@ \
      file and prints the outputs of the system at each step.\
    @]"

  let input_file_default = ""
  let input_file = ref input_file_default
  let _ = add_spec
    "--interpreter_input_file"
    (Arg.Set_string input_file)
    (fun fmt ->
      Format.fprintf fmt "@[<v>Read input from file@]"
    )
  let input_file () = !input_file

  let steps_default = 0
  let steps = ref steps_default
  let _ = add_spec
    "--interpreter_steps"
    (Arg.Set_int steps)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Run number of steps, override the number of steps given in the@ \
          input file@ \
          Default: %d\
        @]"
        steps_default
    )
  let steps () = !steps

end





(* ********************************************************************** *)
(* Maps identifiers to modules flag specifications and description        *)
(* ********************************************************************** *)

let usage_msg_header = Filename.basename Sys.executable_name |> Format.sprintf "\
  Usage: \x1b[1m%s [options] [input_file]\x1b[0m\
"

let all_modules_id = "all"

let module_map = [
  (Smt.id,
    (module Smt: FlagModule)
  ) ;
  (BmcKind.id,
    (module BmcKind: FlagModule)
  ) ;
  (IC3.id,
    (module IC3: FlagModule)
  ) ;
  (Invgen.id,
    (module Invgen: FlagModule)
  ) ;
  (C2I.id,
    (module C2I: FlagModule)
  ) ;
  (Testgen.id,
    (module Testgen: FlagModule)
  ) ;
  (Interpreter.id,
    (module Interpreter: FlagModule)
  ) ;
  (QE.id,
    (module QE: FlagModule)
  ) ;
  (Contracts.id,
    (module Contracts: FlagModule)
  ) ;
  (IVC.id,
    (module IVC: FlagModule)
  ) ;
  (MCS.id,
    (module MCS: FlagModule)
  ) ;
  (Arrays.id,
    (module Arrays: FlagModule)
  ) ;
  (Certif.id,
    (module Certif: FlagModule)
  ) ;
]

(* Formats an element of [module_map]. *)
let fmt_module_info fmt (id, m0d) =
  let module Flags = (val m0d: FlagModule) in
  Format.fprintf fmt
    "\
      |===| Module \x1b[1m%s\x1b[0m:@.@.\
      @[<v>%t@]\
      @.@.  @[<v>%a@]@.\
    "
    id
    Flags.fmt_explain
    (pp_print_list fmt_flag "@ ")
    (Flags.all_specs () |> List.rev)

(* Prints module info for a list of identifiers. If ["all"] is in the list,
prints info for all modules.
If the input list is not empty and all identifiers are defined, exits with
status [0]. If some operators are undefined, exits with [2]. Does nothing if
the list is empty. *)
let print_module_info = function
| [] -> ()
| (hd :: tl) as ids -> (
  Format.printf "%s@.@." usage_msg_header ;
  if List.mem all_modules_id ids then (
    Format.printf
      "%a"
      (pp_print_list fmt_module_info "@.@.")
      module_map
  ) else (
    (
      try (
        let m0d = module_map |> List.assoc hd in
        Format.printf "%a" fmt_module_info (hd, m0d)
      ) with Not_found -> (
        Format.printf
          "Unknown module \"%s\", legal values are@.  all, %a@."
          hd
          (pp_print_list
            (fun fmt (key,_) -> Format.fprintf fmt "%s" key)
            ", "
          ) module_map ;
        exit 2
      )
    ) ;
    tl |> List.iter ( fun id ->
      try (
        let m0d = module_map |> List.assoc id in
        Format.printf "@.%a" fmt_module_info (id, m0d)
      ) with Not_found -> (
        Format.printf
          "Unknown module \"%s\", legal values are@.  all, %a@."
          id
          (pp_print_list
            (fun fmt (key,_) -> Format.fprintf fmt "%s" key)
            ", "
          ) module_map ;
        exit 2
      )
    )
  ) ;
  exit 0
)




(* ********************************************************************** *)
(* Global flags                                                           *)
(* ********************************************************************** *)



(* Global flags. *)
module Global = struct

  include Make_Spec (struct end)

  (* Returns all flags in all Kind 2 modules. *)
  let all_kind2_specs () = List.fold_left (
    fun l (_, m0d) ->
      let module Flags = (val m0d: FlagModule) in
      l @ (Flags.all_specs ())
  ) (all_specs ()) module_map

  let usage_msg = Format.sprintf "\
    %s@.\
    Prove properties over the Lustre program in <input_file> or from standard@ \
    input (in Lustre) if no file is given.@.\
    Global options follow, \
    use \"--help_of\" for module-specific information.\
  " usage_msg_header


  (* Prints help. *)
  let print_help () =
    Format.printf "%s@.  " usage_msg ;
    all_specs () |> List.rev |> print_flags ;
    Format.printf "@."


  (* All files in the cone of influence of the input file. *)
  let all_input_files = ref []
  let all_input_ids = ref FileId.FileIdSet.empty
  let clear_input_files () = (all_input_files := []; all_input_ids := FileId.FileIdSet.empty)
  let add_input_file file = (
    let id = FileId.get_id file in
    if not (FileId.FileIdSet.mem id !all_input_ids) then (
      all_input_files := file :: ! all_input_files ;
      all_input_ids := FileId.FileIdSet.add (FileId.get_id file) !all_input_ids; true
    ) else false
  )
  let get_all_input_files () = ! all_input_files

  (* Input flag. *)
  let input_file_default = ""
  let input_file = ref input_file_default
  let set_input_file f = (input_file := f; add_input_file f |> ignore)
  let input_file () = !input_file


  (* Print help. *)
  let help_requested_default = false
  let help_requested = ref help_requested_default
  let _ = add_specs [
    (
      "-h",
      (Arg.Unit
        (fun () -> print_help () ; exit 0)
      ),
      (fun fmt -> Format.fprintf fmt "Prints this message")
    ) ;
    (
      "--help",
      (Arg.Unit
        (fun () -> print_help () ; exit 0)
      ),
      (fun fmt -> Format.fprintf fmt "Prints this message too")
    ) ;
  ]



  (* Explain modules. *)
  let help_of_default = []
  let help_of = ref help_of_default
  let help_of_desc fmt =
    Format.fprintf fmt
      "\
        Explains and shows the flags for a Kind 2 module@ \
        <string> should be a legal module identifier among@   @[<v>\
          %a@ \
          %-15s explanation and flags for all Kind 2 modules\
        @]\
      "
      (pp_print_list
        ( fun fmt (key, m0d) ->
          let module Flags = (val m0d: FlagModule) in
          Format.fprintf fmt
            "%-15s %s" (Format.sprintf "%s" key) Flags.desc
        ) "@ "
      ) module_map
      all_modules_id
  let _ = add_spec
    "--help_of"
    (Arg.String 
      (fun str ->
        if str = all_modules_id || List.mem_assoc str module_map then (
          if List.mem str !help_of |> not then help_of := str :: !help_of
        ) else BadArg (
          Format.sprintf "unknown module identifier \"%s\"" str,
          (
            "--help_of",
            Arg.String (fun _ -> ()),
            help_of_desc
          )
        ) |> raise
      )
    )
    help_of_desc
  let help_of () = !help_of


  (* Main lustre node. *)
  let lus_main_of_string s = Some s
  let string_of_lus_main = function
    | None -> "(none)"
    | Some s -> s
  let lus_main_default = None

  let lus_main = ref lus_main_default
  let _ = add_spec
    "--lus_main"
    (Arg.String (fun str -> lus_main := Some str))
    (fun fmt ->
      Format.fprintf fmt
        "\
          where <string> is node identifier from the Lustre input file@ \
          Specifies the top node in the Lustre input file@ \
          Default: \"--%%MAIN\" annotation in source if any, last node@ \
          otherwise\
        "
    )
  let lus_main () = !lus_main


  (* Input format. *)
  type input_format = [
    `Lustre | `Horn | `Native
  ]
  let input_format_of_string = function
    | "extension" -> `Extension
    | "lustre" -> `Lustre
    | "horn" -> `Horn
    | "native" -> `Native
    | _ -> raise (Arg.Bad "Bad value for --input_format")
  let string_of_input_format = function
    | `Extension -> "extension"
    | `Lustre -> "lustre"
    | `Horn -> "horn"
    | `Native -> "native"
  let input_format_values = [
    `Lustre ; `Native; `Extension
  ] |> List.map string_of_input_format |> String.concat ", "
  let input_format_default = `Extension

  let input_format = ref input_format_default
  let _ = add_spec
    "--input_format"
    (Arg.String (fun str -> input_format := input_format_of_string str))
    (fun fmt ->
      Format.fprintf fmt
        "\
          where <string> can be %s@ \
          Format of input file@ \
          Default: %s\
        "
        input_format_values
        (string_of_input_format input_format_default)
    )

  let set_input_format s =
    if !input_format = `Extension then
      if Filename.check_suffix s ".kind2" then
        input_format := `Native
      else input_format := `Lustre

  let input_format () =
    match !input_format with
    | `Extension -> `Lustre
    | (`Lustre | `Native | `Horn) as f -> f


  (* Output directory. *)
  let output_dir_default = ""
  (* Do not change this ~~~^^
  This is how `set_output_dir` knows this flag was not set by the user. *)
  let output_dir = ref output_dir_default
  let output_dir_action d =
    output_dir := d;
    Smt.set_trace_dir d

  let _ = add_spec
    "--output_dir"
    (Arg.String output_dir_action)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Output directory for the files generated:@ \
          SMT traces, compilation, testgen, certification...@ \
          Default: \"<path_to_filename>.out\"\
        "
    )

  let set_output_dir s = match ! output_dir with
    | "" -> s ^ ".out" |> output_dir_action
    | _ -> ()

  let output_dir () = !output_dir


  let include_dirs = ref []
  let _ = add_spec
    "--include_dir"
    (Arg.String
      (fun dir -> include_dirs := dir :: !include_dirs)
    )
    (fun fmt ->
      Format.fprintf fmt
        "\
          where <string> is a directory to be included in the search path@ \
          The directory will be searched after the current include directory,@ \
          and any other directory added before it (left-to-right order) when@ \
          an include directive is found\
        "
    )
  let include_dirs () = List.rev (!include_dirs)

  (* Real precision. *)
  type real_precision = [
    `Rational | `Float
  ]
  let real_precision_of_string = function
    | "rational" -> `Rational
    | "float" -> `Float
    | _ -> raise (Arg.Bad "Bad value for --real_precision")
  let string_of_real_precision = function
    | `Rational -> "rational"
    | `Float -> "float"
  let real_precision_values = [
    `Rational ; `Float
  ] |> List.map string_of_real_precision |> String.concat ", "
  let real_precision_default = `Rational

  let real_precision = ref real_precision_default
  let _ = add_spec
    "--real_precision"
    (Arg.String
      (fun str -> real_precision := real_precision_of_string str)
    )
    (fun fmt ->
      Format.fprintf fmt
      "\
        where <string> can be %s@ \
        Adjust precision of real values in model output@ \
        In floating-point format f<nn> means a relative error less than 2^-nn@ \
        Default: %s\
      "
      real_precision_values
      (string_of_real_precision real_precision_default)
    )

  let real_precision () = !real_precision


  (* Log invariants. *)
  let log_invs_default = false
  let log_invs = ref log_invs_default
  let _ = add_spec
    "--log_invs"
    (bool_arg log_invs)
    (fun fmt ->
      Format.fprintf fmt
        "Logs strengthening invariants as contracts after minimization.@ \
        Default: %b"
        log_invs_default
    )
  let log_invs () = ! log_invs


  (* Print invariants. *)
  let print_invs_default = false
  let print_invs = ref print_invs_default
  let _ = add_spec
    "--print_invs"
    (bool_arg print_invs)
    (fun fmt ->
      Format.fprintf fmt
        "Prints list of discovered invariants after minimization.@ \
        Default: %b"
        print_invs_default
    )
  let print_invs () = ! print_invs


  (* Timeout. *)
  let timeout_wall_default = 0.
  let timeout_wall = ref timeout_wall_default
  let _ = add_specs ([
    ( "--timeout",
      Arg.Set_float timeout_wall,
      fun fmt ->
        Format.fprintf fmt
          "\
            Wallclock timeout in seconds@ \
            Default: %1.f\
          "
          timeout_wall_default
    ) ;
    ( "--timeout_wall",
      Arg.Set_float timeout_wall,
      fun fmt ->
        Format.fprintf fmt
          "Same as \"--timeout\", for legacy"
    )
  ])
  let timeout_wall () = !timeout_wall


  (* Timeout. *)
  let timeout_analysis_default = 0.
  let timeout_analysis = ref timeout_analysis_default
  let _ = add_specs ([
    ( "--timeout_analysis",
      Arg.Set_float timeout_analysis,
      fun fmt ->
        Format.fprintf fmt
          "\
            Per-analysis wallclock timeout in seconds (0 for none)@ \
            Default: %1.f\
          "
          timeout_analysis_default
    )
  ])
  let timeout_analysis () = !timeout_analysis

  (* Only parse mode. *)
  let only_parse_default = false
  let only_parse = ref only_parse_default
  let _ = add_spec
    "--only_parse"
    (bool_arg only_parse)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Only parse the Lustre program. No analysis is performed.@ \
          Default: %a\
        "
        fmt_bool only_parse_default
    )
  let only_parse () = !only_parse

  (* LSP mode. *)
  let lsp_default = false

  let lsp = ref lsp_default

  let _ =
    add_spec "--lsp" (bool_arg lsp) (fun fmt ->
        Format.fprintf fmt "Provide AST info for language-servers.@ Default: %a"
          fmt_bool lsp_default)

  let lsp () = !lsp

  (* Only typecheck mode. *)
  let only_tc_default = false
  let only_tc = ref only_tc_default
  let _ = add_spec
    "--only_tc"
    (bool_arg only_tc)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Stop after type checking the Lustre program. No analysis is performed.@ \
          Default: %a\
        "
        fmt_bool only_tc_default
    )
  let only_tc () = !only_tc

  (* Do not run typechecker *)
  let no_tc_default = true
  let no_tc = ref no_tc_default
  let _ = add_spec
    "--no_tc"
    (bool_arg no_tc)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Skip the typechecking pass.@ \
          Default: %a\
        "
        fmt_bool no_tc_default
    )
  let no_tc () = !no_tc
                 
                    
  (* Modules enabled. *)
  type enable = kind_module list
  let kind_module_of_string = function
    | "IC3" -> `IC3
    | "BMC" -> `BMC
    | "IND" -> `IND
    | "IND2" -> `IND2
    | "INVGEN" -> `INVGEN
    | "INVGENOS" -> `INVGENOS
    | "INVGENINT" -> `INVGENINT
    | "INVGENINTOS" -> `INVGENINTOS
    | "INVGENMACH" -> `INVGENMACH
    | "INVGENMACHOS" -> `INVGENMACHOS
    | "INVGENREAL" -> `INVGENREAL
    | "INVGENREALOS" -> `INVGENREALOS
    | "C2I" -> `C2I
    | "interpreter" -> `Interpreter
    | "MCS" -> `MCS
    | "CONTRACTCK" -> `CONTRACTCK
    | unexpected -> Arg.Bad (
      Format.sprintf "Unexpected value '%s' for flag --enable" unexpected
    ) |> raise

  let string_of_kind_module = function
    | `IC3 -> "IC3"
    | `BMC -> "BMC"
    | `IND -> "IND"
    | `IND2 -> "IND2"
    | `INVGEN -> "INVGEN"
    | `INVGENOS -> "INVGENOS"
    | `INVGENINT -> "INVGENINT"
    | `INVGENINTOS -> "INVGENINTOS"
    | `INVGENMACH -> "INVGENMACH"
    | `INVGENMACHOS -> "INVGENMACHOS"
    | `INVGENREAL -> "INVGENREAL"
    | `INVGENREALOS -> "INVGENREALOS"
    | `C2I -> "C2I"
    | `Interpreter -> "interpreter"
    | `MCS -> "MCS"
    | `CONTRACTCK -> "CONTRACTCK"
  let string_of_enable = function
    | head :: tail -> (
      List.fold_left
        ( fun s m -> s ^ ", " ^ (string_of_kind_module m) )
        ("[" ^ (string_of_kind_module head))
        tail
      ) ^ "]"
    | [] -> "[]"
  let enable_values = [
    `IC3 ; `BMC ; `IND ; `IND2 ;
    `INVGEN ; `INVGENOS ;
    `INVGENINT ; `INVGENINTOS ;
    `INVGENMACH ; `INVGENMACHOS ;
    `INVGENREAL ; `INVGENREALOS ;
    `C2I ; `Interpreter ; `MCS ; `CONTRACTCK
  ] |> List.map string_of_kind_module |> String.concat ", "

  let enable_default_init = []
  let disable_default_init = []

  let enable_default_after = [
    `BMC ; `IND ; `IND2 ; `IC3 ;
    `INVGEN ; `INVGENOS ;
    (* `INVGENINT ; *) `INVGENINTOS ; `INVGENMACHOS ;
    (* `INVGENREAL ; *) `INVGENREALOS ;
  ]
  let enabled = ref enable_default_init
  let disable modul3 =
    enabled := (! enabled) |> List.filter (fun m -> m <> modul3)
  let disabled = ref disable_default_init
  let finalize_enabled () =
    (* If [enabled] is unchanged, set it do default after init. *)
    if !enabled = enable_default_init then (
      enabled := enable_default_after
    ) 
    else if !enabled = `MCS::enable_default_init then (
      enabled := `MCS::enable_default_after
    ) ;
    (* Remove disabled modules. *)
    enabled := !enabled |> List.filter (
      fun mdl -> List.mem mdl !disabled |> not
    )
  let _ = add_spec
    "--enable"
    (Arg.String
      (fun str ->
        let mdl = kind_module_of_string str in
        if List.mem mdl !enabled |> not
        then enabled := mdl :: !enabled
      )
    )
    (fun fmt ->
      Format.fprintf fmt
        "\
          where <string> can be %s@ \
          Enable Kind module, repeat option to enable several modules@ \
          Default: %s\
        "
        enable_values
        (string_of_enable enable_default_after)
    )
  let enable mdl = enabled := mdl :: !enabled
  let enabled () = !enabled

  (* Returns the invariant generation techniques enabled. *)
  let invgen_enabled () = enabled () |> List.filter (
    function
    | `INVGEN
    | `INVGENOS
    | `INVGENINT
    | `INVGENINTOS
    | `INVGENMACH
    | `INVGENMACHOS
    | `INVGENREAL
    | `INVGENREALOS -> true
    | _ -> false
  )

  (* Modules disabled. *)
  let _ = add_spec
    "--disable"
    (Arg.String
      (fun str ->
        let mdl = kind_module_of_string str in
        if List.mem mdl !disabled |> not
        then disabled := mdl :: !disabled
      )
    )
    (fun fmt ->
      Format.fprintf fmt
      "\
        where <string> can be %s@ \
        Disable a Kind module\
      "
      enable_values
    )
  let disabled () = !disabled


  (* Modular mode. *)
  let modular_default = false
  let modular = ref modular_default
  let _ = add_spec
    "--modular"
    (bool_arg modular)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Bottom-up analysis of each node@ \
          Default: %a\
        "
        fmt_bool modular_default
    )
  let modular () = !modular


  let slice_nodes_default = true
  let slice_nodes = ref slice_nodes_default
  let _ = add_spec
    "--slice_nodes"
    (bool_arg slice_nodes)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Only equations that are relevant for checking the contract and@ \
          properties of a node are considered during the analysis@ \
          Default: %a\
        "
        fmt_bool slice_nodes_default
    )
  let slice_nodes () = !slice_nodes


  let check_subproperties_default = true
  let check_subproperties = ref check_subproperties_default
  let _ = add_spec
    "--check_subproperties"
    (bool_arg check_subproperties)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Check properties of subnodes in addition to properties of the main node@ \
          Default: %a\
        "
        fmt_bool check_subproperties_default
    )
  let check_subproperties () = !check_subproperties


  let lus_compile_default = false
  let lus_compile = ref lus_compile_default
  let _ = add_spec
    "--compile"
    (bool_arg lus_compile)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Nodes proved correct will be compiled to Rust@ \
          Note that uninitialized pre's are not allowed in this mode@ \
          Default: %a\
        "
        fmt_bool lus_compile_default
    )
  let lus_compile () = !lus_compile


  (* Reject unguarded pre's in Lustre file. *)
  let lus_strict_default = false
  let lus_strict = ref lus_strict_default
  let _ = add_spec
    "--lus_strict"
    (bool_arg lus_strict)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Strict mode in Lustre: uninitialized pre and undefined@ \
          Local variables are not allowed when this flag is present@ \
          Default: %a\
        "
        fmt_bool lus_strict_default
    )
  let lus_strict () = !lus_strict || (lus_compile ())

  (* Active debug sections. *)
  let debug_default = []
  let debug_ref = ref debug_default
  let _ = add_spec
    "--debug"
    (Arg.String (fun str -> debug_ref := str :: !debug_ref))
    (fun fmt ->
      Format.fprintf fmt
        "\
          Enable debug output for a section, give one --debug option@ \
          for each section to be enabled\
        "
    )
  let debug () = !debug_ref


  (* Debug messages to file. *)
  let debug_log_default = None
  let debug_log = ref debug_log_default
  let _ = add_spec
    "--debug_log"
    (Arg.String (fun str -> debug_log := Some str))
    (fun fmt ->
      Format.fprintf fmt
      "\
        where <string> is a file path in an existing directory.@ \
        Output debug messages to file@ \
        Default: stdout\
      "
    )
  let debug_log () = ! debug_log


  (* Log level. *)
  let _ = set_log_level default_log_level
  let _ = add_specs ([
    ( "-qq",
      Arg.Unit (fun () -> set_log_level L_off),
      fun fmt ->
        Format.fprintf fmt "Disable output completely"
    ) ;
    ( "-q",
      Arg.Unit (fun () -> set_log_level L_fatal),
      fun fmt ->
        Format.fprintf fmt "Disable output, fatal errors only"
    ) ;
    ( "-s",
      Arg.Unit (fun () -> set_log_level L_error),
      fun fmt ->
        Format.fprintf fmt "Silence output, errors only"
    ) ;
    ( "-v",
      Arg.Unit (fun () -> set_log_level L_info),
      fun fmt ->
        Format.fprintf fmt "Output informational messages"
    ) ;
    ( "-vv",
      Arg.Unit (fun () -> set_log_level L_debug),
      fun fmt ->
        Format.fprintf fmt "Output informational and debug messages"
    ) ;
    ( "-vvv",
      Arg.Unit (fun () -> set_log_level L_trace),
      fun fmt ->
        Format.fprintf fmt "Output informational, debug and trace messages"
    )
  ])
  let log_level () = get_log_level ()

  (** ********************** Log formats ************************* **)

  let log_format_default = Log.get_log_format ()

  (* Use add_format_spec instead of add_spec *)

  (* XML log. *)
  let _ = add_format_spec
    "-xml"
    (Arg.Unit (fun () ->
         Log.set_log_format_xml ()
       ))
    (fun fmt -> Format.fprintf fmt "Output in XML format")
  let log_format_xml () = Log.get_log_format () = Log.F_xml

  (* JSON log. *)
  let _ = add_format_spec
    "-json"
    (Arg.Unit (fun () ->
         Log.set_log_format_json ()
       ))
    (fun fmt -> Format.fprintf fmt "Output in JSON format")
  let log_format_json () = Log.get_log_format () = Log.F_json

  (** ************************************************************ **)

  (* Colored output *)
  let color_default = true
  let color = ref color_default
  let _ = add_spec
    "--color"
    (bool_arg color)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Display colors in ascii output (deactivated when using -xml or -json)@ \
          Default: %a\
        "
        fmt_bool color_default
    )
  let color () = !color

  
  (* Use weak hash-consing. *)
  let weakhcons_default = false
  let weakhcons = ref weakhcons_default
  let _ = add_spec
    "--weakhcons"
    (bool_arg weakhcons)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Use weak hash-consing.@ \
          Default: %a\
        "
        fmt_bool weakhcons_default
    )
  let weakhcons () = !weakhcons
  
  (* Version flag. *)
  let _ = add_spec
    "--version"
    (Arg.Unit
      (fun () -> 
        Format.printf "%t@." pp_print_version ;
        exit 0
      )
    )
    (fun fmt -> Format.fprintf fmt "Print version information and exit")

  let only_filename_default = false
  let only_filename = ref only_filename_default
  (* marker to allow files that start with - *)
  let _ = add_spec
    "--"
    (Arg.Set only_filename)
    (fun fmt -> Format.fprintf fmt "What follows on the command line is \
                                    a file name.")

end

(* Re-exports. *)
type enable = Global.enable
type input_format = Global.input_format
type real_precision = Global.real_precision


(* ********************************************************************** *)
(* Accessor functions for flags                                           *)
(* ********************************************************************** *)

(* |===| The following functions allow to access global flags directly. *)

let output_dir = Global.output_dir
let include_dirs = Global.include_dirs
let log_invs = Global.log_invs
let print_invs = Global.print_invs
let only_parse = Global.only_parse
let lsp = Global.lsp
let only_tc = Global.only_tc
let no_tc = Global.no_tc            
let enabled = Global.enabled
let invgen_enabled = Global.invgen_enabled
let disable = Global.disable
let lus_strict = Global.lus_strict
let modular = Global.modular
let slice_nodes = Global.slice_nodes
let check_subproperties = Global.check_subproperties
let lus_main = Global.lus_main
let debug = Global.debug
let debug_log = Global.debug_log
let log_level = Global.log_level
let log_format_xml = Global.log_format_xml
let log_format_json = Global.log_format_json
let input_format = Global.input_format
let real_precision = Global.real_precision
let timeout_wall = Global.timeout_wall
let timeout_analysis = Global.timeout_analysis
let input_file = Global.input_file
let all_input_files = Global.get_all_input_files
let clear_input_files = Global.clear_input_files
let add_input_file = Global.add_input_file
let lus_compile = Global.lus_compile
let color = Global.color
let weakhcons = Global.weakhcons

(* Path to subdirectory for a system (in the output directory). *)
let subdir_for scope =
  Filename.concat
    (output_dir ())
    (String.concat "_" scope)


(* ********************************************************************** *)
(* Parsing of command-line options into flags                             *)
(* ********************************************************************** *)

let set_input_file s =
  try Global.set_input_file s with Unix.Unix_error _ -> ()

let anon_action s =
  match Global.input_file () with
  | "" -> (
    (* filenames that start with - are allowed after the flag -- *)
    if not !Global.only_filename && s.[0] = '-' then raise (UnknownFlag s);
    set_input_file s ;
    Global.set_input_format s;
    Global.set_output_dir s
  )
  | _ ->
    if s.[0] = '-' then raise (UnknownFlag s)
    else raise (Arg.Bad ("More than one input file given: "^s))


let arg_bool_of_string ((flag, _, desc) as tuple) s =
  if List.mem s true_strings then true else
  if List.mem s false_strings then false else BadArg (
    Format.sprintf "expected bool but got \"%s\"" s,
    tuple
  ) |> raise

let arg_int_of_string ((flag, _, desc) as tuple) s = try (
  int_of_string s
) with _ -> BadArg (
  Format.sprintf "expected int but got \"%s\"" s, tuple
) |> raise

let arg_float_of_string ((flag, _, desc) as tuple) s = try (
  float_of_string s
) with _ -> BadArg (
  Format.sprintf "expected float but got \"%s\"" s, tuple
) |> raise

let parse_clas specs anon_action global_usage_msg =
  match Array.to_list Sys.argv with
  | _ :: args ->

    (* Iterates over the specs to find the action for a CLA. *)
    let rec spec_loop clas flag = function
      | ((flag', spec, desc) as tuple) :: _ when flag = flag' -> (
        match spec with
        (* Unit specs, applying. *)
        | Arg.Unit f -> f () ; clas
        | Arg.Set b_ref -> b_ref := true ; clas
        | Arg.Clear b_ref -> b_ref := false ; clas
        (* Not unit spec, checking out next CLA. *)
        | _ -> (
          match clas with
          (* Got nothing, bad argument. *)
          | [] -> BadArg ("expected value, got nothing", tuple) |> raise
          (* Got a next argument, matching on spec. *)
          | arg :: clas ->
            (match spec with
              | Arg.Bool f -> arg_bool_of_string tuple arg |> f
              | Arg.String f -> f arg
              | Arg.Set_string s_ref -> s_ref := arg
              | Arg.Int f -> arg_int_of_string tuple arg |> f
              | Arg.Set_int i_ref -> i_ref := arg_int_of_string tuple arg
              | Arg.Float f -> arg_float_of_string tuple arg |> f
              | Arg.Set_float f_ref -> f_ref := arg_float_of_string tuple arg
              | _ ->
                failwith "unsupported specification (Tuple, Symbol, or Rest)"
            ) ;
            clas
        )
      )
      | _ :: tail -> spec_loop clas flag tail
      | [] -> UnknownFlag flag |> raise
    in

    (* Iterates over the CLAs. *)
    let rec cla_loop = function
      | [] -> ()
      | arg :: tail ->
        if !Global.only_filename then begin
          anon_action arg;
          cla_loop tail
        end
        else
          try spec_loop tail arg specs |> cla_loop
          with UnknownFlag flag ->
            anon_action flag;
            cla_loop tail
    in

    let check_format_flags args =
      if Log.get_log_format () = Global.log_format_default then
      (
        (* Look for a non-processed format argument *)
        let format_specs = Global.format_specs () in
        let format_arg_specs = List.fold_left (fun acc arg ->
          try List.find (fun (flag',_,_) -> arg = flag') format_specs :: acc
          with Not_found -> acc
        ) [] args
        in
        (* Last argument prevails over previous ones *)
        match List.rev format_arg_specs with
        | (_, Arg.Unit f, _) :: _ -> f () | _ -> ()
      )
    in

    (
      try args |> cla_loop
      with
      | UnknownFlag flag -> (
        check_format_flags args;
        (
          match Log.get_log_format () with
          | Log.F_pt | Log.F_relay -> (
            Global.print_help () ;
            Format.printf "\n\x1b[31;1mError\x1b[0m: unknown flag \"%s\".@." flag
          )
          | Log.F_xml | Log.F_json -> (
            Log.log L_error "Unknown flag '%s'" flag
          )
        );
        exit 2
      )
      | BadArg (error, spec) ->
        check_format_flags args;
        (
          match Log.get_log_format () with
          | Log.F_pt | Log.F_relay -> (
            Format.printf
              "\x1b[31;1mError on flag\x1b[0m@.@[<v>%a@]@.%s@."
              fmt_flag spec error
          )
          | Log.F_xml | Log.F_json -> (
            let flag, _, _ = spec in
            Log.log L_error "Error on flag '%s': %s" flag error
          )
        );
        exit 2
      | Arg.Bad expl ->
        check_format_flags args;
        (
          match Log.get_log_format () with
          | Log.F_pt | Log.F_relay -> (
            Format.printf
              "\x1b[31;1mBad argument\x1b[0m: @[<v>%s.@]@." expl
          )
          | Log.F_xml -> (
            Log.log L_error "Bad argument:@ @[<v>%s@]@." expl
          )
          | Log.F_json -> (
            Log.log L_error "Bad argument: %s" expl
          )
        );
        exit 2
    )

  | [] ->
    failwith "expected at least one argument, got zero"


let solver_dependant_actions solver =

  let get_version with_patch cmd =
    let get_rev output idx =
      int_of_string (Str.matched_group idx output)
    in
    let version_re =
      if with_patch then Str.regexp "\\([0-9]\\)\\.\\([0-9]\\)\\.\\([0-9]\\)"
      else Str.regexp "\\([0-9]\\)\\.\\([0-9]\\)"
    in
    let output = syscall cmd in
    try
      let _ = Str.search_forward version_re output 0 in
      let major_rev = get_rev output 1 in
      let minor_rev = get_rev output 2 in
      let patch_rev = if with_patch then get_rev output 3 else 0 in
      Some (major_rev, minor_rev, patch_rev)
    with Not_found -> None
  in

  match solver with
  | `Boolector_SMTLIB -> (
    let cmd = Format.asprintf "%s --version" (Smt.boolector_bin ()) in
    match get_version false cmd with
    | Some (major_rev, minor_rev, _) ->
      if major_rev < 3 then (
        if Smt.check_sat_assume () then (
          Log.log L_warn "Detected Boolector 2.4.1 or older: disabling check_sat_assume";
          Smt.set_check_sat_assume false
        )
      )
    | None -> Log.log L_warn "Couldn't determine Boolector version"
  )
  | `MathSAT_SMTLIB -> (
    let cmd = Format.asprintf "%s -version" (Smt.mathsat_bin ()) in
    match get_version true cmd with
    | Some (major_rev, minor_rev, patch_rev) ->
      if major_rev < 5 || (major_rev = 5 && (minor_rev < 5 || (minor_rev = 5 && patch_rev < 4)))  then (
        if Smt.check_sat_assume () then (
          Log.log L_warn "Detected MathSAT 5.5.3 or older: disabling check_sat_assume";
          Smt.set_check_sat_assume false
        )
      ); if BmcKind.compress () then (
          BmcKind.disable_compress () ;
          Log.log L_warn "Detected MathSAT: disabling ind_compress"
      )
    | None -> Log.log L_warn "Couldn't determine MathSAT version"
  ) 
  | `Z3_SMTLIB -> (
    let cmd = Format.asprintf "%s -version" (Smt.z3_bin ()) in
    match get_version false cmd with
    | Some (major_rev, minor_rev, _) ->
      if major_rev < 4 || (major_rev = 4 && minor_rev < 6) then (
        if Smt.check_sat_assume () then (
          Log.log L_warn "Detected Z3 4.5.x or older: disabling check_sat_assume";
          Smt.set_check_sat_assume false
        )
      )
    | None -> Log.log L_warn "Couldn't determine Z3 version"
  )
  | `Yices_SMTLIB -> (
    let cmd = Format.asprintf "%s --version" (Smt.yices2smt2_bin ()) in
    match get_version true cmd with
    | Some (major_rev, minor_rev, patch_rev) ->
      if major_rev < 2 || (major_rev = 2 && minor_rev < 6) then (
        let actions = [] in
        let actions =
          if List.mem `IC3 (Global.enabled ()) then
            (Global.disable `IC3; "disabling IC3" :: actions)
          else actions
        in
        let actions =
          if Smt.logic () = `None then (
            Smt.set_logic `detect;
            "enabling detection of SMT logic" :: actions
          )
          else actions
        in
        let actions =
          if Smt.check_sat_assume () then (
            Smt.set_check_sat_assume false;
            "disabling check_sat_assume" :: actions
          )
          else actions
        in
        if actions <> [] then (
          Log.log L_warn "Detected Yices 2.5.x or older: %a"
            (pp_print_list Format.pp_print_string ",@ ") actions
        )
      )
      else if (major_rev > 2 || minor_rev > 6 || patch_rev > 1) then (
        Smt.set_yices2_smt2models true
      )
    | None -> Log.log L_warn "Couldn't determine Yices 2 version"
  )
  | `CVC4_SMTLIB -> (
    let cmd = Format.asprintf "%s --version" (Smt.cvc4_bin ()) in
    match get_version false cmd with
    | Some (major_rev, minor_rev, _) ->
      if major_rev < 1 || (major_rev = 1 && minor_rev < 7) then (
        if Smt.check_sat_assume () then (
          Log.log L_warn "Detected CVC4 1.6 or older: disabling check_sat_assume";
          Smt.set_check_sat_assume false
        )
      )
      else if (major_rev > 1 || minor_rev >= 8) then (
        Smt.set_cvc4_rewrite_divk false;
        Smt.set_cvc4_bv_consts_in_binary false
      )
    | None -> Log.log L_warn "Couldn't determine CVC4 version"
  )
  | `Yices_native -> (
    let cmd = Format.asprintf "%s --version" (Smt.yices_bin ()) in
    match get_version false cmd with
    | Some (major_rev, minor_rev, _) ->
      if major_rev > 1 then (
        Log.log L_error "Selected Yices 1 (native format), but found Yices 2 or later";
        exit 2
      )
    | None -> Log.log L_warn "Couldn't determine Yices version"
  )
  | _ -> ()


let name_of_category = function
  | `NODE_CALL -> ("node_calls", "nodeCalls")
  | `CONTRACT_ITEM -> ("contracts", "contracts")
  | `EQUATION -> ("equations", "equations")
  | `ASSERTION -> ("assertions", "assertions")
  | `ANNOTATIONS -> ("annotations", "annotations")

(* XML starting with options *)
let print_xml_options () =
    let pp_print_category_str fmt cat =
      Format.fprintf fmt "%s" (name_of_category cat |> fst)
    in
    Format.fprintf !log_ppf "@[<v>\
      <Results \
        xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" \
        enabled=\"%a\" \
        timeout=\"%f\" \
        bmc_max=\"%d\" \
        compositional=\"%b\" \
        modular=\"%b\"%s%s\
      >@.@.@.\
    "
    (pp_print_list Log.pp_print_kind_module_xml_src ",") (Global.enabled ())
    (Global.timeout_wall ())
    (BmcKind.max ())
    (Contracts.compositional ())
    (Global.modular ())
    (
      if IVC.compute_ivc ()
      then
        Format.asprintf " \
        ivc_category=\"%a\" \
        ivc_all=\"%b\" \
        ivc_approximate=\"%b\" \
        ivc_smallest_first=\"%b\" \
        ivc_only_main_node=\"%b\" \
        ivc_must_set=\"%b\""
        (pp_print_list pp_print_category_str ",") (IVC.ivc_category ())
        (IVC.ivc_all ()) (IVC.ivc_approximate ()) (IVC.ivc_smallest_first ())
        (IVC.ivc_only_main_node ()) (IVC.ivc_must_set ())
      else ""
    )
    (
      if MCS.compute_mcs () || (Global.enabled () |> List.exists (fun m -> m = `MCS))
      then
        Format.asprintf " \
        mcs_category=\"%a\" \
        mcs_all=\"%b\" \
        mcs_only_main_node=\"%b\""
        (pp_print_list pp_print_category_str ",") (MCS.mcs_category ())
        (MCS.mcs_all ()) (MCS.mcs_only_main_node ())
      else ""
    )

let print_json_options () =
    let pp_print_module_str fmt mdl =
      Format.fprintf fmt "\"%s\"" (Lib.short_name_of_kind_module mdl)
    in
    let pp_print_category_str fmt cat =
      Format.fprintf fmt "\"%s\"" (name_of_category cat |> snd)
    in
    Format.fprintf !log_ppf "{@[<v 1>@,\
        \"objectType\" : \"kind2Options\",@,\
        \"enabled\" :@,[@[<v 1>@,%a@]@,],@,\
        \"timeout\" : %f,@,\
        \"bmcMax\" : %d,@,\
        \"compositional\" : %b,@,\
        \"modular\" : %b%s%s\
        @]@.}@.\
    "
    (pp_print_list pp_print_module_str ",@,") (Global.enabled ())
    (Global.timeout_wall ())
    (BmcKind.max ())
    (Contracts.compositional ())
    (Global.modular ())
    (
      if IVC.compute_ivc ()
      then
        Format.asprintf ",@.  \
        \"ivc\" :@,  \
        { @[<v>@,\
        \"ivcCategory\" :@,[@[<v 1>@,%a@]@,],@,\
        \"ivcAll\" : %b,@,\
        \"ivcApproximate\" : %b,@,\
        \"ivcSmallestFirst\" : %b,@,\
        \"ivcOnlyMainNode\" : %b,@,\
        \"ivcMustSet\" : %b\
        @]@.  }"
        (pp_print_list pp_print_category_str ",@,") (IVC.ivc_category ())
        (IVC.ivc_all ()) (IVC.ivc_approximate ()) (IVC.ivc_smallest_first ())
        (IVC.ivc_only_main_node ()) (IVC.ivc_must_set ())
      else ""
    )
    (
      if MCS.compute_mcs () || (Global.enabled () |> List.exists (fun m -> m = `MCS))
      then
        Format.asprintf ",@.  \
        \"mcs\" :@,  \
        { @[<v>@,\
        \"mcsCategory\" :@,[@[<v 1>@,%a@]@,],@,\
        \"mcsAll\" : %b,@,\
        \"mcsOnlyMainNode\" : %b\
        @]@.  }"
        (pp_print_list pp_print_category_str ",@,") (MCS.mcs_category ())
        (MCS.mcs_all ()) (MCS.mcs_only_main_node ())
      else ""
    )

let post_argv_parse_actions () =

  if Global.log_format_xml () then print_xml_options ();
  if Global.log_format_json () then Format.fprintf !log_ppf "[@.";

  (* Don't print banner if no output at all. *)
  if not (Global.log_level () = L_off) then (
    (* Temporarily set log level to info and output logo. *)
    let old_log_level = get_log_level () in
    set_log_level L_info ;
    Log.log L_info "%a" pp_print_banner () ;
    if Global.log_format_json () then Format.fprintf !log_ppf ",@.";
    (* Reset log level. *)
    set_log_level old_log_level ;
  );
  if Global.log_format_json () then print_json_options ()


let parse_argv () =
  (* CLAPing. *)
  parse_clas (Global.all_kind2_specs ()) anon_action Global.usage_msg ;

  (* Colors if flag is not false and not in xml or json mode *)
  let open Format in
  if color () && not (log_format_xml () || log_format_json ()) then begin
    pp_set_tags std_formatter true;
    pp_set_tags err_formatter true;
    pp_set_tags !Lib.log_ppf true;
  end;

  (* If any module info was requested, print it and exit. *)
  Global.help_of () |> List.rev |> print_module_info ;

  (* Check solver on path *)
  Smt.check_smtsolver ();

  Smt.check_qe_solver ();

  (* Finalize the list of enabled module. *)
  Global.finalize_enabled ();

  IVC.finalize_ivc_elements ();
  MCS.finalize_mcs_elements ();

  post_argv_parse_actions ();
  
  solver_dependant_actions (Smt.solver ());

  (match Smt.solver (), Smt.qe_solver () with
  | `Z3_SMTLIB, `Z3_SMTLIB -> ()
  | `CVC4_SMTLIB, `CVC4_SMTLIB -> ()
  | _, `Z3_SMTLIB -> solver_dependant_actions `Z3_SMTLIB
  | _, `CVC4_SMTLIB -> solver_dependant_actions `CVC4_SMTLIB
  | _, _ -> ()) ;

  if IVC.compute_ivc () && BmcKind.compress () then (
    BmcKind.disable_compress () ;
    Log.log L_warn "IVC post-analysis enabled: disabling ind_compress"
  )


(* Parsing command line arguments at load time *)
let () = parse_argv ()


(*
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End:
*)
