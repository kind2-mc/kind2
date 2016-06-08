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


module Make_Spec (Dummy:sig end) = struct
  (* All the flag specification of this module. *)
  let all_specs = ref []
  let add_specs specs = all_specs := !all_specs @ specs
  let add_spec flag parse desc = all_specs := (flag, parse, desc) :: !all_specs

  (* Returns all the flag specification of this module. *)
  let all_specs () = !all_specs
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
    | `Z3_SMTLIB
    | `CVC4_SMTLIB
    | `MathSat5_SMTLIB
    | `Yices_SMTLIB
    | `Yices_native
    | `detect
  ]
  let solver_of_string = function
    | "Z3" -> `Z3_SMTLIB
    | "CVC4" -> `CVC4_SMTLIB
    | "MathSat5" -> `MathSat5_SMTLIB
    | "Yices2" -> `Yices_SMTLIB
    | "Yices" -> `Yices_native
    | _ -> Arg.Bad "Bad value for --smt_solver" |> raise
  let string_of_solver = function
    | `Z3_SMTLIB -> "Z3"
    | `CVC4_SMTLIB -> "CVC4"
    | `Yices_SMTLIB -> "Yices2"
    | `Yices_native -> "Yices"
    | `MathSat5_SMTLIB -> "MathSat5"
    | `detect -> "detect"
  let solver_values = "Z3, CVC4, MathSat5, Yices, Yices2"
  let solver_default = `detect
  let solver = ref solver_default
  let _ = add_spec
    "--smt_solver"
    (Arg.String (fun str -> solver := solver_of_string str))
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          where <string> can be %s@ \
          Choose an SMT solver@ \
          Default: %s\
        @]"
        solver_values
        (string_of_solver solver_default)
    )
  let set_solver s = solver := s
  let solver () = !solver

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
  let logic_default = `None
  let logic = ref logic_default
  let _ = add_spec
    "--smt_logic"
    (Arg.String (fun str -> logic := logic_of_string str))
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          where <string> is none, detect, or a legal SMT-LIB logic@ \
          Select logic for SMT solvers@ \
          \"none\" for no logic (default)@ \
          \"detect\" to detect with the input system@ \
          Other SMT-LIB logics will be passed to the solver\
        @]"
    )
    
  let detect_logic_if_none () =
    if !logic = `None then logic := `detect
          
  let logic () = !logic

  (* Activates check-sat with assumptions when supported. *)
  let check_sat_assume_of_string s = s
  let string_of_check_sat_assume s = s
  let check_sat_assume_default = true
  let check_sat_assume = ref check_sat_assume_default
  let _ = add_spec
    "--check_sat_assume"
    (bool_arg check_sat_assume)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          Use check-sat with assumptions, or simulate with push/pop@ \
          when false@ \
          Default: %a\
        @]"
      fmt_bool check_sat_assume_default
    )
  let check_sat_assume () = !check_sat_assume

  (* Use short name for variables at SMT level. *)
  let short_names_of_string s = s
  let string_of_short_names s = s
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

  (* Z3 binary. *)
  let z3_bin_of_string s = s
  let string_of_z3_bin s = s
  let z3_bin_default = "z3"
  let z3_bin = ref z3_bin_default
  let _ = add_spec
    "--z3_bin"
    (Arg.Set_string z3_bin)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Executable of Z3 solver@ Default: \"%s\"@]"
        (string_of_z3_bin z3_bin_default)
    )
  let set_z3_bin str = z3_bin := str
  let z3_bin () = ! z3_bin

  (* CVC4 binary. *)
  let cvc4_bin_of_string s = s
  let string_of_cvc4_bin s = s
  let cvc4_bin_default = "cvc4"
  let cvc4_bin = ref cvc4_bin_default
  let _ = add_spec
    "--cvc4_bin"
    (Arg.Set_string cvc4_bin)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Executable of CVC4 solver@ Default: \"%s\"@]"
        (string_of_cvc4_bin cvc4_bin_default)
    )
  let set_cvc4_bin str = cvc4_bin := str
  let cvc4_bin () = !cvc4_bin

  (* Mathsat 5 binary. *)
  let mathsat5_bin_of_string s = s
  let string_of_mathsat5_bin s = s
  let mathsat5_bin_default = "mathsat"
  let mathsat5_bin = ref mathsat5_bin_default
  let _ = add_spec
    "--mathsat5_bin"
    (Arg.Set_string mathsat5_bin)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Executable of MathSAT5 solver@ Default: \"%s\"@]"
        (string_of_mathsat5_bin mathsat5_bin_default)
    )
  let set_mathsat5_bin str = mathsat5_bin := str
  let mathsat5_bin () = !mathsat5_bin

  (* Yices binary. *)
  let yices_bin_of_string s = s
  let string_of_yices_bin s = s
  let yices_bin_default = "yices"
  let yices_bin = ref yices_bin_default
  let _ = add_spec
    "--yices_bin"
    (Arg.Set_string yices_bin)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Executable of Yices solver@ Default: \"%s\"@]"
        (string_of_yices_bin yices_bin_default)
    )
  let set_yices_bin str = yices_bin := str
  let yices_bin () = !yices_bin

  (* Yices 2 binary. *)
  let yices2smt2_bin_of_string s = s
  let string_of_yices2smt2_bin s = s
  let yices2smt2_bin_default = "yices-smt2"
  let yices2smt2_bin = ref yices2smt2_bin_default
  let _ = add_spec
    "--yices2_bin"
    (Arg.Set_string yices2smt2_bin)
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>Executable of Yices2 SMT2 solver@ Default: \"%s\"@]"
        (string_of_yices2smt2_bin yices2smt2_bin_default)
    )
  let set_yices2smt2_bin str = yices2smt2_bin := str
  let yices2smt2_bin () = !yices2smt2_bin

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
  let trace () = !trace

  (* Folder to log the SMT traces into. *)
  let trace_dir = ref "."
  let set_trace_dir s =
    trace_dir := Filename.concat s "smt_trace"
  let trace_dir () = !trace_dir
      
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

  type qe = [
    `Z3 | `Z3_impl | `Z3_impl2 | `Cooper
  ]
  let qe_of_string = function
    | "Z3" -> `Z3
    | "Z3-impl" -> `Z3_impl
    | "Z3-impl2" -> `Z3_impl2
    | "cooper" -> `Cooper
    | _ -> raise (Arg.Bad "Bad value for --ic3_qe")
  let string_of_qe = function
    | `Z3 -> "Z3"
    |  `Z3_impl -> "Z3-impl"
    |  `Z3_impl2 -> "Z3-impl2"
    | `Cooper -> "cooper"
  let qe_values = [
    `Z3 ; `Z3_impl ; `Z3_impl2 ; `Cooper
  ] |> List.map string_of_qe |> String.concat ", "
  let qe_default = `Cooper
  let qe = ref qe_default
  let _ = add_spec
    "--ic3_qe"
    (Arg.String (fun str -> qe := qe_of_string str))
    (fun fmt ->
      Format.fprintf fmt
        "@[<v>\
          where <string> can be %s@ \
          Choose quantifier elimination algorithm@ \
          Default: %s\
        @]"
        qe_values (string_of_qe qe_default)
    )
  let set_qe q = qe := q
  let qe () = !qe

  type extract = [ `First | `Vars ]
  let extract_of_string = function
    | "first" -> `First
    | "vars" -> `Vars
    | _ -> raise (Arg.Bad "Bad value for --ic3_extract")
  let string_of_extract = function
    | `First -> "first"
    | `Vars -> "vars"
  let extract_values = [
    `First ; `Vars
  ] |> List.map string_of_extract |> String.concat ", "
  let extract_default = `First
  let extract = ref extract_default
  let _ = add_spec
    "--ic3_extract"
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
      The QE implemented in Kind 2 does not support real arithmetic. If the@ \
      solver used is z3, then z3's QE will be used instead of the internal@ \
      one for systems with real variables.@ \
      IC3 (module \"ic3\") is the only Kind 2 technique that uses QE.\
    @]"

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
  let id = "contract"
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
  let add_specs specs = all_specs := !all_specs @ specs
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
  (Certif.id,
    (module Certif: FlagModule)
  ) ;
]

(* Formats an element of [module_map]. *)
let fmt_module_info fmt (id, m0d) =
  let module Flags = (val m0d: FlagModule) in
  Format.fprintf fmt
    "\
      |===| Module \x1b[1m%s\x1b[0m:@.\
      @[<v>%t@]\
      @.  @[<v>%a@]@.\
    "
    id
    Flags.fmt_explain
    (pp_print_list fmt_flag "@ ")
    (Flags.all_specs ())

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
    input if no file is given.@.\
    Global options follow, \
    use \"--help_of\" for module-specific information.\
  " usage_msg_header


  (* Prints help. *)
  let print_help () =
    Format.printf "%s@.  " usage_msg ;
    all_specs () |> print_flags ;
    Format.printf "@."


  (* Input flag. *)
  let input_file_default = ""
  let input_file = ref input_file_default
  let set_input_file f = input_file := f
  let input_file () = !input_file

  (* All files in the cone of influence of the input file. *)
  let all_input_files = ref []
  let clear_input_files () = all_input_files := []
  let add_input_file file = all_input_files := file :: !all_input_files
  let get_all_input_files () = ! all_input_files


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
    | `Extension -> assert false
    | (`Lustre | `Native | `Horn) as f -> f


  (* Output directory. *)
  let output_dir_default = "kind2"
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
          Default: \"<filename>.out\"\
        "
    )

  let set_output_dir s =
    if !output_dir = "kind2" then
      let b = Filename.basename s in
      let d = try Filename.chop_extension b with Invalid_argument _ -> b in
      output_dir_action(d ^ ".out")

  let output_dir () = !output_dir


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


  (* Modules enabled. *)
  type enable = kind_module list
  let kind_module_of_string = function
    | "IC3" -> `IC3
    | "BMC" -> `BMC
    | "IND" -> `IND
    | "IND2" -> `IND2
    | "INVGEN" -> `INVGEN
    | "INVGENOS" -> `INVGENOS
    | "C2I" -> `C2I
    | "interpreter" -> `Interpreter
    | unexpected -> Arg.Bad (
      Format.sprintf "Unexpected value \"%s\" for flag --enable" unexpected
    ) |> raise
  let string_of_kind_module = function
    | `IC3 -> "IC3"
    | `BMC -> "BMC"
    | `IND -> "IND"
    | `IND2 -> "IND2"
    | `INVGEN -> "INVGEN"
    | `INVGENOS -> "INVGENOS"
    | `C2I -> "C2I"
    | `Interpreter -> "interpreter"
  let string_of_enable = function
    | head :: tail -> (
      List.fold_left
        ( fun s m -> s ^ ", " ^ (string_of_kind_module m) )
        ("[" ^ (string_of_kind_module head))
        tail
      ) ^ "]"
    | [] -> "[]"
  let enable_values = [
    `IC3 ; `BMC ; `IND ; `IND2 ; `INVGEN ; `INVGENOS ; `C2I ; `Interpreter
  ] |> List.map string_of_kind_module |> String.concat ", "

  let enable_default_init = []
  let disable_default_init = []

  let enable_default_after = [
    `BMC ; `IND ; `IND2 ; `IC3 ; `INVGEN ; `INVGENOS
  ]
  let enabled = ref enable_default_init
  let disabled = ref disable_default_init
  let finalize_enabled () =
    (* If [enabled] is unchanged, set it do default after init. *)
    if !enabled = enable_default_init then (
      enabled := enable_default_after
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
  let enabled () = !enabled

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
  let lus_strict () = !lus_strict

  let lus_compile_default = false
  let lus_compile = ref lus_compile_default
  let _ = add_spec
    "--compile"
    (bool_arg lus_compile)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Nodes proved correct will be compiled to Rust@ \
          Default: %a\
        "
        fmt_bool lus_compile_default
    )
  let lus_compile () = !lus_compile

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
  let log_level_default = L_warn
  let log_level = ref log_level_default
  let _ = add_specs ([
    ( "-qq",
      Arg.Unit (fun () -> log_level := L_off),
      fun fmt ->
        Format.fprintf fmt "Disable output completely"
    ) ;
    ( "-q",
      Arg.Unit (fun () -> log_level := L_fatal),
      fun fmt ->
        Format.fprintf fmt "Disable output, fatal errors only"
    ) ;
    ( "-s",
      Arg.Unit (fun () -> log_level := L_error),
      fun fmt ->
        Format.fprintf fmt "Silence output, errors only"
    ) ;
    ( "-v",
      Arg.Unit (fun () -> log_level := L_info),
      fun fmt ->
        Format.fprintf fmt "Output informational messages"
    ) ;
    ( "-vv",
      Arg.Unit (fun () -> log_level := L_debug),
      fun fmt ->
        Format.fprintf fmt "Output informational and debug messages"
    ) ;
    ( "-vvv",
      Arg.Unit (fun () -> log_level := L_trace),
      fun fmt ->
        Format.fprintf fmt "Output informational, debug and trace messages"
    )
  ])
  let log_level () = !log_level


  (* XML log. *)
  let log_format_xml_default = false
  let log_format_xml = ref log_format_xml_default
  let _ = add_spec
    "-xml"
    (Arg.Set log_format_xml)
    (fun fmt -> Format.fprintf fmt "Output in XML format")
  let log_format_xml () = !log_format_xml

  
  (* Colored output *)
  let color_default = true
  let color = ref color_default
  let _ = add_spec
    "--color"
    (bool_arg color)
    (fun fmt ->
      Format.fprintf fmt
        "\
          Display colors in ascii output (deactivated when using -xml)@ \
          Default: %a\
        "
        fmt_bool color_default
    )
  let color () = !color

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
    (fun fmt -> Format.fprintf fmt "What follows on the command line is\
                                    a file name.")

end

(* Re-exports. *)
type enable = Global.enable
type input_format = Global.input_format


(* ********************************************************************** *)
(* Accessor functions for flags                                           *)
(* ********************************************************************** *)

(* |===| The following functions allow to access global flags directly. *)

let output_dir = Global.output_dir
let enable = Global.enabled
let lus_strict = Global.lus_strict
let modular = Global.modular
let lus_main = Global.lus_main
let debug = Global.debug
let debug_log = Global.debug_log
let log_level = Global.log_level
let log_format_xml = Global.log_format_xml
let input_format = Global.input_format
let timeout_wall = Global.timeout_wall
let input_file = Global.input_file
let all_input_files = Global.get_all_input_files
let clear_input_files = Global.clear_input_files
let add_input_file = Global.add_input_file
let lus_compile = Global.lus_compile
let color = Global.color

(* Path to subdirectory for a system (in the output directory). *)
let subdir_for scope =
  Filename.concat
    (output_dir ())
    (String.concat "_" scope)


(* ********************************************************************** *)
(* Parsing of command-line options into flags                             *)
(* ********************************************************************** *)

let anon_action s =
  match Global.input_file () with
  | "" ->
    (* filenames that start with - are allowed after the flag -- *)
    if not !Global.only_filename && s.[0] = '-' then raise (UnknownFlag s);
    Global.set_input_file s;
    Global.set_input_format s;
    Global.set_output_dir s;
  | _ -> raise (Arg.Bad "More than one input file given")

let set_smtsolver = function

  | `Z3_SMTLIB as smtsolver ->

    (function z3_bin ->
      Smt.set_solver smtsolver ;
      Smt.set_z3_bin z3_bin )

  | `CVC4_SMTLIB as smtsolver ->

    (function cvc4_bin ->
      Smt.set_solver smtsolver ;
      Smt.set_cvc4_bin cvc4_bin )

  | `MathSat5_SMTLIB as smtsolver ->

    (function mathsat5_bin ->
      Smt.set_solver smtsolver ;
      Smt.set_mathsat5_bin mathsat5_bin )

  | `Yices_native as smtsolver ->

    (function yices_bin ->
      Smt.set_solver smtsolver ;
      Smt.set_yices_bin yices_bin )

  | `Yices_SMTLIB as smtsolver ->

    (function yices2smt2_bin ->
      Smt.set_solver smtsolver ;
      Smt.set_yices2smt2_bin yices2smt2_bin )

  | `detect -> (function _ -> ())


let bool_of_string ((flag, _, desc) as tuple) s =
  if List.mem s true_strings then true else
  if List.mem s false_strings then false else BadArg (
    Format.sprintf "expected bool but got \"%s\"" s,
    tuple
  ) |> raise

let int_of_string ((flag, _, desc) as tuple) s = try (
  int_of_string s
) with _ -> BadArg (
  Format.sprintf "expected int but got \"%s\"" s, tuple
) |> raise

let float_of_string ((flag, _, desc) as tuple) s = try (
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
              | Arg.Bool f -> bool_of_string tuple arg |> f
              | Arg.String f -> f arg
              | Arg.Set_string s_ref -> s_ref := arg
              | Arg.Int f -> int_of_string tuple arg |> f
              | Arg.Set_int i_ref -> i_ref := int_of_string tuple arg
              | Arg.Float f -> float_of_string tuple arg |> f
              | Arg.Set_float f_ref -> f_ref := float_of_string tuple arg
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

    (
      try Array.to_list Sys.argv |> List.tl |> cla_loop
      with
      | UnknownFlag flag ->
        Global.print_help () ;
        Format.printf "\n\x1b[31;1mError\x1b[0m: unknown flag \"%s\".@." flag;
        exit 2
      | BadArg (error, flag) ->
        Format.printf
          "\x1b[31;1mError on flag\x1b[0m@.@[<v>%a@]@.%s@."
          fmt_flag flag error ;
      | Arg.Bad expl ->
        Format.printf
          "\x1b[31;1mBad argument\x1b[0m: @[<v>%s.@]@." expl;
        exit 2
    )

  | [] ->
    failwith "expected at least one argument, got zero"


let parse_argv () =
  (* CLAPing. *)
  parse_clas (Global.all_kind2_specs ()) anon_action Global.usage_msg ;

  (* If any module info was requested, print it and exit. *)
  Global.help_of () |> List.rev |> print_module_info ;

  (* Finalize the list of enabled module. *)
  Global.finalize_enabled ();


  (* Colors if flag is not false and not in xml mode *)
  let open Format in
  if color () && not (log_format_xml ()) then begin
    pp_set_tags std_formatter true;
    pp_set_tags err_formatter true;
    pp_set_tags !Lib.log_ppf true;
  end




(*
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End:
*)
