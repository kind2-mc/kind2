(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020 by the Board of Trustees of the University of Iowa

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

include GenericSMTLIBDriver

(* Configuration for MathSAT *)
let cmd_line 
    logic timeout 
    _ (* produce_models *)
    _ (* produce_proofs *)
    _ (* produce_unsat_cores *)
    _ (* produce_unsat_assumptions *)
    _ (* minimize_cores *)
    _ (* produce_interpolants *) =

  (let open TermLib in
    let open TermLib.FeatureSet in
    match logic with
    | `Inferred l when mem BV l && (mem IA l || mem RA l) -> (
     let msg =
       Format.asprintf
         "In %a: MathSAT does not support programs with both integers/reals and machine integers"
           Lib.pp_print_kind_module (KEvent.get_module ())
     in
     failwith msg
   )
   | _ -> ()
  );

  (* Path and name of MathSAT executable *)
  let mathsat_bin = Flags.Smt.mathsat_bin () in

  (* Timeout based on Flags.timeout_wall has been disabled because
     it seems to cause performance regressions on some models... *)
  let timeout_global =
    None
    (* if Flags.timeout_wall () > 0.
       then Some (Stat.remaining_timeout () +. 1.0)
       else None*)
  in
  let timeout_local =
    if timeout > 0 then Some (float_of_int timeout) else None
  in
  let timeout = Lib.min_option timeout_global timeout_local in

  (* 
    Disable common flags.
    shallow_incrementality=true
    allow_bool_function_args=true
    preprocessor.simplification=2
    theory.bv.eager=true
   *)

  let cmd =
    [|
      mathsat_bin;
      (* Workaround for a bug in MathSAT (last checked version: 5.6.10) *)
      "-preprocessor.interpolation_ite_elimination=true";
      (* Required for interpolation *)
      "-theory.bv.eager=false"
    |]
  in
    match timeout with
    | None -> cmd
    | Some timeout ->
      let timeout =
        Format.sprintf "-timeout=%.0f" ((1000.0 *. timeout) |> ceil)
      in
      Array.append cmd [|timeout|]


let pp_print_symbol ?arity ppf s =
  (* Workaround for a bug in MathSAT (last checked version: 5.6.10):
     (get-value (= x #b0000)) throws "syntax error, unexpected BINCONSTANT"
     (get-value (= x (_ bv0 4))) works fine
  *)
  match Symbol.node_of_symbol s with
  | `UBV b -> Bitvector.pp_smtlib_print_bitvector_d ppf b 
  | `BV b -> Bitvector.pp_smtlib_print_bitvector_d ppf b
  | n -> GenericSMTLIBDriver.pp_print_symbol_node ?arity ppf n

let string_of_symbol ?arity s = Format.asprintf "%a" (pp_print_symbol ?arity) s

(* Pretty-print a term (based on pp_print_symbol implementation above) *)
let pp_print_term ppf t =
  Term.T.pp_print_term_w pp_print_symbol Var.pp_print_var pp_print_sort ppf t

(* Pretty-print an expression (based on pp_print_symbol implementation above) *)
let pp_print_expr = pp_print_term
