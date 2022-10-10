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

include GenericSMTLIBDriver


(* Configuration for Yices *)
let cmd_line
    logic
    timeout
    _ (* produce_assignments *) 
    _ (* produce_proofs *)
    _ (* produce_unsat_cores *)
    _ (* produce_unsat_assumptions *)
    _ (* minimize_cores *) 
    _ (* produce_interpolants *) = 

  (let open TermLib in
   let open TermLib.FeatureSet in
   match logic with
   | `Inferred l when mem NA l && Flags.Smt.check_sat_assume () -> (
     Flags.Smt.set_check_sat_assume false;
     KEvent.log Lib.L_warn
       "In %a: Yices 2 does not support check-sat-assuming with non-linear models.@ \
        Disabling check_sat_assume."
       Lib.pp_print_kind_module (KEvent.get_module ())
   )
   | `Inferred l when mem BV l && (mem IA l || mem RA l) -> (
     let msg =
       Format.asprintf
         "In %a: Yices 2 does not support programs with both integers/reals and machine integers"
           Lib.pp_print_kind_module (KEvent.get_module ())
     in
     failwith msg
   )
   | _ -> ()
  );

  (* Path and name of Yices executable *)
  let yices2smt2_bin = Flags.Smt.yices2smt2_bin () in

  let base_cmd = [| yices2smt2_bin; "--incremental" |] in

  (* Timeout based on Flags.timeout_wall has been disabled because
     it seems to cause performance regressions on some models... *)
  let timeout_global = None
  (*  if Flags.timeout_wall () > 0.
    then Some (Stat.remaining_timeout () +. 1.0)
    else None*)
  in
  let timeout_local =
    if timeout > 0
    then Some (float_of_int timeout)
    else None
  in
  let timeout = Lib.min_option timeout_global timeout_local in

  let cmd =
    match timeout with
    | None -> base_cmd
    | Some timeout ->
      let timeout =
        Format.sprintf "--timeout=%.0f" (timeout |> ceil)
      in
      Array.append base_cmd [|timeout|]
  in

  if Flags.Smt.yices2_smt2models () then
    Array.append cmd [|"--smt2-model-format"|]
  else
    cmd


let check_sat_limited_cmd _ = 
  failwith "check-sat with timeout not implemented for Yices2"

