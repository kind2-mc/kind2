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

(* Configuration for cvc5 *)
let cmd_line
    _ (* logic *)
    timeout
    _ (* produce_assignments *) 
    _ (* produce_proofs *)
    _ (* produce_unsat_cores *)
    _ (* produce_unsat_assumptions *)
    _ (* minimize_cores *) 
    _ (* produce_interpolants *) =

  (* Path and name of cvc5 executable *)
  let cvc5_bin = Flags.Smt.cvc5_bin () in

  let common_flags =
    [|
      "--incremental";
      "--ext-rew-prep=agg";
      "--mbqi";                (* Use model-based quantifier instantiation (best for sat) *)
      "--full-saturate-quant"; (* Resort to full effort techniques instead of answering
                                  unknown due to limited quantifier reasoning (best for unsat) *)
    |]
  in

  let base_cmd = [| cvc5_bin; "--lang=smt2" |] in

  (* Timeout based on Flags.timeout_wall has been disabled because
     it seems to cause performance regressions on some models... *)
  let timeout_global = None
  (*  if Flags.timeout_wall () > 0.
    then Some (Stat.remaining_timeout () +. 1.0)
    else None*)
  in
  let timeout_local =
    if timeout > 0 then Some (float_of_int timeout) else None
  in
  let timeout = Lib.min_option timeout_global timeout_local in

  let cmd =
    match timeout with
    | None -> base_cmd
    | Some timeout ->
        let timeout =
          Format.sprintf "--tlimit=%.0f" (1000.0 *. timeout |> ceil)
        in
        Array.append base_cmd [| timeout |]
  in

  Array.concat [ cmd; common_flags ]

let check_sat_limited_cmd _ =
  failwith "check-sat with timeout not implemented for cvc5"
