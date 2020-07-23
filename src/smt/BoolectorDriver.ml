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

(* Configuration for Boolector *)
let cmd_line logic timeout produce_assignments produce_proofs produce_cores
    minimize_cores produce_interpolants =
  (* Path and name of Boolector executable *)
  let boolector_bin = Flags.Smt.boolector_bin () in

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

  let base_cmd = [| boolector_bin; "--smt2"; "--incremental" |] in
  match timeout with
  | None -> base_cmd
  | Some timeout ->
      let timeout = Format.sprintf "--time=%.0f" (timeout |> ceil) in
      Array.append base_cmd [| timeout |]

(* Command to limit check-sat in Z3 to run for the given numer of ms
   at most *)
let check_sat_limited_cmd ms =
  failwith "check-sat with timeout not implemented for Boolector"

let string_of_logic l =
  let open TermLib in
  let open TermLib.FeatureSet in
  match l with
  | `Inferred fs ->
      if mem IA fs || mem RA fs then
        failwith "Boolector only supports BV logics"
      else
        (* We add BV because Boolector does not support QF_UF logic *)
        GenericSMTLIBDriver.string_of_logic (`Inferred (add BV fs))
  | `None -> "ALL"
  | `SMTLogic s ->
      if String.contains s 'I' || String.contains s 'R' then
        failwith "Boolector only supports BV logics"
      else if not (String.contains s 'B') then
        (* We add BV because Boolector does not support QF_UF logic *)
        String.concat "" [ s; "BV" ]
      else s

let pp_print_logic fmt l = Format.pp_print_string fmt (string_of_logic l)
