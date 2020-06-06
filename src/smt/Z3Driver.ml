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

(* Configuration for Z3 *)
let cmd_line 
    logic
    produce_assignments
    produce_proofs
    produce_cores
    produce_interpolants = 

  (* Path and name of Z3 executable *)
  let z3_bin = Flags.Smt.z3_bin () in
  let base_cmd = [| z3_bin; "-smt2"; "-in" |] in
  if Flags.timeout_wall () > 0. then (
    let timeout =
      let timeout_val = Stat.remaining_timeout () +. 1.0 in
      Format.sprintf "-T:%.0f" (timeout_val |> ceil)
    in
    Array.append base_cmd [| timeout |]
  )
  else base_cmd

(* Command to limit check-sat in Z3 to run for the given numer of ms
   at most *)
let check_sat_limited_cmd ms = 
  Format.sprintf "(check-sat-using (try-for smt %d))" ms


let headers () = ["(set-option :interactive-mode true)"]


let string_of_logic l =
  let open TermLib in
  let open TermLib.FeatureSet in
  match l with
  | `Inferred l when mem IA l && mem RA l ->
    if mem Q l then "AUFLIRA"
    else "QF_AUFLIRA"
  | _ -> GenericSMTLIBDriver.string_of_logic l
    
let pp_print_logic fmt l = Format.pp_print_string fmt (string_of_logic l)
