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
    _ (* logic *)
    timeout
    _ (* produce_models *) 
    _ (* produce_proofs *)
    _ (* produce_unsat_cores *)
    _ (* produce_unsat_assumptions *)
    _ (* minimize_cores *) 
    _ (* produce_interpolants *) = 

  (* Path and name of Z3 executable *)
  let z3_bin = Flags.Smt.z3_bin () in

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

  let base_cmd = [| z3_bin; "-smt2"; "-in" |] in
  match timeout with
  | None -> base_cmd
  | Some timeout ->
    let timeout = 
      Format.sprintf "-T:%.0f" (timeout |> ceil)
    in
    Array.append base_cmd [| timeout |]

(* Command to limit check-sat in Z3 to run for the given numer of ms
   at most *)
let check_sat_limited_cmd ms = 
  Format.sprintf "(check-sat-using (try-for smt %d))" ms


let headers minimize_cores =
  (* Core minimization only supported by Z3 for now *)
  (if minimize_cores then ["(set-option :smt.core.minimize true)"] else [])

let string_of_logic l =
  let open TermLib in
  let open TermLib.FeatureSet in
  let l' =
    match l with
    | `Inferred l when mem IA l && mem RA l -> (
      (* Accepted: QF_LIRA, QF_NIRA, QF_UFNIRA, QF_AUFLIRA, QF_AUFNIRA, UFNIRA, AUFLIRA, AUFNIRA
         Unsupported: QF_UFLIRA, QF_ALIRA, QF_ANIRA, LIRA, NIRA, UFLIRA, ALIRA, ANIRA *)
      if (mem NA l) then (
        let l = if not (Flags.Arrays.smt()) then remove A l else l in
        (* QF_NIRA, QF_UFNIRA, QF_AUFNIRA, UFNIRA, AUFNIRA, ~QF_ANIRA, ~NIRA, ~ANIRA *)
        if (mem A l || mem Q l) then `Inferred (add UF l)
        else `Inferred l
      )
      else 
        (* QF_LIRA, ~QF_UFLIRA, QF_AUFLIRA, ~UFLIRA, AUFLIRA, ~QF_ALIRA, ~LIRA, ~ALIRA *)
        if (mem UF l) then `Inferred (add A l)
        else if (mem A l) then `Inferred (add UF l)
        else if (mem Q l) then `Inferred (add UF (add A l))
        else `Inferred l
    )
    | `Inferred l when not (Flags.Arrays.smt()) -> `Inferred (remove A l)
    | _ -> l
  in
  TermLib.string_of_logic ~enforce_logic:true l'
    
let pp_print_logic fmt l = Format.pp_print_string fmt (string_of_logic l)
