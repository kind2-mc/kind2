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

(* Configuration for MathSAT5 *)
let cmd_line 
    logic
    produce_assignments
    produce_proofs
    produce_cores
    produce_interpolants = 
  
  (* Path and name of MathSAT5 executable *)
  let mathsat5_bin = Flags.mathsat5_bin () in
  [| mathsat5_bin; "-input=smt2" |]


let check_sat_limited_cmd _ = 
  failwith "check-sat with timeout not implemented for MathSAT5"


let check_sat_assuming_cmd () = "check-sat-assumptions"
  

let check_sat_assuming_supported () = false


let check_sat_assumptions_cmd () = "(check-sat-assumptions (%a))"


