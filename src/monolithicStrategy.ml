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

module A = Analysis
module S = SubSystem

let next_analysis ({ S.scope } as system) = function 

(* First analysis *)
| [] -> Some {

  (* Analyze top system *) 
  A.top = scope ; 

  (* Implementations for all systems *)
  A.abstraction_map = [
    S.all_subsystems system |> List.map (fun { scope } -> (scope, false))
  ] ;

  (* No assumptions *)
  A.assumptions = []
}

(* One analysis only, terminate after first analysis *)
| _ -> None

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
