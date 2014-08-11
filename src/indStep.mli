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

(** k-inductive step procedure 

    @author Christoph Sticksel
*)

(** SMT Solver used for the inductive step *)
module S : SolverMethods.S

(** Inductive step for given [k]

    Assume: Solver context contains 
    - transition relation T[x_0,x_1] ... T[x_k-1,x_k], 
    - Invariants C[x_0] ... C[x_k]
    - properties in [props_unknown] P[x_0] ... P[x_k]
    
    Extend this solver context to k+1, and check which properties in
    [props_unknown] are k-inductive. 
    
    Return a pair of lists, where the first list contains properties
    that are k-inductive, and the second list properties that are not
    k-inductive. *)
val ind_step : S.t -> TransSys.t -> (string * Term.t) list -> (string * Term.t) list -> Numeral.t -> (string * Term.t) list * (string * Term.t) list


(** Entry point *)
val main : TransSys.t -> unit

(** Cleanup before exit *)
val on_exit : TransSys.t option -> unit


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
