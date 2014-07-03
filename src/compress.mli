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

(** Path compression for k-induction 

    @author Christoph Sticksel *)

(** Initialize compression 

    The first argument is the function to declare an uninterpreted
    function symbol in a solver instance, the second the transition
    system. *)
val init : (UfSymbol.t -> unit) -> TransSys.t -> unit

val incr_k : unit -> unit 

(** Given an inductive counterexample return a list of terms to force
    those states on the path to be different that are equivalent under
    some simulation relations. *)
val check_and_block : (UfSymbol.t -> unit) -> TransSys.t -> (StateVar.t * Term.t list) list -> Term.t list


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
