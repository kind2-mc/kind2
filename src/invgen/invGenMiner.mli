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

(** Module generating candidate terms for invariant generation. *)
module type CandGen = sig
  (** Generates sets of candidate terms from a transition system, and its
  subsystems if the second flag require it. First flag is for two-state. *)
  val mine : bool -> bool -> TransSys.t -> (TransSys.t * Term.TermSet.t) list
end

(** Bool candidate term miner. *)
module Bool : CandGen

(** Integer candidate term miner. *)
module Int : CandGen

(** Real candidate term miner. *)
module Real : CandGen

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
