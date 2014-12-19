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

(** Generates candidate terms for a transition system, and its
    subsystems if the flags require it. The first parameter is a flag
    for two state candidate terms generation. The result features the
    number of candidate terms generated.
    {b These sets do NOT contain [true] and [false].} *)
val generate_candidate_terms :
  bool -> TransSys.t -> (TransSys.t * Term.TermSet.t) list * int

(** Generates implication graphs for a transition system, and its
    subsystems if the flags require it. The first parameter is a flag
    for two state candidate terms generation. The result features the
    number of candidate terms generated. *)
val generate_graphs :
  bool -> TransSys.t -> (TransSys.t * ImplicationGraph.t * int) list * int
  
(** Creates a graph for a transition system using the specified list
    of invariants. *)
val create_graph : TransSys.t -> Term.TermSet.t -> ImplicationGraph.t

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

