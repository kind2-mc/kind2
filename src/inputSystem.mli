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

(** Delegate to concrete functions for input formats 

    All functionality outside this module should be agnostic of the
    input format, with the exception of modules specialized to a
    particular input. Only here we distinguish the actual input
    format and delegate to the respective functions.

    @author Christoph Sticksel *)

type _ t

(** Read input from file *)
val read_input_lustre : string -> LustreNode.t t


(** Return the next system to analyze and the systems to abstract *)
val next_analysis_of_strategy : 'a t -> Analysis.result list -> Analysis.param option


(** Return a transition system for an analysis run *)
val trans_sys_of_analysis : 'a t -> Analysis.param -> TransSys.t * 'a t

(** Output a path in the input system *)
val pp_print_path_pt : _ t -> TransSys.t -> bool -> Format.formatter -> Model.path -> unit 

(** Output a path in the input system *)
val pp_print_path_xml : _ t -> TransSys.t -> bool -> Format.formatter -> Model.path -> unit 

val slice_to_abstraction_and_term : 'a t -> Analysis.param -> TransSys.t -> Term.t -> 'a t

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
