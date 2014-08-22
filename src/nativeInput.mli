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

(** Parse a file in native input format into a transition system 

    @author Christoph Sticksel
*)

(** Parse from the channel *)
val of_channel : in_channel -> TransSys.t

(** Parse from the file *)
val of_file : string -> TransSys.t

val pp_print_path_pt : Format.formatter -> (StateVar.t * Term.t list) list -> unit

val pp_print_path_xml : Format.formatter -> (StateVar.t * Term.t list) list -> unit


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
