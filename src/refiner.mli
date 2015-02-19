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


open Lib

type abstraction = string list list

(** Returns the concrete subsystems of a system. *)
val concretes_of_abstraction:
  TransSys.t -> string list list

(** Returns the concrete subsystems of a system with respect to an
    abstraction. *)
val concretes_of_forced_abstraction:
  TransSys.t -> abstraction -> string list list

(** Pretty prints an abstraction. *)
val pp_print_abstraction:
  Format.formatter -> abstraction -> unit

(** Pretty prints the abstracted subsystems of a system. *)
val pp_print_abstracted:
  Format.formatter -> TransSys.t -> unit

(** Pretty prints the concrete subsystems of a system. *)
val pp_print_concrete:
  Format.formatter -> TransSys.t -> unit

(** The first abstraction to start with. *)
val set_first_abstraction: TransSys.t -> unit

(** Sets the system's abstraction to abstract nothing. *)
val set_no_abstraction: TransSys.t -> unit

(** Looks for a system to refine. *)
val refine: TransSys.t -> abstraction option

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
