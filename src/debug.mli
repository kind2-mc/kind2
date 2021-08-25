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

(** Debug ouput, controlled by {!Flags}. *)


(** Types of debug functions *)
type 'a t = ('a, Format.formatter, unit) format -> 'a

(** Set the formatter for debugging *)
val set_formatter : Format.formatter -> unit

(** Set all debug flags based on input list *)
val set_dflags : string list -> unit

(** {3 Available debug functions } *)

val certif : 'a t
val event : 'a t
val extract : 'a t
val fec : 'a t
val invgencand : 'a t
val kind2 : 'a t
val ltree : 'a t
val messaging : 'a t
val parse : 'a t
val qe : 'a t
val qedetailed : 'a t
val simplify : 'a t
val smt : 'a t
val smtexpr : 'a t
val transsys : 'a t
val c2i : 'a t
val ic3 : 'a t
val compress : 'a t
val native : 'a t
val realiz : 'a t

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

