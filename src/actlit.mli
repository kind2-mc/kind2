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

open Lib

(* Removed because too unsafe.

   (** Returns an actlit built from a string. Beware of name
      collisions. *)
   val actlit_of_string: string -> UfSymbol.t

   (** Creates a positive actlit as a bool UF constant. *)
   val generate_actlit: Term.t -> UfSymbol.t

   (** Creates a negative actlit as a bool UF constant. *)
   val generate_negative_actlit: Term.t -> UfSymbol.t
*)

(** Creates a fresh actlit as a bool UF constant. *)
val fresh_actlit: unit -> UfSymbol.t

(** Returns the term corresponding to the input actlit. *)
val term_of_actlit: UfSymbol.t -> Term.t

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

