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

(** Literals 

    A literal is just a term, we do not check if it is atomic or even
    if the term is Boolean. See {!Clause} and {!CNF}.

    @author Christoph Sticksel *)

(** A literal *)
type t = Term.t

(** Convert a term to a literal *)
val of_term : Term.t -> t

(** Convert a literal to a term *)
val to_term : t -> Term.t

(** Total ordering on literals *)
val compare : t -> t -> int

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
