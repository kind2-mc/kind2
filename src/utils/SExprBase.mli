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

(** S-Expressions 

    This module defines S-expressions over arbitrary atoms. Use the
    functor {!Make} to instantiate the type to a concrete type, see
    {!HStringSExpr}.

    (Incorporating code from the OCaml sexplib, which is part of the
    OCaml Core alternative standard library)

    @author Christoph Sticksel
*)

(** {1 Functorized interface} *)

(** Signature of an S-expression atom as input for the functor {!Make} *)
module type SExprAtom = sig 
  type t 
  val pp_print_atom : Format.formatter -> t -> unit 
end
  
(** Output signature of the functor {!Make} *)
module type S = 
sig

  (** Atom in an S-expression *)
  type atom

  (** S-expression is either an atom or a list of S-expressions *)
  type t = Atom of atom | List of t list

  (** Pretty-print an S-expression *)
  val pp_print_sexpr : Format.formatter -> t -> unit

  (** Pretty-print a list of S-expressions enclosed in parentheses *)
  val pp_print_sexpr_list : Format.formatter -> t list -> unit

  (** Pretty-print an S-expression to the standard formatter *)
  val print_sexpr : t -> unit

  (** Pretty-print an S-expression *)
  val pp_print_sexpr_indent : int -> Format.formatter -> t -> unit
  val pp_print_sexpr_indent_compact : int -> Format.formatter -> t -> unit

  (** Return a string representation of an S-Expression *)
  val string_of_sexpr : t -> string

end
  
(** Functor to make S-expressions of atoms of type [atom] *)
module Make : functor (Atom: SExprAtom) -> S with type atom = Atom.t
  

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
