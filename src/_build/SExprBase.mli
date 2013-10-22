(*
This file is part of the Kind verifier

* Copyright (c) 2007-2012 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(** S-Expressions 

    This module defines S-expressions over arbitrary atoms. Use the
    functor {!Make} to instantiate the type to a concrete type, see
    {!StringSExpr}.

    @author Christoph Sticksel 
    
    (Incorporating code from the OCaml sexplib, which is part of the
    OCaml Core alternative standard library)
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
