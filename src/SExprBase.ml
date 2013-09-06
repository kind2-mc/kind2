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

(* S-Expressions 
   
   Code adapted from the OCaml sexplib, which is part of the
   ocaml-core alternative standard library for OCaml.

   Most of the sexplib in the ocaml-core library was written by:
   
   Markus Mottl          <markus.mottl@gmail.com>
   
   This work in turn is derived from the library "Tywith", version
   0.45.  The library "Tywith" was written and is distributed by:
   
   Martin Sandin         <msandin@hotmail.com>

*)

open Lib

(* Signature of an S-expression atom as input for the functor {!Make} *)
module type SExprAtom = sig 
  type t 
  val pp_print_atom : Format.formatter -> t -> unit 
end
    
module type S = 
sig
  type atom
  type t = Atom of atom | List of t list
  val pp_print_sexpr : Format.formatter -> t -> unit
  val pp_print_sexpr_list : Format.formatter -> t list -> unit 
  val print_sexpr : t -> unit
  val string_of_sexpr : t -> string
end

(* Functor to make S-expressions of atoms of type [atom] *)
module Make = functor (Atom : SExprAtom) -> struct 

  (* Atom from the input module *)
  type atom = Atom.t

      
  (* Type of S-expressions: either an atom or a list of S-expressions *)
  type t = Atom of atom | List of t list


  (* Pretty-print an S-expression *)
  let rec pp_print_sexpr ppf = function 
    | Atom s -> Atom.pp_print_atom ppf s
    | List l -> pp_print_sexpr_list ppf l
      
  (* Pretty-print a list of S-expressions in parentheses *)
  and pp_print_sexpr_list ppf l = 
    Format.pp_open_hvbox ppf 1;
    Format.pp_print_string ppf "(";
    pp_print_sexpr_list' ppf l;
    Format.pp_print_string ppf ")";
    Format.pp_close_box ppf ()
      
  (* Pretty-print a list of S-expressions without parentheses *)
  and pp_print_sexpr_list' ppf = function 
    | [] -> ()
    | e :: [] -> pp_print_sexpr ppf e
    | e :: tl -> 
      pp_print_sexpr ppf e; 
      Format.pp_print_space ppf ();
      pp_print_sexpr_list' ppf tl
	
  (* Pretty-print an S-expression to the standard formatter *)
  let print_sexpr = pp_print_sexpr Format.std_formatter

  (* Return a string representation of an S-Expression *)
  let string_of_sexpr s = 
    string_of_t pp_print_sexpr s      

end

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
