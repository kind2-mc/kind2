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
