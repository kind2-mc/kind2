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

(* Translates the hash of a term into a string .*)
let string_of_term term = string_of_int (Term.tag term)

(* Returns an actlit built from a string. Beware of name
   collisions. *)
let actlit_of_string string =
  UfSymbol.mk_uf_symbol string [] (Type.mk_bool ())

(* Creates a positive actlit as a UF. *)
let generate_actlit term =
  String.concat "_" [ "actlit" ; string_of_term term ]
  |> actlit_of_string

(* Creates a negative actlit as a UF. *)
let generate_negative_actlit term =
  String.concat "_" [ "actlit" ; "negative" ; string_of_term term ]
  |> actlit_of_string

let i = ref 0

(* Creates a fresh actlit as a bool UF constant. *)
let fresh_actlit () =
  let string =
    String.concat
      "_" [ "fresh" ; "actlit" ; string_of_int !i ]
  in
  i := !i + 1 ;
  actlit_of_string string

(* Returns the term corresponding to the input actlit. *)
let term_of_actlit actlit = Term.mk_uf actlit []

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

