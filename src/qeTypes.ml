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

(* A term, consisting of a list of a coefficient variable pairs

   The dummy variable o is used for a constant *)
type term = (int * string) list

(* A relation symbol *)
type relation = 
    EQ
  | LT
  | LTE
  | GT
  | GTE
      
(* A formula *)
type formula =
    Rel of (relation * term * term)
  | And of (formula * formula)
  | Or of (formula * formula)
  | Not of (formula)


(* Print a pair of coefficient and variable into the given
   pretty-printer *)
let pp_print_atom ppf = function 

  (* o is the dummy variable, print constant *)
  | (c, "o") ->
    
    Format.pp_print_int ppf c
      
  (* Print as coefficient and constant as product in a horizontal
     box *)
  | (c, x) ->
    
    Format.pp_open_hbox ppf ();
    Format.pp_print_string ppf "(*";
    Format.pp_print_space ppf ();
    Format.pp_print_int ppf c;
    Format.pp_print_space ppf ();
    Format.pp_print_string ppf x;
    Format.pp_print_string ppf ")";
    Format.pp_close_box ppf ()


(* Print a list of atoms into the given pretty-printer *)
let rec pp_print_term' ppf = function 

  | [] -> ()

  (* Do not print a space after the final element in the list *)
  | t :: [] -> pp_print_atom ppf t

  (* Print a space after every inner element in the list *)
  | t :: tl -> 
    pp_print_atom ppf t;
    Format.pp_print_space ppf ();
    pp_print_term' ppf tl


(* Print a term into the given pretty-printer *)
let pp_print_term ppf = function
  
  (* Print a constant zero for the empty term *)
  | [] -> Format.pp_print_int ppf 0

  (* Print coefficient variable pair only for term with one atom *)
  | t :: [] -> pp_print_atom ppf t

  | t -> 

    (* Print term as a sum of variable coefficient pairs *)
    Format.pp_open_hvbox ppf 2;
    Format.pp_print_string ppf "(+";
    Format.pp_print_space ppf ();
    pp_print_term' ppf t;
    Format.pp_print_string ppf ")";
    Format.pp_close_box ppf ()
      

(* Print a relation into the given pretty-printer *)
let pp_print_relation ppf = function 

  (* Print a string representation of the relation *)
  | EQ -> Format.pp_print_string ppf "="
  | LT -> Format.pp_print_string ppf "<"
  | LTE -> Format.pp_print_string ppf "<="
  | GT -> Format.pp_print_string ppf ">"
  | GTE -> Format.pp_print_string ppf ">="

(* Print a formula into the given pretty-printer *)
let rec pp_print_formula ppf = function 

  | Rel (r, s, t) -> 

    (* Open a horizontal-vertical box and print the relation *)
    Format.pp_open_hvbox ppf 2;
    Format.pp_print_string ppf "(";
    pp_print_relation ppf r;
    Format.pp_print_space ppf ();
    pp_print_term ppf s;
    Format.pp_print_space ppf ();
    pp_print_term ppf t;
    Format.pp_print_string ppf ")";
    Format.pp_close_box ppf ()
    
  (* Open a horizontal-vertical box and print the conjunction *)
  | And (f, g) -> 
    Format.pp_open_hvbox ppf 2;
    Format.pp_print_string ppf "(";
    Format.pp_print_string ppf "and";
    Format.pp_print_space ppf ();
    pp_print_formula ppf f;
    Format.pp_print_space ppf ();
    pp_print_formula ppf g;
    Format.pp_print_string ppf ")";
    Format.pp_close_box ppf ()

  (* Open a horizontal-vertical box and print the disjunction *)
  | Or (f, g) -> 
    Format.pp_open_hvbox ppf 2;
    Format.pp_print_string ppf "(";
    Format.pp_print_string ppf "or";
    Format.pp_print_space ppf ();
    pp_print_formula ppf f;
    Format.pp_print_space ppf ();
    pp_print_formula ppf g;
    Format.pp_print_string ppf ")";
    Format.pp_close_box ppf ()
    
  (* Open a horizontal-vertical box and print the negation *)
  | Not f -> 
    Format.pp_open_hvbox ppf 2;
    Format.pp_print_string ppf "(";
    Format.pp_print_string ppf "not";
    Format.pp_print_space ppf ();
    pp_print_formula ppf f;
    Format.pp_print_string ppf ")";
    Format.pp_close_box ppf ()
      
(* Return a string representation of the formula *)
let formula_to_string f = 
  
  (* Create a buffer to print into *)
  let buf = Buffer.create 100 in

  (* Create a pretty-printer into the buffer *)
  let ppf = Format.formatter_of_buffer buf in

  (* Print the formula into the buffer *)
  pp_print_formula ppf f;

  (* Return the contents of the buffer *)
  Buffer.contents buf

let test () = 
  
  let o1 = (1, "o") in
  let x2 = (2, "x") in
  let y3 = (3, "y") in
  let z4 = (4, "z") in

  let f1 = Rel (EQ, [x2; y3], [o1]) in
  let f2 = Rel (LT, [x2; y3], [o1]) in
  let f3 = Rel (LTE, [x2; y3], [o1]) in
  let f4 = Rel (GT, [x2; y3], [o1]) in
  let f5 = Rel (GTE, [x2; y3], [o1]) in
  let f6 = Not f1 in
  let f7 = And (f1, f2) in
  let f8 = Or (f4, f4) in
  
  pp_print_formula Format.std_formatter f1;
  Format.pp_print_newline Format.std_formatter ();
  pp_print_formula Format.std_formatter f2;  
  Format.pp_print_newline Format.std_formatter ();
  pp_print_formula Format.std_formatter f3;  
  Format.pp_print_newline Format.std_formatter ();
  pp_print_formula Format.std_formatter f4;  
  Format.pp_print_newline Format.std_formatter ();
  pp_print_formula Format.std_formatter f5;  
  Format.pp_print_newline Format.std_formatter ();
  pp_print_formula Format.std_formatter f6;  
  Format.pp_print_newline Format.std_formatter ();
  pp_print_formula Format.std_formatter f7;  
  Format.pp_print_newline Format.std_formatter ();
  pp_print_formula Format.std_formatter f8;
  Format.pp_print_newline Format.std_formatter ()

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
