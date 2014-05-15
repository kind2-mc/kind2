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
open Genlex

(***************************)
(* parser definition      
 * We use Genlex to do the tokenizing 
 * and camlp4 to do the parsing
 * *)
(***************************)

let lexer = make_lexer [","; "true"; "false"]

(* Parse one line in CSV file *)
let rec parse_stream = parser

    [< 'Ident name; 'Kwd "," ; sequence = parse_sequence >] ->

  try
    
    (* Find the state variable "name" *) 
    StateVar.state_var_of_string (name, []), sequence
    
  with Not_found ->
    
    Event.log
      `Interpreter
      Event.L_fatal
      "Cannot find state variable: %s\n" 
      name;
    
    failwith (Format.sprintf "Cannot find state variable: %s" name)
      
(* Match the element type of the sequence with int, float and bool *)
and parse_sequence = parser
    
  | [< 'Int value; 
       int_sequence = parse_int_sequence [Term.mk_num_of_int value] >] ->  

  int_sequence

         (* TODO: parse this as a rational number with numerator and denominator 
                |[<'Float value;
                    float_sequence = parse_float_sequence  [Term.mk_dec_of_float value] >] ->  float_sequence
*)

  | [< 'Kwd "true"; 
       bool_sequence = parse_bool_sequence [Term.t_true] >] -> 

  bool_sequence


  | [< 'Kwd "false"; 
       bool_sequence = parse_bool_sequence [Term.t_false] >] -> 
  
  bool_sequence


and parse_int_sequence l = parser

  | [< 'Kwd ","; 
       'Int value; 
       int_sequence = parse_int_sequence
                        ((Term.mk_num_of_int value) :: l) >] -> 

    int_sequence

  | [< >] -> List.rev l

(*                              
  and parse_float_sequence l = parser
                |[<'Kwd "," ;'Float value;  float_sequence = parse_float_sequence ((Term.mk_dec_of_float value)::l)>] -> float_sequence
                |[<>] -> List.rev l
*)                              

and parse_bool_sequence l  = parser

  | [< 'Kwd ","; b = parse_bool_sequence_aux l >] -> b

  | [< >] -> List.rev l
                                
and parse_bool_sequence_aux l = parser

  |[< 'Kwd "true"; 
      bool_sequence = parse_bool_sequence (Term.t_true :: l) >] -> 

    bool_sequence

  | [< 'Kwd "false"; 
       bool_sequence = parse_bool_sequence (Term.t_false :: l) >] -> 

    bool_sequence

let parse s = 
  
  parse_stream (lexer (Stream.of_string s))

(*
let implode l =
  let s = String.create (List.length l) in
  let rec f n = function
    | x :: xs -> s.[n] <- x; f (n + 1) xs
    | [] -> s
  in f 0 l;;

        (* convert list of chars to string *)
let remove_whitespaces s = 
        let ch_list = [] in
        String.iter 
                ((fun ch) -> 
                        let _ = match ch with
                | ' ' | '\n' | '\r' | '\t' -> ch_list
                |_ -> ch::ch_list) s;;

*)

(*Read in a csv file*)
let read_file filename = 
  let chan = open_in filename in
  let rec parse_chan acc  = 
    try
      let line = input_line chan in
      parse_chan ((parse line)::acc)
    with End_of_file ->
      close_in chan; 
      acc
  in
  
  parse_chan []




(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
