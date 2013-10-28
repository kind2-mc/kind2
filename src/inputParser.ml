(*
This file is part of the Kind verifier

* Copyright (c) 2007-2013 by the Board of Trustees of the University of Iowa, 
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
open Lib
open Genlex

(***************************)
(* parser definition      
 * We use Genlex to do the tokenizing 
 * and camlp4 to do the parsing
 * *)
(***************************)

let lexer = make_lexer [","; "true"; "false"];;

(*Parse one line in excel file *)
let rec parse_stream = parser

  [< 'Ident name; 'Kwd "," ; sequence = parse_sequence>] ->
    try
      (*Find the state variable "name"*) 
      StateVar.state_var_of_original_name name, sequence
    with Not_found ->
      Event.log `Interpreter Event.L_fatal "Cannot find state variable: %s\n" name;
      failwith (Format.sprintf "Cannot find state variable: %s" name)
            
(*match the element type of the sequence with int, float and bool*)						
  and parse_sequence = parser
        |[< 'Int value; 
            int_sequence = parse_int_sequence [Term.mk_num_of_int value] >] ->  int_sequence
		|[<'Float value;
		    float_sequence = parse_float_sequence  [Term.mk_dec_of_float value] >] ->  float_sequence
		|[<'Kwd "true";  bool_sequence = parse_bool_sequence [ Term.t_true] >]  -> bool_sequence
		|[<'Kwd "false"; bool_sequence = parse_bool_sequence [Term.t_false] >] ->  bool_sequence

  and parse_int_sequence l = parser
		|[<'Kwd "," ;'Int value; int_sequence = parse_int_sequence ((Term.mk_num_of_int value)::l) >] -> int_sequence
		|[<>] -> List.rev l
				
  and parse_float_sequence l = parser
		|[<'Kwd "," ;'Float value;  float_sequence = parse_float_sequence ((Term.mk_dec_of_float value)::l)>] -> float_sequence
		|[<>] -> List.rev l
				
  and parse_bool_sequence l  = parser
		|[<'Kwd "," ; b = parse_bool_sequence_aux l >] -> b
		|[<>] -> List.rev l
				
  and parse_bool_sequence_aux l = parser
		|[<'Kwd "true"; bool_sequence = parse_bool_sequence (Term.t_true::l) >] -> bool_sequence
		|[<'Kwd "false"; bool_sequence = parse_bool_sequence (Term.t_false::l) >] -> bool_sequence

let parse (s:string) = 
     parse_stream(lexer(Stream.of_string s))

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


















