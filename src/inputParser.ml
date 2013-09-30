open Genlex;;
(***************************)
(* parser definition      
 * We use Genlex to do the tokenizing 
 * and camlp4 to do the parsing
 * *)
(***************************)

let lexer = make_lexer [","; "true"; "false"];;

(*Parse one line in excel file *)

let rec parse_stream = parser
        [< 'Ident name; 'Kwd "," ; sequence = parse_sequence>] ->StateVar.state_var_of_string name, sequence
and parse_sequence = parser
        | [< 'Int value;  int_sequence = parse_int_sequence [Term.mk_num_of_int value] >] ->  int_sequence
				| [<  'Float value;  float_sequence = parse_float_sequence  [Term.mk_dec_of_float value] >] ->  float_sequence
				| [<   'Kwd "true";  bool_sequence = parse_bool_sequence [ Term.t_true] >]  -> bool_sequence
				| [<   'Kwd "false"; bool_sequence = parse_bool_sequence [Term.t_false] >] ->  bool_sequence

and parse_int_sequence l = parser
				|[<   'Kwd "," ;'Int value; int_sequence = parse_int_sequence ((Term.mk_num_of_int value)::l) >] -> int_sequence
				| [<>] -> List.rev l
				
and parse_float_sequence l = parser
				|[<  'Kwd "," ;'Float value;  float_sequence = parse_float_sequence ((Term.mk_dec_of_float value)::l)>] -> float_sequence
				|[<>] -> List.rev l
and parse_bool_sequence l  = parser
				|[< 'Kwd "," ; b = parse_bool_sequence_aux l >] -> b
				|[<>] -> List.rev l
and parse_bool_sequence_aux l = parser
		    | [< 'Kwd "true"; bool_sequence = parse_bool_sequence (Term.t_true::l) >] -> bool_sequence
				| [< 'Kwd "false"; bool_sequence = parse_bool_sequence (Term.t_false::l) >] -> bool_sequence

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


















