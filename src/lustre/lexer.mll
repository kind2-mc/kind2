{
(* This file is part of the Kind verifier

 * Copyright (c) 2007-2009 by the Board of Trustees of the University of Iowa, 
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


open Parser

(* Pretty-print an array of integers *)
let rec pp_print_int_array i ppf a = 

  if i = 0 then 
    Format.fprintf ppf "@[<hv 3>[|";
  
  if i >= Array.length a then

    Format.fprintf ppf "|]@]"

  else

    ( 

      Format.fprintf ppf "%d" a.(i);

      if i+2 = Array.length a then 
	Format.fprintf ppf ";@ ";
      
      pp_print_int_array (succ i) ppf a
    
    )

(* Pretty-print a position *)
let pp_print_position ppf 
    { Lexing.pos_fname;
      Lexing.pos_lnum;
      Lexing.pos_bol;
      Lexing.pos_cnum } =

  Format.fprintf ppf 
    "@[<hv 2>{ pos_fname : %s;@ \
     pos_lnum : %d;@ \
     pos_bol : %d;@ \
     pos_cnum : %d; }@]"
    pos_fname
    pos_lnum
    pos_bol
    pos_cnum


(* Pretty-print a lexing buffer *)
let pp_print_lexbuf ppf     
  { Lexing.lex_buffer; 
    Lexing.lex_buffer_len; 
    Lexing.lex_abs_pos; 
    Lexing.lex_start_pos; 
    Lexing.lex_curr_pos; 
    Lexing.lex_last_pos;
    Lexing.lex_last_action;
    Lexing.lex_eof_reached;
    Lexing.lex_mem;
    Lexing.lex_start_p;
    Lexing.lex_curr_p } =

  Format.fprintf ppf 
    "@[<hv 2>{ lex_buffer : %s;@ \
     lex_buffer_len : %d;@ \
     lex_abs_pos : %d;@ \
     lex_start_pos : %d;@ \
     lex_curr_pos : %d;@ \
     lex_last_pos : %d;@ \
     lex_last_action : %d;@ \
     lex_eof_reached : %B;@ \
     lex_mem : %a;@ \
     lex_start_p : %a;@ \
     lex_curr_p : %a;@]"
    lex_buffer
    lex_buffer_len
    lex_abs_pos
    lex_start_pos
    lex_curr_pos
    lex_last_pos
    lex_last_action
    lex_eof_reached
    (pp_print_int_array 0) lex_mem
    pp_print_position lex_start_p
    pp_print_position lex_curr_p

 

(* A stack of pairs of channels and lexing buffers to handle included files 

   The channel at the head of the list is the current channel to read
   from, the lexing buffer is the one to return to once all characters
   have been read from the channel.

   Have only one lexing buffer and push a shallow copy of it to this
   stack when switching to an included file. At the end of the
   included file, restore the state of the lexing buffer from its
   shallow copy.

   When an eof is read from the lexing buffer, do not terminate but
   call pop_channel_of_lexbuf continue. If this raises the exception
   End_of_file, all input files have been read.
   
*)
let lexbuf_stack = ref []


(* Initialize the stack *)
let lexbuf_init channel = 

  (* A dummy lexing buffer to return to *)
  let lexbuf = Lexing.from_channel channel in

  (* Initialize the stack *)
  lexbuf_stack := [(channel, lexbuf)]


(* Switch to a new channel *)
let lexbuf_switch_to_channel lexbuf channel = 

  (* Add channel and shallow copy of the previous lexing buffer to the top of the stack *)
  lexbuf_stack := 
    (channel, { lexbuf with Lexing.lex_buffer = String.copy lexbuf.Lexing.lex_buffer}) :: !lexbuf_stack;

  (*
    Format.printf "Pushing buffer to stack@\n%a@." pp_print_lexbuf lexbuf; 
  *)

  (* Flush lexing buffer *)
  lexbuf.Lexing.lex_curr_pos <- 0;
  lexbuf.Lexing.lex_abs_pos <- 0;
  lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_cnum = 0};
  lexbuf.Lexing.lex_buffer_len <- 0


(* Pop lexing buffer from the stack an restore state of the lexing buffer *)
let pop_channel_of_lexbuf lexbuf =

  match !lexbuf_stack with 

    (* Exception if last channel has been popped off the stack *)
    | [] -> raise End_of_file

    (* Take channel and lexing buffer from top of stack *)
    | (ch, prev_lexbuf) :: tl -> 


      (* Close channel *)
      close_in ch; 

      (* Pop off stack *)
      lexbuf_stack := tl; 

      (* Restore state of the lexing buffer *)
      lexbuf.Lexing.lex_curr_pos <- prev_lexbuf.Lexing.lex_curr_pos;
      lexbuf.Lexing.lex_abs_pos <- prev_lexbuf.Lexing.lex_abs_pos;
      lexbuf.Lexing.lex_curr_p <- prev_lexbuf.Lexing.lex_curr_p;
      lexbuf.Lexing.lex_buffer <- prev_lexbuf.Lexing.lex_buffer;
      lexbuf.Lexing.lex_buffer_len <- prev_lexbuf.Lexing.lex_buffer_len

(*
      Format.printf "Restoring buffer@\n%a@." pp_print_lexbuf prev_lexbuf;
      Format.printf "Resulting buffer@\n%a@." pp_print_lexbuf lexbuf
*)


(* Function to read from the channel at the top of the stack *)
let read_from_lexbuf_stack buf n = 

  match !lexbuf_stack with 
    | [] -> 0
    | (ch, _) :: _ -> input ch buf 0 n


(* Create and populate a hashtable *)
let mk_hashtbl size init =
  let tbl = Hashtbl.create size in
  List.iter
    (function (k, v) -> Hashtbl.add tbl k v)
    init;
  tbl
  
(* Use hash tables instead of rule matches to keep numer of transition
   of lexer small *)

(* Hashtable of keywords *)
let keyword_table = 
  mk_hashtbl 
    43
    [

      (* Types *)
      ("type", TYPE);
      ("int", INT);
      ("real", REAL);
      ("bool", BOOL);
      ("subrange", SUBRANGE);
      ("of", OF);
      ("array", ARRAY);

      (* Constant declaration *)
      ("const", CONST);
      
      (* Node declaration *)
      ("node", NODE);
      ("function", FUNCTION);
      ("returns", RETURNS);
      ("var", VAR);
      ("let", LET);
      ("tel", TEL);
      
      (* Assertion *)
      ("assert", ASSERT);
      
      (* Boolean operators *)
      ("true", TRUE);
      ("false", FALSE);
      ("not", NOT);
      ("and", AND);
      ("xor", XOR);
      ("or", OR);
      ("if", IF);
      ("then", THEN);
      ("else", ELSE);
      ("=>", IMPL);
      
      (* Relations *)
      ("<=", LTE);
      (">=", GTE);
      ("<", LT);
      (">", GT);
      ("<>", NEQ);
      
      (* Arithmetic operators *)
      ("-", MINUS);
      ("+", PLUS);
      ("/", DIV);
      ("*", MULT);
      ("div", INTDIV);
      ("mod", MOD);
      
      (* Clock operators *)
      ("when", WHEN);
      ("current", CURRENT);
      ("condact", CONDACT);
      
      (* Temporal operators *)
      ("pre", PRE);
      ("fby", FBY);
      ("->",  ARROW)
      
    ]
    
}


(* Identifier *)
let id = ['a'-'z' 'A'-'Z' '_' '~'] ['a'-'z' 'A'-'Z' '_' '~' '0'-'9']*
  
(* Keep these separated from alphabetic characters, otherwise a->b would be one token *)
let printable = ['+' '-' '*' '/' '>' '<' '=' ]+

(* Floating point decimal *)
let decimal = ['0'-'9']+ '.' ['0'-'9']+ ('E' ('+'|'-')? ['0'-'9']+)?

(* Integer numeral *)
let numeral = ['0'-'9']+

(* Whitespace *)
let whitespace = [' ' '\t']

(* Newline *)
let newline = '\r'* '\n'

(* Toplevel function *)
rule token = parse
(*
  (* Annotation *)
  | "--%" (id as p) 
      { try Hashtbl.find annotation_table p with 
	| Not_found -> 
	  (Format.printf "Warninng: unknown annotation %s skipped@." p; 
	   skip_to_eol lexbuf ) }

  (* Comment until end of line *)
  | "--" [^'\n'] * newline { Lexing.new_line lexbuf; token lexbuf }
*)

  (* Comment until end of line 

     Need to have the '-'* here, otherwise "---" would be matched as operator *)
  | "--" '-'* { comment lexbuf }

  (* Multi-line comment *)
  |  "/*" { skip_commented lexbuf }

  (* Include file *)
  | "include" whitespace* '\"' ([^'\"']* as p) '\"' 

      { 

	(* Open include file *)
	let include_channel = 
	  try open_in p with 
	    | Sys_error e -> 
	      failwith (Format.sprintf "Error opening include file %s: %s" p e)
	in
	
	(* New lexing buffer from include file *)
	lexbuf_switch_to_channel lexbuf include_channel;
	
	Lexing.flush_input lexbuf;

	(* Starting position in new file *)
	let zero_pos = 
	  { Lexing.pos_fname = p;
	    Lexing.pos_lnum = 1;
	    Lexing.pos_bol = 0;
	    Lexing.pos_cnum = 0 } 
	in

	(* Set new position in lexing buffer *)
	lexbuf.Lexing.lex_curr_p <- zero_pos;

	(* Continue with included file *)
	token lexbuf
	  
      }

  (* Delimiters *)
  | ';' { SEMICOLON }
  | '=' { EQUALS }
  | ':' { COLON }
  | ',' { COMMA }
  | '[' { LSQBRACKET }
  | ']' { RSQBRACKET }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '.' { DOT }
  | '^' { CARET }
  | "{" { LCURLYBRACKET }
  | "}" { RCURLYBRACKET }
  | "[|" { LARRAYBRACKET }
  | "|]" { RARRAYBRACKET }
  | '|' { PIPE }

  (* Decimal or numeral *)
  | decimal as p { DECIMAL p }
  | numeral as p { NUMERAL p } 

  (* Keyword *)
  | id as p 
      { try Hashtbl.find keyword_table p with 
	| Not_found -> (SYM p) }

  (* Symbol that is not a delimiter *)
  | printable+ as p 
      { try Hashtbl.find keyword_table p with 
	| Not_found -> failwith (Format.sprintf "Unknown operator %s" p) }

  (* Whitespace *)
  | whitespace { token lexbuf }

  (* Newline *)
  | newline { Lexing.new_line lexbuf; token lexbuf }

  (* End of file *)
  | eof 

      (* Pop previous lexing buffer form stack if at end of included file *)
      { try pop_channel_of_lexbuf lexbuf; token lexbuf with End_of_file -> EOF }

  (* Unrecognized character *)
  | _ as c 
      { failwith 
          (Format.sprintf "Unrecognized token %c (0x%X)" c (Char.code c)) }

(* Parse until end of comment, count newlines and otherwise discard
   characters *)
and skip_commented = parse 

  (* End of comment *)
  | "*/" { token lexbuf } 

  (* Count new line *)
  | newline { Lexing.new_line lexbuf; skip_commented lexbuf } 

  | eof 
      { failwith (Format.sprintf "Unterminated comment") }

  (* Ignore characters in comments *)
  | _ { skip_commented lexbuf }


(* Parse until end of line and otherwise discard characters *)
and comment = parse 

  (* Annotation *)
  | "%" (id as p) 
      { match p with 

        (* Ignore rest of line and return token *)
        | "MAIN" -> return_at_eol MAIN lexbuf

        (* Return token, continue with rest of line *)
        | "PROPERTY" -> PROPERTY

        (* Warn and ignore rest of line *)
        | _ -> (Format.printf "Warninng: unknown annotation %s skipped@." p; 
	        skip_to_eol lexbuf ) }

  (* Contract *)
  | "@" (id as p) 
      { match p with 

        (* Return token, continue with rest of line *)
        | "requires" -> REQUIRES

        (* Return token, continue with rest of line *)
        | "ensures" -> ENSURES

        (* Warn and ignore rest of line *)
        | _ -> (Format.printf "Warninng: unknown contract %s skipped@." p; 
	        skip_to_eol lexbuf ) }

  (* Count new line and resume *)
  | newline { Lexing.new_line lexbuf; token lexbuf } 

  (* Line ends at end of file *)
  | eof { token lexbuf }

  (* Ignore characters *)
  | _ { skip_to_eol lexbuf }

and skip_to_eol = parse

  (* Count new line and resume *)
  | newline { Lexing.new_line lexbuf; token lexbuf } 

  (* Line ends at end of file *)
  | eof { token lexbuf }

  (* Ignore characters *)
  | _ { skip_to_eol lexbuf }


and return_at_eol t = parse

  (* Count new line and resume *)
  | newline { Lexing.new_line lexbuf; t } 

  (* Line ends at end of file *)
  | eof { t }

  (* Ignore characters *)
  | _ { return_at_eol t lexbuf }



{

  (* Test code *)
  let main () = 
    
    (* Read all tokens and output their positions *)
    let rec aux ppf lexbuf =

      (* Read a token *)
      let token = token lexbuf in

      (* Output position and the token *)
      Format.fprintf 
        ppf 
        "%a %s" 
        pp_print_position lexbuf.Lexing.lex_start_p
        (Lexing.lexeme lexbuf);

      (* Terminate at the end of the file, otherwise continue *)
      if token = EOF then () else
        
        (Format.fprintf ppf "@,";
         aux ppf lexbuf)
         
    in
    
    (* Create lexing buffer *)
    let lexbuf = Lexing.from_function read_from_lexbuf_stack in

    (* Read from file or standard input *)
    let in_ch = 
      if Array.length Sys.argv > 1 then 
	(let fname = Sys.argv.(1) in 	

	 let zero_pos = 
	   { Lexing.pos_fname = fname;
	     Lexing.pos_lnum = 1;
	     Lexing.pos_bol = 0;
	     Lexing.pos_cnum = 0 } 
	in
	 lexbuf.Lexing.lex_curr_p <- zero_pos; 

	 open_in fname) 
      else
	stdin
    in

    (* Initialize lexing buffer with channel *)
    lexbuf_init in_ch;

    (* Output all tokens and their positions *)
    Format.printf "@[<v>%t@]@." (function ppf -> aux ppf lexbuf)

;;

main ()

}
