{
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


open LustreParser

(* XML or plain text warning.

   Adrien: Relying on Event causes circular build. Factor in Lib, along with
     context warnings? *)
let print_warning fmt =
  if Flags.log_format_xml () then
    Format.printf ("@[<hov 2>\
        <Log class=\"warn\" source=\"parse\">@,\
          @[<hov>" ^^ fmt ^^ "@]\
        @;<0 -2></Log>\
      @]@.")
  else
    Format.printf ("%s @[<v>" ^^ fmt ^^ "@]@.") Lib.warning_tag

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

 

(* A stack of pairs of channels, a directory and lexing buffers to
   handle included files 

   The channel at the head of the list is the current channel to read
   from, the directory is the directory the channel is in, the lexing 
   buffer is the one to return to once all characters have been read 
   from the channel.

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
let lexbuf_init channel curdir = 

  (* A dummy lexing buffer to return to *)
  let lexbuf = Lexing.from_channel channel in

  (* Initialize the stack *)
  lexbuf_stack := [(channel, curdir, lexbuf)]


(* Switch to a new channel *)
let lexbuf_switch_to_channel lexbuf channel curdir = 

  (* Add channel and shallow copy of the previous lexing buffer to the
     top of the stack *)
  lexbuf_stack := 
    (channel, 
     curdir, 
     { lexbuf with 
         Lexing.lex_buffer = Bytes.copy lexbuf.Lexing.lex_buffer}) :: 
      !lexbuf_stack;
  
  (* Flush lexing buffer *)
  lexbuf.Lexing.lex_curr_pos <- 0;
  lexbuf.Lexing.lex_abs_pos <- 0;
  lexbuf.Lexing.lex_curr_p <- 
    { lexbuf.Lexing.lex_curr_p with Lexing.pos_cnum = 0 };
  lexbuf.Lexing.lex_buffer_len <- 0


(* Pop lexing buffer from the stack an restore state of the lexing buffer *)
let pop_channel_of_lexbuf lexbuf =

  match !lexbuf_stack with 

    (* Exception if last channel has been popped off the stack *)
    | [] -> raise End_of_file

    (* Take channel and lexing buffer from top of stack *)
    | (ch, _, prev_lexbuf) :: tl -> 


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


(* Get the directory associated with the current channel *)
let curdir_of_lexbuf_stack () = match !lexbuf_stack with 
  | [] -> Sys.getcwd ()
  | (_, curdir, _) :: _ -> curdir



(* Function to read from the channel at the top of the stack *)
let read_from_lexbuf_stack buf n = 

  match !lexbuf_stack with 
    | [] -> 0
    | (ch, _, _) :: _ -> input ch buf 0 n


(* Create and populate a hashtable *)
let mk_hashtbl init =
  let tbl = List.length init |> Hashtbl.create in
  init |> List.iter (fun (k, v) -> Hashtbl.add tbl k v) ;
  tbl
  
(* Use hash tables instead of rule matches to keep numer of transition
   of lexer small *)

(* Hashtable of keywords *)
let keyword_table = mk_hashtbl [

  (* Types *)
  ("type", TYPE) ;
  ("int", INT) ; ("real", REAL) ; ("bool", BOOL) ;
  ("subrange", SUBRANGE) ; ("of", OF) ;
  (* ("array", ARRAY) ; *)
  ("struct", STRUCT) ;
  ("enum", ENUM) ;

  (* Constant declaration *)
  ("const", CONST) ;
  
  (* Node / function declaration *)
  ("node", NODE) ; ("function", FUNCTION) ;
  ("returns", RETURNS) ;
  ("var", VAR) ;
  ("let", LET) ;
  ("tel", TEL) ;
  
  (* Assertion *)
  ("assert", ASSERT) ;

  (* Annotations. *)
  ("PROPERTY", PROPERTY) ;
  ("MAIN", MAIN) ;
  (* Contract related things. *)
  ("contract", CONTRACT) ;

  (* Boolean operators *)
  ("true", TRUE) ; ("false", FALSE) ;
  ("not", NOT) ; ("and", AND) ; ("xor", XOR) ; ("or", OR) ;
  ("if", IF) ;
  ("then", THEN) ;
  ("else", ELSE) ;
  ("with", WITH) ;
  ("div", INTDIV) ; ("mod", MOD) ;
  
  (* Clock operators *)
  ("when", WHEN) ;
  ("current", CURRENT) ;
  ("condact", CONDACT) ;
  ("activate", ACTIVATE) ;
  ("initial", INITIAL) ;
  ("default", DEFAULT) ;
  ("every", EVERY) ;
  ("merge", MERGE) ;
  
  (* Temporal operators *)
  ("pre", PRE) ; ("fby", FBY) ;
      
]
    
}


(* Identifier 

   C syntax: alphanumeric characters including the underscore, starting 
   with a letter or the underscore *)
let id = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*
  
(* Keep these separated from alphabetic characters, otherwise a->b would 
   be one token *)
let printable = ['+' '-' '*' '/' '>' '<' '=' ]+

(* Floating point decimal 

   Don't allow floats like "2." this will conflict with array slicing "2..3" *)
let decimal = ['0'-'9']+ '.' ['0'-'9']+ ('E' ('+'|'-')? ['0'-'9']+)?

(* Floating-point decimal with exponent only *)
let exponent_decimal = ['0'-'9']+ 'E' ('+'|'-')? ['0'-'9']+

(* Integer numeral *)
let numeral = ['0'-'9']+

(* Whitespace *)
let whitespace = [' ' '\t']

(* Newline *)
let newline = '\r'* '\n'

(* Toplevel function *)
rule token = parse


  (* |===| Annotations. *)

  (* Inline. *)
  | "--%" { PERCENTANNOT }
  | "--!" { BANGANNOT }
  | "--@mode" { INLINEMODE }
  | "--@require" { INLINEREQUIRE }
  | "--@ensure" { INLINEENSURE }
  | "--@const" { INLINECONST }
  | "--@var" { INLINEVAR }

  (* Parenthesis star (PS) block annotations. *)
  | "(*%" { PSPERCENTBLOCK }
  | "(*!" { PSBANGBLOCK }
  | "(*@" { PSATBLOCK }

  (* End of parenthesis star (PS). *)
  | "*)" { PSBLOCKEND }

  (* Slash star (SS) block annotations. *)
  | "/*%" { SSPERCENTBLOCK }
  | "/*!" { SSBANGBLOCK }
  | "/*@" { SSATBLOCK }

  (* End of slash star (SS). *)
  | "*/" { SSBLOCKEND }


  (* |===| Block annotation contract stuff. *)

  | "@mode" { MODE }
  | "@require" { REQUIRE }
  | "@ensure" { ENSURE }


  (* |===| Actual comments. *)

  (* Inline.
    Need to have the '-'* here, otherwise "---" would be matched 
    as operator *)
  | "--" '-'* { skip_to_eol lexbuf }

  (* Multi-line. *)
  | "/*" { skip_commented_slashstar lexbuf }
  | "(*" { skip_commented_parenstar lexbuf }


  (* |===| Include file. *)
  | "include" whitespace* '\"' ([^'\"']* as p) '\"' {

    (* Open include file *)
    let include_channel, include_curdir =
      try (
        let include_channel, include_curdir = 
          open_in (Filename.concat (curdir_of_lexbuf_stack ()) p),
          Filename.dirname p
        in

        include_channel, include_curdir
      ) with Sys_error e -> 
        Format.sprintf "Error opening include file %s: %s" p e
        |> failwith
    in
    
    (* New lexing buffer from include file *)
    lexbuf_switch_to_channel lexbuf include_channel include_curdir ;
    
    Lexing.flush_input lexbuf ;

    (* Starting position in new file *)
    let zero_pos =
      { Lexing.pos_fname = p ;
        Lexing.pos_lnum = 1  ;
        Lexing.pos_bol = 0   ;
        Lexing.pos_cnum = 0  }
    in

    (* Set new position in lexing buffer *)
    lexbuf.Lexing.lex_curr_p <- zero_pos ;

    (* Continue with included file *)
    token lexbuf
  }

  (* Operators that are not identifiers *)
  | ';' { SEMICOLON }
  | '=' { EQUALS }
  | ':' { COLON }
  | ',' { COMMA }
  | '[' { LSQBRACKET }
  | ']' { RSQBRACKET }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | ')' { RPAREN }
  | '.' { DOT }
  | ".." { DOTDOT }
  | '^' { CARET }
  | '{' { LCURLYBRACKET }
  | '}' { RCURLYBRACKET }
  | '}' { RCURLYBRACKET }
  | ".%" { DOTPERCENT }
  | '|' { PIPE }
  | "<<" { LPARAMBRACKET }
  | ">>" { RPARAMBRACKET }
  | "=>" { IMPL }
  | '#' { HASH }
  | "<=" { LTE }
  | ">=" { GTE }
  | '<' { LT }
  | '>' { GT }
  | "<>" { NEQ }
  | '-' { MINUS }
  | '+' { PLUS }
  | '/' { DIV }
  | '*' { MULT }
  | "->" { ARROW }

  (* Decimal or numeral *)
  | decimal as p { DECIMAL p }
  | exponent_decimal as p { DECIMAL p }
  | numeral as p { NUMERAL p }

  (* Keyword *)
  | id as p {
    try Hashtbl.find keyword_table p with Not_found -> (SYM p)
  }

  (* Whitespace *)
  | whitespace { token lexbuf }

  (* Newline *)
  | newline { Lexing.new_line lexbuf ; token lexbuf }

  (* End of file *)
  | eof {
    (* Pop previous lexing buffer form stack if at end of included file *)
    try pop_channel_of_lexbuf lexbuf ; token lexbuf with End_of_file -> EOF
  }

  (* Unrecognized character *)
  | _ as c {
    Format.sprintf "Unrecognized token %c (0x%X)" c (Char.code c) |> failwith
  }

(* Parse until end of comment, count newlines and otherwise discard
   characters *)
and skip_commented_slashstar = parse 

  (* End of comment *)
  | "*/" { token lexbuf } 

  (* Count new line *)
  | newline { Lexing.new_line lexbuf ; skip_commented_slashstar lexbuf } 

  | eof { Format.sprintf "Unterminated comment" |> failwith }

  (* Ignore characters in comments *)
  | _ { skip_commented_slashstar lexbuf }


(* Parse until end of comment, count newlines and otherwise discard
   characters *)
and skip_commented_parenstar = parse 

  (* End of comment *)
  | "*)" { token lexbuf } 

  (* Count new line *)
  | newline { Lexing.new_line lexbuf; skip_commented_parenstar lexbuf } 

  | eof { Format.sprintf "Unterminated comment" |> failwith }

  (* Ignore characters in comments *)
  | _ { skip_commented_parenstar lexbuf }

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

(*

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
*)

}

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
  
