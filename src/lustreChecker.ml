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

let main () = 

  (* Create lexing buffer *)
  let lexbuf = Lexing.from_function LustreLexer.read_from_lexbuf_stack in
  
  (* Read from file or standard input *)
  let in_ch, curdir = 
    if Array.length Sys.argv > 1 then 
      (let fname = Sys.argv.(1) in 
       
       let zero_pos = 
         { Lexing.pos_fname = fname;
           Lexing.pos_lnum = 1;
           Lexing.pos_bol = 0;
           Lexing.pos_cnum = 0 } 
       in
       lexbuf.Lexing.lex_curr_p <- zero_pos; 
       
       let curdir = 
         Filename.dirname fname
       in

       open_in fname, curdir) 
    else
      (stdin, Sys.getcwd ())
  in
  
  (* Initialize lexing buffer with channel *)
  LustreLexer.lexbuf_init in_ch curdir;
  
  (* Lustre file is a list of declarations *)
  let declarations = 

    try 

      (* Parse file to list of declarations *)
      LustreParser.main LustreLexer.token lexbuf 

    with 
      | LustreParser.Error ->

        let 
            { Lexing.pos_fname; 
              Lexing.pos_lnum; 
              Lexing.pos_bol; 
              Lexing.pos_cnum } = 
          Lexing.lexeme_start_p lexbuf 
        in
        
        Format.printf 
          "Syntax error in line %d at column %d in %s: %s@." 
          pos_lnum
          (pos_cnum - pos_bol)
          pos_fname
          (Lexing.lexeme lexbuf);
        
        exit 1
          
  in

  (* Simplify declarations to a list of nodes *)
  let nodes = LustreSimplify.declarations_to_nodes declarations in
  
  List.fold_left
    LustreTransSys.definition_of_node
    []
    (List.rev nodes);
    
;;

main ()

(* 
   Local Variables:
   compile-command: "make -C .. lustre-checker"
   indent-tabs-mode: nil
   End: 
*)
  
