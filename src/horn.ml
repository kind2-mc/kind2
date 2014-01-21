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


let rec parse lexbuf transSys = 

  (* Parse S-expression *)
  match SExprParser.sexp SExprLexer.main lexbuf with 
  
    | e -> 

      raise 
        (Failure 
           (Format.asprintf 
              "@[<hv>Unexpected S-expression@ @[<hv 1>%a@]@]" 
              HStringSExpr.pp_print_sexpr e))


(* Parse SMTLIB2 Horn format from channel *)
let of_channel in_ch =   

  (* Initialise buffer for lexing *)
  let lexbuf = Lexing.from_channel in_ch in

  parse lexbuf TransSys.empty


(* Parse SMTLIB2 Horn format from file *)
let of_file filename = 

  (* Open the given file for reading *)
  let use_file = open_in filename in
  let in_ch = use_file in

  of_channel in_ch

      
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
