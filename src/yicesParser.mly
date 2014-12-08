%{
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


  open Parsing
  open SExprBase

  type yices_resp_p =
    | YRespSat of (HStringSExpr.t * HStringSExpr.t) list
    | YRespUnknown of (HStringSExpr.t * HStringSExpr.t) list
    | YRespUnsat of int list

 
  let parse_failure pos what =
    (* Removed for menhir *)
    (* let pos = symbol_start_pos () in *)
    let msg =
      Printf.sprintf "YicesParser: failed to parse line %d char %d: %s"
                     pos.pos_lnum (pos.pos_cnum - pos.pos_bol) what in
    failwith msg

%}

%token UNSAT SAT UNKNOWN
%token ID CORE IDS UNSATISFIED ASSERTION
%token LEFTPAR RIGHTPAR COLON EQ
%token <string> IDENT
%token <int> INT
%token EOF


%start resp
%type <yices_resp_p> resp

%start assertion_id
%type <int> assertion_id

%%

resp:
| unsat_resp { #1 }
| sat_resp { #1 }
| unknown_resp { #1 }
;

unsat_resp:
| UNSAT { YRespUnsat [] }
| UNSAT UNSAT CORE IDS COLON integer_list { YRespUnsat #6 }
;

sat_resp:
| SAT { YRespSat [] }
| SAT model { YRespSat #2 }
;

unknown_resp:
| UNKNOWN { YRespUnknown [] }
| UNKNOWN model { YRespUnknown #2 }
;

assertion_id:
| ID COLON INT { #3 }
;

integer_list:
| { [] }
| INT integer_list { $1 :: $2 }
;

ident:
| IDENT { Atom (Hstring.make $1) }
;
  
ident_list:
| { [] }
| ident ident_list { $1 :: $2 }
;

sexpr:
| LEFTPAR ident_list RIGHTPAR { List $2 }
| LEFTPAR sexpr_list RIGHTPAR { List $2 }
;

sexpr_list
| { [] }
| sexpr sexpr_list { $2 :: $1 }
;

eq_term_value
| LEFTPAR EQ sexpr ident RIGHTPAR { ($3, $4) }
| LEFTPAR EQ sexpr sexpr RIGHTPAR { ($3, $4) }
;

model
| eq_term_value { [$1] }
| eq_term_value model { $1 :: $2 }
;
