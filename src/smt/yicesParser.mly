%{
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

  open Lexing
  open YicesResponse
 
  let parse_failure pos what =
    (* Removed for menhir *)
    (* let pos = symbol_start_pos () in *)
    let msg =
      Printf.sprintf "YicesParser: failed to parse line %d char %d: %s"
                     pos.pos_lnum (pos.pos_cnum - pos.pos_bol) what in
    failwith msg

%}

%token SAT UNSAT UNKNOWN // ERROR
%token ID CORE IDS // UNSATISFIED ASSERTION
%token LEFTPAR RIGHTPAR COLON EQ
%token <string> IDENT
// %token <string> LINE
%token <int> INT
%token <Decimal.t> DECIMAL
%token SUCCESS // CUSTOM
%token <string> ERROR_MSG
%token <string> CUSTOM_RESP
%token EOF

%start resp
%type <YicesResponse.yices_resp_p> resp

%start error_msg
%type <string> error_msg

%start assertion_id
%type <int> assertion_id

%%

resp:
| unsat_resp SUCCESS { $1 }
| sat_resp SUCCESS { $1 }
| unknown_resp SUCCESS { $1 }
| custom_resp { $1 }
| SUCCESS { YSuccess }
| EOF { YError }
(* | EOF { Format.eprintf "parse EOF@."; YNoResp } *)
;

error_msg:
| ERROR_MSG { $1 }
;

custom_resp:
| CUSTOM_RESP { YCustom $1 }
;

unsat_resp:
| UNSAT { YRespUnsat [] }
| UNSAT UNSAT CORE IDS id_list { YRespUnsat $5 }
;

sat_resp:
| SAT { YRespSat [] }
| SAT model { YRespSat $2 }
;

unknown_resp:
| UNKNOWN { YRespUnknown [] }
| UNKNOWN model { YRespUnknown $2 }
;

assertion_id:
| ID COLON INT EOF { $3 }
;

id_list:
| { [] }
| INT id_list { (YicesResponse.yices_id_of_int $1) :: $2 }
;

expr:
| DECIMAL { HStringSExpr.HStringSExpr.Atom
              (HString.mk_hstring (Decimal.string_of_decimal $1)) }
| INT { HStringSExpr.Atom (HString.mk_hstring (string_of_int $1)) }
| IDENT { HStringSExpr.Atom (HString.mk_hstring $1) }
;

sexpr:
| expr { $1 }
| LEFTPAR sexpr_list RIGHTPAR { HStringSExpr.List $2 }
;

sexpr_list:
| { [] }
| sexpr sexpr_list { $1 :: $2 }
;

eq_term_value:
| LEFTPAR EQ sexpr sexpr RIGHTPAR { ($3, $4) }
;

model:
| eq_term_value { [$1] }
| eq_term_value model { $1 :: $2 }
;
