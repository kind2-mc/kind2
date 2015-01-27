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


type error_response = [ `Error of string ]
       
type no_response = [ `NoResponse ]

type decl_response = [
  | no_response
  | `Unsupported
  | `Success 
  | error_response
]

type check_sat_response = [
  | `Sat
  | `Unsat
  | `Unknown
  | error_response
]

type get_value_response = [
  | `Values of (Term.t * Term.t) list
  | error_response
]

type get_unsat_core_response = [
  | `Unsat_core of string list
  | error_response
]

type custom_response = [
  | `Custom of HStringSExpr.t list
  | error_response
]

type response = [
  | decl_response
  | check_sat_response
  | get_value_response
  | get_unsat_core_response
  | custom_response
]


(* Pretty-print a response to a list of expression pairs *)
let rec pp_print_values ppf = function 

  | [] -> ()

  | (e, v) :: [] -> 

    Format.pp_open_hvbox ppf 2;
    Format.pp_print_string ppf "(";
    Term.pp_print_term ppf e;
    Format.pp_print_space ppf ();
    Term.pp_print_term ppf v;
    Format.pp_print_string ppf ")";
    Format.pp_close_box ppf ()

  | (e, v) :: tl -> 

    pp_print_values ppf [(e,v)];
    Format.pp_print_space ppf ();
    pp_print_values ppf tl


(* Pretty-print a command response *)
let pp_print_response ppf = function

  | `NoResponse -> Format.pp_print_string ppf "NoResponse"

  | `Unsupported -> Format.pp_print_string ppf "Unsupported"

  | `Success -> Format.pp_print_string ppf "Success"

  | `Error e -> 
    Format.pp_print_string ppf "Error: "; 
    Format.pp_print_string ppf e

  | `Sat -> Format.pp_print_string ppf "Sat"

  | `Unsat -> Format.pp_print_string ppf "Unsat"

  | `Unknown -> Format.pp_print_string ppf "Unknown"

  | `Values v -> 
    Format.pp_print_space ppf ();
    Format.pp_open_hvbox ppf 1;
    Format.pp_print_string ppf "(";
    pp_print_values ppf v;
    Format.pp_print_string ppf ")";
    Format.pp_close_box ppf ()

  | `Unsat_core c -> 
    Format.fprintf 
      ppf 
      "@[<hv 1>(%a)@]"
      (Lib.pp_print_list Format.pp_print_string "@ ") c

  | `Custom r -> 
    Format.pp_print_newline ppf ();
    Format.pp_open_vbox ppf 0;
    Lib.pp_print_list HStringSExpr.pp_print_sexpr "" ppf r;
    Format.pp_close_box ppf ()
