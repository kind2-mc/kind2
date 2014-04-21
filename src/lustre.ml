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

(* String representation of symbol in Lustre *)
let string_of_symbol = function
  | `TRUE -> "true"
  | `FALSE -> "false"
  | `NOT -> "not"
  | `IMPLIES -> "=>"
  | `AND -> "and"
  | `OR -> "or"
  | `XOR -> "xor"
  | `EQ -> "="
  | `NUMERAL n -> Numeral.string_of_numeral n
  | `DECIMAL d -> Decimal.string_of_decimal d
  | `MINUS -> "-"
  | `PLUS -> "+"
  | `TIMES -> "*"
  | `DIV -> "/"
  | `INTDIV ->"div"
  | `MOD -> "mod"
  | `ABS -> "abs"
  | `LEQ -> "<="
  | `LT -> "<"
  | `GEQ -> ">="
  | `GT -> ">"

let pp_print_symbol ppf s = Format.fprintf ppf "%s" (string_of_symbol s) 

let rec pp_print_var depth ppf var = match depth with

  | 0 -> 

    StateVar.pp_print_state_var_original
      ppf 
      (Var.state_var_of_state_var_instance var)

  | _ -> 

    Format.fprintf ppf "@[<hv 2>pre(%a)@]" (pp_print_var (pred depth)) var

and pp_print_term_node depth ppf t = match Term.T.destruct t with
    
  | Term.T.Var var -> 

    pp_print_var 
      (depth - (Numeral.to_int (Var.offset_of_state_var_instance var))) 
      ppf 
      var
      
  | Term.T.Const s -> Symbol.pp_print_symbol ppf s
      
  | Term.T.App (s, l) -> pp_print_app depth ppf (Symbol.node_of_symbol s) l
      
and pp_print_app_left' depth s ppf = function 
	  
  | h :: tl -> 
    
    Format.fprintf ppf 
      " %a@ %a%t" 
      pp_print_symbol s 
      (pp_print_term_node depth) h 
      (function ppf -> pp_print_app_left' depth s ppf tl)
      
  | [] -> ()
    
and pp_print_app_left depth s ppf = function 

  | [] -> assert false

  | h :: tl -> 

    Format.fprintf ppf
      "@[<hv 2>(%a%t)@]" 
      (pp_print_term_node depth) h 
      (function ppf -> pp_print_app_left' depth s ppf tl)

and pp_print_app_right' depth s arity ppf = function 
	  
  | [] -> assert false 

  | [h] -> 

    let rec aux ppf = function 
      | 0 -> ()
      | i -> 
        Format.fprintf ppf
          "%t)@]"
          (function ppf -> aux ppf (pred i))
    in

    Format.fprintf ppf
      "%a%t" 
      (pp_print_term_node depth) h 
      (function ppf -> aux ppf arity)

  | h :: tl -> 
    
    Format.fprintf ppf 
      "@[<hv 2>(%a %a@ %t" 
      (pp_print_term_node depth) h 
      pp_print_symbol s 
      (function ppf -> pp_print_app_right' depth s arity ppf tl)
      

and pp_print_app_right depth s ppf l =
  pp_print_app_right' depth s (List.length l - 1) ppf l
      
and pp_print_app_chain depth s ppf = function 
      
  | []
  | [_] -> assert false 
    
  | [l; r] -> 
    
    Format.fprintf ppf 
      "@[<hv 2>(%a %a@ %a)@]" 
      (pp_print_term_node depth) l 
      pp_print_symbol s
      (pp_print_term_node depth) r
      
  | l :: r :: tl -> 
    
    Format.fprintf ppf 
      "@[<hv 2>(%a %a@ %a) and %a@]" 
      (pp_print_term_node depth) l
      pp_print_symbol s
      (pp_print_term_node depth) r
      (pp_print_app_chain depth s) (r :: tl)
      
and pp_print_app depth ppf = function 
  
  (* Nullary symbols *)
  | `TRUE
  | `FALSE
  | `NUMERAL _
  | `DECIMAL _
  | `BV _ -> (function _ -> assert false)
      
  (* Unary symbols *) 
  | `NOT
  | `ABS as s -> 

    (function [a] -> 
      Format.fprintf ppf
        "@[<hv 2>(%a@ %a)@]" 
        pp_print_symbol s 
        (pp_print_term_node depth) a

      | _ -> assert false)
      
  (* Unary and left-associative binary *)
  | `MINUS as s ->
      
      (function 
	| [] -> assert false 
	| [a] ->

	  Format.fprintf ppf
            "%a%a" 
            pp_print_symbol s 
            (pp_print_term_node depth) a

	| _ as l -> pp_print_app_left depth s ppf l)
	
    (* Binary left-associative symbols with two or more arguments *)
    | `AND
    | `OR
    | `XOR
    | `PLUS
    | `TIMES
    | `DIV
    | `INTDIV as s ->
      
      (function 
	| [] 
	| [_] -> assert false
	| _ as l -> pp_print_app_left depth s ppf l)
	    
    (* Binary right-associative symbols *)
    | `IMPLIES as s -> pp_print_app_right depth s ppf
        
    (* Chainable binary symbols *)
    | `EQ
    | `LEQ
    | `LT
    | `GEQ
    | `GT as s -> pp_print_app_chain depth s ppf
	      
    (* if-then-else *)
    | `ITE ->
      
      (function [p; l; r] ->

	Format.fprintf ppf
          "if %a then %a else %a" 
          (pp_print_term_node depth) p
          (pp_print_term_node depth) l
          (pp_print_term_node depth) r
          
	| _ -> assert false)
	
    (* Binary symbols *)
    | `MOD as s ->
      
      (function [l; r] ->

	Format.fprintf ppf 
          "@[<hv 2>(%a %a@ %a)@]" 
          (pp_print_term_node depth) l 
          pp_print_symbol s
          (pp_print_term_node depth) r
	
	| _ -> assert false)
	
    (* Divisibility *) 
    | `DIVISIBLE n -> 
      
      (function [a] -> 
	
	(* a divisble n becomes a mod n = 0 *)
	pp_print_app 
	  depth
	  ppf
          `EQ
          [Term.T.mk_app 
             (Symbol.mk_symbol `MOD) 
             [a; Term.T.mk_const (Symbol.mk_symbol (`NUMERAL n))];
           Term.T.mk_const (Symbol.mk_symbol (`NUMERAL Numeral.zero))]
	  
	| _ -> assert false)
	
    (* Unsupported functions symbols *)
    | `DISTINCT
    | `CONCAT
    | `EXTRACT _
    | `BVNOT
    | `BVNEG
    | `BVAND
    | `BVOR
    | `BVADD
    | `BVMUL
    | `BVDIV
    | `BVUREM
    | `BVSHL
    | `BVLSHR
    | `BVULT
    | `SELECT
    | `STORE
    | `TO_REAL
    | `TO_INT
    | `IS_INT
    | `UF _ -> (function _ -> assert false)
      

(* Pretty-print a hashconsed term *)
let pp_print_term ppf term =
  pp_print_term_node 0 ppf term


(* Pretty-print a hashconsed term to the standard formatter *)
let print_term = pp_print_term Format.std_formatter 


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)


      
