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

(* Abbreviations *)
(* module T = LustreType *)
module I = LustreIdent
module ISet = I.LustreIdentSet


(* Exceptions *)
exception Type_mismatch
exception Clock_mismatch


(* A Lustre expression is a term *)
type expr = Term.t


(* Map from state variables to indexed identifiers *)
let state_var_ident_map  = StateVar.StateVarHashtbl.create 7


(* Return the identifier of a state variable *)
let ident_of_state_var state_var = 

  try 
    
    (* Find original indexed identifier *)
    StateVar.StateVarHashtbl.find state_var_ident_map state_var

  (* No identifier found *)
  with Not_found -> 
    
    (* Create new identifier of state variable *)
    I.mk_string_ident (StateVar.string_of_state_var state_var)
      


(* Equality on expressions *)
let equal_expr = Term.equal


(* A Lustre clock *)
type clock = unit


(* A typed and clocked Lustre expression *)
type t = { 
  
  (* Lustre expression for the initial state *)
  expr_init: expr;

  (* Lustre expression after initial state *)
  expr_step: expr;
  
  (* Clock of expression *)
  expr_clock: unit;
  
  (* Type of expression

     Keep the type here instead of reading from expr_init or
     expr_step, otherwise we need to get both types and merge *)
  expr_type: Type.t 

}


(* ********************************************************************** *)
(* Pretty-printing                                                        *)
(* ********************************************************************** *)


(* String representation of a symbol in Lustre *)
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
  | _ -> failwith "string_of_symbol"

(* Pretty-print a symbol *)
let pp_print_symbol ppf s = Format.fprintf ppf "%s" (string_of_symbol s) 


let pp_print_lustre_var safe ppf state_var = 

    (* Indexed identifier for state variable *)
    let ident = ident_of_state_var state_var in
    
    I.pp_print_ident safe ppf ident


(* Pretty-print a variable under [depth] pre operators *)
let rec pp_print_var safe depth ppf var = match depth with

  (* Variable without pre *)
  | 0 -> 

    (* Get state variable of variable *)
    let state_var = Var.state_var_of_state_var_instance var in
    
    pp_print_lustre_var safe ppf state_var

  (* Variable with at least one pre *)
  | _ -> 

    (* Print one pre and recurse *)
    Format.fprintf ppf
      "@[<hv 2>pre(%a)@]"
      (pp_print_var safe (pred depth)) 
      var


(* Pretty-print a term *)
and pp_print_term_node safe depth ppf t = match Term.T.destruct t with
    
  | Term.T.Var var -> 

    pp_print_var 
      safe
      (depth - (Numeral.to_int (Var.offset_of_state_var_instance var))) 
      ppf 
      var
      
  | Term.T.Const s -> 
    
    pp_print_symbol ppf (Symbol.node_of_symbol s)
      
  | Term.T.App (s, l) -> 
    
    pp_print_app safe depth ppf (Symbol.node_of_symbol s) l

  | Term.T.Attr (t, _) -> 
    
    pp_print_term_node safe depth ppf t
      

(* Pretty-print second and following arguments of a left-associative
   function application *)
and pp_print_app_left' safe depth s ppf = function 

  | h :: tl -> 

    Format.fprintf ppf 
      " %a@ %a%t" 
      pp_print_symbol s 
      (pp_print_term_node safe depth) h 
      (function ppf -> pp_print_app_left' safe depth s ppf tl)

  | [] -> ()


(* Pretty-print a left-associative function application

   Print (+ a b c) as (a + b + c) *)
and pp_print_app_left safe depth s ppf = function 

  (* Function application must have arguments, is a constant
     otherwise *)
  | [] -> assert false

  (* Print first argument *)
  | h :: tl -> 

    Format.fprintf ppf
      "@[<hv 2>(%a%t)@]" 
      (pp_print_term_node safe depth) h 
      (function ppf -> pp_print_app_left' safe depth s ppf tl)


(* Pretty-print arguments of a right-associative function application *)
and pp_print_app_right' safe depth s arity ppf = function 

  (* Function application must have arguments, is a constant
     otherwise *)
  | [] -> assert false 

  (* Last or only argument *)
  | [h] -> 

    (* Print closing parentheses for all arguments *)
    let rec aux ppf = function 
      | 0 -> ()
      | i -> 
        Format.fprintf ppf
          "%t)@]"
          (function ppf -> aux ppf (pred i))
    in

    (* Print last argument and close all parentheses *)
    Format.fprintf ppf
      "%a%t" 
      (pp_print_term_node safe depth) h 
      (function ppf -> aux ppf arity)

  (* Second last or earlier argument *)
  | h :: tl -> 

    (* Open parenthesis and print argument *)
    Format.fprintf ppf 
      "@[<hv 2>(%a %a@ %t" 
      (pp_print_term_node safe depth) h 
      pp_print_symbol s 
      (function ppf -> pp_print_app_right' safe depth s arity ppf tl)


(* Pretty-print a right-associative function application 

   Print (=> a b c) as (a => (b => c)) *)
and pp_print_app_right safe depth s ppf l =
  pp_print_app_right' safe depth s (List.length l - 1) ppf l


(* Pretty-print a chaining function application 

   Print (= a b c) as (a = b) and (b = c) *)
and pp_print_app_chain safe depth s ppf = function 

  (* Chaining function application must have more than one argument *)
  | []
  | [_] -> assert false 

  (* Last or only pair of arguments *)
  | [l; r] -> 

    Format.fprintf ppf 
      "@[<hv 2>(%a %a@ %a)@]" 
      (pp_print_term_node safe depth) l 
      pp_print_symbol s
      (pp_print_term_node safe depth) r

  (* Print function application of first pair, conjunction and continue *)
  | l :: r :: tl -> 

    Format.fprintf ppf 
      "@[<hv 2>(%a %a@ %a) and %a@]" 
      (pp_print_term_node safe depth) l
      pp_print_symbol s
      (pp_print_term_node safe depth) r
      (pp_print_app_chain safe depth s) (r :: tl)


(* Pretty-print a function application *)
and pp_print_app safe depth ppf = function 

  (* Function application must have arguments, cannot have nullary
     symbols here *)
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
        (pp_print_term_node safe depth) a

      | _ -> assert false)
      
  (* Unary and left-associative binary symbols *)
  | `MINUS as s ->
      
      (function 
        | [] -> assert false 
        | [a] ->

          Format.fprintf ppf
            "%a%a" 
            pp_print_symbol s 
            (pp_print_term_node safe depth) a

        | _ as l -> pp_print_app_left safe depth s ppf l)
        
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
        | _ as l -> pp_print_app_left safe depth s ppf l)
            
    (* Binary right-associative symbols *)
    | `IMPLIES as s -> pp_print_app_right safe depth s ppf
        
    (* Chainable binary symbols *)
    | `EQ
    | `LEQ
    | `LT
    | `GEQ
    | `GT as s -> pp_print_app_chain safe depth s ppf
              
    (* if-then-else *)
    | `ITE ->
      
      (function [p; l; r] ->

        Format.fprintf ppf
          "if %a then %a else %a" 
          (pp_print_term_node safe depth) p
          (pp_print_term_node safe depth) l
          (pp_print_term_node safe depth) r
          
        | _ -> assert false)
        
    (* Binary symbols *)
    | `MOD as s ->
      
      (function [l; r] ->

        Format.fprintf ppf 
          "@[<hv 2>(%a %a@ %a)@]" 
          (pp_print_term_node safe depth) l 
          pp_print_symbol s
          (pp_print_term_node safe depth) r
        
        | _ -> assert false)
        
    (* Divisibility *) 
    | `DIVISIBLE n -> 
      
      (function [a] -> 
        
        (* a divisble n becomes a mod n = 0 *)
        pp_print_app 
          safe 
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
let pp_print_expr safe ppf expr =
  pp_print_term_node safe 0 ppf expr


(* Pretty-print a hashconsed term to the standard formatter *)
let print_expr safe = pp_print_expr safe Format.std_formatter 


(* Pretty-print a clocked and typed Lustre expression *)
let pp_print_lustre_expr safe ppf = function

  (* Same expression for initial state and following states *)
  | { expr_init; expr_step } when equal_expr expr_init expr_step -> 

    pp_print_expr safe ppf expr_step

  (* Print expression of initial state followed by expression for
     following states *)
  | { expr_init; expr_step } -> 

    Format.fprintf ppf 
      "@[<hv 1>(%a@ ->@ %a)@]" 
      (pp_print_expr safe) expr_init
      (pp_print_expr safe) expr_step


(* ********************************************************************** *)
(* Clocks                                                                 *)
(* ********************************************************************** *)


(* The base clock *)
let base_clock = ()


(* TODO: clock checking *)
let clock_check _ _ = true


(* ********************************************************************** *)
(* Generic constructors                                                   *)
(* ********************************************************************** *)


(* Construct a unary expression *)
let mk_unary eval type_of expr = 

  let res_type = type_of expr.expr_type in

  { expr_init = eval expr.expr_init;
    expr_step = eval expr.expr_step;
    expr_type = res_type;
    expr_clock = expr.expr_clock } 


(* Construct a binary expression *)
let mk_binary eval type_of expr1 expr2 = 

  let res_clock = 
    if clock_check expr1.expr_clock expr2.expr_clock then 
      expr1.expr_clock
    else
      raise Clock_mismatch
  in  

  let res_type = 
    type_of expr1.expr_type expr2.expr_type 
  in

  { expr_init = eval expr1.expr_init expr2.expr_init;
    expr_step = eval expr1.expr_step expr2.expr_step;
    expr_type = res_type;
    expr_clock = res_clock } 


(* Construct a binary expression *)
let mk_ternary eval type_of expr1 expr2 expr3 = 

  let res_clock = 
    if 
      clock_check expr1.expr_clock expr2.expr_clock && 
      clock_check expr2.expr_clock expr3.expr_clock 
    then 
      expr1.expr_clock
    else
      raise Clock_mismatch
  in  

  let res_type = 
    type_of expr1.expr_type expr2.expr_type expr3.expr_type 
  in

  { expr_init = eval expr1.expr_init expr2.expr_init expr3.expr_init;
    expr_step = eval expr1.expr_step expr2.expr_step expr3.expr_step;
    expr_type = res_type;
    expr_clock = res_clock } 


(* ********************************************************************** *)
(* Constant constructors                                                  *)
(* ********************************************************************** *)
  

(* Create or return state variable of identifier *)
let state_var_of_ident scope ident ident_type = 

  (* Convert identifier to a string *)
  let ident_string = I.string_of_ident true ident in 

  (* Create or return state variable of string *)
  let state_var = StateVar.mk_state_var ident_string scope ident_type in 

  (* Add to hashtable unless already present *)
  (if not (StateVar.StateVarHashtbl.mem state_var_ident_map state_var) then 
     StateVar.StateVarHashtbl.add state_var_ident_map state_var ident);

  (* Return state variable *)
  state_var 


(* Boolean constant true on base clock *)
let t_true = 

  let expr = Term.t_true in

  { expr_init = expr; 
    expr_step = expr; 
    expr_type = Type.t_bool; 
    expr_clock = base_clock } 


(* Boolean constant false on base clock *)
let t_false =  

  let expr = Term.t_false in

  { expr_init = expr; 
    expr_step = expr; 
    expr_type = Type.t_bool; 
    expr_clock = base_clock } 


(* Integer constant on base clock *)
let mk_int d =  

  let expr = Term.mk_num d in

  { expr_init = expr; 
    expr_step = expr; 
    expr_type = Type.mk_int_range d d; 
    expr_clock = base_clock } 


(* Real constant on base clock *)
let mk_real f =  

  let expr = Term.mk_dec f in

  { expr_init = expr; 
    expr_step = expr; 
    expr_type = Type.t_real; 
    expr_clock = base_clock } 


(* Current state variable of state variable *)
let mk_var_of_state_var state_var expr_clock = 

  (* Variable at offset zero of identifier *)
  let var = Var.mk_state_var_instance state_var Numeral.zero in 

  (* Term of variable *)
  let expr = Term.mk_var var in

  { expr_init = expr;
    expr_step = expr;
    expr_type = StateVar.type_of_state_var state_var;
    expr_clock = expr_clock } 


(* Current-state variable *)
let mk_var scope ident expr_type expr_clock = 

  (* State variable of identifier *)
  let state_var = state_var_of_ident scope ident expr_type in

  mk_var_of_state_var state_var expr_clock



(* Previous-state variable *)
let mk_var_pre scope ident expr_type expr_clock = 

  (* State variable of identifier *)
  let state_var = state_var_of_ident scope ident expr_type in

  (* Variable at offset zero of identifier *)
  let var = Var.mk_state_var_instance state_var Numeral.one in 

  (* Term of variable *)
  let expr = Term.mk_var var in

  { expr_init = expr;
    expr_step = expr;
    expr_type = expr_type;
    expr_clock = expr_clock } 


let type_of_bool_bool = function 
  | t when Type.is_bool t -> Type.t_bool
  | _ -> raise Type_mismatch


let type_of_bool_bool_bool = function 
  | t when Type.is_bool t -> 
    (function 
      | t when Type.is_bool t -> Type.t_bool 
      | _ -> raise Type_mismatch)
  | _ -> raise Type_mismatch


(* ********************************************************************** *)
(* Type checking constructors                                             *)
(* ********************************************************************** *)


(* Type check for int -> int -> int *)
let type_of_int_int_int = function 

  | t when Type.is_int t || Type.is_int_range t -> 
    (function 
      | t when Type.is_int t || Type.is_int_range t -> Type.t_int 
      | _ -> raise Type_mismatch)
  | _ -> raise Type_mismatch


(* Type check for real -> real -> real *)
let type_of_real_real_real = function 

  | t when Type.is_real t -> 
    (function 
      | t when Type.is_real t -> Type.t_real
      | _ -> raise Type_mismatch)
    
  | _ -> raise Type_mismatch


(* Type check for int -> int -> int, real -> real -> real *)
let type_of_num_num_num = function 

  | t when Type.is_int t || Type.is_int_range t -> 
    (function 
      | t when Type.is_int t || Type.is_int_range t -> Type.t_int 
      | _ -> raise Type_mismatch)

  | t when Type.is_real t -> 
    (function 
      | t when Type.is_real t -> Type.t_real
      | _ -> raise Type_mismatch)
    
  | _ -> raise Type_mismatch


(* Type check for 'a -> 'a -> 'a *)
let type_of_a_a_a type1 type2 = 

  (* If first type is subtype of second, choose second type *)
  if Type.check_type type1 type2 then type2 else 

    (* If second type is subtype of first, choose first type *)
  if Type.check_type type2 type1 then type1 else 

    (* Extend integer ranges if one is not a subtype of the other *)
    (match type1, type2 with 
      | s, t 
        when (Type.is_int_range s && Type.is_int_range t) ||
             (Type.is_int_range s && Type.is_int t) ||
             (Type.is_int s && Type.is_int_range t) -> Type.t_int

      (* Fail if types are incompatible *)
      | _ -> raise Type_mismatch)


(* Type check for 'a -> 'a -> bool *)
let type_of_a_a_bool type1 type2 = 

  (* One type must be subtype of the other *)
  if Type.check_type type1 type2 || Type.check_type type2 type1 then 

    Type.t_bool 

  else 

    (* Extend integer ranges if one is not a subtype of the other *)
    (match type1, type2 with 
      | s, t 
        when (Type.is_int_range s && Type.is_int_range t) ||
             (Type.is_int_range s && Type.is_int t) ||
             (Type.is_int s && Type.is_int_range t) -> Type.t_bool

      (* Fail if types are incompatible *)
      | _ -> raise Type_mismatch)


(* Type check for int -> int -> bool, real -> real -> bool *)
let type_of_num_num_bool = function

  | t when Type.is_int t || Type.is_int_range t -> 
    (function 
      | t when Type.is_int t || Type.is_int_range t -> Type.t_bool 
      | _ -> raise Type_mismatch)

  | t when Type.is_real t -> 
    (function 
      | t when Type.is_real t -> Type.t_bool
      | _ -> raise Type_mismatch)
    
  | _ -> raise Type_mismatch


(* ********************************************************************** *)


(* Evaluate unary negation

   not true -> false
   not false -> true
*)
let eval_not = function 
  | t when t == Term.t_true -> Term.t_false
  | t when t == Term.t_false -> Term.t_true
  | expr -> Term.mk_not expr


(* Type of unary negation 

   not: bool -> bool 
*)
let type_of_not = type_of_bool_bool


(* Unary negation of expression *)
let mk_not expr = mk_unary eval_not type_of_not expr


(* ********************************************************************** *)


(* Evaluate unary minus

   -(c) -> (-c)
   -(-x) -> x
*)
let eval_uminus expr = match Term.destruct expr with 

  | Term.T.Const s when Symbol.is_numeral s -> 
    Term.mk_num Numeral.(- Symbol.numeral_of_symbol s)

  | Term.T.Const s when Symbol.is_decimal s -> 
    Term.mk_dec Decimal.(- Symbol.decimal_of_symbol s)

  | Term.T.App (s, [e]) when s == Symbol.s_minus -> e

  | _ -> Term.mk_minus [expr]


(* Type of unary minus 

   -: int -> int 
   -: int_range(l, u) -> int_range(-u, -l)
   -: real -> real 
*)
let type_of_uminus = function
  | t when Type.is_int t -> Type.t_int
  | t when Type.is_real t -> Type.t_real
  | t when Type.is_int_range t -> 
    let (ubound, lbound) = Type.bounds_of_int_range t in
    Type.mk_int_range Numeral.(- ubound) Numeral.(- lbound)
  | _ -> raise Type_mismatch


(* Unary negation of expression *)
let mk_uminus expr = mk_unary eval_uminus type_of_uminus expr


(* ********************************************************************** *)


(* Evaluate conversion to integer *)
let eval_to_int expr = match Term.destruct expr with 
  | Term.T.Const s when Symbol.is_decimal s -> 
    Term.mk_num
      (Numeral.of_big_int
         (Decimal.to_big_int
            (Symbol.decimal_of_symbol s)))

  | _ -> Term.mk_to_int expr


(* Type of conversion to integer  

   int: real -> int 
*)
let type_of_to_int = function
  | t when Type.is_real t -> Type.t_int
  | _ -> raise Type_mismatch


(* Conversion to integer *)
let mk_to_int expr = mk_unary eval_to_int type_of_to_int expr 


(* ********************************************************************** *)


(* Evaluate conversion to real *)
let eval_to_real expr = match Term.destruct expr with 
  | Term.T.Const s when Symbol.is_numeral s -> 
    Term.mk_dec
      (Decimal.of_big_int
         (Numeral.to_big_int
            (Symbol.numeral_of_symbol s)))

  | _ -> Term.mk_to_real expr

(* Type of conversion to real  

   real: int -> real 
*)
let type_of_to_real = function
  | t when Type.is_int t || Type.is_int_range t -> Type.t_real
  | _ -> raise Type_mismatch


(* Conversion to integer *)
let mk_to_real expr = mk_unary eval_to_real type_of_to_real expr 


(* ********************************************************************** *)


(* Evaluate Boolean conjunction

   true and e2 -> e2 
   false and e2 -> false
   e1 and true -> e1
   e1 and false -> false *)
let eval_and = function 
  | t when t == Term.t_true -> (function expr2 -> expr2)
  | t when t == Term.t_false -> (function expr2 -> Term.t_false)
  | expr1 -> 
    (function 
      | t when t == Term.t_true -> expr1
      | t when t == Term.t_false -> Term.t_false
      | expr2 -> Term.mk_and [expr1; expr2])


(* Type of Boolean conjunction 

   and: bool -> bool -> bool *)
let type_of_and = type_of_bool_bool_bool


(* Boolean conjunction *)
let mk_and expr1 expr2 = mk_binary eval_and type_of_and expr1 expr2 


(* ********************************************************************** *)


(* Evaluate Boolean disjunction

   true or e2 -> true
   false or e2 -> e2
   e1 or true -> true
   e1 or false -> e1 *)
let eval_or = function 
  | t when t == Term.t_true -> (function expr2 -> Term.t_true)
  | t when t == Term.t_false -> (function expr2 -> expr2)
  | expr1 -> 
    (function 
      | t when t == Term.t_true -> Term.t_true
      | t when t == Term.t_false -> expr1
      | expr2 -> Term.mk_or [expr1; expr2])


(* Type of Boolean disjunction 

   or: bool -> bool -> bool *)
let type_of_or = type_of_bool_bool_bool


(* Boolean disjunction *)
let mk_or expr1 expr2 = mk_binary eval_or type_of_or expr1 expr2 


(* ********************************************************************** *)


(* Evaluate Boolean exclusive disjunction

   true xor e2 -> not e2
   false xor e2 -> e2
   e1 xor true -> not e1
   e1 xor false -> e1 *)
let eval_xor = function 
  | t when t == Term.t_true -> (function expr2 -> Term.mk_not expr2)
  | t when t == Term.t_false -> (function expr2 -> expr2)
  | expr1 -> 
    (function 
      | t when t == Term.t_true -> Term.mk_not expr1
      | t when t == Term.t_false -> expr1
      | expr2 -> Term.mk_xor [expr1; expr2])


(* Type of Boolean exclusive disjunction 

   xor: bool -> bool -> bool *)
let type_of_xor = type_of_bool_bool_bool


(* Boolean exclusive disjunction *)
let mk_xor expr1 expr2 = mk_binary eval_xor type_of_xor expr1 expr2 


(* ********************************************************************** *)


(* Evaluate Boolean implication

   true => e2 -> e2
   false => e2 -> true
   e1 => true -> true
   e1 => false -> not e1 *)
let eval_impl = function 
  | t when t == Term.t_true -> (function expr2 -> expr2)
  | t when t == Term.t_false -> (function expr2 -> Term.t_true)
  | expr1 -> 
    (function 
      | t when t == Term.t_true -> Term.t_true
      | t when t == Term.t_false -> Term.mk_not expr1
      | expr2 -> Term.mk_implies [expr1; expr2])


(* Type of Boolean implication 

   =>: bool -> bool -> bool *)
let type_of_impl = type_of_bool_bool_bool


(* Boolean implication *)
let mk_impl expr1 expr2 = mk_binary eval_impl type_of_impl expr1 expr2 


(* ********************************************************************** *)


(* Evaluate integer modulus *)
let eval_mod expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && Symbol.is_numeral c2 -> 

      Term.mk_num 
        Numeral.(Symbol.numeral_of_symbol c1 mod 
                 Symbol.numeral_of_symbol c2) 

    | _ -> Term.mk_mod expr1 expr2


(* Type of integer modulus 

   mod: int -> int -> int *)
let type_of_mod = type_of_int_int_int

(* Integer modulus *)
let mk_mod expr1 expr2 = mk_binary eval_mod type_of_mod expr1 expr2 


(* ********************************************************************** *)


(* Evaluate subtraction *)
let eval_minus expr1 expr2 = 
  
  match Term.destruct expr1, Term.destruct expr2 with
    
    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && Symbol.is_numeral c2 -> 
      
      Term.mk_num 
        Numeral.(Symbol.numeral_of_symbol c1 -
                 Symbol.numeral_of_symbol c2) 
        
    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_decimal c1 && Symbol.is_decimal c2 -> 
      
      Term.mk_dec
        Decimal.(Symbol.decimal_of_symbol c1 -
                 Symbol.decimal_of_symbol c2) 
        
    | _ -> Term.mk_minus [expr1; expr2]
             

(* Type of subtraction 
   
   -: int -> int -> int
      real -> real -> real *)
let type_of_minus = type_of_num_num_num 


(* Subtraction *)
let mk_minus expr1 expr2 = mk_binary eval_minus type_of_minus expr1 expr2 


(* ********************************************************************** *)


(* Evaluate addition *)
let eval_plus expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && Symbol.is_numeral c2 -> 

      Term.mk_num 
        Numeral.(Symbol.numeral_of_symbol c1 +
                 Symbol.numeral_of_symbol c2) 

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_decimal c1 && Symbol.is_decimal c2 -> 

      Term.mk_dec
        Decimal.(Symbol.decimal_of_symbol c1 +
                 Symbol.decimal_of_symbol c2) 

  | _ -> Term.mk_plus [expr1; expr2]


(* Type of addition 

   +: int -> int -> int
      real -> real -> real *)
let type_of_plus = type_of_num_num_num 


(* Addition *)
let mk_plus expr1 expr2 = mk_binary eval_plus type_of_plus expr1 expr2 


(* ********************************************************************** *)


(* Evaluate real division *)
let eval_div expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_decimal c1 && Symbol.is_decimal c2 -> 

      Term.mk_dec
        Decimal.(Symbol.decimal_of_symbol c1 /
                 Symbol.decimal_of_symbol c2) 

  | _ -> Term.mk_div [expr1; expr2]


(* Type of real division

   /: real -> real -> real *)
let type_of_div = type_of_real_real_real


(* Real division *)
let mk_div expr1 expr2 = mk_binary eval_div type_of_div expr1 expr2 


(* ********************************************************************** *)


(* Evaluate multiplication *)
let eval_times expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && Symbol.is_numeral c2 -> 

      Term.mk_num 
        Numeral.(Symbol.numeral_of_symbol c1 *
                 Symbol.numeral_of_symbol c2) 

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_decimal c1 && Symbol.is_decimal c2 -> 

      Term.mk_dec
        Decimal.(Symbol.decimal_of_symbol c1 *
                 Symbol.decimal_of_symbol c2) 

  | _ -> Term.mk_times [expr1; expr2]


(* Type of multiplication

   *: int -> int -> int
      real -> real -> real *)
let type_of_times = type_of_num_num_num


(* Multiplication *)
let mk_times expr1 expr2 = mk_binary eval_times type_of_times expr1 expr2 


(* ********************************************************************** *)


(* Evaluate integer division *)
let eval_intdiv expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && Symbol.is_numeral c2 -> 

      Term.mk_num
        Numeral.(Symbol.numeral_of_symbol c1 /
                 Symbol.numeral_of_symbol c2) 

  | _ -> Term.mk_intdiv [expr1; expr2]


(* Type of integer division

   div: int -> int -> int *)
let type_of_intdiv = type_of_int_int_int


(* Integer division *)
let mk_intdiv expr1 expr2 = mk_binary eval_intdiv type_of_intdiv expr1 expr2 


(* ********************************************************************** *)


(* Evaluate equality *)
let eval_eq expr1 expr2 = match expr1, expr2 with

  (* true = e2 -> e2 *)
  | t, _ when t == Term.t_true -> expr2

  (* false = e2 -> not e2 *)
  | t, _ when t == Term.t_false -> Term.mk_not expr2

  (* e1 = true -> e1 *)
  | _, t when t == Term.t_true -> expr1

  (* e1 = false -> not e1 *)
  | _, t when t == Term.t_false -> Term.mk_not expr1

  (* e = e -> true *)
  | _ when equal_expr expr1 expr2 -> Term.t_true

  | _ -> 

    match Term.destruct expr1, Term.destruct expr2 with
      
      | Term.T.Const c1, Term.T.Const c2 when
          Symbol.is_numeral c1 && 
          Symbol.is_numeral c2 -> 
    
        if Numeral.(Symbol.numeral_of_symbol c1 =
                    Symbol.numeral_of_symbol c2) then 

          Term.t_true

        else

          Term.t_false

      | Term.T.Const c1, Term.T.Const c2 when
          Symbol.is_decimal c1 && 
          Symbol.is_decimal c2 -> 
    
        if Decimal.(Symbol.decimal_of_symbol c1 =
                    Symbol.decimal_of_symbol c2) then 

          Term.t_true

        else

          Term.t_false


      | _ -> Term.mk_eq [expr1; expr2]


(* Type of equality

   =: 'a -> 'a -> bool *)
let type_of_eq = type_of_a_a_bool


(* Equality *)
let mk_eq expr1 expr2 = mk_binary eval_eq type_of_eq expr1 expr2 


(* ********************************************************************** *)

(*
(* Evaluate disequality *)
let eval_neq = function

  (* true <> e2 -> not e2 *)
  | True -> (function expr2 -> UnaryOp(Not, expr2))

  (* false <> e2 -> e2 *)
  | False -> (function expr2 -> expr2)

  | expr1 -> 

    (function

      (* e1 <> true -> not e1 *)
      | True -> (UnaryOp(Not, expr1))

      (* e1 <> false -> e1 *)
      | False -> expr1

      (* e = e -> false *)
      | expr2 when not (equal_expr expr1 expr2) -> True

      | expr2 -> BinaryOp(Neq, (expr1, expr2)))
*)

let eval_neq expr1 expr2 = eval_not (eval_eq expr1 expr2)

(* Type of disequality

   <>: 'a -> 'a -> bool *)
let type_of_neq = type_of_a_a_bool


(* Disequality *)
let mk_neq expr1 expr2 = mk_binary eval_neq type_of_neq expr1 expr2 


(* ********************************************************************** *)


(* Evaluate inequality *)
let eval_lte expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && 
        Symbol.is_numeral c2 -> 

      if Numeral.(Symbol.numeral_of_symbol c1 <=
                  Symbol.numeral_of_symbol c2) then 

        Term.t_true

      else

        Term.t_false

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_decimal c1 && 
        Symbol.is_decimal c2 -> 

      if Decimal.(Symbol.decimal_of_symbol c1 <=
                  Symbol.decimal_of_symbol c2) then 

        Term.t_true

      else

        Term.t_false


    | _ -> Term.mk_leq [expr1; expr2]


(* Type of inequality

   <=: int -> int -> bool
       real -> real -> bool *)
let type_of_lte = type_of_num_num_bool


(* Disequality *)
let mk_lte expr1 expr2 = mk_binary eval_lte type_of_lte expr1 expr2 


(* ********************************************************************** *)


(* Evaluate inequality *)
let eval_lt expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && 
        Symbol.is_numeral c2 -> 

      if Numeral.(Symbol.numeral_of_symbol c1 <
                  Symbol.numeral_of_symbol c2) then 

        Term.t_true

      else

        Term.t_false

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_decimal c1 && 
        Symbol.is_decimal c2 -> 

      if Decimal.(Symbol.decimal_of_symbol c1 <
                  Symbol.decimal_of_symbol c2) then 

        Term.t_true

      else

        Term.t_false


    | _ -> Term.mk_lt [expr1; expr2]


(* Type of inequality

   <: int -> int -> bool
      real -> real -> bool *)
let type_of_lt = type_of_num_num_bool


(* Disequality *)
let mk_lt expr1 expr2 = mk_binary eval_lt type_of_lt expr1 expr2 


(* ********************************************************************** *)


(* Evaluate inequality *)
let eval_gte expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && 
        Symbol.is_numeral c2 -> 

      if Numeral.(Symbol.numeral_of_symbol c1 >=
                  Symbol.numeral_of_symbol c2) then 

        Term.t_true

      else

        Term.t_false

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_decimal c1 && 
        Symbol.is_decimal c2 -> 

      if Decimal.(Symbol.decimal_of_symbol c1 >=
                  Symbol.decimal_of_symbol c2) then 

        Term.t_true

      else

        Term.t_false


    | _ -> Term.mk_geq [expr1; expr2]


(* Type of inequality

   >=: int -> int -> bool
       real -> real -> bool *)
let type_of_gte = type_of_num_num_bool


(* Disequality *)
let mk_gte expr1 expr2 = mk_binary eval_gte type_of_gte expr1 expr2 


(* ********************************************************************** *)


(* Evaluate inequality *)
let eval_gt expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && 
        Symbol.is_numeral c2 -> 

      if Numeral.(Symbol.numeral_of_symbol c1 >
                  Symbol.numeral_of_symbol c2) then 

        Term.t_true

      else

        Term.t_false

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_decimal c1 && 
        Symbol.is_decimal c2 -> 

      if Decimal.(Symbol.decimal_of_symbol c1 >
                  Symbol.decimal_of_symbol c2) then 

        Term.t_true

      else

        Term.t_false


    | _ -> Term.mk_gt [expr1; expr2]


(* Type of inequality

   >=: int -> int -> bool
       real -> real -> bool *)
let type_of_gt = type_of_num_num_bool


(* Disequality *)
let mk_gt expr1 expr2 = mk_binary eval_gt type_of_gt expr1 expr2 




(* ********************************************************************** *)


(* Evaluate if-then-else *)
let eval_ite = function 
  | t when t == Term.t_true -> (function expr2 -> (function _ -> expr2))
  | t when t == Term.t_false -> (function _ -> (function expr3 -> expr3))
  | expr1 -> 
    (function expr2 -> 
      (function expr3 -> 
        if equal_expr expr2 expr3 then 
          expr2 
        else
          (Term.mk_ite expr1 expr2 expr3))) 


(* Type of if-then-else

   ite: bool -> 'a -> 'a -> 'a *)
let type_of_ite = function 
  | t when t = Type.t_bool -> 

    (function type2 -> function type3 ->

       (* If first type is subtype of second, choose second type *)
       if Type.check_type type2 type3 then type3 else 

         (* If second type is subtype of first, choose first type *)
       if Type.check_type type3 type2 then type2 else 

         (* Extend integer ranges if one is not a subtype of the other *)
         (match type2, type3 with 
           | s, t 
             when (Type.is_int_range s && Type.is_int_range t) ||
                  (Type.is_int_range s && Type.is_int t) ||
                  (Type.is_int s && Type.is_int_range t) -> Type.t_int

           | _ -> raise Type_mismatch))

  | _ -> (function _ -> function _ -> raise Type_mismatch)


(* If-then-else *)
let mk_ite expr1 expr2 expr3 = 
  mk_ternary eval_ite type_of_ite expr1 expr2 expr3


(* ********************************************************************** *)


(* Followed by expression *)
let mk_arrow expr1 expr2 = 

  let res_clock = 
    if clock_check expr1.expr_clock expr2.expr_clock then 
      expr1.expr_clock
    else
      raise Clock_mismatch
  in  

  let res_type = 
    type_of_a_a_a expr1.expr_type expr2.expr_type 
  in

  { expr_init = expr1.expr_init;
    expr_step = expr2.expr_step;
    expr_type = res_type;
    expr_clock = res_clock } 
  

(* Pre expression *)
let rec mk_pre 
    mk_new_var_ident 
    ((vars, calls) as defs)
    ({ expr_init; expr_step; expr_type; expr_clock } as expr) = 

  (* Apply pre to initial state expression *)
  let expr_init', ((vars', calls') as defs') = match expr_init with 

    (* Expression is a variable *)
    | t when Term.is_free_var t -> (Term.bump_state Numeral.(- one) t, defs)

    (* Expression is a constant *)
    | t when 
        t == Term.t_true || 
        t == Term.t_false || 
        (match Term.destruct t with 
          | Term.T.Const c1 when 
              Symbol.is_numeral c1 || Symbol.is_decimal c1 -> true
          | _ -> false) -> (expr_init, defs)

    (* Expression is not constant and no variable *)
    | _ -> 
      
      (* Identifier for a fresh variable *)
      let new_var_ident = mk_new_var_ident () in

      (* State variable of identifier *)
      let state_var = state_var_of_ident scope new_var_ident expr_type in 

      (* Variable at previous instant *)
      let var = Var.mk_state_var_instance state_var Numeral.(- one) in

      (* Return term and new definitions *)
      (Term.mk_var var, ((state_var, expr) :: vars, calls))
      
  in

  (* Apply pre to step state expression *)
  let expr_step', defs'' = match expr_step with 

    (* Expression is identical to initial state *)
    | _ when equal_expr expr_step expr_init -> 

      (* Re-use abstraction for initial state *)
      (expr_init', defs')

    (* Expression is a variable *)
    | t when Term.is_free_var t -> (Term.bump_state Numeral.(- one) t, defs')

    (* Expression is not constant and no variable *)
    | _ -> 
      
      (* Identifier for a fresh variable *)
      let new_var_ident = mk_new_var_ident () in

      (* State variable of identifier *)
      let state_var = state_var_of_ident new_var_ident expr_type in 

      (* Variable at previous instant *)
      let var = Var.mk_state_var_instance state_var Numeral.(- one) in

      (* Return term and new definitions *)
      (Term.mk_var var, ((state_var, expr) :: vars', calls'))
      
  in

  (* Return expression and new definitions *)
  ({ expr with expr_init = expr_init'; expr_step = expr_step' }, 
   defs'') 


(*

  (* pre x is unguarded *)
  | VarPre _ :: _ -> true

  | [] -> false

  | Var _ :: tl -> pre_in_expr tl

  | True :: tl -> pre_in_expr tl
  | False :: tl -> pre_in_expr tl
  | Int _ :: tl -> pre_in_expr tl
  | Real _ :: tl -> pre_in_expr tl
  | UnaryOp (_, e) :: tl -> pre_in_expr (e :: tl)
  | BinaryOp (_, (e1, e2)) :: tl -> pre_in_expr (e1 :: e2 :: tl)
  | VarOp (_, l) :: tl -> pre_in_expr (l @ tl)
  | Ite (e1, e2, e3) :: tl -> pre_in_expr (e1 :: e2 :: e3 :: tl)
*)

  
(* ********************************************************************** *)
(* Predicates                                                             *)
(* ********************************************************************** *)


(* Return true if there is an unguarded pre operator in the expression *)
let pre_is_unguarded { expr_init } = 

  (* Check if there is a pre operator in the init expression *)
  match Term.var_offsets_of_term expr_init with 
    | None, _ -> false
    | Some c, _ -> Numeral.(c < zero)


(* Return true if expression is a variable at given instant *)
let is_var_at_offset { expr_init; expr_step } offset = 

  (* Initial value and step value must be identical *)
  (expr_init == expr_step) && 

  (* Term must be a free variable *)
  (Term.is_free_var expr_init) && 

  (* Get free variable of term *)
  (let var = Term.free_var_of_term expr_init in 

   (* Variable must be an instance of a state variable *)
   Var.is_state_var_instance var && 

   (* Variable must be at instant zero *)
   Numeral.(Var.offset_of_state_var_instance var = offset))


(* Return true if expression is a current state variable *)
let is_var expr = is_var_at_offset expr Numeral.zero


(* Return true if expression is a previous state variable *)
let is_pre_var expr = is_var_at_offset expr Numeral.(- one)


(* Return the state variable of a variable *)
let state_var_of_expr { expr_init; expr_step } = 

  (* Initial value and step value must be identical *)
  if expr_init == expr_step then

    try 
      
      (* Get free variable of term *)
      let var = Term.free_var_of_term expr_init in 
      
      (* Get instance of state variable *)
      Var.state_var_of_state_var_instance var
        
    (* Fail if any of the above fails *)
    with Invalid_argument _ -> raise (Invalid_argument "state_var_of_expr")

  else

    (* Fail if initial value is different from step value *)
    raise (Invalid_argument "state_var_of_expr")

(*

(* Return the variables in the expression *)
let rec vars_of_expr' accum = function 

  (* All expressions processed: return *)
  | [] -> accum 

  (* Expression is a variable: add variable and continue *)
  | Var ident :: tl -> vars_of_expr' (ISet.add ident accum) tl

  (* Expresssion is a non-variable leaf: continue *)
  | (VarPre _
    | True
    | False
    | Int _ 
    | Real _) :: tl -> vars_of_expr' accum tl

  (* Expression is unary: add variables in argument *)
  | UnaryOp (_, expr) :: tl -> 

    vars_of_expr' accum (expr :: tl)

  (* Expression is binary: add variables in arguments *)
  | BinaryOp (_, (expr1, expr2)) :: tl -> 

    vars_of_expr' accum (expr1 :: expr2 :: tl)

  (* Expression is variadic: add variables in arguments *)
  | VarOp (_, expr_list) :: tl -> 

    vars_of_expr' accum (expr_list @ tl)

  (* Expression is ternary: add variables in arguments *)
  | Ite (expr1, expr2, expr3) :: tl -> 

    vars_of_expr' accum (expr1 :: expr2 :: expr3 :: tl)



(* Return the variables in the expression *)
let vars_of_expr expr = ISet.elements (vars_of_expr' ISet.empty [expr])

*)

(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
