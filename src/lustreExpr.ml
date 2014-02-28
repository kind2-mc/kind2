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
module T = LustreType
module I = LustreIdent
module ISet = I.LustreIdentSet


(* Exceptions *)
exception Type_mismatch
exception Clock_mismatch


(* A unary operator symbol *)
type unary_op =
  | Not
  | Uminus
  | ToInt
  | ToReal


(* Pretty-print a unary operator symbol *)
let pp_print_unary_op ppf = 
  let p = Format.fprintf ppf "%s" in
  
  function
    | Not -> p "not"
    | Uminus -> p "-"
    | ToInt -> p "int"
    | ToReal -> p "real"
      

(* A binary operator symbol *)
type binary_op =
  | And 
  | Or
  | Xor
  | Impl
  | Mod
  | Minus
  | Plus 
  | Div
  | Times 
  | IntDiv
  | Eq
  | Neq
  | Lte
  | Lt
  | Gte
  | Gt


(* Pretty-print a binary operator symbol *)
let pp_print_binary_op ppf = 
  let p = Format.fprintf ppf "%s" in
  
  function
    | And -> p "and"
    | Or -> p "or"
    | Xor -> p "xor"
    | Impl -> p "=>"
    | Mod -> p "mod"
    | Minus -> p "-"
    | Plus  -> p "+"
    | Div -> p "/"
    | Times  -> p "*"
    | IntDiv -> p "div"
    | Eq -> p "="
    | Neq -> p "<>"
    | Lte -> p "<="
    | Lt -> p "<"
    | Gte -> p ">="
    | Gt -> p ">"


(* A variadic operator symbol *)
type var_op =
  | OneHot


(* Pretty-print a variadic operator symbol *)
let pp_print_var_op ppf = 
  let p = Format.fprintf ppf "%s" in
  
  function
    | OneHot -> p "#"


(* A Lustre expression *)
type expr = 
  | Var of I.t
  | VarPre of I.t
  | True
  | False
  | Int of Numeral.t
  | Real of Decimal.t
  | UnaryOp of unary_op * expr
  | BinaryOp of binary_op * (expr * expr)
  | VarOp of var_op * expr list 
  | Ite of expr * expr * expr


(* Equaliy of expressions

   Need to compare with equality functions, since numerals and
   decimals are abstract values for OCaml's (=) function and so are
   indexed variables. *)
let rec equal_expr e1 e2 = match e1, e2 with 

  | Var v1, Var v2 
    when I.equal v1 v2 -> true

  | VarPre v1, VarPre v2 
    when I.equal v1 v2 -> true

  | True, True -> true

  | False, False -> true

  | Int i1, Int i2
    when Numeral.equal i1 i2 -> true

  | Real r1, Real r2
    when Decimal.equal r1 r2 -> true

  | UnaryOp (o1, a1), UnaryOp (o2, a2)
    when o1 = o2 && equal_expr a1 a2 -> true

  | BinaryOp (o1, (a1, b1)), BinaryOp (o2, (a2, b2)) 
    when o1 = o2 && equal_expr a1 a2 && equal_expr b1 b2 -> true

  | VarOp (o1, l1), VarOp (o2, l2) 
    when o1 = o2 && 
         List.length l1 = List.length l1 && 
         List.for_all2 equal_expr l1 l2 -> true

  | Ite (p1, l1, r1), Ite (p2, l2, r2) 
    when equal_expr p1 p2 && 
         equal_expr l1 l2 && 
         equal_expr r1 r2 -> true

  | _ -> false

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
  
  (* Type of expression *)
  expr_type: T.t;

  (* Current-state variables the expression depends on *)
  expr_vars : ISet.t;

  (* Pre-state variables the expression depends on *)
  expr_pre_vars : ISet.t;

}


(* Pretty-print a Lustre expression *)
let rec pp_print_expr safe ppf = function 
  
  | Var x -> Format.fprintf ppf "%a" (I.pp_print_ident safe) x
  | VarPre x -> 
    Format.fprintf ppf "@[<hv 1>(pre@ %a)@]" (I.pp_print_ident safe) x
  | True -> Format.fprintf ppf "true"
  | False -> Format.fprintf ppf "false"
  | Int i -> Format.fprintf ppf "%a" Numeral.pp_print_numeral i
  | Real f -> Format.fprintf ppf "%a" Decimal.pp_print_decimal f

  | UnaryOp (o, e) -> 

    Format.fprintf ppf
      "@[<hv 1>(%a@ %a)@]" 
      pp_print_unary_op o 
      (pp_print_expr safe) e

  | BinaryOp (o, (e1, e2)) -> 

    Format.fprintf ppf 
      "@[<hv 1>(%a@ %a@ %a)@]" 
      (pp_print_expr safe) e1 
      pp_print_binary_op o 
      (pp_print_expr safe) e2

  | VarOp (o, l) -> 

    Format.fprintf ppf 
      "@[<hv 1>%a(%a)@]" 
      pp_print_var_op o 
      (pp_print_list (pp_print_expr safe) ",@ ") l

  | Ite (p, l, r) -> 

    Format.fprintf ppf 
      "@[<hv 3>(if@ %a@;<1 -2>then@ %a@;<1 -2>else@ %a)@]" 
      (pp_print_expr safe) p
      (pp_print_expr safe) l 
      (pp_print_expr safe) r


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
    expr_clock = expr.expr_clock;
    expr_vars = expr.expr_vars;
    expr_pre_vars = expr.expr_pre_vars } 


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
    expr_clock = res_clock;
    expr_vars = ISet.union expr1.expr_vars expr2.expr_vars;
    expr_pre_vars = ISet.union expr1.expr_pre_vars expr2.expr_pre_vars } 


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
    expr_clock = res_clock;
    expr_vars = 
      ISet.union 
        expr1.expr_vars 
        (ISet.union expr2.expr_vars expr3.expr_vars);
    expr_pre_vars = 
      ISet.union 
        expr1.expr_pre_vars 
        (ISet.union expr2.expr_pre_vars expr3.expr_pre_vars) } 


(* ********************************************************************** *)
(* Constant constructors                                                  *)
(* ********************************************************************** *)
  

(* Boolean constant true on base clock *)
let t_true = 

  let expr = True in

  { expr_init = expr; 
    expr_step = expr; 
    expr_type = T.t_bool; 
    expr_clock = base_clock;
    expr_vars = ISet.empty;
    expr_pre_vars = ISet.empty } 


(* Boolean constant false on base clock *)
let t_false =  

  let expr = False in

  { expr_init = expr; 
    expr_step = expr; 
    expr_type = T.t_bool; 
    expr_clock = base_clock;
    expr_vars = ISet.empty;
    expr_pre_vars = ISet.empty } 


(* Integer constant on base clock *)
let mk_int d =  

  let expr = Int d in

  { expr_init = expr; 
    expr_step = expr; 
    expr_type = T.mk_int_range d d; 
    expr_clock = base_clock;
    expr_vars = ISet.empty;
    expr_pre_vars = ISet.empty } 


(* Real constant on base clock *)
let mk_real f =  

  let expr = Real f in

  { expr_init = expr; 
    expr_step = expr; 
    expr_type = T.t_real; 
    expr_clock = base_clock;
    expr_vars = ISet.empty;
    expr_pre_vars = ISet.empty } 


(* Current-state variable *)
let mk_var ident expr_type expr_clock = 

  let expr = Var ident in

  { expr_init = expr;
    expr_step = expr;
    expr_type = expr_type;
    expr_clock = expr_clock;
    expr_vars = ISet.singleton ident;
    expr_pre_vars = ISet.empty } 


(* Previous-state variable *)
let mk_var_pre  ident expr_type expr_clock = 

  let expr = VarPre ident in

  { expr_init = expr;
    expr_step = expr;
    expr_type = expr_type;
    expr_clock = expr_clock;
    expr_vars = ISet.empty;
    expr_pre_vars = ISet.singleton ident } 


let type_of_bool_bool = function 

  | T.Bool -> T.t_bool

  | _ -> raise Type_mismatch


let type_of_bool_bool_bool = function 
  | T.Bool -> (function T.Bool -> T.t_bool | _ -> raise Type_mismatch)
  | _ -> raise Type_mismatch


(* ********************************************************************** *)
(* Type checking constructors                                             *)
(* ********************************************************************** *)


(* Type check for int -> int -> int *)
let type_of_int_int_int = function 

  | T.Int | T.IntRange _ -> 
    (function 
      | T.Int | T.IntRange _ -> T.t_int 
      | _ -> raise Type_mismatch)
  | _ -> raise Type_mismatch


(* Type check for real -> real -> real *)
let type_of_real_real_real = function 

  | T.Real -> 
    (function 
      | T.Real -> T.t_real
      | _ -> raise Type_mismatch)
    
  | _ -> raise Type_mismatch


(* Type check for int -> int -> int, real -> real -> real *)
let type_of_num_num_num = function 

  | T.Int | T.IntRange _ -> 
    (function 
      | T.Int | T.IntRange _ -> T.t_int 
      | _ -> raise Type_mismatch)

  | T.Real -> 
    (function 
      | T.Real -> T.t_real
      | _ -> raise Type_mismatch)
    
  | _ -> raise Type_mismatch


(* Type check for 'a -> 'a -> 'a *)
let type_of_a_a_a type1 type2 = 

  (* If first type is subtype of second, choose second type *)
  if T.check_type type1 type2 then type2 else 

    (* If second type is subtype of first, choose first type *)
  if T.check_type type2 type1 then type1 else 

    (* Extend integer ranges *)
    (match type1, type2 with 
      | T.IntRange _, T.IntRange _ 
      | T.IntRange _, T.Int
      | T.Int, T.IntRange _ -> T.t_int

      (* Fail if types are incompatible *)
      | _ -> raise Type_mismatch)


(* Type check for 'a -> 'a -> bool *)
let type_of_a_a_bool type1 type2 = 

  (* One type must be subtype of the other *)
  if T.check_type type1 type2 || T.check_type type2 type1 then 

    T.t_bool 

  else 

    (* Extend integer ranges *)
    (match type1, type2 with 
      | T.IntRange _, T.IntRange _ 
      | T.IntRange _, T.Int
      | T.Int, T.IntRange _ -> T.t_bool

      (* Fail if types are incompatible *)
      | _ -> raise Type_mismatch)




(* Type check for int -> int -> bool, real -> real -> bool *)
let type_of_num_num_bool = function

  | T.Int | T.IntRange _ -> 
    (function 
      | T.Int | T.IntRange _ -> T.t_bool 
      | _ -> raise Type_mismatch)

  | T.Real -> 
    (function 
      | T.Real -> T.t_bool
      | _ -> raise Type_mismatch)
    
  | _ -> raise Type_mismatch


(* ********************************************************************** *)


(* Evaluate unary negation

   not true -> false
   not false -> true
*)
let eval_not = function 
  | True -> False
  | False -> True
  | expr -> UnaryOp (Not, expr)


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
let eval_uminus = function
  | Int d -> Int Numeral.(- d)
  | Real f -> Real Decimal.(- f)
  | UnaryOp(Uminus, expr) -> expr
  | expr -> UnaryOp(Uminus, expr) 


(* Type of unary minus 

   -: int -> int 
   -: int_range(l, u) -> int_range(-u, -l)
   -: real -> real 
*)
let type_of_uminus = function
  | T.Int -> T.t_int
  | T.Real -> T.t_real
  | T.IntRange (lbound, ubound) -> 
    T.mk_int_range Numeral.(- ubound) Numeral.(- lbound)
  | _ -> raise Type_mismatch


(* Unary negation of expression *)
let mk_uminus expr = mk_unary eval_uminus type_of_uminus expr


(* ********************************************************************** *)


(* Evaluate conversion to integer *)
let eval_to_int = function 
  | Real f -> Int (Numeral.of_big_int (Decimal.to_big_int f))
  | expr -> UnaryOp(ToInt, expr)


(* Type of conversion to integer  

   int: real -> int 
*)
let type_of_to_int = function
  | T.Real -> T.t_int
  | _ -> raise Type_mismatch


(* Conversion to integer *)
let mk_to_int expr = mk_unary eval_to_int type_of_to_int expr 


(* ********************************************************************** *)


(* Evaluate conversion to real *)
let eval_to_real = function 
  | Int d -> Real (Decimal.of_big_int (Numeral.to_big_int d))
  | expr -> UnaryOp(ToReal, expr)


(* Type of conversion to real  

   real: int -> real 
*)
let type_of_to_real = function
  | T.Int -> T.t_real
  | T.IntRange _ -> T.t_real
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
  | True -> (function expr2 -> expr2)
  | False -> (function expr2 -> False)
  | expr1 -> 
    (function 
      | True -> expr1
      | False -> False
      | expr2 -> BinaryOp(And, (expr1, expr2)))


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
  | True -> (function expr2 -> True)
  | False -> (function expr2 -> expr2)
  | expr1 -> 
    (function 
      | True -> True
      | False -> expr1
      | expr2 -> BinaryOp(Or, (expr1, expr2)))


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
  | True -> (function expr2 -> UnaryOp(Not, expr2))
  | False -> (function expr2 -> expr2)
  | expr1 -> 
    (function 
      | True -> UnaryOp(Not, expr1)
      | False -> expr1
      | expr2 -> BinaryOp(Xor, (expr1, expr2)))


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
  | True -> (function expr2 -> expr2)
  | False -> (function expr2 -> True)
  | expr1 -> 
    (function 
      | True -> True
      | False -> UnaryOp(Not, expr1)
      | expr2 -> BinaryOp(Impl, (expr1, expr2)))


(* Type of Boolean implication 

   =>: bool -> bool -> bool *)
let type_of_impl = type_of_bool_bool_bool


(* Boolean implication *)
let mk_impl expr1 expr2 = mk_binary eval_impl type_of_impl expr1 expr2 


(* ********************************************************************** *)


(* Evaluate integer modulus *)
let eval_mod expr1 expr2 = match expr1, expr2 with
  | Int d1, Int d2 -> Int Numeral.(d1 mod d2) 
  | _ -> BinaryOp(Mod, (expr1, expr2))


(* Type of integer modulus 

   mod: int -> int -> int *)
let type_of_mod = type_of_int_int_int

(* Boolean implication *)
let mk_mod expr1 expr2 = mk_binary eval_mod type_of_mod expr1 expr2 


(* ********************************************************************** *)


(* Evaluate subtraction *)
let eval_minus expr1 expr2 = match expr1, expr2 with
  | Int d1, Int d2 -> Int Numeral.(d1 - d2) 
  | Real f1, Real f2 -> Real Decimal.(f1 - f2) 
  | _ -> BinaryOp(Minus, (expr1, expr2))


(* Type of subtraction 

   -: int -> int -> int
      real -> real -> real *)
let type_of_minus = type_of_num_num_num 


(* Subtraction *)
let mk_minus expr1 expr2 = mk_binary eval_minus type_of_minus expr1 expr2 


(* ********************************************************************** *)


(* Evaluate addition *)
let eval_plus expr1 expr2 = match expr1, expr2 with
  | Int d1, Int d2 -> Int Numeral.(d1 + d2) 
  | Real f1, Real f2 -> Real Decimal.(f1 + f2) 
  | _ -> BinaryOp(Plus, (expr1, expr2))


(* Type of addition 

   +: int -> int -> int
      real -> real -> real *)
let type_of_plus = type_of_num_num_num 


(* Addition *)
let mk_plus expr1 expr2 = mk_binary eval_plus type_of_plus expr1 expr2 


(* ********************************************************************** *)


(* Evaluate real division *)
let eval_div expr1 expr2 = match expr1, expr2 with
  | Real f1, Real f2 -> Real Decimal.(f1 / f2) 
  | _ -> BinaryOp(Div, (expr1, expr2))


(* Type of real division

   /: real -> real -> real *)
let type_of_div = type_of_real_real_real


(* Real division *)
let mk_div expr1 expr2 = mk_binary eval_div type_of_div expr1 expr2 


(* ********************************************************************** *)


(* Evaluate multiplication *)
let eval_times expr1 expr2 = match expr1, expr2 with
  | Int d1, Int d2 -> Int Numeral.(d1 * d2) 
  | Real f1, Real f2 -> Real Decimal.(f1 * f2) 
  | _ -> BinaryOp(Times, (expr1, expr2))


(* Type of multiplication

   *: int -> int -> int
      real -> real -> real *)
let type_of_times = type_of_num_num_num


(* Multiplication *)
let mk_times expr1 expr2 = mk_binary eval_times type_of_times expr1 expr2 


(* ********************************************************************** *)


(* Evaluate integer division *)
let eval_intdiv expr1 expr2 = match expr1, expr2 with
  | Int d1, Int d2 -> Int Numeral.(d1 / d2) 
  | _ -> BinaryOp(IntDiv, (expr1, expr2))


(* Type of integer division

   div: int -> int -> int *)
let type_of_intdiv = type_of_int_int_int


(* Integer division *)
let mk_intdiv expr1 expr2 = mk_binary eval_intdiv type_of_intdiv expr1 expr2 


(* ********************************************************************** *)


(* Evaluate equality *)
let eval_eq expr1 expr2 = match expr1, expr2 with

  (* true = e2 -> e2 *)
  | True, _ ->  expr2

  (* false = e2 -> not e2 *)
  | False, _ -> UnaryOp(Not, expr2)

  (* e1 = true -> e1 *)
  | _, True -> expr1

  (* e1 = false -> not e1 *)
  | _, False -> (UnaryOp(Not, expr1))

  | Int d1, Int d2 when Numeral.(d1 = d2) -> True

  | Int d1, Int d2 -> False

  | Real f1, Real f2 when Decimal.(f1 = f2) -> True

  | Real f1, Real f2 -> False

  (* e = e -> true *)
  | _ when equal_expr expr1 expr2 -> True

  | _ -> BinaryOp(Eq, (expr1, expr2))


(* Type of equality

   =: 'a -> 'a -> bool *)
let type_of_eq = type_of_a_a_bool


(* Equality *)
let mk_eq expr1 expr2 = mk_binary eval_eq type_of_eq expr1 expr2 


(* ********************************************************************** *)


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


(* Type of disequality

   <>: 'a -> 'a -> bool *)
let type_of_neq = type_of_a_a_bool


(* Disequality *)
let mk_neq expr1 expr2 = mk_binary eval_neq type_of_neq expr1 expr2 


(* ********************************************************************** *)


(* Evaluate inequality *)
let eval_lte expr1 expr2 = match expr1, expr2 with
  | Int d1, Int d2 when Numeral.(d1 <= d2) -> True
  | Int d1, Int d2 -> False
  | Real f1, Real f2 when Decimal.(f1 <= f2) -> True
  | Real f1, Real f2 -> False
  | _ -> BinaryOp(Lte, (expr1, expr2))


(* Type of inequality

   <=: int -> int -> bool
       real -> real -> bool *)
let type_of_lte = type_of_num_num_bool


(* Disequality *)
let mk_lte expr1 expr2 = mk_binary eval_lte type_of_lte expr1 expr2 


(* ********************************************************************** *)


(* Evaluate inequality *)
let eval_lt expr1 expr2 = match expr1, expr2 with
  | Int d1, Int d2 when Numeral.(d1 < d2) -> True
  | Int d1, Int d2 -> False
  | Real f1, Real f2 when Decimal.(f1 < f2) -> True
  | Real f1, Real f2 -> False
  | _ -> BinaryOp(Lt, (expr1, expr2))


(* Type of inequality

   <: int -> int -> bool
      real -> real -> bool *)
let type_of_lt = type_of_num_num_bool


(* Disequality *)
let mk_lt expr1 expr2 = mk_binary eval_lt type_of_lt expr1 expr2 


(* ********************************************************************** *)


(* Evaluate inequality *)
let eval_gte expr1 expr2 = match expr1, expr2 with
  | Int d1, Int d2 when Numeral.(d1 >= d2) -> True
  | Int d1, Int d2 -> False
  | Real f1, Real f2 when Decimal.(f1 >= f2) -> True
  | Real f1, Real f2 -> False
  | _ -> BinaryOp(Gte, (expr1, expr2))


(* Type of inequality

   >=: int -> int -> bool
       real -> real -> bool *)
let type_of_gte = type_of_num_num_bool


(* Disequality *)
let mk_gte expr1 expr2 = mk_binary eval_gte type_of_gte expr1 expr2 


(* ********************************************************************** *)


(* Evaluate inequality *)
let eval_gt expr1 expr2 = match expr1, expr2 with
  | Int d1, Int d2 when Numeral.(d1 > d2) -> True
  | Int d1, Int d2 -> False
  | Real f1, Real f2 when Decimal.(f1 > f2) -> True
  | Real f1, Real f2 -> False
  | _ -> BinaryOp(Gt, (expr1, expr2))


(* Type of inequality

   >=: int -> int -> bool
       real -> real -> bool *)
let type_of_gt = type_of_num_num_bool


(* Disequality *)
let mk_gt expr1 expr2 = mk_binary eval_gt type_of_gt expr1 expr2 




(* ********************************************************************** *)


(* Evaluate if-then-else *)
let eval_ite = function 
  | True -> (function expr2 -> (function _ -> expr2))
  | False -> (function _ -> (function expr3 -> expr3))
  | expr1 -> 
    (function expr2 -> 
      (function expr3 -> 
        if equal_expr expr2 expr3 then 
          expr2 
        else
          (Ite (expr1, expr2, expr3)))) 


(* Type of if-then-else

   ite: bool -> 'a -> 'a -> 'a *)
let type_of_ite = function 
  | T.Bool -> 

    (function type2 -> function type3 ->

       (* If first type is subtype of second, choose second type *)
       if T.check_type type2 type3 then type3 else 

         (* If second type is subtype of first, choose first type *)
       if T.check_type type3 type2 then type2 else 

         (* Extend integer ranges *)
         (match type2, type3 with 
           | T.IntRange _, T.IntRange _ 
           | T.IntRange _, T.Int
           | T.Int, T.IntRange _ -> T.t_int

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
    expr_clock = res_clock;
    expr_vars = expr2.expr_vars;
    expr_pre_vars = expr2.expr_pre_vars } 
  

(* Pre expression *)
let mk_pre_expr mk_new_var_ident = function 

  | Var ident as expr -> (expr, None) 

  | expr -> 

    let new_var_ident = mk_new_var_ident () in

    (VarPre new_var_ident, Some (new_var_ident, expr))


let mk_pre 
    mk_new_var_ident 
    ((vars, calls) as defs)
    ({ expr_init; expr_step } as expr) = 

  (* Apply pre to initial state expression *)
  let expr_init', ((vars', calls') as defs') = match expr_init with 

    (* Expression is a variable *)
    | Var ident -> (VarPre ident, defs)

    (* Expression is a constant *)
    | True
    | False
    | Int _
    | Real _ -> (expr_init, defs)

    (* Expression is not constant and no variable *)
    | _ -> 
      
      (* Identifier for a fresh variable *)
      let new_var_ident = mk_new_var_ident () in
      
      (* Abstract expression to fresh variable *)
      (VarPre new_var_ident, 
       ((new_var_ident, expr) :: vars, calls))

  in

  (* Apply pre to step state expression *)
  let expr_step', defs'' = match expr_step with 

    (* Expression is identical to initial state *)
    | _ when equal_expr expr_step expr_init -> 

      (* Re-use abstraction for initial state *)
      (expr_init', defs')

    (* Expression is a variable *)
    | Var ident -> (VarPre ident, defs')

    (* Expression is not constant and no variable *)
    | _ -> 
      
      (* Identifier for a fresh variable *)
      let new_var_ident = mk_new_var_ident () in
      
      (* Abstract expression to fresh variable *)
      (VarPre new_var_ident, 
       ((new_var_ident, expr) :: vars', calls'))

  in

  (* Return expression and new definitions *)
  ({ expr with expr_init = expr_init'; expr_step = expr_step' }, 
   defs'') 


(* Return true if there is an pre operator in the expression *)
let rec pre_in_expr = function 
  
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

  

(* Return true if there is an unguarded pre operator in the expression *)
let pre_is_unguarded { expr_init } = 
  
  (* Check if there is a pre operator in the init expression *)
  pre_in_expr [ expr_init ]


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


(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
