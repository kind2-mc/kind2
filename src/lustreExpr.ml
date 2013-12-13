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
  | Int of int
  | Real of float
  | UnaryOp of unary_op * expr
  | BinaryOp of binary_op * (expr * expr)
  | VarOp of var_op * expr list 
  | Ite of expr * expr * expr


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
let rec pp_print_expr ppf = function 
  
  | Var x -> Format.fprintf ppf "%a" I.pp_print_ident x
  | VarPre x -> Format.fprintf ppf "@[<hv 1>(pre@ %a)@]" I.pp_print_ident x
  | True -> Format.fprintf ppf "true"
  | False -> Format.fprintf ppf "false"
  | Int i -> Format.fprintf ppf "%d" i
  | Real f -> Format.fprintf ppf "%f" f

  | UnaryOp (o, e) -> 

    Format.fprintf ppf
      "@[<hv 1>(%a@ %a)@]" 
      pp_print_unary_op o 
      pp_print_expr e

  | BinaryOp (o, (e1, e2)) -> 

    Format.fprintf ppf 
      "@[<hv 1>(%a@ %a@ %a)@]" 
      pp_print_expr e1 
      pp_print_binary_op o 
      pp_print_expr e2

  | VarOp (o, l) -> 

    Format.fprintf ppf 
      "@[<hv 1>%a(%a)@]" 
      pp_print_var_op o 
      (pp_print_list pp_print_expr ",@ ") l

  | Ite (p, l, r) -> 

    Format.fprintf ppf 
      "@[<hv 1>(if %a@;<1 -1>then@ %a@;<1 -1>else@ %a)@]" 
      pp_print_expr p
      pp_print_expr l 
      pp_print_expr r


(* Pretty-print a clocked and typed Lustre expression *)
let pp_print_lustre_expr ppf = function

  (* Same expression for initial state and following states *)
  | { expr_init; expr_step } when expr_init = expr_step -> 

    pp_print_expr ppf expr_step

  (* Print expression of initial state followed by expression for
     following states *)
  | { expr_init; expr_step } -> 

    Format.fprintf ppf 
      "@[<hv 1>(%a@ ->@ %a)@]" 
      pp_print_expr expr_init
      pp_print_expr expr_step


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

  let res_type = 
    let t = type_of expr.expr_type in
    if t = type_of expr.expr_type then t else raise Type_mismatch
  in

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
    
    (* Fail if types are incompatible *)
    raise Type_mismatch


(* Type check for 'a -> 'a -> bool *)
let type_of_a_a_bool type1 type2 = 

  (* One type must be subtype of the other *)
  if T.check_type type1 type2 || T.check_type type2 type1 then 

    T.t_bool 

  else 
    
    raise Type_mismatch


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
  | Int d -> Int (- d)
  | Real f -> Real (-. f)
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
  | T.IntRange (lbound, ubound) -> T.mk_int_range (- ubound) (- lbound)
  | _ -> raise Type_mismatch


(* Unary negation of expression *)
let mk_uminus expr = mk_unary eval_uminus type_of_uminus expr


(* ********************************************************************** *)


(* Evaluate conversion to integer *)
let eval_to_int = function 
  | Real f -> Int (int_of_float f)
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
  | Int d -> Real (float_of_int d)
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
  | Int d1, Int d2 -> Int (d1 mod d2) 
  | _ -> BinaryOp(Mod, (expr1, expr2))


(* Type of integer modulus 

   mod: int -> int -> int *)
let type_of_mod = type_of_int_int_int

(* Boolean implication *)
let mk_mod expr1 expr2 = mk_binary eval_mod type_of_mod expr1 expr2 


(* ********************************************************************** *)


(* Evaluate subtraction *)
let eval_minus expr1 expr2 = match expr1, expr2 with
  | Int d1, Int d2 -> Int (d1 - d2) 
  | Real f1, Real f2 -> Real (f1 -. f2) 
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
  | Int d1, Int d2 -> Int (d1 + d2) 
  | Real f1, Real f2 -> Real (f1 +. f2) 
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
  | Real f1, Real f2 -> Real (f1 /. f2) 
  | _ -> BinaryOp(Div, (expr1, expr2))


(* Type of real division

   /: real -> real -> real *)
let type_of_div = type_of_real_real_real


(* Real division *)
let mk_div expr1 expr2 = mk_binary eval_div type_of_div expr1 expr2 


(* ********************************************************************** *)


(* Evaluate multiplication *)
let eval_times expr1 expr2 = match expr1, expr2 with
  | Int d1, Int d2 -> Int (d1 * d2) 
  | Real f1, Real f2 -> Real (f1 *. f2) 
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
  | Int d1, Int d2 -> Int (d1 / d2) 
  | _ -> BinaryOp(IntDiv, (expr1, expr2))


(* Type of integer division

   div: int -> int -> int *)
let type_of_intdiv = type_of_int_int_int


(* Integer division *)
let mk_intdiv expr1 expr2 = mk_binary eval_intdiv type_of_intdiv expr1 expr2 


(* ********************************************************************** *)


(* Evaluate equality *)
let eval_eq = function

  (* true = e2 -> e2 *)
  | True -> (function expr2 -> expr2)

  (* false = e2 -> not e2 *)
  | False -> (function expr2 -> UnaryOp(Not, expr2))

  | expr1 -> 

    (function

      (* e1 = true -> e1 *)
      | True -> expr1

      (* e1 = false -> not e1 *)
      | False -> (UnaryOp(Not, expr1))

      (* e = e -> true *)
      | expr2 when expr1 = expr2 -> True

      | expr2 -> BinaryOp(Eq, (expr1, expr2)))


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
      | expr2 when expr1 = expr2 -> True

      | expr2 -> BinaryOp(Neq, (expr1, expr2)))


(* Type of disequality

   <>: 'a -> 'a -> bool *)
let type_of_neq = type_of_a_a_bool


(* Disequality *)
let mk_neq expr1 expr2 = mk_binary eval_neq type_of_neq expr1 expr2 


(* ********************************************************************** *)


(* Evaluate inequality *)
let eval_lte expr1 expr2 = match expr1, expr2 with
  | Int d1, Int d2 when d1 <= d2 -> True
  | Int d1, Int d2 -> False
  | Real f1, Real f2 when f1 <= f2 -> True
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
  | Int d1, Int d2 when d1 < d2 -> True
  | Int d1, Int d2 -> False
  | Real f1, Real f2 when f1 < f2 -> True
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
  | Int d1, Int d2 when d1 >= d2 -> True
  | Int d1, Int d2 -> False
  | Real f1, Real f2 when f1 >= f2 -> True
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
  | Int d1, Int d2 when d1 > d2 -> True
  | Int d1, Int d2 -> False
  | Real f1, Real f2 when f1 > f2 -> True
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
      (function expr3 -> (Ite (expr1, expr2, expr3)))) 


(* Type of if-then-else

   ite: bool -> 'a -> 'a -> 'a *)
let type_of_ite = function 
  | T.Bool -> 

    (function 

      | T.Int | T.IntRange _ -> 
        (function 
          | T.Int | T.IntRange _ -> T.t_int 
          | _ -> raise Type_mismatch)

      | T.Real -> 
        (function 
          | T.Real -> T.t_real
          | _ -> raise Type_mismatch)
        
      | T.Bool -> 
        (function 
          | T.Bool -> T.t_bool
          | _ -> raise Type_mismatch)
        
      | _ -> raise Type_mismatch)
         
  | _ -> (function _ -> function _ -> raise Type_mismatch)


(* If-then-else *)
let mk_ite expr1 expr2 expr3 = 
  mk_ternary eval_ite type_of_ite expr1 expr2 expr3


(* ********************************************************************** *)


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
  


let mk_pre_expr mk_new_var_ident = function 

  | Var ident as expr -> (expr, None) 

  | expr -> 

    let new_var_ident = mk_new_var_ident () in

    (VarPre new_var_ident, Some (new_var_ident, expr))


let mk_pre 
    mk_new_var_ident 
    ((vars, calls) as defs)
    ({ expr_init; expr_step } as expr) = 

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

  let expr_step', defs'' = match expr_step with 

    (* Expression is identical to initial state *)
    | _ when expr_step = expr_init -> 

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

  

(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
