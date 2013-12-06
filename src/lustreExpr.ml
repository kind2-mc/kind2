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

module T = LustreType
module I = LustreIdent

exception Type_mismatch

exception Clock_mismatch


type unary_op =
  | Not
  | Uminus
  | ToInt
  | ToReal


let pp_print_unary_op ppf = 
  let p = Format.fprintf ppf "%s" in
  
  function
    | Not -> p "not"
    | Uminus -> p "-"
    | ToInt -> p "int"
    | ToReal -> p "real"
      

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
  | Arrow


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
    | Arrow -> p "->"


type var_op =
  | OneHot


let pp_print_var_op ppf = 
  let p = Format.fprintf ppf "%s" in
  
  function
    | OneHot -> p "#"


type expr = 
  | Var of I.t
  | VarPre of I.t
  | True
  | False
  | Int of int
  | Real of float
  | UnaryOp of unary_op * expr
  | BinaryOp of binary_op * (expr * expr)
  | Ite of expr * expr * expr

type clock = unit

type t = { 
  
  (* Lustre expression *)
  expr: expr;
  
  (* Clock of expression *)
  expr_clock: unit;
  
  (* Type of expression *)
  expr_type: T.t }



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
      pp_print_binary_op o 
      pp_print_expr e1 
      pp_print_expr e2

  | Ite (p, l, r) -> 

    Format.fprintf ppf 
      "@[<hv 1>(if %a@;<1 -1>then@ %a@:<1 -1>else@ %a)@]" 
      pp_print_expr p
      pp_print_expr l 
      pp_print_expr r

let pp_print_lustre_expr ppf { expr } = pp_print_expr ppf expr

let base_clock = ()


(* TODO: clock checking *)
let clock_check _ _ = true


(* Boolean constant true on base clock *)
let t_true = 

  { expr = True; 
    expr_type = T.t_bool; 
    expr_clock = base_clock } 


(* Boolean constant false on base clock *)
let t_false =  

  { expr = False; 
    expr_type = T.t_bool; 
    expr_clock = base_clock } 


(* Integer constant on base clock *)
let mk_int d =  

  { expr = Int d; 
    expr_type = T.mk_int_range d d; 
    expr_clock = base_clock } 


(* Real constant on base clock *)
let mk_real f =  

  { expr = Real f; 
    expr_type = T.t_real; 
    expr_clock = base_clock } 


(* Current-state variable *)
let mk_var ident expr_type expr_clock = 

  { expr = Var ident;
    expr_type = expr_type;
    expr_clock = expr_clock } 


(* Previous-state variable *)
let mk_var_pre  ident expr_type expr_clock = 

  { expr = VarPre ident;
    expr_type = expr_type;
    expr_clock = expr_clock } 


(* Construct a unary expression *)
let mk_unary op expr expr_type expr_clock = 

  { expr = UnaryOp (op, expr);
    expr_type = expr_type;
    expr_clock = expr_clock } 


(* Construct a binary expression *)
let mk_binary op expr1 expr2 expr_type expr1_clock expr2_clock = 

  if clock_check expr1_clock expr2_clock then 

    { expr = BinaryOp (op, (expr1, expr2));
      expr_type = expr_type;
      expr_clock = expr1_clock } 
    
  else
    
    raise Clock_mismatch


(* not: bool -> bool *)
let mk_not = function 

  | { expr; expr_type = T.Bool; expr_clock } -> 

    mk_unary Not expr T.t_bool expr_clock

  | _ -> raise Type_mismatch


(* -: int -> int, 
      real -> real, 
      int_range(l,u) -> int_range(-u,-l) *)
let mk_uminus = function

  | { expr; expr_type = T.Int; expr_clock } -> 

    mk_unary Uminus expr T.t_int expr_clock

  | { expr; expr_type = T.Real; expr_clock } -> 

    mk_unary Uminus expr T.t_real expr_clock

  | { expr; expr_type = T.IntRange (lbound, ubound); expr_clock } -> 

    mk_unary 
      Uminus 
      expr
      (T.mk_int_range (- ubound) (- lbound)) 
      expr_clock

  | _ -> raise Type_mismatch


(* int: real -> int *)
let mk_to_int = function 

  | { expr; expr_type = T.Real; expr_clock } -> 

    mk_unary ToInt expr T.t_int expr_clock

  | _ -> raise Type_mismatch


(* real: int -> real *)
let mk_to_real = function

  | { expr; expr_type = T.Int; expr_clock } -> 

    mk_unary ToInt expr T.t_real expr_clock

  | _ -> raise Type_mismatch


(* and: bool -> bool -> bool *)
let mk_and = function 

    | { expr = expr1; expr_type = T.Bool; expr_clock = expr1_clock } -> 

      (function 

        | { expr = expr2; expr_type = T.Bool; expr_clock = expr2_clock } -> 
          
          mk_binary And expr1 expr2 T.t_bool expr1_clock expr2_clock

        | _ -> raise Type_mismatch)

    | _ -> raise Type_mismatch


(* or: bool -> bool -> bool *)
let mk_or = function

    | { expr = expr1; expr_type = T.Bool; expr_clock = expr1_clock } -> 

      (function 

        | { expr = expr2; expr_type = T.Bool; expr_clock = expr2_clock } -> 
          
          mk_binary Or expr1 expr2 T.t_bool expr1_clock expr2_clock

        | _ -> raise Type_mismatch)

    | _ -> raise Type_mismatch


(* xor: bool -> bool -> bool *)
let mk_xor = function

    | { expr = expr1; expr_type = T.Bool; expr_clock = expr1_clock } -> 

      (function 

        | { expr = expr2; expr_type = T.Bool; expr_clock = expr2_clock } -> 
          
          mk_binary Xor expr1 expr2 T.t_bool expr1_clock expr2_clock

        | _ -> raise Type_mismatch)

    | _ -> raise Type_mismatch


(* =>: bool -> bool -> bool *)
let mk_impl = function

    | { expr = expr1; expr_type = T.Bool; expr_clock = expr1_clock } -> 

      (function 

        | { expr = expr2; expr_type = T.Bool; expr_clock = expr2_clock } -> 
          
          mk_binary Impl expr1 expr2 T.t_bool expr1_clock expr2_clock

        | _ -> raise Type_mismatch)

    | _ -> raise Type_mismatch


(* mod: int -> int -> int

   Expand integer range types to integer type *)
let mk_mod = function 

    | { expr = expr1; expr_type = T.Int; expr_clock = expr1_clock } 
    | { expr = expr1; expr_type = T.IntRange _; expr_clock = expr1_clock } -> 

      (function 

        | { expr = expr2; 
            expr_type = T.Int; 
            expr_clock = expr2_clock } 

        | { expr = expr2; 
            expr_type = T.IntRange _; 
            expr_clock = expr2_clock } -> 
          
          mk_binary Mod expr1 expr2 T.t_int expr1_clock expr2_clock

        | _ -> raise Type_mismatch)

    | _ -> raise Type_mismatch


(* -: int -> int -> int
      real -> real -> real

   Expand integer range types to integer type *)
let mk_minus = function

    | { expr = expr1; expr_type = T.Int; expr_clock = expr1_clock } 
    | { expr = expr1; expr_type = T.IntRange _; expr_clock = expr1_clock } -> 

      (function 

        | { expr = expr2; 
            expr_type = T.Int; 
            expr_clock = expr2_clock } 
 
        | { expr = expr2; 
            expr_type = T.IntRange _; 
            expr_clock = expr2_clock } -> 
         
          mk_binary Minus expr1 expr2 T.t_int expr1_clock expr2_clock

        | _ -> raise Type_mismatch)

    | { expr = expr1; expr_type = T.Real; expr_clock = expr1_clock } -> 

      (function 

        | { expr = expr2; expr_type = T.Real; expr_clock = expr2_clock } -> 
          
          mk_binary Minus expr1 expr2 T.t_real expr1_clock expr2_clock

        | _ -> raise Type_mismatch)

    | _ -> raise Type_mismatch


(* +: int -> int -> int
      real -> real -> real

   Expand integer range types to integer type *)
let mk_plus = function

    | { expr = expr1; expr_type = T.Int; expr_clock = expr1_clock } 
    | { expr = expr1; expr_type = T.IntRange _; expr_clock = expr1_clock } -> 

      (function 

        | { expr = expr2; 
            expr_type = T.Int; 
            expr_clock = expr2_clock } 

        | { expr = expr2; 
            expr_type = T.IntRange _; 
            expr_clock = expr2_clock } -> 
          
          mk_binary Plus expr1 expr2 T.t_int expr1_clock expr2_clock

        | _ -> raise Type_mismatch)

    | { expr = expr1; expr_type = T.Real; expr_clock = expr1_clock } -> 

      (function 

        | { expr = expr2; expr_type = T.Real; expr_clock = expr2_clock } -> 
          
          mk_binary Plus expr1 expr2 T.t_real expr1_clock expr2_clock

        | _ -> raise Type_mismatch)

    | _ -> raise Type_mismatch


(* /: real -> real -> real *)
let mk_div = function

    | { expr = expr1; expr_type = T.Real; expr_clock = expr1_clock } -> 

      (function 

        | { expr = expr2; expr_type = T.Real; expr_clock = expr2_clock } -> 
          
          mk_binary Div expr1 expr2 T.t_real expr1_clock expr2_clock

        | _ -> raise Type_mismatch)

    | _ -> raise Type_mismatch


(* *: int -> int -> int
      real -> real -> real

   Expand integer range types to integer type *)
let mk_times = function

    | { expr = expr1; expr_type = T.Int; expr_clock = expr1_clock } 
    | { expr = expr1; expr_type = T.IntRange _; expr_clock = expr1_clock } -> 

      (function 

        | { expr = expr2; 
            expr_type = T.Int; 
            expr_clock = expr2_clock } 

        | { expr = expr2; 
            expr_type = T.IntRange _; 
            expr_clock = expr2_clock } -> 
          
          mk_binary Times expr1 expr2 T.t_int expr1_clock expr2_clock

        | _ -> raise Type_mismatch)

    | { expr = expr1; expr_type = T.Real; expr_clock = expr1_clock } -> 

      (function 

        | { expr = expr2; expr_type = T.Real; expr_clock = expr2_clock } -> 
          
          mk_binary Times expr1 expr2 T.t_real expr1_clock expr2_clock

        | _ -> raise Type_mismatch)

    | _ -> raise Type_mismatch


(* div: int -> int -> int

   Expand integer range types to integer type *)
let mk_intdiv = function

    | { expr = expr1; expr_type = T.Int; expr_clock = expr1_clock } 
    | { expr = expr1; expr_type = T.IntRange _; expr_clock = expr1_clock } -> 

      (function 

        | { expr = expr2; 
            expr_type = T.Int; 
            expr_clock = expr2_clock } 

        | { expr = expr2; 
            expr_type = T.IntRange _; 
            expr_clock = expr2_clock } -> 
          
          mk_binary IntDiv expr1 expr2 T.t_int expr1_clock expr2_clock

        | _ -> raise Type_mismatch)

    | _ -> raise Type_mismatch


(* =: 'a -> 'a -> bool

   Either the first type is a subtype of the second or vice versa *)
let mk_eq = function

    | { expr = expr1; expr_type = expr1_type; expr_clock = expr1_clock } ->

      (function 

        | { expr = expr2; 
            expr_type = expr2_type; 
            expr_clock = expr2_clock } 
          when 
            T.check_type expr1_type expr2_type ||
            T.check_type expr2_type expr1_type ->

          mk_binary Eq expr1 expr2 T.t_bool expr1_clock expr2_clock

        | _ -> raise Type_mismatch)


(* <>: 'a -> 'a -> bool 

   Either the first type is a subtype of the second or vice versa *)
let mk_neq = function

    | { expr = expr1; expr_type = expr1_type; expr_clock = expr1_clock } ->

      (function 

        | { expr = expr2; 
            expr_type = expr2_type; 
            expr_clock = expr2_clock } 
          when 
            T.check_type expr1_type expr2_type || 
            T.check_type expr2_type expr1_type ->

          mk_binary Eq expr1 expr2 T.t_bool expr1_clock expr2_clock

        | _ -> raise Type_mismatch)


(* <=: 'a -> 'a -> bool 

   Either the first type is a subtype of the second or vice versa *)
let mk_lte = function

    | { expr = expr1; expr_type = expr1_type; expr_clock = expr1_clock } ->

      (function 

        | { expr = expr2; 
            expr_type = expr2_type; 
            expr_clock = expr2_clock } 
          when 
            T.check_type expr1_type expr2_type || 
            T.check_type expr2_type expr1_type ->

          mk_binary Lte expr1 expr2 T.t_bool expr1_clock expr2_clock

        | _ -> raise Type_mismatch)


(* <: 'a -> 'a -> bool 

   Either the first type is a subtype of the second or vice versa *)
let mk_lt = function

    | { expr = expr1; expr_type = expr1_type; expr_clock = expr1_clock } ->

      (function 

        | { expr = expr2; 
            expr_type = expr2_type; 
            expr_clock = expr2_clock } 
          when 
            T.check_type expr1_type expr2_type || 
            T.check_type expr2_type expr1_type ->

          mk_binary Lt expr1 expr2 T.t_bool expr1_clock expr2_clock

        | _ -> raise Type_mismatch)


(* >=: 'a -> 'a -> bool 

   Either the first type is a subtype of the second or vice versa *)
let mk_gte = function

    | { expr = expr1; expr_type = expr1_type; expr_clock = expr1_clock } ->

      (function 

        | { expr = expr2; 
            expr_type = expr2_type; 
            expr_clock = expr2_clock } 
          when 
            T.check_type expr1_type expr2_type || 
            T.check_type expr2_type expr1_type ->

          mk_binary Gte expr1 expr2 T.t_bool expr1_clock expr2_clock

        | _ -> raise Type_mismatch)


(* >: 'a -> 'a -> bool 

   Either the first type is a subtype of the second or vice versa *)
let mk_gt = function

    | { expr = expr1; expr_type = expr1_type; expr_clock = expr1_clock } ->

      (function 

        | { expr = expr2; 
            expr_type = expr2_type; 
            expr_clock = expr2_clock } 
          when 
            T.check_type expr1_type expr2_type || 
            T.check_type expr2_type expr1_type ->

          mk_binary Gt expr1 expr2 T.t_bool expr1_clock expr2_clock

        | _ -> raise Type_mismatch)


(* ->: 'a -> 'a -> 'a 

   Either the first type is a subtype of the second or vice versa,
   choose the greater type for the resulting type *)
let mk_arrow = function

  | { expr = expr1; expr_type = expr1_type; expr_clock = expr1_clock } ->

    (function 

      | { expr = expr2; 
          expr_type = expr2_type; 
          expr_clock = expr2_clock } 
        when 
          T.check_type expr1_type expr2_type ->

        mk_binary Gt expr1 expr2 expr2_type expr1_clock expr2_clock

      | { expr = expr2; 
          expr_type = expr2_type; 
          expr_clock = expr2_clock } 
        when 
          T.check_type expr2_type expr1_type ->

        mk_binary Gt expr1 expr2 expr1_type expr1_clock expr2_clock

      | _ -> raise Type_mismatch)


(* ite: bool -> 'a -> 'a -> 'a 

   Either the second type is a subtype of the third or vice versa,
   choose the greater type for the resulting type *)
let mk_ite = function

  | { expr = expr1; expr_type = T.Bool; expr_clock = expr1_clock } ->

    (function 

      | { expr = expr2; 
          expr_type = expr2_type; 
          expr_clock = expr2_clock } -> 

        (function 

          (* Type of second argument is subtype of third argument *)
            | { expr = expr3; 
                expr_type = expr3_type; 
                expr_clock = expr3_clock } 
              when 
                T.check_type expr2_type expr3_type ->

              (* All clocks identical? *)
              if clock_check expr1_clock expr2_clock && 
                 clock_check expr2_clock expr3_clock then

                (* Use type of third arguement *)
                { expr = Ite (expr1, expr2, expr3);
                  expr_type = expr3_type;
                  expr_clock = expr1_clock } 
                
              else
                
                raise Clock_mismatch

            (* Type of third argument is subtype of second argument *)
            | { expr = expr3; 
                expr_type = expr3_type; 
                expr_clock = expr3_clock } 
              when 
                T.check_type expr3_type expr2_type ->

              if clock_check expr1_clock expr2_clock && 
                 clock_check expr2_clock expr3_clock then

                (* Use type of second arguement *)
                { expr = Ite (expr1, expr2, expr3);
                  expr_type = expr2_type;
                  expr_clock = expr1_clock } 
                
              else
                
                raise Clock_mismatch

            | _ -> raise Type_mismatch))

    | _ -> raise Type_mismatch


(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
