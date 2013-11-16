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

(*
let listmin = List.fold_left min max_int
let listmax = List.fold_left max min_int

exception Type_error

*)

type unary_op =
  | Not
  | Uminus

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

type var_op =
  | OneHot

type expr =
  | Ident of I.t
  | Pre of I.t
  | True
  | False
  | Int of int
  | Real of float
  | UnaryOp of unary_op * expr
  | BinaryOp of binary_op * (expr * expr)
  | Ite of expr * expr * expr


type t = expr
(*
  { 

    clock: I.t;

    ltype: T.t;

    expr: expr;

  }
*)

let t_true = True

let t_false = False

let mk_int n = Int n

let mk_real r = Real r

let mk_ident n = Ident n

let mk_pre n = Pre n

let mk_unary op e = UnaryOp (op, e)

let mk_not = mk_unary Not 

let mk_uminus = mk_unary Uminus

let mk_binary op e1 e2 = BinaryOp (op, (e1, e2))

let mk_and = mk_binary And 

let mk_or = mk_binary Or

let mk_xor = mk_binary Xor

let mk_impl = mk_binary Impl

let mk_mod = mk_binary Mod

let mk_minus = mk_binary Minus

let mk_plus = mk_binary Plus 

let mk_div = mk_binary Div

let mk_times = mk_binary Times 

let mk_intdiv = mk_binary IntDiv

let mk_eq = mk_binary Eq

let mk_neq = mk_binary Neq

let mk_lte = mk_binary Lte

let mk_lt = mk_binary Lt

let mk_gte = mk_binary Gte

let mk_gt = mk_binary Gt

let mk_arraw = mk_binary Arrow

let mk_ite p e1 e2 = Ite (p, e1, e2)

(*


let type_of_unary_expr = function 

  (* Bool -> Bool *)
  | Not -> 

    (function 
      | T.Bool -> T.bool
      | _ -> raise Type_error)

  (* Int -> Int *)
  (* Real -> Real *)
  (* IntRange (i, j) -> IntRange (-j,-i) *)
  | Uminus -> 

    (function 
      | T.Int -> T.int
      | T.Real -> T.real
      | T.IntRange (i, j) -> T.mk_int_range (-j) (-i)
      | _ -> raise Type_error)


let int_range_of_binary_op op (a, b) (c, d) = match op with 
  
  (* [a,b] mod [c,d] = [0, *)
  | Mod -> T.mk_int_range (min 0 d) (max 0 d)

  (*  *)
  | IntDiv -> 

    (match c < 0, d < 0 with
      
      (* c and d positive *)
      | false, false -> T.mk_int_range (min 0 a) (max 0 b)

      (* c and d negative *)
      | true, true -> T.mk_int_range (min 0 (-b)) (max 0 (-a))

      (* c negative and d positive *)
      | true, false 
      | false, true -> 

        let m = max (abs a) (abs b) in 
        T.mk_int_range (-m) m

    )

  (* [a,b] + [c,d] = [a+c, b+d] *)
  | Plus -> T.mk_int_range (a + c) (b + d)

  (* [a,b] - [c,d] = [a-d, b-c] *)
  | Minus -> T.mk_int_range (a - d) (b - c)

  (* Take the minimum and maximum of all pairs *)
  | Times -> 
    T.mk_int_range
      (listmin [a*c; a*d; b*c; b*d])
      (listmax [a*c; a*d; b*c; b*d])

  | _ -> assert false


let type_of_binary_expr = function

  (* Bool -> Bool -> Bool *)
  | And
  | Or
  | Xor
  | Impl -> 

    (function 
      | T.Bool, T.Bool -> T.bool
      | _ -> raise Type_error)

  (* Int -> Int -> Int *)
  | Mod
  | IntDiv as op -> 

    (function 

      | T.Int, T.Int
      | T.Int, T.IntRange _
      | T.IntRange _, T.Int -> T.int

      | T.IntRange r1, 
        T.IntRange r2 -> 

        int_range_of_binary_op op r1 r2

      | _ -> raise Type_error)


  (* Real -> Real -> Real *)
  | Div ->

    (function 

      | T.Real, T.Real -> T.real

      | _ -> raise Type_error)


  (* Int -> Int -> Int *)
  (* Real -> Real -> Real *)
  | Minus
  | Plus 
  | Times as op -> 

    (function 

      | T.Int, T.Int
      | T.Int, T.IntRange _
      | T.IntRange _, T.Int -> T.int

      | T.IntRange r1, 
        T.IntRange r2 -> 
       
        int_range_of_binary_op op r1 r2

      | T.Real, T.Real -> T.real

      | _ -> raise Type_error)
 

  (* Bool -> Bool -> Bool *)
  (* Int -> Int -> Bool *)
  (* Real -> Real -> Bool *)
  | Eq
  | Neq ->

    (function 
      | T.Bool, T.Bool  -> T.bool

      | T.Int, T.Int
      | T.IntRange _, T.Int
      | T.Int, T.IntRange _
      | T.IntRange _, T.IntRange _  -> T.bool

      | T.Real, T.Real -> T.bool

      | _ -> raise Type_error)
 

  (* Int -> Int -> Bool *)
  (* Real -> Real -> Bool *)
  | Lte
  | Lt
  | Gte
  | Gt ->

    (function 

      | T.Int, T.Int
      | T.IntRange _, T.Int
      | T.Int, T.IntRange _
      | T.IntRange _, T.IntRange _ -> T.bool

      | T.Real, T.Real -> T.bool

      | _ -> raise Type_error)
 

  (* 'a -> 'a -> 'a *)
  | Arrow -> 

    (function 

      | T.Int, T.Int 
      | T.IntRange _, T.Int
      | T.Int, T.IntRange _ -> T.int

      | T.IntRange (i1, j1), 
        T.IntRange (i2, j2) -> 

        T.mk_int_range (min i1 i2) (max j1 j2)

      | T.Real, T.Real -> T.real

      | _ -> raise Type_error)


let clock_of_unary_expr op clock = 

  match op with 
    | Not -> clock
    | Uminus -> clock

let clock_of_binary_expr op (clock, _)  = 

  match op with 
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
    | Arrow -> clock


let mk_unary_expr op { ltype = t; clock = c; expr = e } = 

  let t' = type_of_unary_expr op t in

  let c' = clock_of_unary_expr op c in 

  let e' = UnaryOp (op, e) in

  { clock = c'; ltype = t'; expr = e' }


let mk_binary_expr 
    op 
    { ltype = t1; clock = c1; expr = e1}  
    { ltype = t2; clock = c2; expr = e2} =

  let t' = type_of_binary_expr op (t1, t2) in

  let c' = clock_of_binary_expr op (c1, c2) in 

  let e' = BinaryOp (op, (e1, e2)) in

  { clock = c'; ltype = t'; expr = e' }

*)

(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
