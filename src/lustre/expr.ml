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


let listmin = List.fold_left min max_int
let listmax = List.fold_left max min_int

exception Type_error

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
  | Ident of Ident.t
  | True
  | False
  | UnaryOp of unary_op * expr
  | BinaryOp of binary_op * (expr * expr)
  | Ite of expr * expr * expr
  | Pre of Ident.t


type t =
  { 

    clock: Ident.t;

    ltype: Type.t;

    expr: expr;

  }


let type_of_unary_expr = function 

  (* Bool -> Bool *)
  | Not -> 

    (function 
      | Type.Bool -> Type.bool
      | _ -> raise Type_error)

  (* Int -> Int *)
  (* Real -> Real *)
  (* IntRange (i, j) -> IntRange (-j,-i) *)
  | Uminus -> 

    (function 
      | Type.Int -> Type.int
      | Type.Real -> Type.real
      | Type.IntRange (i, j) -> Type.mk_int_range (-j) (-i)
      | _ -> raise Type_error)


let int_range_of_binary_op op (a, b) (c, d) = match op with 
  
  (* [a,b] mod [c,d] = [0, *)
  | Mod -> Type.mk_int_range (min 0 d) (max 0 d)

  (*  *)
  | IntDiv -> 

    (match c < 0, d < 0 with
      
      (* c and d positive *)
      | false, false -> Type.mk_int_range (min 0 a) (max 0 b)

      (* c and d negative *)
      | true, true -> Type.mk_int_range (min 0 (-b)) (max 0 (-a))

      (* c negative and d positive *)
      | true, false 
      | false, true -> 

        let m = max (abs a) (abs b) in 
        Type.mk_int_range (-m) m

    )

  (* [a,b] + [c,d] = [a+c, b+d] *)
  | Plus -> Type.mk_int_range (a + c) (b + d)

  (* [a,b] - [c,d] = [a-d, b-c] *)
  | Minus -> Type.mk_int_range (a - d) (b - c)

  (* Take the minimum and maximum of all pairs *)
  | Times -> 
    Type.mk_int_range
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
      | Type.Bool, Type.Bool -> Type.bool
      | _ -> raise Type_error)

  (* Int -> Int -> Int *)
  | Mod
  | IntDiv as op -> 

    (function 

      | Type.Int, Type.Int
      | Type.Int, Type.IntRange _
      | Type.IntRange _, Type.Int -> Type.int

      | Type.IntRange r1, 
        Type.IntRange r2 -> 

        int_range_of_binary_op op r1 r2

      | _ -> raise Type_error)


  (* Real -> Real -> Real *)
  | Div ->

    (function 

      | Type.Real, Type.Real -> Type.real

      | _ -> raise Type_error)


  (* Int -> Int -> Int *)
  (* Real -> Real -> Real *)
  | Minus
  | Plus 
  | Times as op -> 

    (function 

      | Type.Int, Type.Int
      | Type.Int, Type.IntRange _
      | Type.IntRange _, Type.Int -> Type.int

      | Type.IntRange r1, 
        Type.IntRange r2 -> 
       
        int_range_of_binary_op op r1 r2

      | Type.Real, Type.Real -> Type.real

      | _ -> raise Type_error)
 

  (* Bool -> Bool -> Bool *)
  (* Int -> Int -> Bool *)
  (* Real -> Real -> Bool *)
  | Eq
  | Neq ->

    (function 
      | Type.Bool, Type.Bool  -> Type.bool

      | Type.Int, Type.Int
      | Type.IntRange _, Type.Int
      | Type.Int, Type.IntRange _
      | Type.IntRange _, Type.IntRange _  -> Type.bool

      | Type.Real, Type.Real -> Type.bool

      | _ -> raise Type_error)
 

  (* Int -> Int -> Bool *)
  (* Real -> Real -> Bool *)
  | Lte
  | Lt
  | Gte
  | Gt ->

    (function 

      | Type.Int, Type.Int
      | Type.IntRange _, Type.Int
      | Type.Int, Type.IntRange _
      | Type.IntRange _, Type.IntRange _ -> Type.bool

      | Type.Real, Type.Real -> Type.bool

      | _ -> raise Type_error)
 

  (* 'a -> 'a -> 'a *)
  | Arrow -> 

    (function 

      | Type.Int, Type.Int 
      | Type.IntRange _, Type.Int
      | Type.Int, Type.IntRange _ -> Type.int

      | Type.IntRange (i1, j1), 
        Type.IntRange (i2, j2) -> 

        Type.mk_int_range (min i1 i2) (max j1 j2)

      | Type.Real, Type.Real -> Type.real

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

(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
