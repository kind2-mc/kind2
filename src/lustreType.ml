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

module I = LustreIdent

module IdentSet = Set.Make (I)

(* ********************************************************************** *)
(* Types                                                                  *)
(* ********************************************************************** *)

(* A type *)
type t = 
  | Bool
  | Int
  | Real
  | IntRange of (int * int)
  | FreeType of I.t
  | Enum of I.t list


(* Lexicographic comparison of pairs *)
let compare_int_range (al, au) (bl, bu) = 

  match compare al bl with

    (* First elements are equal: compare second elements *)
    | 0 -> compare au bu
      
    (* Return order of first elements *)
    | c -> c


(* Compare lists of identifiers as sets *)
let compare_enum a b = 

  (* Set of identifiers in a *)
  let a_set = 
    List.fold_left (fun a i -> IdentSet.add i a)  IdentSet.empty a
  in

  (* Set of identifiers in b *)
  let b_set = 
    List.fold_left (fun a i -> IdentSet.add i a)  IdentSet.empty b
  in

  (* Return true if e and f contain the same identifiers *)
  IdentSet.compare a_set b_set
  

(* Compare types *)
let compare s t = match s, t with 

  | Bool, Bool -> 0
  | Bool, Int
  | Bool, Real
  | Bool, IntRange _
  | Bool, FreeType _
  | Bool, Enum _ -> -1 

  | Int, Bool -> 1
  | Int, Int -> 0
  | Int, Real
  | Int, IntRange _
  | Int, FreeType _
  | Int, Enum _ -> -1

  | Real, Bool 
  | Real, Int -> 1
  | Real, Real -> 0
  | Real, IntRange _
  | Real, FreeType _
  | Real, Enum _ -> -1 

  | IntRange _, Bool
  | IntRange _, Int 
  | IntRange _, Real -> 1
  | IntRange a, IntRange b -> compare_int_range a b
  | IntRange _, FreeType _ 
  | IntRange _, Enum _ -> -1

  | FreeType _, Bool
  | FreeType _, Int
  | FreeType _, Real
  | FreeType _, IntRange _ -> 1
  | FreeType a, FreeType b -> compare a b
  | FreeType _, Enum _-> -1

  | Enum _, Bool
  | Enum _, Int
  | Enum _, Real
  | Enum _, IntRange _
  | Enum _, FreeType _ -> 1
  | Enum a, Enum b -> compare_enum a b

    
(* Reduce equality to comparision *)
let equal a b = compare a b = 0


(* Pretty-print a type *)
let pp_print_lustre_type ppf = function   
  | Bool -> Format.fprintf ppf "bool"
  | Int -> Format.fprintf ppf "int"
  | Real -> Format.fprintf ppf "real"
  | IntRange (i, j) -> Format.fprintf ppf "subrange [%d,%d] of int" i j
  | FreeType t -> Format.fprintf ppf "%a" I.pp_print_ident t
  | Enum l ->     
    Format.fprintf ppf 
      "enum @[<hv 2>{ %a }@]" 
      (pp_print_list I.pp_print_ident ",@ ") l


let t_bool = Bool

let t_int = Int

let t_real = Real

let mk_int_range i j = IntRange (min i j, max i j)

let mk_free_type t = FreeType t

let mk_enum l = Enum l

(* Check if [t1] is a subtype of [t2] *)
let rec check_type t1 t2 = match t1, t2 with 

  (* Types are identical *)
  | Int, Int
  | Real, Real
  | Bool, Bool -> true

  (* IntRange is a subtype of Int *)
  | IntRange _, Int -> true

  (* IntRange is subtype of IntRange if the interval is a subset *)
  | IntRange (l1, u1), IntRange (l2, u2) when l1 >= l2 && u1 <= u2 -> true

  (* Enum types are subtypes if the sets of elements are subsets *)
  | Enum l1, Enum l2 -> 

    List.for_all
      (function e -> List.mem e l2)
      l1

  (* Free types are subtypes if identifiers match *)
  | FreeType i1, FreeType i2 when i1 = i2 -> true

  (* No other subtype relationships *)
  | _ -> false



(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
