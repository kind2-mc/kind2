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
  | IntRange of (Numeral.t * Numeral.t)
  | FreeType of I.t
  | Enum of I.t list


(* Lexicographic comparison of pairs *)
let compare_int_range (al, au) (bl, bu) = 

  match Numeral.compare al bl with

    (* First elements are equal: compare second elements *)
    | 0 -> Numeral.compare au bu
      
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
let pp_print_lustre_type safe ppf = function   
  | Bool -> Format.fprintf ppf "bool"
  | Int -> Format.fprintf ppf "int"
  | Real -> Format.fprintf ppf "real"

  | IntRange (i, j) -> 
    Format.fprintf ppf 
      "subrange [%a,%a] of int" 
      Numeral.pp_print_numeral i 
      Numeral.pp_print_numeral j

  | FreeType t -> Format.fprintf ppf "%a" (I.pp_print_ident safe) t
  | Enum l ->     
    Format.fprintf ppf 
      "enum @[<hv 2>{ %a }@]" 
      (pp_print_list (I.pp_print_ident safe) ",@ ") l


let t_bool = Bool

let t_int = Int

let t_real = Real

let mk_int_range i j = IntRange Numeral.(min i j, max i j)

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
  | IntRange (l1, u1), IntRange (l2, u2) 
    when Numeral.(l1 >= l2) && Numeral.(u1 <= u2) -> true

  (* Enum types are subtypes if the sets of elements are subsets *)
  | Enum l1, Enum l2 -> 

    List.for_all
      (function e -> List.mem e l2)
      l1

  (* Free types are subtypes if identifiers match *)
  | FreeType i1, FreeType i2 when I.equal i1 i2 -> true

  (* No other subtype relationships *)
  | _ -> false



(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
