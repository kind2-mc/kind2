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

(* We need to hashcons types, since the type occurs in a hoasTerm,
   which is hashconsed. We need to make sure that equality of all
   subterms in a hashconsed type is physical. *)

(* ********************************************************************* *)
(* Types and hash-consing                                                *)
(* ********************************************************************* *)


(* Type of an expression in KIND *)
type kindtype = 
  | Bool
  | Int
  | IntRange of Numeral.t * Numeral.t
  | Real
  | BV of int
  | Array of t * t


(* A private type that cannot be constructed outside this module

   This is necessary to ensure the invariant that all subterms of a
   term are hashconsed. We can construct and thus pattern match on the
   {!kindtype} type, but not on the {!kindtype_node} type *)
and kindtype_node = kindtype


(* Properties of a type

   Only keep essential properties here that are shared by all
   modules. For local properties use a hashtable in the respective
   module. 

   No properties for now. *)
and kindtype_prop = unit


(* Hashconsed type *) 
and t = (kindtype_node, kindtype_prop) Hashcons.hash_consed


(* Hashing and equality on uninterpreted symbols *) 
module Kindtype_node = struct 

  (* Type node *)
  type t = kindtype_node

  (* Properties of type *)
  type prop = kindtype_prop

  (* Hashing for types *)
  let hash = Hashtbl.hash 

  (* Equality of types *)
  let equal = (=)

end


(* Hashconsed types *)
module Hkindtype = Hashcons.Make (Kindtype_node)


(* Storage for uninterpreted function symbols *)
let ht = Hkindtype.create 7


(* Return the node of a type *)
let node_of_type { Hashcons.node = s } = s


(* ********************************************************************* *)
(* Hashtables, maps and sets                                             *)
(* ********************************************************************* *)


(* Comparison function on types *)
let compare_types = Hashcons.compare

(* Equality function on types *)
let equal_types = Hashcons.equal 

(* Hashing function on types *)
let hash_type = Hashcons.hash 


(* Module as input to functors *)
module HashedType = struct 

  (* Dummy type to prevent writing [type t = t] which is cyclic *)
  type z = t
  type t = z

  (* Compare tags of hashconsed symbols for equality *)
  let equal = equal_types
    
  (* Use hash of symbol *)
  let hash = hash_type

end

(* Module as input to functors *)
module OrderedType = struct 

  (* Dummy type to prevent writing [type t = t] which is cyclic *)
  type z = t
  type t = z

  (* Compare tags of hashconsed symbols *)
  let compare = compare_types

end

(* Hashtable of symbols *)
module TypeHashtbl = Hashtbl.Make (HashedType)

(* Set of symbols

   Try to turn this into a patricia set with Hset for another small
   gain in efficiency. *)
module TypeSet = Set.Make (OrderedType)


(* Map of symbols

   Try to turn this into a patricia set with Hset for another small
   gain in efficiency. *)
module TypeMap = Map.Make (OrderedType)


(* ********************************************************************* *)
(* Pretty-printing                                                       *)
(* ********************************************************************* *)


(* Pretty-print a type *)
let rec pp_print_type_node ppf = function 

  | Bool -> Format.pp_print_string ppf "Bool"

  | Int -> Format.pp_print_string ppf "Int"

  | IntRange (i, j) -> 
    Format.fprintf
      ppf 
      "IntRange %a %a" 
      Numeral.pp_print_numeral i 
      Numeral.pp_print_numeral j

  | Real -> Format.pp_print_string ppf "Real"

  | BV i -> 
    Format.fprintf
      ppf 
      "BitVec %d" 
      i 

  | Array (s, t) -> 
    Format.fprintf
      ppf 
      "Array %a %a" 
      pp_print_type s 
      pp_print_type t


(* Pretty-print a hashconsed variable *)
and pp_print_type ppf { Hashcons.node = t } = pp_print_type_node ppf t


(* Return a string representation of a type *)
let string_of_type t = string_of_t pp_print_type t


(* ********************************************************************* *)
(* Constructors                                                          *)
(* ********************************************************************* *)


(* Return a hashconsed type *)
let mk_type t = Hkindtype.hashcons ht t ()

let mk_bool () = Hkindtype.hashcons ht Bool ()

let mk_int () = Hkindtype.hashcons ht Int ()

let mk_int_range l u = Hkindtype.hashcons ht (IntRange (l, u)) ()

let mk_real () = Hkindtype.hashcons ht Real ()

let mk_bv w = Hkindtype.hashcons ht (BV w) ()

let mk_array i t = Hkindtype.hashcons ht (Array (i, t)) ()


(* Import a type from a different instance into this hashcons table *)
let rec import { Hashcons.node = n } = match n with 

  (* Import leaf types directly *)
  | Bool
  | Int
  | IntRange _
  | Real
  | BV _ as t -> mk_type t

  (* Import index and value types of array type *)
  | Array (i, t) -> mk_array (import i) (import t)


(* Static values *)
let t_bool = mk_bool ()
let t_int = mk_int ()
let t_real = mk_real ()


(* ********************************************************************* *)
(* Predicates                                                            *)
(* ********************************************************************* *)


let is_int { Hashcons.node = t } = match t with
  | Int
  | IntRange _ -> true 
  | Bool 
  | Real
  | BV _
  | Array _ -> false

let is_bool { Hashcons.node = t } = match t with
  | Bool -> true
  | Int
  | IntRange _
  | Real
  | BV _
  | Array _ -> false

let is_real { Hashcons.node = t } = match t with
  | Real -> true
  | BV _
  | Array _
  | Bool
  | Int
  | IntRange _ -> false

let is_bv { Hashcons.node = t } = match t with
  | BV _ -> true
  | Bool
  | Int
  | IntRange _
  | Real
  | Array _ -> false

let is_array { Hashcons.node = t } = match t with
  | Array _ -> true
  | Bool
  | Int
  | IntRange _
  | Real
  | BV _ -> true



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
