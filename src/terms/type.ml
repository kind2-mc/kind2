(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

(* We need to hashcons types, since the type occurs in a term,
   which is hashconsed. We need to make sure that equality of all
   subterms in a hashconsed type is physical. *)

(* ********************************************************************* *)
(* Types and hash-consing                                                *)
(* ********************************************************************* *)

(* Tells if the range actually encodes an enumerated datatype *)
type rangekind = Range | Enum

(* Type of an expression in KIND *)
type kindtype = 
  | Bool
  | Int
  | IntRange of Numeral.t * Numeral.t * rangekind
  | Real
  | UBV of int
  | BV of int
  (* First is element type, second is index type, and third is the size *)
  | Array of t * t
  | Abstr of string

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
  let rec equal t1 t2 = match t1, t2 with 
    | Bool, Bool -> true
    | Bool, _ -> false
    | Int, Int -> true
    | Int, _ -> false    
    | IntRange (l1, u1, k1), IntRange (l2, u2, k2) ->
      k1 = k2 && Numeral.equal l1 l2 && Numeral.equal u1 u2 
    | IntRange _, _ -> false
    | Real, Real -> true
    | Real, _ -> false
    | UBV i, UBV j -> i = j
    | UBV i, _ -> false
    | BV i, BV j -> i = j
    | BV i, _ -> false
    | Array (i1, t1), Array (i2, t2) -> (i1 == i2) && (t1 == t2)
    | Array (_, _), _ -> false
    | Abstr s1, Abstr s2 -> s1 = s2
    | Abstr _, _ -> false
      
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

  | IntRange (i, j, Range) -> 

    Format.fprintf
      ppf 
      "(IntRange %a %a)" 
      Numeral.pp_print_numeral i 
      Numeral.pp_print_numeral j

  | IntRange (i, j, Enum) -> 

    Format.fprintf
      ppf 
      "(Enum %a %a)" 
      Numeral.pp_print_numeral i 
      Numeral.pp_print_numeral j

  | Real -> Format.pp_print_string ppf "Real"

  | UBV i -> 

    Format.fprintf
      ppf 
      "(_ BitVec %d)" 
      i 

  | BV i -> 

    Format.fprintf
      ppf 
      "(_ BitVec %d)" 
      i

  | Array (s, t) -> 
    Format.fprintf
      ppf 
      "(Array %a %a)"
      pp_print_type s 
      pp_print_type t

  | Abstr s -> Format.pp_print_string ppf s


(* Pretty-print a hashconsed variable *)
and pp_print_type ppf { Hashcons.node = t } = pp_print_type_node ppf t

let print_type = pp_print_type Format.std_formatter

(* Return a string representation of a type *)
let string_of_type t = string_of_t pp_print_type t


(* ********************************************************************* *)
(* DEBUGGING Pretty-printing                                             *)
(* ********************************************************************* *)

(* Pretty-print a type *)
let rec pp_print_type_node2 ppf = function 

  | Bool -> Format.pp_print_string ppf "Bool"

  | Int -> Format.pp_print_string ppf "Int"

  | IntRange (i, j, Range) -> 

    Format.fprintf
      ppf 
      "(IntRange %a %a)" 
      Numeral.pp_print_numeral i 
      Numeral.pp_print_numeral j

  | IntRange (i, j, Enum) -> 

    Format.fprintf
      ppf 
      "(Enum %a %a)" 
      Numeral.pp_print_numeral i 
      Numeral.pp_print_numeral j

  | Real -> Format.pp_print_string ppf "Real"

  | UBV i -> 

    Format.fprintf
      ppf 
      "uint%d" 
      i 

  | BV i -> 

    Format.fprintf
      ppf 
      "int%d" 
      i

  | Array (s, t) -> 
    Format.fprintf
      ppf 
      "(Array %a %a)"
      pp_print_type s 
      pp_print_type t

  | Abstr s -> Format.pp_print_string ppf s


(* Pretty-print a hashconsed variable *)
and pp_print_type2 ppf { Hashcons.node = t } = pp_print_type_node2 ppf t

let print_type2 = pp_print_type2 Format.std_formatter

(* Return a string representation of a type *)
let string_of_type2 t = string_of_t pp_print_type2 t


(* ********************************************************************* *)
(* Constructors                                                          *)
(* ********************************************************************* *)


(* Return a hashconsed type *)
let mk_type t = Hkindtype.hashcons ht t ()

let mk_bool () = Hkindtype.hashcons ht Bool ()

let mk_int () = Hkindtype.hashcons ht Int ()

let mk_int_range l u = Hkindtype.hashcons ht (IntRange (l, u, Range)) ()

let mk_real () = Hkindtype.hashcons ht Real ()

let mk_ubv w = Hkindtype.hashcons ht (UBV w) ()

let mk_bv w = Hkindtype.hashcons ht (BV w) ()

let mk_array i t = Hkindtype.hashcons ht (Array (i, t)) ()

let mk_abstr s = Hkindtype.hashcons ht (Abstr s) ()


module HNum = Hashtbl.Make (struct
    type t = Numeral.t
    let equal = Numeral.equal
    let hash = Hashtbl.hash
  end)
    

(* Table from constructors to name if any and encoding to ranges *)
let enums_table = Hashtbl.create 7
(* Table from numeral encoding to a constructor and its type *)
let num_enums = HNum.create 17
(* Talbe from constructors to their numeral encoding *)
let constr_nums = Hashtbl.create 7

let mk_enum =
  let next_n = ref 0 in
  fun name cs ->
    try Hashtbl.find enums_table cs |> snd
    with Not_found ->
      let size = List.length cs in
      let n = !next_n in
      let l, u = Numeral.of_int n, Numeral.of_int (n + size - 1) in
      let range = Hkindtype.hashcons ht (IntRange (l, u, Enum)) () in
      List.iteri (fun i c ->
          let nu = Numeral.of_int (n + i) in
          HNum.add num_enums nu (c, cs, range);
          Hashtbl.add constr_nums c nu;
        ) cs;
      Hashtbl.add enums_table cs (name, range);
      next_n := n + size;
      range


let get_constr_of_num n =
  let c, _, _ = HNum.find num_enums n in c

let get_enum_range_of_num n =
  let _, _, r = HNum.find num_enums n in r

let get_constrs_of_num n =
  let _, cs, _ = HNum.find num_enums n in cs

let get_num_of_constr c = Hashtbl.find constr_nums c

let get_enum_range_of_constrs cs = Hashtbl.find enums_table cs |> snd

let get_enum_name_of_constrs cs = Hashtbl.find enums_table cs |> fst

let enum_of_constr c =
  get_num_of_constr c |> get_enum_range_of_num

let get_enum_name_of_num n =
  get_constrs_of_num n |> get_enum_name_of_constrs


(* Import a type from a different instance into this hashcons table *)
let rec import { Hashcons.node = n } = match n with 
  (* Import leaf types directly *)
  | Bool
  | Int
  | IntRange _
  | UBV _
  | BV _ 
  | Real as t -> mk_type t


  (* Import index and value types of array type *)
  | Array (i, t) -> mk_array (import i) (import t)

  | Abstr s -> mk_abstr s


(* Static values *)
let t_bool = mk_bool ()
let t_int = mk_int ()
let t_ubv w = mk_ubv w
let t_bv w = mk_bv w
let t_real = mk_real ()


let get_all_abstr_types () =
  Hkindtype.fold (fun ty acc -> match ty with
      | { Hashcons.node = Abstr _ } -> ty :: acc
      | _ -> acc) ht []
  |> List.rev



(* ********************************************************************* *)
(* Predicates                                                            *)
(* ********************************************************************* *)


let rec is_int { Hashcons.node = t } = match t with
  | Int -> true 
  | Array (t, _) -> false (* is_int t *)
  | _-> false

let rec is_int_range { Hashcons.node = t } = match t with
  | IntRange (_,_,Range) -> true 
  | Array (t, _) -> false (* is_int_range t *)
  |  _ -> false

let rec is_ubitvector { Hashcons.node = t } = match t with
  | UBV _ -> true
  | _ -> false

let rec is_bitvector { Hashcons.node = t } = match t with
  | BV _ -> true
  | _ -> false

let bitvectorsize { Hashcons.node = t } = match t with
  | UBV n -> n
  | BV n -> n
  | _ -> 0
  
let rec is_uint8 { Hashcons.node = t } = match t with
  | UBV 8 -> true 
  | _-> false

let rec is_uint16 { Hashcons.node = t } = match t with
  | UBV 16 -> true 
  | _-> false

let rec is_uint32 { Hashcons.node = t } = match t with
  | UBV 32 -> true 
  | _-> false

let rec is_uint64 { Hashcons.node = t } = match t with
  | UBV 64 -> true 
  | _-> false

let rec is_int8 { Hashcons.node = t } = match t with
  | BV 8 -> true 
  | _-> false

let rec is_int16 { Hashcons.node = t } = match t with
  | BV 16 -> true 
  | _-> false

let rec is_int32 { Hashcons.node = t } = match t with
  | BV 32 -> true 
  | _-> false

let rec is_int64 { Hashcons.node = t } = match t with
  | BV 64 -> true 
  | _-> false

let rec is_enum { Hashcons.node = t } = match t with
  | IntRange (_,_,Enum) -> true 
  |  _ -> false

let rec is_bool { Hashcons.node = t } = match t with
  | Bool -> true
  | Array (t, _) -> false (* is_bool t *)
  |  _ -> false

let rec is_real { Hashcons.node = t } = match t with
  | Real -> true
  | Array (t, _) -> false (* is_real t *)
  | _ -> false


let is_abstr { Hashcons.node = t } = match t with
  | Abstr _ -> true
  | _ -> false


let is_array { Hashcons.node = t } = match t with
  | Array _ -> true
  | _ -> false

(* let rec is_scalar { Hashcons.node = t } = match t with *)
(*   | Scalar _ -> true *)
(*   | Array (_, t) -> is_scalar t *)
(*   | _ -> false *)



(* Return bounds of an integer range type *)
let bounds_of_int_range = function
  | { Hashcons.node = IntRange (l, u, _) } -> (l, u)
  | _ -> raise (Invalid_argument "bounds_of_int_range")

(* Return type of array index *)
let index_type_of_array = function 
  | { Hashcons.node = Array (_, i) } -> i
  | _ -> raise (Invalid_argument "index_type_of_array")

(* Return all index types of nested array type *)
let rec all_index_types_of_array' accum = function 
  | { Hashcons.node = Array (e, i) } -> all_index_types_of_array' (i :: accum) e
  | _ -> List.rev accum 

let all_index_types_of_array = all_index_types_of_array' []

(* Return type of array elements *)
let elem_type_of_array = function 
  | { Hashcons.node = Array (e, _) } -> e
  | _ -> raise (Invalid_argument "elem_type_of_array")


(* Return element of nested array type *)
let rec last_elem_type_of_array = function 
  | { Hashcons.node = Array (e,_) } when is_array e -> last_elem_type_of_array e
  | { Hashcons.node = Array (e,_) } -> e
  | _ -> assert false


let constructors_of_enum = function
  | { Hashcons.node = IntRange (l, _, Enum) } ->
    (try get_constrs_of_num l
     with Not_found -> raise (Invalid_argument "constructors_of_enum"))
  | _ -> raise (Invalid_argument "constructors_of_enum")


let name_of_enum = function
  | { Hashcons.node = IntRange (l, _, Enum) } ->
    (try get_enum_name_of_num l
     with Not_found -> raise (Invalid_argument "constructors_of_enum"))
  | _ -> raise (Invalid_argument "constructors_of_enum")


(* ********************************************************************* *)
(* Type checking                                                         *)
(* ********************************************************************* *)


(* Check if [t1] is a subtype of [t2] *)
let rec check_type  { Hashcons.node = t1 }  { Hashcons.node = t2 } = 
  
  match t1, t2 with 

    (* Types are identical *)
    | Int, Int
    | Real, Real
    | Bool, Bool -> true

    | UBV i, UBV j -> i = j
    
    | BV i, BV j -> i = j
    
    | Abstr s1, Abstr s2 -> s1 = s2
      
    (* IntRange is a subtype of Int *)
    | IntRange _, Int -> true

    (* IntRange is subtype of IntRange if the interval is a subset *)
    | IntRange (l1, u1, k1), IntRange (l2, u2, k2) ->
      k1 = k2 && Numeral.(l1 >= l2) && Numeral.(u1 <= u2)

    (* Array is a subtype of array if both index type and element type
       are subtype *)
    | Array (i1, t1), Array (i2, t2) ->
      (check_type i1 i2) (* && (check_type t2 t1) *)

    (* No other subtype relationships *)
    | _ -> false


let rec generalize t = match node_of_type t with
  | IntRange (_,_,Range) -> t_int
  | Array (e, i) -> mk_array (generalize e) (generalize i)
  | _ -> t




(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
