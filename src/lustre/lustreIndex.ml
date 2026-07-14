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

module I = LustreIdent
module E = LustreExpr

open Lib

(* ********************************************************************** *)
(* Indexes                                                                *)
(* ********************************************************************** *)

(* A single index entry *)
type one_index = 

  (* Record field *)
  | RecordIndex of string

  (* Tuple field *)
  | TupleIndex of int

  (* List element *)
  | ListIndex of int

  (* Array field indexed by integer *)
  | ArrayIntIndex of int

  (* Array field indexed by variable *)
  | ArrayVarIndex of E.expr

  | SetMapIndex of E.expr 

  (* Index to the representation field of an abstract type *)
  | AbstractTypeIndex of string

  (* Discriminant field of a desugared ADT; string is the ADT type name *)
  | AdtTagIndex of string

  (* Payload field of a desugared ADT; ctor name and field position *)
  | AdtPayloadIndex of string * int


(* Pretty-print a single index *)
let pp_print_one_index' db = function 
  
  | false ->

    (function ppf -> function 
       | RecordIndex _ -> ()
       | TupleIndex i -> Format.fprintf ppf "(%d)" i
       | ListIndex i -> Format.fprintf ppf "{%d}" i
       | ArrayIntIndex i -> Format.fprintf ppf "[%d]" i
       | ArrayVarIndex _ -> () (* Format.fprintf ppf "[X%d(%a)]" db (E.pp_print_expr false) v ) *)
       | SetMapIndex _ -> ()
       | AbstractTypeIndex _ -> ()
       | AdtTagIndex _ -> ()
       | AdtPayloadIndex _ -> ())

  | true ->

    (function ppf -> function 
       | RecordIndex i -> Format.fprintf ppf ".%s" i
       | TupleIndex i -> Format.fprintf ppf "_%d" i
       | ListIndex i -> Format.fprintf ppf "_%d" i
       | ArrayIntIndex i -> Format.fprintf ppf "_%d" i
       | ArrayVarIndex _ ->  Format.fprintf ppf "_X%d" db
       | SetMapIndex _ ->  Format.fprintf ppf "_Y%d" db
       | AbstractTypeIndex i -> Format.fprintf ppf ".%s" i
       | AdtTagIndex ty -> Format.fprintf ppf ".%s_tag" ty
       | AdtPayloadIndex (c, j) -> Format.fprintf ppf ".%s_%d" c j)


(* Pretty-print a list of single indexes, given the number of previously seen *)
let rec pp_print_index' db safe ppf = function
  | [] -> ()
  | h :: tl -> 

    (* Print single index with current counter for array variable *)
    pp_print_one_index' db safe ppf h; 

    pp_print_index' 

      (* Increment the counter if we have just printed an array
         index *)
      (match h with ArrayVarIndex _ -> succ db | _ -> db) 
      safe 
      ppf 
      tl


(* Pretty-print an index *)
let pp_print_index = pp_print_index' 1

(* Pretty-print an index *)
let pp_print_one_index = pp_print_one_index' 1



let string_of_index safe = string_of_t (pp_print_index safe)

(* The empty index *)
let empty_index = []


(* An index is a sequence of index entries *)
type index = one_index list


(* Comparison of indexes *)
let compare_one_index a b = match a, b with 

  (* Use polymorphic comparison on strings and integers *)
  | RecordIndex a, RecordIndex b
  | AbstractTypeIndex a, AbstractTypeIndex b -> String.compare a b
  | TupleIndex a, TupleIndex b
  | ListIndex a, ListIndex b
  | ArrayIntIndex a, ArrayIntIndex b -> Int.compare a b
  | AdtTagIndex a, AdtTagIndex b -> String.compare a b
  | AdtPayloadIndex (a, i), AdtPayloadIndex (b, j) ->
    let c = String.compare a b in if c <> 0 then c else Int.compare i j

  (* Variable indexes are equal regardless of the bound expression *)
  | ArrayVarIndex _, ArrayVarIndex _ -> 0
  | SetMapIndex _, SetMapIndex _ -> 0

  (* Record indexes are greatest *)
  | RecordIndex _, TupleIndex _
  | RecordIndex _, ListIndex _
  | RecordIndex _, ArrayIntIndex _
  | RecordIndex _, ArrayVarIndex _
  | RecordIndex _, SetMapIndex _
  | RecordIndex _, AdtTagIndex _
  | RecordIndex _, AdtPayloadIndex _
  | RecordIndex _, AbstractTypeIndex _ -> 1

  (* Tuple indexes are only smaller than record indexes *)
  | TupleIndex _, RecordIndex _ -> -1
  | TupleIndex _, ListIndex _
  | TupleIndex _, ArrayIntIndex _
  | TupleIndex _, ArrayVarIndex _
  | TupleIndex _, SetMapIndex _
  | TupleIndex _, AdtTagIndex _
  | TupleIndex _, AdtPayloadIndex _
  | TupleIndex _, AbstractTypeIndex _ -> 1

  (* List indexes are smaller than tuple and record indexes *)
  | ListIndex _, RecordIndex _
  | ListIndex _, TupleIndex _ -> -1 
  | ListIndex _, ArrayIntIndex _
  | ListIndex _, ArrayVarIndex _
  | ListIndex _, SetMapIndex _
  | ListIndex _, AdtTagIndex _
  | ListIndex _, AdtPayloadIndex _
  | ListIndex _, AbstractTypeIndex _ -> 1 

  (* Integer array indexes are greater than array variables, map indexes,
     ADT indexes, and abstract type indexes *)
  | ArrayIntIndex _, RecordIndex _
  | ArrayIntIndex _, TupleIndex _
  | ArrayIntIndex _, ListIndex _ -> -1
  | ArrayIntIndex _, ArrayVarIndex _
  | ArrayIntIndex _, SetMapIndex _
  | ArrayIntIndex _, AdtTagIndex _
  | ArrayIntIndex _, AdtPayloadIndex _
  | ArrayIntIndex _, AbstractTypeIndex _ -> 1

  (* Array variable indexes are greater than map indexes, ADT indexes,
   * and abstract type indexes *)
  | ArrayVarIndex _, RecordIndex _
  | ArrayVarIndex _, ArrayIntIndex _
  | ArrayVarIndex _, ListIndex _
  | ArrayVarIndex _, TupleIndex _ -> -1
  | ArrayVarIndex _, SetMapIndex _
  | ArrayVarIndex _, AdtTagIndex _
  | ArrayVarIndex _, AdtPayloadIndex _
  | ArrayVarIndex _, AbstractTypeIndex _ -> 1

  (* Map indexes are greater than ADT indexes and abstract type indexes *)
  | SetMapIndex _, RecordIndex _
  | SetMapIndex _, ArrayIntIndex _
  | SetMapIndex _, ListIndex _
  | SetMapIndex _, TupleIndex _ 
  | SetMapIndex _, ArrayVarIndex _ -> -1
  | SetMapIndex _, AdtTagIndex _
  | SetMapIndex _, AdtPayloadIndex _
  | SetMapIndex _, AbstractTypeIndex _ -> 1

  (* ADT tag indexes are greater only than ADT payload indexes and abstract type indexes *)
  | AdtTagIndex _, RecordIndex _
  | AdtTagIndex _, TupleIndex _
  | AdtTagIndex _, ListIndex _
  | AdtTagIndex _, ArrayIntIndex _
  | AdtTagIndex _, ArrayVarIndex _
  | AdtTagIndex _, SetMapIndex _ -> -1
  | AdtTagIndex _, AdtPayloadIndex _
  | AdtTagIndex _, AbstractTypeIndex _ -> 1

  (* ADT payload indexes are greater only than abstract type indexes *)
  | AdtPayloadIndex _, RecordIndex _
  | AdtPayloadIndex _, TupleIndex _
  | AdtPayloadIndex _, ListIndex _
  | AdtPayloadIndex _, ArrayIntIndex _
  | AdtPayloadIndex _, ArrayVarIndex _
  | AdtPayloadIndex _, SetMapIndex _
  | AdtPayloadIndex _, AdtTagIndex _ -> -1
  | AdtPayloadIndex _, AbstractTypeIndex _ -> 1

  (* Abstract type indexes are the smallest *)
  | AbstractTypeIndex _, RecordIndex _
  | AbstractTypeIndex _, ArrayIntIndex _
  | AbstractTypeIndex _, ListIndex _
  | AbstractTypeIndex _, TupleIndex _
  | AbstractTypeIndex _, ArrayVarIndex _ 
  | AbstractTypeIndex _, SetMapIndex _
  | AbstractTypeIndex _, AdtTagIndex _
  | AbstractTypeIndex _, AdtPayloadIndex _ -> -1

(* Equality of indexes *)
let equal_one_index a b = match a,b with 
  
  (* String indexes are equal if the strings are *)
  | RecordIndex a, RecordIndex b
  | AbstractTypeIndex a, AbstractTypeIndex b -> a = b

  (* Integer indexes are equal if the integers are *)
  | TupleIndex a, TupleIndex b
  | ListIndex a, ListIndex b
  | ArrayIntIndex a, ArrayIntIndex b -> a = b

  (* Variable indexes are equal regardless of the bound expressions *)
  | ArrayVarIndex _, ArrayVarIndex _ -> true

  | AdtTagIndex a, AdtTagIndex b -> a = b
  | AdtPayloadIndex (a, i), AdtPayloadIndex (b, j) -> a = b && i = j

  | _ -> false


(* Lexicographic comparison of lists of indexes *)
let compare_indexes a b = match a, b with 

  (* Lists are equal *)
  | [], [] -> 0

  (* Longer list is greater *)
  | _, [] -> 1 

  (* Shorter list is smaller *)
  | [], _ -> -1 

  (* Compare head elements of lists *)
  | a :: atl, b :: btl -> match compare_one_index a b with 
    
    (* Head elements are equal, recurse to compare tails *)
    | 0 -> compare atl btl 
             
    (* Return comparison of head elements *)
    | c -> c 


(* Indexes are equal if all elements in the lists are equal *)
let equal_index a b = 
  List.length a = List.length b && List.for_all2 equal_one_index a b


(* Extract array bounds from index *)
let array_bounds_of_index idx = 

  List.fold_left 
    (fun a -> function 
       | ArrayVarIndex e -> e :: a 
       | _ -> a)
    []
    idx

(* Extract array bounds from index *)
let array_vars_of_index idx = 

  List.fold_left 
    (fun a -> function 
       | ArrayVarIndex e -> 
         StateVar.mk_state_var
           ((List.length a)
            |> I.push_index I.index_ident
            |> I.string_of_ident true)
           I.reserved_scope
           (Term.type_of_term (e :> Term.t)) 
         :: a
       | _ -> a)
    []
    idx
    
(* Module for of single indexes *)  
module LustreOneIndex =
    (struct 
      type t = one_index
      let compare = compare_one_index
    end)


(* Trie of idexes *)  
module LustreIndexTrie = Trie.Make (LustreOneIndex)

include LustreIndexTrie

(* Trie with a single element for the empty index *)
let singleton k v = add k v empty

(* Get the greatest integer of an indexed trie *)
let top_max_index t = 

  try 

    LustreIndexTrie.max_binding t
    |> fst
    |> (function 
        | ListIndex i :: _ -> i
        | [] -> (- 1)
        | _ -> raise (Invalid_argument "top_max_index"))

  with Not_found -> (-1)


let filter_array_indices index = List.filter (
  function
  | ArrayVarIndex _
  | ArrayIntIndex _ 
  | SetMapIndex _ -> false 
  | RecordIndex _
  | TupleIndex _
  | ListIndex _
  | AbstractTypeIndex _
  | AdtTagIndex _
  | AdtPayloadIndex _ -> true)
  index

let compatible_one_index i1 i2 = match i1, i2 with
  | RecordIndex s1, RecordIndex s2 -> s1 = s2
  | TupleIndex i1, TupleIndex i2 -> i1 = i2
  | ListIndex i1, ListIndex i2 -> i1 = i2
  | ArrayIntIndex i1, ArrayIntIndex i2 -> i1 = i2
  | ArrayIntIndex _, ArrayVarIndex _
  | ArrayVarIndex _, ArrayIntIndex _
  | ArrayVarIndex _, ArrayVarIndex _ -> true
  | AbstractTypeIndex s1, AbstractTypeIndex s2 -> s1 = s2
  | AdtTagIndex s1, AdtTagIndex s2 -> s1 = s2
  | AdtPayloadIndex (s1, j1), AdtPayloadIndex (s2, j2) -> s1 = s2 && j1 = j2
  | _ -> false

let compatible_indexes = List.for_all2 compatible_one_index



let pp_print_index_trie safe pp_e ppf t = 
  bindings t |> 
  pp_print_list
    (fun ppf (i, e) -> 
       if i = empty_index then 
         pp_e ppf e
       else
         Format.fprintf 
           ppf
           "%a: %a"
           (pp_print_index safe) i
           pp_e e)
    ";@ "
    ppf


let pp_print_trie_expr safe ppf expr =
  pp_print_index_trie safe
    (E.pp_print_lustre_expr safe) ppf expr


let pp_print_trie_ty safe ppf ty =
  pp_print_index_trie safe
    Type.pp_print_type ppf ty  

let mk_scope_for_index index =
  List.rev_map
    (fun i ->
       string_of_t (pp_print_one_index true) i
       |> String.length
       |> string_of_int
       |> Ident.of_string)
    (filter_array_indices index)
  |> Scope.mk_scope


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
