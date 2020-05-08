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

  (* Index to the representation field of an abstract type *)
  | AbstractTypeIndex of string


(* Pretty-print a single index *)
let pp_print_one_index' db = function 
  
  | false ->
    
    (function ppf -> function 
       | RecordIndex i -> ()
       | TupleIndex i -> Format.fprintf ppf "(%d)" i
       | ListIndex i -> Format.fprintf ppf "{%d}" i
       | ArrayIntIndex i -> Format.fprintf ppf "[%d]" i
       | ArrayVarIndex v -> () (* Format.fprintf ppf "[X%d(%a)]" db (E.pp_print_expr false) v ) *)
       | AbstractTypeIndex i -> ())

  | true ->
    
    (function ppf -> function 
       | RecordIndex i -> Format.fprintf ppf ".%s" i
       | TupleIndex i -> Format.fprintf ppf "_%d" i
       | ListIndex i -> Format.fprintf ppf "_%d" i
       | ArrayIntIndex i -> Format.fprintf ppf "_%d" i
       | ArrayVarIndex v ->  Format.fprintf ppf "_X%d" db
       | AbstractTypeIndex i -> Format.fprintf ppf ".%s" i)


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
  | AbstractTypeIndex a, AbstractTypeIndex b -> Pervasives.compare a b
  | TupleIndex a, TupleIndex b
  | ListIndex a, ListIndex b
  | ArrayIntIndex a, ArrayIntIndex b -> Pervasives.compare a b

  (* Variable indexes are equal regardless of the bound expression *)
  | ArrayVarIndex _, ArrayVarIndex _ -> 0

  (* Record indexes are greatest *)
  | RecordIndex _, TupleIndex _
  | RecordIndex _, ListIndex _
  | RecordIndex _, ArrayIntIndex _
  | RecordIndex _, ArrayVarIndex _
  | RecordIndex _, AbstractTypeIndex _ -> 1 

  (* Tuple indexes are only smaller than record indexes *)
  | TupleIndex _, RecordIndex _ -> -1 
  | TupleIndex _, ListIndex _
  | TupleIndex _, ArrayIntIndex _
  | TupleIndex _, ArrayVarIndex _
  | TupleIndex _, AbstractTypeIndex _ -> 1 

  (* List indexes are smaller than tuple and record indexes *)
  | ListIndex _, RecordIndex _
  | ListIndex _, TupleIndex _ -> -1 
  | ListIndex _, ArrayIntIndex _
  | ListIndex _, ArrayVarIndex _
  | ListIndex _, AbstractTypeIndex _ -> 1 

  (* Intger array indexes are greater than array variables
   * and abstract type indexes *)
  | ArrayIntIndex _, RecordIndex _
  | ArrayIntIndex _, TupleIndex _
  | ArrayIntIndex _, ListIndex _ -> -1
  | ArrayIntIndex _, ArrayVarIndex _
  | ArrayIntIndex _, AbstractTypeIndex _ -> 1

  (* Array variable indexes are only greater than abstract type indexes *)
  | ArrayVarIndex _, RecordIndex _
  | ArrayVarIndex _, ArrayIntIndex _
  | ArrayVarIndex _, ListIndex _
  | ArrayVarIndex _, TupleIndex _ -> -1
  | ArrayVarIndex _, AbstractTypeIndex _ -> 1

  (* Abstract type indexes are the smallest *)
  | AbstractTypeIndex _, RecordIndex _
  | AbstractTypeIndex _, ArrayIntIndex _
  | AbstractTypeIndex _, ListIndex _
  | AbstractTypeIndex _, TupleIndex _
  | AbstractTypeIndex _, ArrayVarIndex _ -> -1

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

  | _ -> false


(* Lexicographic comparison of lists of indexes *)
let rec compare_indexes a b = match a, b with 

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


let compatible_one_index i1 i2 = match i1, i2 with
  | RecordIndex s1, RecordIndex s2 -> s1 = s2
  | TupleIndex i1, TupleIndex i2 -> i1 = i2
  | ListIndex i1, ListIndex i2 -> i1 = i2
  | ArrayIntIndex i1, ArrayIntIndex i2 -> i1 = i2
  | ArrayIntIndex _, ArrayVarIndex _
  | ArrayVarIndex _, ArrayIntIndex _
  | ArrayVarIndex _, ArrayVarIndex _ -> true
  | AbstractTypeIndex s1, AbstractTypeIndex s2 -> s1 = s2
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


let mk_scope_for_index index =
  List.rev_map
    (fun i ->
       string_of_t (pp_print_one_index true) i
       |> String.length
       |> string_of_int
       |> Ident.of_string)
    index
  |> Scope.mk_scope


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
