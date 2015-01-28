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

(* ********************************************************************** *)
(* Types                                                                  *)
(* ********************************************************************** *)

(* An index of an identifier 

   Leave this as IntIndex of int, so that we have a concrete type that
   the polymorphic comparison and equality functions apply to. This
   makes it easier to use association lists. 
*)
type one_index = 

  (* String as index *)
  | StringIndex of string

  (* Integer as index *)
  | IntIndex of int


(* A list of indexes *)
type index = one_index list


(* The empty index *)
let empty_index = []


(* An identifier *)
type t = string * index


(* Comparision of indexes *)
let compare_one_index a b = match a, b with 

  (* Compare strings *)
  | StringIndex a, StringIndex b -> Pervasives.compare a b

  (* Compare integers *)
  | IntIndex a, IntIndex b -> compare a b

  (* String indexes are greater than integer indexes *)
  | StringIndex _, IntIndex _ -> 1 

  (* Integer indexes are smaller than string indexes *)
  | IntIndex _, StringIndex _ -> 1 


(* Lexicographic comparison of lists of indexes *)
let rec compare_index a b = match a, b with 

  (* Lists are equal *)
  | [], [] -> 0

  (* Longer list is greater *)
  | _, [] -> 1 

  (* Shorter list is smaller *)
  | [], _ -> -1 

  (* Compare head elements of lists *)
  | a :: atl, b :: btl -> match compare_one_index a b with 
    
    (* Head elements are equal, recurse to compare tails *)
    | 0 -> compare_index atl btl 
             
    (* Return comparison of head elements *)
    | c -> c 


(* Compare indexed identifiers *)
let compare (a, ia)  (b, ib) = 

  (* Compare strings *)
  match compare a b with 

    (* Strings are equal, compare indexes *)
    | 0 -> compare_index ia ib

    (* Return comparison of strings *)
    | c -> c
  

(* Equality on indexed identifiers *)
let equal i1 i2 = compare i1 i2 = 0


(* Set of identifiers *)  
module LustreIdentSet = Set.Make 
    (struct 
      type z = t
      type t = z
      let compare = compare
    end)


(* ********************************************************************** *)
(* Pretty-printers                                                        *)
(* ********************************************************************** *)


(* Pretty-print an index *)
let pp_print_one_index = function 
  
  | false -> 
    
    (function ppf -> function 
       | StringIndex i -> Format.fprintf ppf ".%s" i
       | IntIndex i -> Format.fprintf ppf "[%d]" i)

  | true -> 
    
    (function ppf -> function 
       | StringIndex i -> Format.fprintf ppf "_%s" i
       | IntIndex i -> Format.fprintf ppf "_%d" i)


(* Pretty-print a list of indexes *)
let pp_print_index safe ppf index = 
  List.iter (pp_print_one_index safe ppf) index


(* Pretty-print an identifier *)
let rec pp_print_ident safe ppf (s, i) = 

  Format.fprintf ppf "%s%a" s (pp_print_index safe) i


let string_of_ident safe = string_of_t (pp_print_ident safe)


(* Construct an identifier of a string *)
let mk_string_ident string = (string, empty_index)


(* Construct an identifier of a string *)
let mk_string_index string = [StringIndex string]


(* Construct an identifier of a string *)
let mk_int_index num = [IntIndex (Numeral.to_int num)]



(* Push the index as an element index to the given index *)
let push_one_index_to_index index1 index2 = index1 :: index2

let push_back_one_index_to_index index1 index2 = index2 @ [index1]


(* Push the string as an element index to the given index *)
let push_string_index_to_index string index = StringIndex string :: index 

let push_back_string_index_to_index string index = index @ [StringIndex string]


(* Push the integer as an element index to the given index *)
let push_int_index_to_index int index = 
  IntIndex (Numeral.to_int int) :: index 

let push_back_int_index_to_index int index = 
  index @ [IntIndex (Numeral.to_int int)]


(* Push the identifier as an element index to the given index *)
let push_ident_index_to_index (base_ident, index1) index2 = 

  StringIndex base_ident :: index1 @ index2

let push_back_ident_index_to_index (base_ident, index1) index2 = 

  index2 @ (StringIndex base_ident :: index1)


(* Push the index as an element index to the given index *)
let push_index_to_index index1 index2 = index1 @ index2

let push_back_index_to_index index1 index2 = index2 @ index1


let push_string_index string (base, index) = 
  (base, push_string_index_to_index string index)


let push_back_string_index string (base, index) = 
  (base, push_back_string_index_to_index string index)


let push_int_index int (base, index) = 
  (base, push_int_index_to_index int index)

let push_back_int_index int (base, index) = 
  (base, push_back_int_index_to_index int index)


let push_ident_index ident (base, index) = 
  (base, push_ident_index_to_index ident index)

let push_back_ident_index ident (base, index) = 
  (base, push_back_ident_index_to_index ident index)


let push_one_index one_index (base, index) = 
  (base, push_one_index_to_index one_index index)

let push_back_one_index one_index (base, index) = 
  (base, push_back_one_index_to_index one_index index)


let push_index index1 (base, index2) = 
  (base, push_index_to_index index1 index2)

let push_back_index index1 (base, index2) = 
  (base, push_back_index_to_index index1 index2)


(* Construct an index of an identifier *)
let index_of_ident (base, index) = push_string_index base index


let split_ident (base, index) = ((base, empty_index), index)

let split_index index = index

let index_of_one_index_list one_index_list = one_index_list 

(* ********************************************************************** *)
(* Constructors                                                           *)
(* ********************************************************************** *)


(* Construct an index of an identifier *)
let index_of_ident (s, i) = StringIndex s :: i


(* Construct an index of an integer *)
let index_of_int i = [IntIndex i]


(* Add a string as an index to an identifier *)
let add_string_index (s, i) j = (s, i @ [StringIndex j])


(* Add an integer as an index to an identifier *)
let add_int_index (s, i) j = (s, i @ [IntIndex j])


let add_ident_index (s, i) = function
  | (j, []) -> (s, i @ [StringIndex j])
  | _ -> raise (Invalid_argument ("Cannot add indexed identifier as index"))

let add_index (s, i) j = (s, i @ j)


let add_int_to_index i j = i @ [IntIndex j]

  

(* ********************************************************************** *)
(* Utility functions                                                      *)
(* ********************************************************************** *)

(* Remove i as prefix from j and return remainder of j *)
let rec get_index_suffix i j = match i, j with 

  (* All of i consumed, return j *)
  | [], j -> j

  (* i is not a prefix of j *)
  | _, [] -> raise Not_found

  (* First element is identical *)
  | StringIndex i :: itl, StringIndex j :: jtl when i = j -> 

    get_index_suffix itl jtl

  (* First element is identical *)
  | IntIndex i :: itl, IntIndex j :: jtl when i = j -> 

    get_index_suffix itl jtl

  (* First element is different, no common prefix *)
  | StringIndex _ :: _, StringIndex _ :: _
  | IntIndex _ :: _, IntIndex _ :: _
  | IntIndex _ :: _, StringIndex _ :: _
  | StringIndex _ :: _, IntIndex _ :: _ -> raise Not_found


(* [i] is a prefix of [j], return the indexes of [j] with the common
   prefix removed *)
let get_suffix (i, li) (j, lj) = 

  if i = j then get_index_suffix li lj else raise Not_found


(* Return a list of strings for index *)
let scope_of_index index =

  List.map 
    (function StringIndex i -> i | IntIndex i -> string_of_int i)
    index

(* Return a list of strings for indexed identifier *)
let scope_of_ident (ident, index) = ident :: (scope_of_index index)


(* Reserved identifiers for abstrations *)
let abs_ident_string =  "__abs" 
let oracle_ident_string =  "__nondet" 
let observer_ident_string =  "__observer" 
let first_tick_ident_string =  "__first_tick" 
let init_uf_string = "__node_init"
let trans_uf_string = "__node_trans"

(* let top_scope_string = "__top" *)


(* Return true if the identifier clashes with internal identifier names *)
let ident_is_reserved ident = 

  (* Get string part of identifier *)
  let ident_string, _ : t :> string * _ = ident in

  (* Return false if identical to any reserved identifier *)
  string_starts_with ident_string abs_ident_string
  || string_starts_with ident_string oracle_ident_string
  || string_starts_with ident_string observer_ident_string
  || string_starts_with ident_string first_tick_ident_string
  || string_starts_with ident_string init_uf_string
  || string_starts_with ident_string trans_uf_string
(*  || string_starts_with ident_string top_scope_string *)
  

(* Identifier for new variables from abstrations *)
let abs_ident = mk_string_ident abs_ident_string

(* Identifier for new oracle input *)
let oracle_ident = mk_string_ident oracle_ident_string

(* Identifier for new oracle input *)
let observer_ident = mk_string_ident observer_ident_string

(* Identifier for new clock initialization flag *)
let first_tick_ident = mk_string_ident first_tick_ident_string

(*
(* Scope for top-level variables *)
let top_scope_index = smk_string_index top_scope_string
*)


(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
