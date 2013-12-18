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


(* ********************************************************************** *)
(* Types                                                                  *)
(* ********************************************************************** *)

(* An index of an identifier *)
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
  | StringIndex a, StringIndex b -> compare a b

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


(* Construct an identifier of a string *)
let mk_string_ident string = (string, empty_index)


(* Construct an identifier of a string *)
let mk_string_index string = [StringIndex string]


(* Construct an identifier of a string *)
let mk_int_index string = [IntIndex string]



(* Push the index as an element index to the given index *)
let push_one_index_to_index index1 index2 = index1 :: index2


(* Push the string as an element index to the given index *)
let push_string_index_to_index string index = StringIndex string :: index 


(* Push the integer as an element index to the given index *)
let push_int_index_to_index int index = IntIndex int :: index 


(* Push the integer as an element index to the given index *)
let push_ident_index_to_index (base_ident, index1) index2 = 

  StringIndex base_ident :: index1 @ index2


(* Push the index as an element index to the given index *)
let push_index_to_index index1 index2 = index1 @ index2


let push_string_index string (base, index) = 
  (base, push_string_index_to_index string index)


let push_int_index int (base, index) = 
  (base, push_int_index_to_index int index)


let push_ident_index ident (base, index) = 
  (base, push_ident_index_to_index ident index)


let push_one_index one_index (base, index) = 
  (base, push_one_index_to_index one_index index)


let push_index index1 (base, index2) = 
  (base, push_index_to_index index1 index2)


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

  (* All of j consumed, return j *)
  | [], j -> j

  (* i is not a prefix of j *)
  | _, [] ->
    raise (Invalid_argument ("get_suffix"))

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
  | StringIndex _ :: _, IntIndex _ :: _ ->
    raise (Invalid_argument ("get_index_suffix"))



(* [i] is a prefix of [j], return the indexes of [j] with the commonp
   prefix removed *)
let get_suffix (i, li) (j, lj) = 

  try 

    if i = j then get_index_suffix li lj else 
      
      raise (Invalid_argument ("get_suffix"))

  with 

    | Invalid_argument "get_index_suffix" -> 

      raise (Invalid_argument ("get_suffix"))

(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
