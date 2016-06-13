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


(* ********************************************************************* *)
(* Types and hash-consing                                                *)
(* ********************************************************************* *)


(* Using strong (as opposed to weak) hash-consing because the table is used for
   memoization *)
module H = HashconsStrong


(* Uninterpreted symbol to be hash-consed *)
type uf_symbol = string 

(* A private type that cannot be constructed outside this module

   This is necessary to ensure the invariant that all subterms of a
   term are hashconsed. We can construct and thus pattern match on the
   {!uf_symbol} type, but not on the {!uf_symbol_node} type *)
type uf_symbol_node = uf_symbol


(* Properties of an uninterpreted symbol

   Only keep essential properties here that are shared by all
   modules. For local properties use a hashtable in the respective
   module. *)
type uf_prop = 
    
    {

      (* Type of arguments *)
      uf_arg_type : Type.t list;

      (* Type of result *)
      uf_res_type : Type.t;

    }


(* Hashconsed uninterpreted symbol *) 
type t = (uf_symbol_node, uf_prop) H.hash_consed


(* Hashing and equality on uninterpreted symbols *) 
module Uf_symbol_node = struct 

  (* Uninterpreted symbol node *)
  type t = uf_symbol_node

  (* Properties of uninterpreted symbol *)
  type prop = uf_prop

  (* Hashing for uninterpreted symbols is hashing of strings *)
  let hash = Hashtbl.hash 

  (* Equality of uninterpreted symbols is comparison of strings *)
  let equal = (=)

end


(* Hashconsed uninterpreted symbols *)
module Huf_symbol = H.Make (Uf_symbol_node)


(* Storage for uninterpreted function symbols *)
let ht = Huf_symbol.create 251


(* ********************************************************************* *)
(* Hashtables, maps and sets                                             *)
(* ********************************************************************* *)


(* Comparison function on uninterpreted function symbols *)
let compare_uf_symbols = H.compare

(* Equality function on uninterpreted function symbols *)
let equal_uf_symbols = H.equal

(* Hashing function on uninterpreted function symbols *)
let hash_uf_symbol = H.hash 


(* Module as input to functors *)
module HashedUfSymbol = struct 

  (* Dummy type to prevent writing [type t = t] which is cyclic *)
  type z = t
  type t = z

  (* Compare tags of hashconsed uninterpreted symbols for equality *)
  let equal = equal_uf_symbols
    
  (* Use hash of uninterpreted symbol *)
  let hash = hash_uf_symbol

end


(* Module as input to functors *)
module OrderedUfSymbol = struct 

  (* Dummy type to prevent writing [type t = t] which is cyclic *)
  type z = t
  type t = z

  (* Compare tags of hashconsed symbols *)
  let compare = compare_uf_symbols

end


(* Hashtable *)
module UfSymbolHashtbl = Hashtbl.Make (HashedUfSymbol)


(* Set *)
module UfSymbolSet = Set.Make (OrderedUfSymbol)


(* Map *)
module UfSymbolMap = Map.Make (OrderedUfSymbol)


(* ********************************************************************* *)
(* Pretty-printing                                                       *)
(* ********************************************************************* *)


(* Pretty-print an uninterpreted function symbol *)
let rec pp_print_uf_symbol_node ppf s = 
  Format.pp_print_string ppf s

(* Pretty-print a hashconsed uninterpreted function symbol *)
and pp_print_uf_symbol ppf { H.node = n } =
  pp_print_uf_symbol_node ppf n


(* Return a string representation of a hashconsed symbol *)
let string_of_uf_symbol s = string_of_t pp_print_uf_symbol s


(* ********************************************************************* *)
(* Accessor function                                                     *)
(* ********************************************************************* *)


(* Return type of arguments of an uninterpreted symbol *)
let name_of_uf_symbol { H.node = s } = s


(* Return type of result of an uninterpreted symbol *)
let res_type_of_uf_symbol { H.prop = { uf_res_type = t } } = t


(* Return type of arguments of an uninterpreted symbol *)
let arg_type_of_uf_symbol { H.prop = { uf_arg_type = t } } = t


(* ********************************************************************* *)
(* Constructors                                                          *)
(* ********************************************************************* *)


(* Return a symbol for an uninterpreted function symbol *)
let mk_uf_symbol s a r = 

  try 
    
    (* Get previous declaration of symbol *)
    let u = Huf_symbol.find ht s in

    if 
      
      (* Argument and return type matches previous declaration? *)
      (Type.equal_types (res_type_of_uf_symbol u) r) && 
      ((List.length (arg_type_of_uf_symbol u)) = (List.length a)) &&
      (List.for_all2 Type.equal_types (arg_type_of_uf_symbol u) a) 
        
    then
      
      (* Return previously declared symbol *)
      u
        
    else

      raise
        (Invalid_argument (
           Format.asprintf
            "@[<v>\
              Uninterpreted symbol %s with signature %a -> %a \
              redeclared with different signature %a -> %a \
            @]"
            s
            (pp_print_list Type.pp_print_type " -> ") (arg_type_of_uf_symbol u)
            Type.pp_print_type (res_type_of_uf_symbol u)
            (pp_print_list Type.pp_print_type " -> ") a
            Type.pp_print_type r
        ) )
        
  (* Uninterpreted symbol is not in the hashcons table *)
  with Not_found  -> 
    
    (* Hashcons uninterpreted symbol *)
    Huf_symbol.hashcons 
      ht
      s
      { uf_arg_type = a; uf_res_type = r }


(* Import an uninterpreted symbol from a different instance into the
   hashcons table 

   TODO: We may have clashes if we import fresh uninterpreted symbols
   from one instance to another.*)
let import u = 

  mk_uf_symbol 
    (name_of_uf_symbol u)
    (List.map Type.import (arg_type_of_uf_symbol u))
    (Type.import (res_type_of_uf_symbol u))


(* Counter for index of fresh uninterpreted symbols *)
let fresh_uf_symbol_id = ref 0


(* Return name of a fresh uninterpreted symbol  *)
let rec next_fresh_uf_symbol () = 

  (* Candidate name for next fresh symbol *)
  let s = Format.sprintf "__C%d" !fresh_uf_symbol_id in

  (* Increment counter *)
  fresh_uf_symbol_id := succ !fresh_uf_symbol_id;

  try 

    (* Check if candidate symbol is already declared *)
    let _ = Huf_symbol.find ht s in
  
    (* Recurse to get another fresh symbol *)
    next_fresh_uf_symbol ()

  (* Candidiate symbol is not declared and can be used *)
  with Not_found  -> s
    
    
(* Return a fresh uninterpreted symbol 

   TODO: How to make a completely separate namespace so that a symbol
   declared later does not clash? *)
let mk_fresh_uf_symbol a r = 

  (* Get name of a fresh uninterpreted symbol *)
  let s = next_fresh_uf_symbol () in

  (* Create symbol with given signature *)
  mk_uf_symbol s a r  


(* Return a previously declared uninterpreted function symbol *)
let uf_symbol_of_string s = 

  try 

    (* Get previous declaration of symbol *)
    Huf_symbol.find ht s 
        
  with Not_found ->

    raise Not_found


(* ********************************************************************* *)
(* Folding and utility functions on uninterpreted function symbols       *)
(* ********************************************************************* *)


(* Fold all variables in the hash cons table *)
let fold_uf_declarations f a = 
  Huf_symbol.fold
    (fun u a ->
      let s, t, r = 
        (function { H.node = s; 
                    H.prop = { uf_arg_type = t; uf_res_type = r } } -> 
          s, t, r)
          u
      in
      f s t r a)
    ht
    a


(* Fold all variables in the hash cons table *)
let iter_uf_declarations f = 
  Huf_symbol.iter
    (fun u ->
      let s, t, r = 
        (function { H.node = s; 
                    H.prop = { uf_arg_type = t; uf_res_type = r } } -> 
          s, t, r)
          u
      in
      f s t r)
    ht


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
