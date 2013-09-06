(*
This file is part of the Kind verifier

* Copyright (c) 2007-2013 by the Board of Trustees of the University of Iowa, 
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


(* ********************************************************************* *)
(* Types and hash-consing                                                *)
(* ********************************************************************* *)


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
type t = (uf_symbol_node, uf_prop) Hashcons.hash_consed


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
module Huf_symbol = Hashcons.Make (Uf_symbol_node)


(* Storage for uninterpreted function symbols *)
let ht = Huf_symbol.create 251


(* ********************************************************************* *)
(* Hashtables, maps and sets                                             *)
(* ********************************************************************* *)


(* Comparison function on uninterpreted function symbols *)
let compare_uf_symbols = Hashcons.compare

(* Equality function on uninterpreted function symbols *)
let equal_uf_symbols = Hashcons.equal

(* Hashing function on uninterpreted function symbols *)
let hash_uf_symbol = Hashcons.hash 


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
and pp_print_uf_symbol ppf { Hashcons.node = n } =
  pp_print_uf_symbol_node ppf n


(* Return a string representation of a hashconsed symbol *)
let string_of_uf_symbol s = string_of_t pp_print_uf_symbol s


(* ********************************************************************* *)
(* Accessor function                                                     *)
(* ********************************************************************* *)


(* Return type of arguments of an uninterpreted symbol *)
let name_of_uf_symbol { Hashcons.node = s } = s


(* Return type of result of an uninterpreted symbol *)
let res_type_of_uf_symbol { Hashcons.prop = { uf_res_type = t } } = t


(* Return type of arguments of an uninterpreted symbol *)
let arg_type_of_uf_symbol { Hashcons.prop = { uf_arg_type = t } } = t


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
      (res_type_of_uf_symbol u = r) && 
        (arg_type_of_uf_symbol u = a) 
        
    then
      
      (* Return previously declared symbol *)
      u
        
    else

      raise 
        (Invalid_argument 
           "Uninterpreted symbol redeclared with different signature")
        
  (* Uninterpreted symbol is not in the hashcons table *)
  with Not_found | Huf_symbol.Key_not_found _ -> 
    
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
  with Not_found | Huf_symbol.Key_not_found _ -> s
    
    
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
        (function { Hashcons.node = s; 
                    Hashcons.prop = { uf_arg_type = t; uf_res_type = r } } -> 
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
        (function { Hashcons.node = s; 
                    Hashcons.prop = { uf_arg_type = t; uf_res_type = r } } -> 
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
