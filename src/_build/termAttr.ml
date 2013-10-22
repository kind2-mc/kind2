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


(* An attribute for a term annotation 

   Currently we only have names for terms *)
type attr = Named of int


(* A private type that cannot be constructed outside this module

   This is necessary to ensure the invariant that all subterms of a
   term are hashconsed. We can construct and thus pattern match on the
   {!attr} type, but not on the {!attr_node} type *)
type attr_node = attr


(* Properties of an attribute

   Only keep essential properties here that are shared by all
   modules. For local properties use a hashtable in the respective
   module.

   No properties for now *)
type attr_prop = unit


(* Hashconsed attribute *)
type t = (attr_node, attr_prop) Hashcons.hash_consed


(* Hashing and equality on attributes *)
module Attr_node = struct

  (* The type of an attribute *)
  type t = attr_node

  (* Properties of an attribute

     No properties for now *)
  type prop = attr_prop

  (* Equality of two variables *)
  let equal v1 v2 = match v1, v2 with

    (* Two name attributes, use equality on integers *)
    | Named n1, Named n2 -> n1 = n2

  (* Return hash of a name attribute *)
  let hash = function Named n -> n

end


(* Hashconsed attributes *)
module Hattr = Hashcons.Make (Attr_node)


(* Storage for hashconsed attributes *)
let ht = Hattr.create 251


(* ********************************************************************* *)
(* Hashtables, maps and sets                                             *)
(* ********************************************************************* *)


(* Comparison function on attributes *)
let compare_attrs = Hashcons.compare

(* Equality function on attributes *)
let equal_attrs = Hashcons.equal 

(* Hashing function on attribute *)
let hash_attr = Hashcons.hash 


(* Module as input to functors *)
module HashedAttr = struct 

  (* Dummy type to prevent writing [type t = t] which is cyclic *)
  type z = t
  type t = z

  (* Compare tags of hashconsed attributes for equality *)
  let equal = equal_attrs
    
  (* Use hash of attributes *)
  let hash = hash_attr

end

(* Module as input to functors *)
module OrderedAttr = struct 

  (* Dummy type to prevent writing [type t = t] which is cyclic *)
  type z = t
  type t = z

  (* Compare tags of hashconsed attributes *)
  let compare = compare_attrs

end

(* Hashtable of attributes *)
module AttrHashtbl = Hashtbl.Make (HashedAttr)

(* Set of attributes

   Try to turn this into a patricia set with Hset for another small
   gain in efficiency. *)
module AttrSet = Set.Make (OrderedAttr)


(* Map of attributes

   Try to turn this into a patricia set with Hset for another small
   gain in efficiency. *)
module AttrMap = Map.Make (OrderedAttr)


(* ********************************************************************* *)
(* Pretty-printing                                                       *)
(* ********************************************************************* *)


(* Pretty-print an attribute *)
let pp_print_attr_node ppf = function 

  (* Pretty-print a name attribute *)
  | Named n ->
    Format.fprintf ppf ":named@ t%d" n

(* Pretty-print an attribute to the standard formatter *)
let print_attr_node = pp_print_attr_node Format.std_formatter 

(* Pretty-print a hashconsed attribute *)
let pp_print_attr ppf { Hashcons.node = v } = pp_print_attr_node ppf v

(* Pretty-print a hashconsed attribute to the standard formatter *)
let print_attr = pp_print_attr Format.std_formatter 

(* Return a string representation of a hashconsed attribute *)
let string_of_attr { Hashcons.node = v } = string_of_t pp_print_attr_node v 


(* ********************************************************************* *)
(* Accessor functions                                                    *)
(* ********************************************************************* *)

(* Return true if the attribute is a name *)
let is_named = function { Hashcons.node = Named _ } -> true

(* Return the name in a name attribute *)
let named_of_attr = function { Hashcons.node = Named n } -> n

(* ********************************************************************* *)
(* Constructors                                                          *)
(* ********************************************************************* *)


(* Return a hashconsed attribute which is a name *)    
let mk_named n = 
  
  (* Create and hashcons name attribute *)
  Hattr.hashcons ht (Named n) ()


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
