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

module type Printer =
  sig
    val pp_print_attr : Format.formatter -> t -> unit
                                                   
    val print_attr : t -> unit
                            
    val string_of_attr : t -> string 

  end

module SMTLIBPrinter : Printer =
  struct

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
  end

module YicesPrinter : Printer =
  struct

    (* Pretty-print an attribute *)
    let pp_print_attr_node ppf = function 

      (* Ignore name attribute for yices *)
      | Named _ -> ()
                     
    (* Pretty-print an attribute to the standard formatter *)
    let print_attr_node = pp_print_attr_node Format.std_formatter 

    (* Pretty-print a hashconsed attribute *)
    let pp_print_attr ppf { Hashcons.node = v } = pp_print_attr_node ppf v

    (* Pretty-print a hashconsed attribute to the standard formatter *)
    let print_attr = pp_print_attr Format.std_formatter 

    (* Return a string representation of a hashconsed attribute *)
    let string_of_attr { Hashcons.node = v } = string_of_t pp_print_attr_node v 
  end
        

(* Select apropriate printer based on solver *)
let select_printer () =
  match Flags.smtsolver () with
  | `Yices_native -> (module YicesPrinter : Printer)
  | _ -> (module SMTLIBPrinter : Printer)

module SelectedPrinter : Printer = (val (select_printer ()))
  
include SelectedPrinter


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
