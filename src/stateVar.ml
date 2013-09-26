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


(* State variable to be has-consed *)
type state_var = string

(* A private type that cannot be constructed outside this module

   This is necessary to ensure the invariant that all subterms of a
   term are hashconsed. We can construct and thus pattern match on the
   {!state_var} type, but not on the {!state_var_node} type *)
type state_var_node = state_var


(* Properties of a state variable

   Only keep essential properties here that are shared by all
   modules. For local properties use a hashtable in the respective
   module. *)
type state_var_prop = 

  { 

    (* The name of the variable *)
    var_type : Type.t;

    (* The uninterpreted symbol associated with the variable *)
    uf_symbol : UfSymbol.t;
  
    (* True if variable does not occur under a pre operator *)
    mutable is_definition : bool;

  }

(* A hashconsed state variable *)
type t = (state_var, state_var_prop) Hashcons.hash_consed


(* Hashing and equality on state variables *) 
module State_var_node = struct 

  (* State variable node *)
  type t = state_var_node

  (* Properties of state variable *)
  type prop = state_var_prop

  (* Hashing for state variables is hashing of strings *)
  let hash = Hashtbl.hash 

  (* Equality of state variables is comparison of strings *)
  let equal = (=)

end


(* Hashconsed state variables *)
module Hstate_var = Hashcons.Make (State_var_node)


(* Storage for state variables *)
let ht = Hstate_var.create 251


(* ********************************************************************* *)
(* Hashtables, maps and sets                                             *)
(* ********************************************************************* *)


(* Comparison function on state variables *)
let compare_state_vars = Hashcons.compare

(* Equality function on state variables *)
let equal_state_vars = Hashcons.equal

(* Hashing function on state variables *)
let hash_state_var = Hashcons.hash 


(* Module as input to functors *)
module HashedStateVar = struct 

  (* Dummy type to prevent writing [type t = t] which is cyclic *)
  type z = t
  type t = z

  (* Compare tags of hashconsed uninterpreted symbols for equality *)
  let equal = equal_state_vars
    
  (* Use hash of uninterpreted symbol *)
  let hash = hash_state_var

end


(* Module as input to functors *)
module OrderedStateVar = struct 

  (* Dummy type to prevent writing [type t = t] which is cyclic *)
  type z = t
  type t = z

  (* Compare tags of hashconsed symbols *)
  let compare = compare_state_vars

end


(* Hashtable *)
module StateVarHashtbl = Hashtbl.Make (HashedStateVar)


(* Set *)
module StateVarSet = Set.Make (OrderedStateVar)


(* Map *)
module StateVarMap = Map.Make (OrderedStateVar)


(* State variable an uninterpreted function symbol is associated with *)
let uf_symbols_map = UfSymbol.UfSymbolHashtbl.create 41 


(* ********************************************************************* *)
(* Pretty-printing                                                       *)
(* ********************************************************************* *)


(* Pretty-print a state variable *)
let pp_print_state_var_node ppf s = 
  Format.pp_print_string ppf s

(* Pretty-print a state variable as it occurred in the original input *)
let pp_print_state_var_node_original ppf s = 
  Format.pp_print_string ppf (Kind1.Tables.internal_name_to_original_name s)

(* Pretty-print a hashconsed state variable *)
let pp_print_state_var ppf { Hashcons.node = n } =
  pp_print_state_var_node ppf n

(* Pretty-print a hashconsed state variable as it occurred in the
   original input *)
let pp_print_state_var_original ppf { Hashcons.node = n } =
  pp_print_state_var_node_original ppf n

(* Return a string representation of a hashconsed state variable *)
let string_of_state_var s = string_of_t pp_print_state_var s


(* ********************************************************************* *)
(* Accessor function                                                     *)
(* ********************************************************************* *)


(* Identifier of a state variable *)
let name_of_state_var { Hashcons.node = s } = s


(* Return true if state variable is a local definition *)
let is_definition { Hashcons.prop = { is_definition = d } } = d


(* Original identifier of a state variable *)
let original_name_of_state_var { Hashcons.node = s } = 
  Kind1.Tables.internal_name_to_original_name s


(* Type of a state variable *)
let type_of_state_var { Hashcons.prop = { var_type = t } } = t


(* Uninterpreted function symbol of a state variable *)
let uf_symbol_of_state_var { Hashcons.prop = { uf_symbol = u } } = u


(* Uninterpreted function symbol of a state variable *)
let state_var_of_uf_symbol u = 
  UfSymbol.UfSymbolHashtbl.find uf_symbols_map u
  


(* ********************************************************************* *)
(* Constructors                                                          *)
(* ********************************************************************* *)


(* Hashcons a state variable *)
let mk_state_var n d t = 

  try 

    (* Get previous declaration of identifier *)
    let { Hashcons.prop = p } as v = Hstate_var.find ht n in

    if 

      (* Return type matches previous declaration? *)
      type_of_state_var v = t

    then

      (

        (* Change from local definition to stateful, but not vice versa *)
        p.is_definition <- p.is_definition || d;
        
        (* Return previously declared symbol *)
        v

      )

    else

      raise 
        (Invalid_argument 
           ("State variable " ^ n ^ " redeclared with different type"))

  (* State variable is not in the hashcons table *)
  with Not_found | Hstate_var.Key_not_found _ -> 

    try 

      let _ = UfSymbol.uf_symbol_of_string n in

      raise 
        (Invalid_argument 
           ("State variable " ^ n ^ " conflicts with uninterpreted function symbol"))

    with Not_found -> 

      (debug stateVar
          "Variable %s, is_definition: %B"
          n
          d
       in

       (* Create an uninterpreted function symbol for the state variable *)
       let u = UfSymbol.mk_uf_symbol n [Type.mk_int ()] t in

       (* Hashcons state variable *)
       let sv = 
         Hstate_var.hashcons 
           ht 
           n 
           { var_type = t; uf_symbol = u; is_definition = d } 
       in

       (* Remember association of uninterpreted function symbol with
          state variable *)
       UfSymbol.UfSymbolHashtbl.add uf_symbols_map u sv;

       (* Return state variable *)
       sv)


(* Import a state variable from a different instance into this
   hashcons table *)
let import v = 
  mk_state_var 
    (name_of_state_var v) 
    (is_definition v) 
    (Type.import (type_of_state_var v))


(* Return a previously declared state variable *)
let state_var_of_string s = 

  (* Get previous declaration of symbol, raise {!Not_found} if
     symbol was not declared *)
  Hstate_var.find ht s 


(* Return a previously declared state variable *)
let state_var_of_original_name s = 

  (* Get internal name of original name *)
  let s' = (Kind1.Tables.internal_name_to_original_name s) in

  (* Return state variable *) 
  state_var_of_string s'

(* ********************************************************************* *)
(* Folding and utility functions on uninterpreted function symbols       *)
(* ********************************************************************* *)


(* Fold all variables in the hash-cons table *)
let fold f a = Hstate_var.fold f ht a

(* Fold all variables in the hash-cons table *)
let iter f = 
  Hstate_var.iter f ht


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
