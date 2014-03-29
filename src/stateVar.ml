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


(* State variable to be has-consed

   Name of a state variable is a string with a list of strings as
   its scope *)
type state_var = string * string list 

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

    (* State variable is a non-deterministic input *)
    is_input : bool

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
  let hash = Hashtbl.hash_param 100 100

  (* Equality of state variables is comparison of strings *)
  let equal = (=)

end


(* Hashconsed state variables *)
module Hstate_var = Hashcons.Make (State_var_node)


(* Storage for state variables *)
let ht = Hstate_var.create 251

let stats () = Hstate_var.stats ht


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


(* Pretty-print a scoped name of a state variable *)
let pp_print_state_var_name ppf (n, s) = 
  Format.fprintf ppf 
    "%a.%s" 
    (pp_print_list Format.pp_print_string ".") s
    n

(* Return a string representation of the name of a state variable *)
let string_of_state_var_name (n, s) = 
  string_of_t pp_print_state_var_name (n, s) 

(* Pretty-print a state variable *)
let pp_print_state_var_node ppf (n, s) = 
  pp_print_state_var_name ppf (n, s)

(*
(* Pretty-print a state variable as it occurred in the original input *)
let pp_print_state_var_node_original ppf s = 
  Format.pp_print_string ppf (Kind1.Tables.internal_name_to_original_name s)
*)

(* Pretty-print a hashconsed state variable *)
let pp_print_state_var ppf { Hashcons.node = (n, s) } =
  pp_print_state_var_node ppf (n, s)

(*
(* Pretty-print a hashconsed state variable as it occurred in the
   original input *)
let pp_print_state_var_original ppf = function 

  | { Hashcons.node = (n, s) } -> pp_print_state_var_node_original ppf n

  (* Cannot have scopes in old parser *)
  | _ -> invalid_arg "pp_print_state_var_original"
*)

(* Return a string representation of a hashconsed state variable *)
let string_of_state_var s = string_of_t pp_print_state_var s


(* ********************************************************************* *)
(* Accessor function                                                     *)
(* ********************************************************************* *)


(* Identifier of a state variable *)
let name_of_state_var { Hashcons.node = (n, _) } = n

(* Identifier of a state variable *)
let scope_of_state_var { Hashcons.node = (_, s) } = s

(* Type of a state variable *)
let type_of_state_var { Hashcons.prop = { var_type = t } } = t

(* Uninterpreted function symbol of a state variable *)
let uf_symbol_of_state_var { Hashcons.prop = { uf_symbol = u } } = u

(* Uninterpreted function symbol of a state variable *)
let state_var_of_uf_symbol u = 
  UfSymbol.UfSymbolHashtbl.find uf_symbols_map u
  
(* Return true if state variable is an input *)
let is_input { Hashcons.prop = { is_input } } = is_input


(* ********************************************************************* *)
(* Constructors                                                          *)
(* ********************************************************************* *)


(* Hashcons a state variable *)
let mk_state_var state_var_name state_var_scope state_var_type is_input = 

  try 

    (* Get previous declaration of identifier *)
    let { Hashcons.prop = p } as v = 
      Hstate_var.find ht (state_var_name, state_var_scope)  
    in

    if 

      (* Given type is a subtype of declared type? *)
      Type.check_type state_var_type (type_of_state_var v)  

    then

      (

        (* Return previously declared symbol *)
        v

      )

    else

      raise 
        (Invalid_argument 
           (Format.asprintf
              "State variable %a redeclared with different type" 
              pp_print_state_var_name 
              (state_var_name, state_var_scope)))

  (* State variable is not in the hashcons table *)
  with Not_found | Hstate_var.Key_not_found _ -> 
    
    try 
      
      let _ = 
        UfSymbol.uf_symbol_of_string 
          (string_of_state_var_name (state_var_name, state_var_scope))
      in

      raise 
        (Invalid_argument 
           (Format.asprintf 
              "State variable %a conflicts with uninterpreted \
               function symbol"
              pp_print_state_var_name 
              (state_var_name, state_var_scope)))

    with Not_found -> 

       (* Create an uninterpreted function symbol for the state variable *)
       let state_var_uf_symbol = 
         UfSymbol.mk_uf_symbol 
           (string_of_state_var_name 
              (state_var_name, state_var_scope))
           [Type.mk_int ()] 
           state_var_type 
       in

       (* Hashcons state variable *)
       let state_var = 
         Hstate_var.hashcons 
           ht 
           (state_var_name, state_var_scope) 
           { var_type = state_var_type; 
             uf_symbol = state_var_uf_symbol;
             is_input = is_input } 
       in

       (* Remember association of uninterpreted function symbol with
          state variable *)
       UfSymbol.UfSymbolHashtbl.add 
         uf_symbols_map 
         state_var_uf_symbol 
         state_var;

       (* Return state variable *)
       state_var


(* Import a state variable from a different instance into this
   hashcons table *)
let import v = 
  mk_state_var 
    (name_of_state_var v) 
    (scope_of_state_var v) 
    (Type.import (type_of_state_var v))
    (is_input v)

(* Return a previously declared state variable *)
let state_var_of_string (state_var_name, state_var_scope) = 

  (* Get previous declaration of symbol, raise {!Not_found} if
     symbol was not declared *)
  Hstate_var.find ht (state_var_name, state_var_scope)


(* ********************************************************************* *)
(* Folding and utility functions on state variables                      *)
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
