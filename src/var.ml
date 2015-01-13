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


(* An variable in a term 

   All variables are instances of state variables for now. *)
type var = 

  (* Variable is an instance of a state variable *)
  | StateVarInstance of StateVar.t * Numeral.t

  (* Variable is a constant state variable *)
  | ConstStateVar of StateVar.t

  (* Temporary variable to be bound to in a let expression or by a
     quantifier *)
  | TempVar of HString.t * Type.t


(* A private type that cannot be constructed outside this module

   This is necessary to ensure the invariant that all subterms of a
   term are hashconsed. We can construct and thus pattern match on the
   {!var} type, but not on the {!var_node} type *)
type var_node = var


(* Properties of a variable

   Only keep essential properties here that are shared by all
   modules. For local properties use a hashtable in the respective
   module.

   No properties for now *)
type var_prop = unit


(* Hashconsed variable *)
type t = (var_node, var_prop) Hashcons.hash_consed


(* Hashing and equality on variables *)
module Var_node = struct

  (* The type of a variable *)
  type t = var_node

  (* Properties of a variable

     No properties for now *)
  type prop = var_prop

  (* Equality of two variables *)
  let equal v1 v2 = match v1, v2 with

    (* Two state variable instances *)
    | StateVarInstance (sv1, i1), StateVarInstance (sv2, i2) ->

      (* Equal if the state variables are equal and the indexes are
         equal *)
      StateVar.equal_state_vars sv1 sv2 && Numeral.equal i1 i2

    (* Two constant state variables *)
    | ConstStateVar sv1, ConstStateVar sv2 ->

      (* Equal if the state variables are equal *)
      StateVar.equal_state_vars sv1 sv2

    (* Two temporary variables *)
    | TempVar (s1, t1), TempVar (s2, t2) -> 

      (* Equal if the hashconsed strings are physically equal and the
         type are physically equal *)
      s1 == s2 && t1 == t2 

    | _ -> false

  (* Return hash of a variable *)
  let hash = function

    | StateVarInstance (sv, i) -> 
      
      (abs ((StateVar.hash_state_var sv) * (Numeral.to_int i)) mod max_int)
      
    | ConstStateVar sv -> StateVar.hash_state_var sv

    | TempVar (s, _) -> HString.hash s

end


(* Hashconsed variables *)
module Hvar = Hashcons.Make (Var_node)


(* Storage for hashconsed variables *)
let ht = Hvar.create 251

let stats () = Hvar.stats ht

(* ********************************************************************* *)
(* Hashtables, maps and sets                                             *)
(* ********************************************************************* *)


(* Comparison function on variables *)
let compare_vars = Hashcons.compare

(* Equality function on variables *)
let equal_vars = Hashcons.equal 

(* Hashing function on variables *)
let hash_var = Hashcons.hash 


(* Module as input to functors *)
module HashedVar = struct 

  (* Dummy type to prevent writing [type t = t] which is cyclic *)
  type z = t
  type t = z

  (* Compare tags of hashconsed variables for equality *)
  let equal = equal_vars
    
  (* Use hash of variables *)
  let hash = hash_var

end

(* Module as input to functors *)
module OrderedVar = struct 

  (* Dummy type to prevent writing [type t = t] which is cyclic *)
  type z = t
  type t = z

  (* Compare tags of hashconsed variables *)
  let compare = compare_vars

end

(* Hashtable of variables *)
module VarHashtbl = Hashtbl.Make (HashedVar)

(* Set of variables

   Try to turn this into a patricia set with Hset for another small
   gain in efficiency. *)
module VarSet = Set.Make (OrderedVar)


(* Map of variables

   Try to turn this into a patricia set with Hset for another small
   gain in efficiency. *)
module VarMap = Map.Make (OrderedVar)


(* ********************************************************************* *)
(* Pretty-printing                                                       *)
(* ********************************************************************* *)


(* Pretty-print a variable *)
let pp_print_var_node ppf = function 

  (* Pretty-print an instance of a state variable *)
  | StateVarInstance (v, o) ->
    Format.fprintf ppf 
      "%a@%a" 
      StateVar.pp_print_state_var v
      Numeral.pp_print_numeral o

  (* Pretty-print a constant state variable *)
  | ConstStateVar v ->
    Format.fprintf ppf 
      "%a" 
      StateVar.pp_print_state_var v
      
  (* Pretty-print a temporary variable *)
  | TempVar (s, _) -> 
    Format.fprintf ppf "%a" HString.pp_print_hstring s

(* Pretty-print a variable to the standard formatter *)
let print_var_node = pp_print_var_node Format.std_formatter

(* Pretty-print a hashconsed variable *)
let pp_print_var ppf { Hashcons.node = v } = pp_print_var_node ppf v

(* Pretty-print a hashconsed variable to the standard formatter *)
let print_var = pp_print_var Format.std_formatter 

(* Return a string representation of a hashconsed variable *)
let string_of_var { Hashcons.node = v } = string_of_t pp_print_var_node v 


(* ********************************************************************* *)
(* Accessor functions                                                    *)
(* ********************************************************************* *)


(* Return the type of the variable *)
let type_of_var = function 
  | { Hashcons.node = StateVarInstance (v, _) } -> StateVar.type_of_state_var v
  | { Hashcons.node = ConstStateVar v } -> StateVar.type_of_state_var v
  | { Hashcons.node = TempVar (_, t) } -> t


(* Return the state variable of a state variable instance *)
let state_var_of_state_var_instance = function 
  | { Hashcons.node = StateVarInstance (v, _) }-> v
  | { Hashcons.node = ConstStateVar v }-> v
  | { Hashcons.node = TempVar _ } -> 
    raise (Invalid_argument "state_var_of_state_var_instance")


(* Return the offset of a state variable instance *)
let offset_of_state_var_instance = function 
  | { Hashcons.node = StateVarInstance (_, o) } -> o
  | { Hashcons.node = ConstStateVar _ } -> 
    raise (Invalid_argument "offset_of_state_var_instance")
  | { Hashcons.node = TempVar _ } -> 
    raise (Invalid_argument "offset_of_state_var_instance")

let hstring_of_temp_var = function 

  | { Hashcons.node = StateVarInstance _ } -> 
    raise (Invalid_argument "string_of_temp_var")

  | { Hashcons.node = ConstStateVar _ } -> 
    raise (Invalid_argument "string_of_temp_var")

  | { Hashcons.node = TempVar (s, _) } -> s


let is_state_var_instance = function 
  | { Hashcons.node = StateVarInstance _ } -> true
  | _ -> false


let is_const_state_var = function 
  | { Hashcons.node = ConstStateVar _ } -> true
  | _ -> false


let is_temp_var = function 
  | { Hashcons.node = TempVar _ } -> true
  | _ -> false


(* ********************************************************************* *)
(* Constructors                                                          *)
(* ********************************************************************* *)


(* Return a hashconsed variable which is a constant state variable *)    
let mk_const_state_var v = 

  (* State variable is constant? *)
  if StateVar.is_const v then

    (* Create and hashcons constant state variable *)
    Hvar.hashcons ht (ConstStateVar v) ()

  else

    raise (Invalid_argument "mk_const_state_var")


(* Return a hashconsed variable which is an instance of a state variable *)    
let mk_state_var_instance v o = 

  (* State variable is constant? *)
  if StateVar.is_const v then

    (* Create and hashcons constant state variable *)
    mk_const_state_var v

  else

    (* Create and hashcons state variable instance *)
    Hvar.hashcons ht (StateVarInstance (v, o)) ()


(* Return a hashconsed variable which is a temporary variable *)    
let mk_temp_var s t = 

  (* Create and hashcons temporary variable *)
  Hvar.hashcons ht (TempVar (s, t)) ()


(* Import a variable from a different instance into this hashcons table *)
let import = function 

  | { Hashcons.node = StateVarInstance (v, o) } ->
    
    mk_state_var_instance (StateVar.import v) o

  | { Hashcons.node = ConstStateVar v } ->
    
    mk_const_state_var (StateVar.import v)

  | { Hashcons.node = TempVar (s, t) } ->

    mk_temp_var (HString.import s) (Type.import t)


(* Counter for index of fresh uninterpreted symbols *)
let fresh_var_ids = Type.TypeHashtbl.create 7


(* Return name of a fresh uninterpreted symbol  *)
let rec next_fresh_var_node var_type = 

  let fresh_var_id = 

    try 
      
      Type.TypeHashtbl.find fresh_var_ids var_type 
        
    with Not_found -> 1

  in

  Type.TypeHashtbl.replace fresh_var_ids var_type (succ fresh_var_id);

  let fresh_var_name = 

    HString.mk_hstring 
      (Format.asprintf 
         "__X_%a_%d" 
         Type.pp_print_type var_type
         fresh_var_id)
      
  in

  (* Candidate name for next fresh symbol *)
  let v = 
    TempVar (fresh_var_name, var_type)
  in

  try 

    (* Check if candidate symbol is already declared *)
    let _ = Hvar.find ht v in
  
    (* Recurse to get another fresh symbol *)
    next_fresh_var_node var_type

  (* Candidiate symbol is not declared and can be used *)
  with Not_found | Hvar.Key_not_found _ -> fresh_var_name
    
    
(* Return a fresh uninterpreted symbol 

   TODO: How to make a completely separate namespace so that a symbol
   declared later does not clash? *)
let mk_fresh_var var_type = 

  (* Get name of a fresh uninterpreted symbol *)
  let v = next_fresh_var_node var_type in

  (* Create symbol with given signature *)
  mk_temp_var v var_type 


(* Add to the offset of a state variable instance

   Negative values are allowed *)
let bump_offset_of_state_var_instance i = function 

  | { Hashcons.node = StateVarInstance (v, o) } -> 
    mk_state_var_instance v Numeral.(o + i)

  | { Hashcons.node = ConstStateVar _ } as v-> v

  | { Hashcons.node = TempVar _ } -> 
    raise (Invalid_argument "bump_offset_of_state_var_instance")

module StringMap = Map.Make(String)

(* Maps strings to state var instances. *)
let unrolled_var_map = ref StringMap.empty
(* Adds a mapping between [string] and [var]. Returns [true] if
   [string] was already bound in the map. *)
let update_unrolled_var_map string var =
  unrolled_var_map := StringMap.add string var !unrolled_var_map
(* Looks for the value associated to [string]. *)
let find_unrolled_var_map string =
  StringMap.find string !unrolled_var_map

let unrolled_uf_of_state_var_instance = function
  | ({ Hashcons.node = ConstStateVar sv } as var) ->

      (* Getting the uf symbol of the state var. *)
      let uf = StateVar.uf_symbol_of_state_var sv in

      (* Updating the map. *)
      update_unrolled_var_map (UfSymbol.name_of_uf_symbol uf) var ;

      uf

  | ({ Hashcons.node = StateVarInstance (v, o) } as var) ->

     (* Getting the uf symbol of the state var. *)
     let uf = StateVar.uf_symbol_of_state_var v in

     (* Building the string representing the unrolled state var. *)
     let string =
       String.concat
         "@"
         [ UfSymbol.name_of_uf_symbol uf ;
           (* String representation of the offset. *)
           Numeral.string_of_numeral o ]
     in

     (* Updating the map. *)
     update_unrolled_var_map string var ;
     
     (* Declaring the uf. *)
     UfSymbol.(
       mk_uf_symbol
         string (arg_type_of_uf_symbol uf) (res_type_of_uf_symbol uf)
     )

(* Declares constant variables as constant ufsymbols using the
    provided function. *)
let rec declare_constant_vars declare = function
  | ({ Hashcons.node = ConstStateVar sv } as var) :: tail ->

      (* Declaring the uf. *)
      declare (unrolled_uf_of_state_var_instance var) ;

      (* Looping. *)
      declare_constant_vars declare tail

  | _ :: tail -> declare_constant_vars declare tail

  | [] -> ()

(* Declares non constant variables as constant ufsymbols using the
    provided function. *)
let rec declare_vars declare = function

  | ({ Hashcons.node = StateVarInstance (v, o) } as var)
    :: tail ->
     
     (* Declaring the uf. *)
     declare (unrolled_uf_of_state_var_instance var) ;

     (* Looping. *)
     declare_vars declare tail

  | _ :: tail -> declare_vars declare tail

  | [] -> ()

(* Gets the state var instance associated with a unrolled
   symbol. Throws [Not_found] if the sym is unknown. *)
let state_var_instance_of_symbol sym =
  Symbol.string_of_symbol sym |> find_unrolled_var_map


(*
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
