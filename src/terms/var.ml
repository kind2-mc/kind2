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


(* An variable in a term 

   All variables are instances of state variables for now. *)
type var = 

  (* Variable is an instance of a state variable *)
  | StateVarInstance of StateVar.t * Numeral.t

  (* Variable is a constant state variable *)
  | ConstStateVar of StateVar.t

  (* Free variable to be bound to in a let expression or by a
     quantifier *)
  | FreeVar of HString.t * Type.t


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

    (* Two free variables *)
    | FreeVar (s1, t1), FreeVar (s2, t2) -> 

      (* Equal if the hashconsed strings are physically equal and the
         type are physically equal *)
      s1 == s2 && t1 == t2 

    | _ -> false

  (* Return hash of a variable *)
  let hash = function

    | StateVarInstance (sv, i) -> 
      
      (abs
         ((StateVar.hash_state_var sv) *
          (Numeral.(succ i |> succ |> to_int)) mod max_int))
      
    | ConstStateVar sv -> StateVar.hash_state_var sv

    | FreeVar (s, _) -> HString.hash s

end


(* Hashconsed variables *)
module Hvar = Hashcons.Make (Var_node)


(* Storage for hashconsed variables *)
(* The hash-cons table is private to the domain using it. A domain
   spawned to run an engine starts with a copy of the table of its
   parent, so it agrees with the parent on everything built before it
   started, and numbers what it builds afterwards on its own. A value
   built by another domain has to be imported before use. *)
let ht_key =
  Domain.DLS.new_key ~split_from_parent:Hvar.copy
    (fun () -> Hvar.create 251)

let ht () = Domain.DLS.get ht_key

let stats () = Hvar.stats (ht ())

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
      
  (* Pretty-print a free variable *)
  | FreeVar (s, _) -> 
    Format.fprintf ppf "%a" HString.pp_print_hstring s

(* Pretty-print a variable to the standard formatter *)
(* let print_var_node = pp_print_var_node Format.std_formatter *)

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
  | { Hashcons.node = FreeVar (_, t) } -> t


(* Return the state variable of a state variable instance *)
let state_var_of_state_var_instance = function 
  | { Hashcons.node = StateVarInstance (v, _) }-> v
  | { Hashcons.node = ConstStateVar v }-> v
  | { Hashcons.node = FreeVar _ } -> 
    raise (Invalid_argument "state_var_of_state_var_instance")


(* Return the offset of a state variable instance *)
let offset_of_state_var_instance = function 
  | { Hashcons.node = StateVarInstance (_, o) } -> o
  | { Hashcons.node = ConstStateVar _ } -> 
    raise (Invalid_argument "offset_of_state_var_instance")
  | { Hashcons.node = FreeVar _ } -> 
    raise (Invalid_argument "offset_of_state_var_instance")

(* Return a string for a free variable *)
let hstring_of_free_var = function 

  | { Hashcons.node = StateVarInstance _ } -> 
    raise (Invalid_argument "hstring_of_free_var")

  | { Hashcons.node = ConstStateVar _ } -> 
    raise (Invalid_argument "hstring_of_free_var")

  | { Hashcons.node = FreeVar (s, _) } -> s


let is_state_var_instance = function 
  | { Hashcons.node = StateVarInstance _ } -> true
  | _ -> false


let is_const_state_var = function 
  | { Hashcons.node = ConstStateVar _ } -> true
  | _ -> false


let is_free_var = function 
  | { Hashcons.node = FreeVar _ } -> true
  | _ -> false


(* ********************************************************************* *)
(* Constructors                                                          *)
(* ********************************************************************* *)

(* Return a hashconsed variable which is a constant state variable *)    
let mk_const_state_var v = 

  (* State variable is constant? *)
  if StateVar.is_const v then

    (* Create and hashcons constant state variable *)
    Hvar.hashcons (ht ()) (ConstStateVar v) ()

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
    Hvar.hashcons (ht ()) (StateVarInstance (v, o)) ()


(* Return a hashconsed variable which is a free variable *)    
let mk_free_var s t = 

  (* Create and hashcons free variable *)
  Hvar.hashcons (ht ()) (FreeVar (s, t)) ()


(* Import a variable from a different instance into this hashcons table *)
let import = function 

  | { Hashcons.node = StateVarInstance (v, o) } ->
    
    mk_state_var_instance (StateVar.import v) o

  | { Hashcons.node = ConstStateVar v } ->
    
    mk_const_state_var (StateVar.import v)

  | { Hashcons.node = FreeVar (s, t) } ->

    mk_free_var (HString.import s) (Type.import t)


(* Counter for index of fresh uninterpreted symbols.

   Private to each domain, copied from the parent at spawn: it
   holds hash-consed values, which only mean anything in the
   tables of the domain that built them. *)
let fresh_var_ids_key =
  Domain.DLS.new_key ~split_from_parent:Type.TypeHashtbl.copy
    (fun () -> Type.TypeHashtbl.create 7)

let fresh_var_ids () = Domain.DLS.get fresh_var_ids_key


(* Return name of a fresh uninterpreted symbol  *)
let rec next_fresh_var_node var_type =

  let fresh_var_id =
    let id =
      try Type.TypeHashtbl.find (fresh_var_ids ()) var_type
      with Not_found -> 1
    in
    Type.TypeHashtbl.replace (fresh_var_ids ()) var_type (succ id);
    id
  in

  let fresh_var_name = 

    HString.mk_hstring 
      (Format.asprintf 
         "__X_%a_%d" 
         Type.pp_print_type var_type
         fresh_var_id)
      
  in

  (* Candidate name for next fresh symbol *)
  let v = 
    FreeVar (fresh_var_name, var_type)
  in

  try 

    (* Check if candidate symbol is already declared *)
    let _ = Hvar.find (ht ()) v in
  
    (* Recurse to get another fresh symbol *)
    next_fresh_var_node var_type

  (* Candidiate symbol is not declared and can be used *)
  with Not_found -> fresh_var_name
    
    
(* Return a fresh uninterpreted symbol 

   TODO: How to make a completely separate namespace so that a symbol
   declared later does not clash? *)
let mk_fresh_var var_type = 

  (* Get name of a fresh uninterpreted symbol *)
  let v = next_fresh_var_node var_type in

  (* Create symbol with given signature *)
  mk_free_var v var_type 


(* Variables standing for the variables of a binder, keyed by the binding
   depth of the binder.

   Private to each domain, copied from the parent at spawn, for the same
   reason as the counter above. *)
let binder_vars_key =
  Domain.DLS.new_key ~split_from_parent:Type.TypeHashtbl.copy
    (fun () -> Type.TypeHashtbl.create 7)

let binder_vars () = Domain.DLS.get binder_vars_key


(* The variables [mk_binder_var] has made, so that they can be told apart from
   the variables of a term. *)
let is_binder_vars_key =
  Domain.DLS.new_key ~split_from_parent:VarHashtbl.copy
    (fun () -> VarHashtbl.create 7)

let is_binder_vars () = Domain.DLS.get is_binder_vars_key


(* Return the variable standing for the variable of the given type of a binder
   at the given binding depth.

   Opening a binder replaces the variable it binds by a free variable, so that
   a term under a binder can be handled as if it had none. The variable this
   returns is memoized rather than fresh, so that opening the same binder
   twice returns the same one: a caller that folds a term to the set of its
   variables must get the same set every time it is asked. It is obtained from
   [mk_fresh_var] the first time, so it is a name no term already uses.

   Two binders at the same depth binding a variable of the same type share
   this variable. That is sound because they are separate scopes: their bodies
   never mention both. *)
let mk_binder_var var_type depth =
  let by_depth =
    try Type.TypeHashtbl.find (binder_vars ()) var_type
    with Not_found ->
      let h = Hashtbl.create 7 in
      Type.TypeHashtbl.add (binder_vars ()) var_type h;
      h
  in
  try Hashtbl.find by_depth depth
  with Not_found ->
    let v = mk_fresh_var var_type in
    Hashtbl.add by_depth depth v;
    VarHashtbl.replace (is_binder_vars ()) v ();
    v


(* Return true if the variable was made by [mk_binder_var], and so stands for
   the variable of an opened binder rather than for a variable of the term
   that binder occurs in.

   Asked of every variable of every term folded to its variables, so answer
   the common case -- a term with no binder in it anywhere, which has left
   this table empty -- without hashing the variable. *)
let is_binder_var v =
  VarHashtbl.length (is_binder_vars ()) > 0
  && VarHashtbl.mem (is_binder_vars ()) v


(* ********************************************************************* *)
(* Changing offsets and state variables                                  *)
(* ********************************************************************* *)

(* Return a state variable at the given offset *)
let set_offset_of_state_var_instance v i = match v with

  (* State variable instance *)
  | { Hashcons.node = StateVarInstance (v, _) } -> 

    (* Keep state variable and set offset *)
    mk_state_var_instance v i

  (* Keep constant state variables or free variables *)
  | { Hashcons.node = ConstStateVar _ } 
  | { Hashcons.node = FreeVar _ } as v -> v


(* Add to the offset of a state variable instance

   Negative values are allowed *)
let bump_offset_of_state_var_instance v i = match v with

  (* State variable instance *)
  | { Hashcons.node = StateVarInstance (v, o) } -> 

    (* Keep state variable and add to offset *)
    mk_state_var_instance v Numeral.(o + i)

  (* Keep constant state variables or free variables *)
  | { Hashcons.node = ConstStateVar _ } 
  | { Hashcons.node = FreeVar _ } as v -> v


(* Replace every state variable by another *)
let map_state_var f v = match v with

  (* State variable instance  *)
  | { Hashcons.node = StateVarInstance (sv, o) } -> 

    (* Keep offset and change state variable *)
    mk_state_var_instance (f sv) o

  (* Constant state variable *)
  | { Hashcons.node = ConstStateVar sv } -> 

    (* Change state variable *)
    mk_const_state_var (f sv)

  (* Keep free variables unchanged *)
  | { Hashcons.node = FreeVar _ } as v -> v


(* ********************************************************************* *)
(* Unrolling of state variable instances to uninterpreted constants      *)
(* ********************************************************************* *)

module StringMap = Map.Make(String)

(* Maps strings to state var instances.

   Private to each domain, copied from the parent at spawn: it
   holds hash-consed values, which only mean anything in the
   tables of the domain that built them. *)
let unrolled_var_map_key =
  Domain.DLS.new_key ~split_from_parent:(fun r -> ref !r)
    (fun () -> ref StringMap.empty)

let unrolled_var_map () = Domain.DLS.get unrolled_var_map_key
(* Adds a mapping between [string] and [var]. Returns [true] if
   [string] was already bound in the map. *)
let update_unrolled_var_map string var =
  (unrolled_var_map ()) := StringMap.add string var !(unrolled_var_map ())
(* Looks for the value associated to [string].

   The map is immutable and the reference is only ever set to a newer
   map, so the read needs no lock: it returns a map that was current at
   some point, which is all a lookup can ask for. *)
let find_unrolled_var_map string =
  StringMap.find string !(unrolled_var_map ())

let unrolled_uf_of_state_var_instance = function
  | ({ Hashcons.node = ConstStateVar sv } as var) ->

      (* Getting the uf symbol of the state var. *)
      let uf = StateVar.uf_symbol_of_state_var sv in

      (* Updating the map. *)
      update_unrolled_var_map (UfSymbol.name_of_uf_symbol uf) var ;

      uf

  | ({ Hashcons.node = FreeVar (_, ty) } as var) ->

    (* Creating a uf symbol for the variable. *)
    let uf =
      UfSymbol.mk_fresh_uf_symbol [] ty in
      (* UfSymbol.mk_uf_symbol (HString.string_of_hstring h) [] ty in *)

    (* Updating the map. *)
    update_unrolled_var_map (UfSymbol.name_of_uf_symbol uf) var ;
    
    uf

  | ({ Hashcons.node = StateVarInstance (v, o) } as var) ->

     (* Getting the uf symbol and type of the state var. *)
     let uf = StateVar.uf_symbol_of_state_var v in
     let ty = StateVar.type_of_state_var v in
     
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
     UfSymbol.(mk_uf_symbol string (arg_type_of_uf_symbol uf) ty)



(* Declares constant variables as constant ufsymbols using the
    provided function. *)
let rec declare_constant_vars declare = function
  | ({ Hashcons.node = ConstStateVar _ } as var) :: tail ->

      (* Declaring the uf. *)
      declare (unrolled_uf_of_state_var_instance var) ;

      (* Looping. *)
      declare_constant_vars declare tail

  | _ :: tail -> declare_constant_vars declare tail

  | [] -> ()

(* Declares non constant variables as constant ufsymbols using the
    provided function. *)
let rec declare_vars declare = function

  | ({ Hashcons.node = StateVarInstance (_, _) } as var)
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

(* Gets the state var instance associated with an unrolled
   uninterpreted symbol. Throws [Not_found] if the sym is unknown. *)
let state_var_instance_of_uf_symbol uf_sym =
  UfSymbol.string_of_uf_symbol uf_sym |> find_unrolled_var_map



(*******************************)
(* Encoding of array variables *)
(*******************************)

let encode_select v =
  StateVar.encode_select @@ state_var_of_state_var_instance v





(*
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
