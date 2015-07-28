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

(** Parameters for the creation of a transition system *)
type param = 

  { 
    
    (** The top system for the analysis run *)
    top : Scope.t;
    
    
    (** Systems flagged [true] are to be represented abstractly, those
        flagged [false] are to be represented by their
        implementation. *)
    abstraction_map : bool Scope.Map.t;

    (** Properties that can be assumed invariant in subsystems *)
    assumptions : (Scope.t * Term.t) list;

  }


(** Result of analysing a transistion system *)
type result = 

  { 
    
    (** System analyzed (see [top] field of record) and parameters of
        the analysis *)
    param : param;

    (** All contracts of the system are valid. *)
    contract_valid : bool;

    (** Contract preconditions of all subsystems are valid *)
    sub_contracts_valid : bool;

    (** Additional properties proved invariant *)
    properties : string list;

  }


(** An analysis consists of a set of transition systems and a set of properties *)
type t = TransSys.t list * Property.t list



(* Return [true] if the scope is flagged as abstract in
   [abstraction_map]. Default to [false] if the node is not in the
   map. *)
let scope_is_abstract { abstraction_map } scope = 

  try

    (* Find node in abstraction map by name *)
    Scope.Map.find
      scope
      abstraction_map 
      
  (* Assume node to be concrete if not in map *)
  with Not_found -> false


(* Return assumptions of scope *)
let assumptions_of_scope { assumptions } scope = 

  List.fold_left 
    (fun a (s, t) -> 
       if Scope.equal s scope then t :: a else a)
    []
    assumptions

(* Abstraction of a property source. *)
type prop_kind = | Contract | Subreq | Prop

(* Creates a [result] from a [param] and a [t]. *)
let result_of (sys_list, props) param =

  (* The [prop_kind] of a property. *)
  let rec kind_of_prop prop = match prop.Property.prop_source with
    | Property.Requirement _ -> Subreq
    | Property.Instantiated (_, prop) -> kind_of_prop prop
    | Property.ContractGlobalEnsure _ -> Contract
    | Property.ContractModeEnsure _ -> Contract
    | _ -> Prop
  in

  let rec loop contract_valid subreqs_valid valid_props = function
    | prop :: tail -> (
      match kind_of_prop prop, Property.get_prop_status prop with

      | _, Property.PropInvariant ->
        loop
          contract_valid
          subreqs_valid
          (prop.Property.prop_name :: valid_props)
          tail

      | Contract, _ ->
        loop false subreqs_valid valid_props tail
      | Subreq, _ ->
        loop contract_valid false valid_props tail
      | _, _ ->
        loop contract_valid subreqs_valid valid_props tail
    )
    | [] -> contract_valid, subreqs_valid, valid_props
  in

  let contract_valid, sub_contracts_valid, properties =
    loop true true [] props
  in

  { param ; contract_valid ; sub_contracts_valid ; properties }


(** Run one analysis *)
let run _ = assert false


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  

