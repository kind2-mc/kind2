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

(** Interface between strategy and low-level analysis 

    An analysis distinguishes exactly one system as the top system,
    and looks at its properties and its contract. Subsystems are view
    either as abstract with their contract or as concrete with their
    implementations.

    The result of an analysis indicates which properties of the top
    system are invariant, whether the system conforms to its contract
    and whether it conforms to the preconditions of all its
    subsystems. 

    Values of type {!param} are produced by a strategy and
    parameterize the input-specific transitions system generators, in
    particular the slicing ot the cone of influence.

    Values of type {!result} are produced by running an analysis of a
    generated transition system. The accumulated results are used by a
    strategey to decide the next steps.

    @author Christoph Sticksel *)


(** Parameters for the creation of a transition system *)
type param = 

  { 
    
    (** The top system for the analysis run *)
    top : Scope.t;
    
    (** Systems flagged [true] are to be represented abstractly, those
        flagged [false] are to be represented by their
        implementation. *)
    abstraction_map : bool Scope.Map.t;

    (** Named properties that can be assumed invariant in subsystems *)
    assumptions : (Scope.t * Term.t) list;

  }


(** Result of analysing a transistion system *)
type result = 

  { 
    
    (** System analyzed (see [top] field of record) and parameters of
        the analysis *)
    param : param;

    (** All contracts of the system are valid *)
    contract_valid : bool;     

    (** Contract preconditions of all subsystems are valid *)
    sub_contracts_valid : bool;

    (** Additional properties proved invariant *)
    properties : string list;

  }


(** An analysis consists of a set of transition systems and a set of properties *)
type t = TransSys.t list * Property.t list


(** Return [true] if the scope is flagged as abstract in
    [abstraction_map]. Default to [false] if the scope is not in the
    map. *)
val scope_is_abstract : param -> Scope.t -> bool


(** Return assumptions of scope *)
val assumptions_of_scope : param -> Scope.t -> Term.t list  


(** Run one analysis *)
val run : t -> result


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
