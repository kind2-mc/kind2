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

(** Abstract system 

    The functions and data types of this module are polymorphic in the
    actual source of the input system. See functions in {!InputSystem}
    to delegate to concrete implementations of an input format.

    A system is a set of subsystems, identified by a unique scope and
    containing instances of one other in a directed acyclic
    manner. Each system has at least an implementation or a contract,
    it may have both.

    @author Christoph Sticksel *)

(** A system parameterized by its actual source *)
type 'a t = {
  
  scope: Scope.t ;         (** Name of the system as a scope *)

  source : 'a ;            (** Original input *)
  
  has_contract : bool ;    (** System can be abstracted to its contract *)

  has_modes : bool ;       (** System has modes. *)

  has_impl : bool ;        (** System can be refined to its implementation *)

  subsystems : 'a t list ; (** Sub-systems *)
}

(** Strategy info of a subsystem. *)
val strategy_info_of: 'a t -> Strategy.info

(** Return all subsystems in topological order with the top system at
    the head of the list *)
val all_subsystems : 'a t -> 'a t list

(** Return the subsystem of the given scope 

   Raise [Not_found] if there is no subsystem of that scope *)
val find_subsystem : 'a t -> Scope.t -> 'a t

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
