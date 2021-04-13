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


(** Current status of a property *)
type prop_status =

  | PropUnknown
  (** Status of property is unknown *)

  | PropKTrue of int
  (** Property is true for at least k steps *)

  | PropInvariant of Certificate.t
  (** Property is true in all reachable states *)

  | PropFalse of (StateVar.t * Model.value list) list
  (** Property is false at some step *)



(** A property of a transition system *)
type t = {
  prop_name : string ;
  (** Identifier for the property *)

  prop_source : prop_source ;
  (** Source of the property *)

  prop_term : Term.t ;
  (** Term with variables at offsets [prop_base] and [prop_base - 1] *)

  mutable prop_status : prop_status ;
  (** Current status *)
}


(** Source of a property *)
and prop_source =

  | PropAnnot of Lib.position
  (** Property is from an annotation *)

  | Generated of Lib.position option * StateVar.t list
  (** Property was generated, for example, from a subrange constraint *)

  | Instantiated of Scope.t * t
  (** Property is an instance of a property in a called node.

     Reference the instantiated property by the [scope] of the subsystem and
     the name of the property *)

  | Assumption of Lib.position * (Scope.t * Lib.position)
  (** Contract assumption that a caller has to prove.

     Reference the assumption by its position, the scope of the subsystem,
     and the position of the node call *)

  | Guarantee of (Lib.position * Scope.t)
  (** Contract guarantees. *)
                 
  | GuaranteeOneModeActive of (Lib.position * Scope.t)
  (** Contract: at least one mode active. *)

  | GuaranteeModeImplication of (Lib.position * Scope.t)
  (** Contract: mode implication. *)

  | Candidate of prop_source option
  (** User supplied candidate invariant *)


val copy : t -> t

(** Pretty-prints a property source. *)
val pp_print_prop_source : Format.formatter -> prop_source -> unit

(** Pretty-prints a property status. *)
val pp_print_prop_status : Format.formatter -> prop_status -> unit

(** Pretty-prints a property (name and source only). *)
val pp_print_prop_quiet : Format.formatter -> t -> unit

(** Pretty-prints a property. *)
val pp_print_property : Format.formatter -> t -> unit

(** Return [true] if the status of the property is known *)
val prop_status_known : prop_status -> bool

val set_prop_status : t -> prop_status -> unit
val set_prop_invariant : t -> Certificate.t ->unit
val set_prop_ktrue : t -> int -> unit
val set_prop_false : t -> (StateVar.t * Model.value list) list -> unit

val set_prop_unknown : t -> unit

val length_of_cex :  (StateVar.t * Model.value list) list -> int

val get_prop_status : t -> prop_status


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
