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

  (** Status of property is unknown *)
  | PropUnknown

  (** Property is true for at least k steps *)
  | PropKTrue of int

  (** Property is true in all reachable states *)
  | PropInvariant of Certificate.t

  (** Property is false at some step *)
  | PropFalse of (StateVar.t * Model.term_or_lambda list) list



(** A property of a transition system *)
type t = {
  (** Identifier for the property *)
  prop_name : string ;

  (** Source of the property *)
  prop_source : prop_source ;

  (** Term with variables at offsets [prop_base] and [prop_base - 1] *)
  prop_term : Term.t ;

  (** Current status *)
  mutable prop_status : prop_status ;
}


(** Source of a property *)
and prop_source =

  (** Property is from an annotation *)
  | PropAnnot of Lib.position

  (** Property was generated, for example, from a subrange constraint *)
  | Generated of StateVar.t list

  (** Property is an instance of a property in a called node.

     Reference the instantiated property by the [scope] of the subsystem and
     the name of the property *)
  | Instantiated of Scope.t * t

  (** Contract assumption that a caller has to prove. The list of state vars is
      the guarantees that proving the requirement yields. *)
  | Assumption of Lib.position * string list

  (** Contract guarantees. *)
  | Guarantee of (Lib.position * Scope.t)
                 
  (** Contract: at least one mode active. *)
  | GuaranteeOneModeActive of Scope.t
                                
  (** Contract: mode implication. *)
  | GuaranteeModeImplication of (Lib.position * Scope.t)

  (** User supplied candidate invariant *)
  | Candidate of prop_source option


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
val set_prop_false : t -> (StateVar.t * Model.term_or_lambda list) list -> unit

val length_of_cex :  (StateVar.t * Model.term_or_lambda list) list -> int

val get_prop_status : t -> prop_status


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
