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

(** Utilty functions for transition systems 

    Functions that use term data structures and can be used by
    any module above {!TransSys} go here.
*)

(*
type invariants = Term.t list
type model = (Var.t * Term.t) list
type path = (StateVar.t * Term.t list) list
type property = (string * Term.t)
type properties = property list
type cex = (property list * path)
type cexs = cex list
*)

(** {1 Properties of transition systems} *)


(** Source of a property *)
type prop_source =

  (** Property is from an annotation *)
  | PropAnnot of Lib.position

  (** Property is part of a contract *)
  | Contract of Lib.position * string

  (** Property was generated, for example, from a subrange
      constraint *)
  | Generated of StateVar.t list

  (** Property is a requirement of a subnode. *)
  | Requirement of Lib.position * string list * StateVar.t list

  (** Property is an instance of a property in a called node

      Reference the instantiated property by the [scope] of the
      subsystem and the name of the property *)
  | Instantiated of string list * string

val pp_print_prop_source : Format.formatter -> prop_source -> unit


(** {1 Utilities functions on terms } *)


(** {2 Default values } *)

(** Return the default value of the type: 

    By default, a Boolean value is false, integer and real values are
    zero, values in a range are equal to the lower bound of the
    range. Array scalar types do not have defaults. The function fails
    with [Invalid_argument] in this case. *)
val default_of_type : Type.t -> Term.t


(** {2 Logic fragments } *)

(** A feature of a logic fragment for terms *)
type feature =
  | Q  (** Quantifiers *)
  | UF (** Equality over uninterpreted functions *)
  | IA (** Integer arithmetic *)
  | RA (** Real arithmetic *)
  | LA (** Linear arithmetic *)
  | NA (** Non-linear arithmetic *)

(** Set of features *)
module FeatureSet : Set.S with type elt = feature

(** Logic fragments for terms *)
type features = FeatureSet.t

(** Returns the sup of the logics given as arguments *)
val sup_logics : features list -> features

(** Returns the logic fragment used by a term *)
val logic_of_term : Term.t -> features

(** Logic fragments for terms *)
type logic = [ `None | `Inferred of features | `SMTLogic of string ]

(** Print a logic *)
val pp_print_logic : Format.formatter -> logic -> unit

(** String correspinding to a logic *)
val string_of_logic : logic -> string

(** Gathers signal related stuff. *)
module Signals: sig

  (** Pretty printer for signal info. *)
  val pp_print_signals: Format.formatter -> unit -> unit

  (** Sets the handler for sigalrm to ignore. *)
  val ignore_sigalrm: unit -> unit
  (** Sets the handler for sigint to ignore. *)
  val ignore_sigint: unit -> unit
  (** Sets the handler for sigquit to ignore. *)
  val ignore_sigquit: unit -> unit
  (** Sets the handler for sigterm to ignore. *)
  val ignore_sigterm: unit -> unit

  (** Sets a timeout handler for sigalrm. *)
  val set_sigalrm_timeout: unit -> unit
  (** Sets an exception handler for sigalarm. *)
  val set_sigalrm_exn: unit -> unit
  (** Sets a handler for sigint. *)
  val set_sigint: unit -> unit
  (** Sets a handler for sigquit. *)
  val set_sigquit: unit -> unit
  (** Sets a handler for sigterm. *)
  val set_sigterm: unit -> unit

  (** Sets a timeout. *)
  val set_timeout: float -> unit
  (** Sets a timeout based on the timeout flag. *)
  val set_timeout_from_flag: unit -> unit
  (** Deactivates timeout. *)
  val unset_timeout: unit -> unit

  (** Raise exception on ctrl+c if true. *)
  val catch_break: bool -> unit

end
 
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

