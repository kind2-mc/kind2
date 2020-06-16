(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020 by the Board of Trustees of the University of Iowa

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

(** Manpulation of sets of equations and model elements
    (equations, assertions, assumptions, guarantees, node calls).
    Make the link between TransSys-level equations and Lustre model elements.

    @author Mickael Laurent *)


(* ----- TRANSITION SYSTEM LEVEL ----- *)

(** Represents an equation of the transition system.
    It is not specific to the 'equation' model elements
    of the source lustre program
    (any model element can be represented by this 'equation' type) *)
type ts_equation = {
  init_opened: Term.t ;
  init_closed: Term.t ;
  trans_opened: Term.t ;
  trans_closed: Term.t ;
}
type core

val term_of_ts_eq : ~init:bool -> ~closed:bool -> ts_equation -> Term.t

val get_actlits_of_scope : core -> Scope.t -> UfSymbol.t list
val get_ts_equation_of_actlit : core -> UfSymbol.t -> ts_equation
val get_sv_of_actlit : core -> UfSymbol.t -> StateVar.t
val core_size : core -> int
val scopes_of_core : core -> Scope.t list
val pick_element_of_core : core -> (Scope.t * UfSymbol.t * core) option

val empty_core : core
val add_new_ts_equation_to_core : Scope.t -> ts_equation -> core -> core
val add_from_other_core : core (* src *) -> Scope.t -> UfSymbol.t -> core (* dst *) -> core
val remove_from_core : UfSymbol.t -> core -> core
val filter_core : UfSymbol.t list -> core -> core
val filter_core_svs : StateVar.t list -> core -> core
val core_union : core -> core -> core
val core_diff : core -> core -> core

(* ----- LUSTRE MODEL LEVEL / MAPPING BACK ----- *)

type model_element
type loc_core

val equal_model_elements : model_element -> model_element -> bool
val get_model_elements_of_scope : loc_core -> Scope.t -> model_element list
val loc_core_size : loc_core -> int
val get_positions_of_model_element : model_element -> Lib.pos list
val scopes_of_loc_core : loc_core -> Scope.t list

val ts_equation_to_model_element : 'a InputSystem.t -> ts_equation -> model_element
val core_to_loc_core : 'a InputSystem.t -> core -> loc_core
val loc_core_to_new_core : core -> loc_core

val empty_Loc_core : loc_core
val add_to_loc_core :
  ?check_already_exists:bool -> Scope.t -> model_element -> loc_core -> loc_core
val remove_from_loc_core : Scope.t -> model_element -> loc_core -> loc_core
val loc_core_diff : loc_core -> loc_core -> loc_core

type category = [ `NODE_CALL | `CONTRACT_ITEM | `EQUATION | `ASSERTION | `ANNOTATIONS ]
val is_model_element_in_categories :
  model_element -> bool (* is_main_node *) -> category list -> bool

exception InitTransMismatch of int * int
val full_loc_core_for_sys :
  'a InputSystem.t -> TransSys.t -> ~only_top_level:bool -> loc_core
val filter_loc_core_by_categories :
  Scope.t (* Toplevel scope *) -> category list -> loc_core -> loc_core * loc_core

(* ----- PRETTY PRINTING ----- *)

type core_print_data

val loc_core_to_print_data :
  'a InputSystem.t -> TransSys.t -> string -> float option -> loc_core -> core_print_data

val attach_counterexample_to_print_data :
  core_print_data -> (StateVar.t * Model.value list) list -> core_print_data

val attach_property_to_print_data :
  core_print_data -> Property.t -> core_print_data

val pp_print_core_data :
  'a InputSystem.t -> Analysis.param -> TransSys.t -> Format.formatter -> core_print_data -> unit

val pp_print_core_data_xml :
  'a InputSystem.t -> Analysis.param -> TransSys.t -> Format.formatter -> core_print_data -> unit

val pp_print_core_data_json :
  'a InputSystem.t -> Analysis.param -> TransSys.t -> Format.formatter -> core_print_data -> unit

val pp_print_mcs_legacy : 'a InputSystem.t -> Analysis.param -> TransSys.t -> mua -> mua -> unit
