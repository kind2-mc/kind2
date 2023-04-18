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


(** {1 TransSys-level cores} *)

(** Represents an equation of the transition system.
    It is not specific to the 'equation' model elements
    of the source lustre program
    (any model element can be represented by this 'equation' type).
    Intuitively, a ts_equation corresponds to a conjunct of the transition system.
    However, some conjuncts might be grouped together if they are related. *)
type ts_equation = {
  init_opened: Term.t ;
  init_closed: Term.t ;
  trans_opened: Term.t ;
  trans_closed: Term.t ;
}

(** Represents a set of equations at the level of the transition system.
    The equations are separated by scope.
    The equations inside are not localized (i.e. they are not mapped to the initial Lustre model).
    This type can be used when manipulating sets of equations: many operations are implemented
    (cores can be filtered, you can get an activation litteral or state variable for each equation, etc.) *)
type core

val term_of_ts_eq : init:bool -> closed:bool -> ts_equation -> Term.t

val get_actlits_of_scope : core -> Scope.t -> UfSymbol.t list
val get_ts_equation_of_actlit : core -> UfSymbol.t -> ts_equation
val get_sv_of_actlit : core -> UfSymbol.t -> StateVar.t

val eq_of_actlit_sv : core -> ?with_act:bool -> UfSymbol.t -> ts_equation
val eq_of_actlit_uf : core -> ?with_act:bool -> UfSymbol.t -> ts_equation

(*val get_actlit_of_sv : core -> StateVar.t -> UfSymbol.t*)
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

(** {1 Lustre-level cores} *)

(** Represents an equation at the level of the transition system
    together with localisation data that relates it to the original Lustre model.
 *)
type model_element

(** Represents a set of localized equations ([model_element]).
    The equations are separated by scope.
    This type can be used to store a set of equations together with their localization data
    and to perform some basic manipulations such as filtering the equations by Lustre category.
    However, the type [core] should be prefered for manipulations at the level of the transition system.
 *)
type loc_core

val equal_model_elements : model_element -> model_element -> bool
val get_model_elements_of_scope : loc_core -> Scope.t -> model_element list
val loc_core_size : loc_core -> int
val get_positions_of_model_element : model_element -> Position.position list
val scopes_of_loc_core : loc_core -> Scope.t list

val ts_equation_to_model_element : 'a InputSystem.t -> ts_equation -> model_element
val core_to_loc_core : 'a InputSystem.t -> core -> loc_core
val loc_core_to_new_core : loc_core -> core
val loc_core_to_filtered_core : loc_core -> core -> core

val empty_loc_core : loc_core
val add_to_loc_core :
  ?check_already_exists:bool -> Scope.t -> model_element -> loc_core -> loc_core
val remove_from_loc_core : Scope.t -> model_element -> loc_core -> loc_core
val loc_core_diff : loc_core -> loc_core -> loc_core

type category = [ `NODE_CALL | `CONTRACT_ITEM | `EQUATION | `ASSERTION | `ANNOTATIONS ]
val is_model_element_in_categories :
  model_element -> bool (* is_main_node *) -> category list -> bool

val full_loc_core_for_sys :
  'a InputSystem.t -> TransSys.t -> only_top_level:bool -> loc_core
val filter_loc_core_by_categories :
  Scope.t (* Toplevel scope *) -> category list -> loc_core -> loc_core * loc_core

(* Separate contract guarantees and mode elements from the rest of the model elements *)
val partition_loc_core_elts_by_guarantees_and_mode_elts : loc_core -> loc_core * loc_core

(** {1 Pretty Printing} *)

type core_print_data

val loc_core_to_print_data :
  'a InputSystem.t -> TransSys.t -> string -> float option -> loc_core -> core_print_data

val attach_counterexample_to_print_data :
  core_print_data -> (StateVar.t * Model.value list) list -> core_print_data

val attach_property_to_print_data :
  core_print_data -> Property.t -> core_print_data

val attach_approx_to_print_data :
  core_print_data -> bool -> core_print_data

val pp_print_core_data :
  'a InputSystem.t -> Analysis.param -> TransSys.t -> Format.formatter -> core_print_data -> unit

val pp_print_core_data_xml :
  ?tag:string ->
  'a InputSystem.t -> Analysis.param -> TransSys.t -> Format.formatter -> core_print_data -> unit

val pp_print_core_data_json :
  'a InputSystem.t -> Analysis.param -> TransSys.t -> Format.formatter -> core_print_data -> unit

val pp_print_no_solution :
  unknown:bool -> Format.formatter -> Property.t -> unit

val pp_print_no_solution_xml :
  string -> unknown:bool -> Format.formatter -> Property.t -> unit

val pp_print_no_solution_json :
  string -> unknown:bool -> Format.formatter -> Property.t -> unit

val all_wa_names_of_loc_core : loc_core -> string list
