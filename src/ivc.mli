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

(** Computation of Inductive Validity Cores and Maximal Unsafe Abstractions / Minimal Cut Sets

    This implementation is inspired from the following paper:

    Berryhill, Ryan & Veneris, Andreas. (2019).
    Chasing Minimal Inductive Validity Cores in Hardware Model Checking.
    19-27. 10.23919/FMCAD.2019.8894268. 

    @author Mickael Laurent *)

module ScMap = Scope.Map
module SVSet = StateVar.StateVarSet

(* ----- INDUCTIVE VALIDITY CORES ----- *)

type term_cat =
| NodeCall of string * SVSet.t
| ContractItem of StateVar.t * LustreContract.svar * LustreNode.contract_item_type
| Equation of StateVar.t
| Assertion of StateVar.t
| Unknown

type equation = {
  init_opened: Term.t ;
  init_closed: Term.t ;
  trans_opened: Term.t ;
  trans_closed: Term.t ;
}

type loc = {
  pos: Lib.position ;
  index: LustreIndex.index ;
}

type loc_equation = equation * (loc list) * term_cat

type ivc = (Property.t list * loc_equation list ScMap.t)

val compare_loc : loc -> loc -> int

(** For a given transition system, returns the full initial inductive validity core
(not minimized, so that it contains all the equations of the transition system).
If the third parameter is false, only the top-level node will be explored. *)
val all_eqs : 'a InputSystem.t -> TransSys.t -> bool -> ivc

(** [complement_of_core all_eqs core] returns the complement of [core], with [all_eqs] being
    the set of all the initial equations (can be retrieved using the [all_eqs] function). *)
val complement_of_core : loc_equation list ScMap.t -> loc_equation list ScMap.t -> loc_equation list ScMap.t

(** Separate an IVC into two IVC, the second one containing elements from the categories selected
    by the user, and the first one containing the others elements *)
val separate_ivc_by_category : 'a InputSystem.t -> ivc -> (ivc * ivc)

(** [minimize_lustre_ast full_ivc ivc ast]
    Minimize the lustre AST [ast] according to the inductive validity core [ivc].
    [full_ivc] should be an IVC containing all the equations, it can be obtained by calling [all_eqs].
    The optional parameter valid_lustre (default: false) determine whether the generated AST must be
    a valid lustre program or not (in this case, it will be more concise). *)
val minimize_lustre_ast : ?valid_lustre:bool -> 'a InputSystem.t -> ivc -> LustreAst.t -> LustreAst.t

(** Outputs a minized (not necessarily minimal) inductive validity core by computing an UNSAT core.
    It [approximate] is set to false, then the unsat core computed is not guaranteed to be minimal. *)
val ivc_uc :
  'a InputSystem.t ->
  ?approximate:bool ->
  TransSys.t ->
  Property.t list option ->
  ivc option

(** Outputs a minimal inductive validity core by trying to remove all the equations one after another
    and running the whole analysis on the new system each time. *)
val ivc_bf :
  'a InputSystem.t ->
  ?use_must_set:(ivc -> unit) option ->
  Analysis.param ->
  (
    bool ->
    Lib.kind_module list -> 'a InputSystem.t -> Analysis.param -> TransSys.t
    -> unit
  ) ->
  TransSys.t ->
  Property.t list option ->
  ivc option

(** Outputs the MUST set by computing all the minimal cut sets of cardinality 1. *)
val must_set :
  'a InputSystem.t ->
  Analysis.param ->
  (
    bool ->
    Lib.kind_module list -> 'a InputSystem.t -> Analysis.param -> TransSys.t
    -> unit
  ) ->
  TransSys.t ->
  Property.t list option ->
  ivc option

(** Outputs a minimal inductive validity core by first computing an UNSAT core (ivc_uc),
    and then trying to remove the remaining equations with bruteforce (ivc_bf).
    This should be faster than ivc_bf. *)
val ivc_ucbf :
  'a InputSystem.t ->
  ?use_must_set:(ivc -> unit) option ->
  Analysis.param ->
  (
    bool ->
    Lib.kind_module list -> 'a InputSystem.t -> Analysis.param -> TransSys.t
    -> unit
  ) ->
  TransSys.t ->
  Property.t list option ->
  ivc option

(** Outputs all minimal inductive validity cores by implementing the UMIVC algorithm.
    The 5th parameter correspond to the parameter 'k'. *)
val umivc :
  'a InputSystem.t ->
  ?use_must_set:(ivc -> unit) option ->
  ?stop_after:int ->
  Analysis.param ->
  (
    bool ->
    Lib.kind_module list -> 'a InputSystem.t -> Analysis.param -> TransSys.t
    -> unit
  ) ->
  TransSys.t ->
  Property.t list option ->
  int ->
  (ivc -> unit) ->
  ivc list

(** Returns the names of the properties for which we may be interested in computing an IVC. *)
val properties_of_interest_for_ivc : TransSys.t -> Property.t list

(* ----- MAXIMAL UNSAFE ABSTRACTIONS / MINIMAL CUTS SETS ----- *)

type mua = ((Property.t * (StateVar.t * Model.value list) list) * loc_equation list ScMap.t)

(** Separate a MUA into two MUA, the second one containing elements from the categories selected
    by the user, and the first one containing the others elements *)
val separate_mua_by_category : 'a InputSystem.t -> mua -> (mua * mua)

(** Compute one/all Maximal Unsafe Abstraction(s) using Automated Debugging
    and duality between MUAs and Minimal Correction Subsets. *)
val mua :
  'a InputSystem.t ->
  Analysis.param ->
  (
    bool ->
    Lib.kind_module list -> 'a InputSystem.t -> Analysis.param -> TransSys.t
    -> unit
  ) ->
  TransSys.t ->
  Property.t list option ->
  ?max_mcs_cardinality:int ->
  bool -> (* Compute them all? *)
  (mua -> unit) ->
  mua list

(** Returns the names of the properties for which we may be interested in computing a MUA. *)
val properties_of_interest_for_mua : TransSys.t -> Property.t list

(* ----- Structures for printing ----- *)

type term_print_data = {
  name: string ;
  category: string ;
  position: Lib.position ;
}

type core_print_data = {
  core_class: string ;
  property: string option ; (* Only for MCSs *)
  counterexample: ((StateVar.t * Model.value list) list) option ; (* Only for MCSs *)
  time: float option ;
  size: int ;
  elements: term_print_data list ScMap.t ;
}

val ivc_to_print_data :
  'a InputSystem.t -> TransSys.t -> bool -> ivc -> core_print_data

val mcs_to_print_data :
  'a InputSystem.t -> TransSys.t -> bool -> mua -> core_print_data

val pp_print_core_data :
  'a InputSystem.t -> Analysis.param -> TransSys.t -> Format.formatter -> core_print_data -> unit

val pp_print_core_data_xml :
  'a InputSystem.t -> Analysis.param -> TransSys.t -> Format.formatter -> core_print_data -> unit

val pp_print_core_data_json :
  'a InputSystem.t -> Analysis.param -> TransSys.t -> Format.formatter -> core_print_data -> unit

val pp_print_mcs_legacy : 'a InputSystem.t -> Analysis.param -> TransSys.t -> mua -> mua -> unit
