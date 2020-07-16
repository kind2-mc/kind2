(* This file is part of the Kind 2 model checker.

   Copyright (c) 2019-2020 by the Board of Trustees of the University of Iowa

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

open ModelElement

type 'a result =
| Solution of 'a
| NoSolution
| Error of string

type 'a analyze_func =
    bool -> bool ->
    Lib.kind_module list ->
    'a InputSystem.t ->
    Analysis.param ->
    TransSys.t ->
    unit

(** {1 Inductive Validity Cores} *)

type ivc

(** [complement_of_ivc in_sys sys ivc] returns the complement of [ivc]. 
    The parameters [in_sys] and [sys] must be the same as the ones used to generate [ivc]. *)
val complement_of_ivc : 'a InputSystem.t -> TransSys.t -> ivc -> ivc

(** [separate_ivc_by_category in_sys ivc] separates [ivc] into two IVCs:
    the first one only contains elements from the categories selected by the user,
    and the second one contains the remaining elements of [ivc].
    The parameters [in_sys] should be the same as the one used to generate [ivc]. *)
val separate_ivc_by_category : 'a InputSystem.t -> ivc -> (ivc * ivc)

(** [minimize_lustre_ast in_sys ivc ast]
    minimizes the lustre AST [ast] according to the inductive validity core [ivc].
    The parameters [in_sys] should be the same as the one used to generate [ivc].
    The optional parameter [valid_lustre] (default: false) determine whether the generated AST must be
    a valid lustre program or a more concise and easily readable program. *)
val minimize_lustre_ast : ?valid_lustre:bool -> 'a InputSystem.t -> ivc -> LustreAst.t -> LustreAst.t

(** [ivc_uc in_sys sys props] computes an approximation of a minimal inductive validity core
    for the input system [in_sys] and the transition system [sys]. Only properties [props] are considered.
    The optional parameter [approximate] determines whether the unsat core computed internally must be minimal or not
    (in any case, the resulting IVC is NOT guaranteed to be minimal). *)
val ivc_uc :
  'a InputSystem.t ->
  ?approximate:bool ->
  TransSys.t ->
  Property.t list ->
  ivc result

(** [ivc_bf in_sys param analyze_func sys props] computes a minimal inductive validity core
    for the input system [in_sys], the analysis parameter [param] and the transition system [sys].
    Only properties [props] are considered.
    If the optional parameter [use_must_set] is not None, a MUST set will be computed first and passed
    to the given continuation. *)
val ivc_bf :
  'a InputSystem.t ->
  ?use_must_set:(ivc -> unit) option ->
  Analysis.param ->
  'a analyze_func ->
  TransSys.t ->
  Property.t list ->
  ivc result

(** [must_set in_sys param analyze_func sys props] computes the MUST set
    for the input system [in_sys], the analysis parameter [param] and the transition system [sys].
    Only properties [props] are considered. *)
val must_set :
  'a InputSystem.t ->
  Analysis.param ->
  'a analyze_func ->
  TransSys.t ->
  Property.t list ->
  ivc result

(** [ivc_ucbf in_sys param analyze_func sys props] computes a minimal inductive validity core
    for the input system [in_sys], the analysis parameter [param] and the transition system [sys].
    Only properties [props] are considered.
    This function first computes an approximation of a minimal IVC, and then tries to reduce it further.
    Most of time, it is faster than using [ivc_bf].
    If the optional parameter [use_must_set] is not None, a MUST set will be computed first and passed
    to the given continuation. *)
val ivc_ucbf :
  'a InputSystem.t ->
  ?use_must_set:(ivc -> unit) option ->
  Analysis.param ->
  'a analyze_func ->
  TransSys.t ->
  Property.t list ->
  ivc result

(** [umivc in_sys param analyze_func sys props k cont] computes all minimal inductive validity cores
    for the input system [in_sys], the analysis parameter [param] and the transition system [sys].
    Only properties [props] are considered.
    Each IVC is passed to the continuation [cont] as soon as it is found.
    The parameter [k] determines up to which cardinality MCSes must be computed before starting searching for IVC.
    A value of -1 will compute all the MCSes,
    and in this case the first IVC found is guaranteed to have a minimal cardinality.
    If the optional parameter [use_must_set] is not None, a MUST set will be computed first and passed
    to the given continuation. If [stop_after] is n > 0, the search will stop after n minimal IVCs being found. *)
val umivc :
  'a InputSystem.t ->
  ?use_must_set:(ivc -> unit) option ->
  ?stop_after:int ->
  Analysis.param ->
  'a analyze_func ->
  TransSys.t ->
  Property.t list ->
  int ->
  (ivc -> unit) ->
  ivc list

(** {1 Minimal Cut Sets} *)

type mcs

(** [complement_of_mcs in_sys sys mcs] returns the complement of [mcs] (the complement of a MCS is a MUA).
    The parameters [in_sys] and [sys] must be the same as the ones used to generate [mcs]. *)
val complement_of_mcs : 'a InputSystem.t -> TransSys.t -> mcs -> mcs

(** [separate_mcs_by_category in_sys mcs] separates [mcs] into two MCSes:
    the first one only contains elements from the categories selected by the user,
    and the second one contains the remaining elements of [mcs].
    The parameters [in_sys] should be the same as the one used to generate [mcs]. *)
val separate_mcs_by_category : 'a InputSystem.t -> mcs -> (mcs * mcs)

(** [mcs in_sys param analyze_func sys props all cont] computes a maximal unsafe abstraction
    for the input system [in_sys], the analysis parameter [param] and the transition system [sys].
    Only properties [props] are considered. If [all] is true, all the MCSes will be computed.
    Each MCS is passed to the continuation [cont] as soon as it is found.
    If the optional parameter [max_mcs_cardinality] is n >= 0, only MCSes of cardinality greater
    or equal to (total_number_of_model_elements - n) will be computed.
    If a global initial MCS analysis has been performed, its result should be passed in [initial_solution],
    otherwise you can omit this parameter. *)
val mcs :
  'a InputSystem.t ->
  Analysis.param ->
  'a analyze_func ->
  TransSys.t ->
  Property.t list ->
  ?initial_solution:mcs option ->
  ?max_mcs_cardinality:int ->
  bool -> (* Compute them all? *)
  bool -> (* Approximate? *)
  (mcs -> unit) ->
  mcs list

val mcs_initial_analysis :
  'a InputSystem.t ->
  Analysis.param ->
  'a analyze_func ->
  ?max_mcs_cardinality:int ->
  TransSys.t ->
  (Property.t * mcs) list

(** {1 Structures for printing} *)

val ivc_to_print_data :
  'a InputSystem.t -> TransSys.t -> string -> float option -> ivc -> core_print_data

val mcs_to_print_data :
  'a InputSystem.t -> TransSys.t -> string -> float option -> mcs -> core_print_data

val pp_print_mcs_legacy : 'a InputSystem.t -> Analysis.param -> TransSys.t -> mcs -> mcs -> unit
