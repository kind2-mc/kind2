(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

(**
  Desugaring of non-recursive algebraic data types (ADTs) to records.

  For each ADT declaration
    [type T = C0 | C1(t1) | C2(t2_0, t2_1)]
  a discriminant enum type and an equivalent record type are produced:
    [type T_tag = C0 | C1 | C2;]
    [type T = \{ T_tag: T_tag; C1_0: t1; C2_0: t2_0; C2_1: t2_1 \}]
  where the tag field encodes the active constructor and payload fields
  for non-selected constructors carry default values.

  [desugar_adts] is the main pipeline entry point: it desugars both
  TypeDecls and all [ADTTerm]/[Match] expressions in one pass.

  @author Rob Lorch
*)

module HStringMap = HString.HStringMap

type adt_info = {
  type_name : HString.t;
  type_params : HString.t list;
  disc_field : HString.t;
  disc_enum : HString.t;
  ctor_variants : HString.t list;
  ctor_fields : (HString.t * LustreAst.lustre_type) list HStringMap.t;
  all_payload_fields : (HString.t * LustreAst.lustre_type) list;
  field_names : (HString.t * HString.t * HString.t) list;
  is_recursive : bool;
}

type adt_map = adt_info HStringMap.t

val build_adt_info :
  HString.t ->
  HString.t list ->
  (HString.t * (HString.t * LustreAst.lustre_type) list) list ->
  is_recursive:bool ->
  adt_info

val record_type_of_adt :
  Lib.position ->
  ?ty_args:LustreAst.lustre_type list ->
  adt_info ->
  LustreAst.lustre_type

(** Whether a bound variable was introduced by [mk_canonical_exprs]. Its
    quantifier characterizes the non-canonical positions of a container and
    must not itself be restricted to canonical values. *)
val is_canonical_bound_var : HString.t -> bool

(** [mk_canonical_exprs ctx adt_map pos expr ty] is the list of constraints
    stating that every ADT value reachable from [expr], of type [ty], is in
    canonical form: the payload fields of the constructors other than the
    active one hold the default value of their type, and sets and maps only
    hold canonical keys.  Every ADT value in a program is kept in this form,
    so ADT equality and set/map membership are plain operations on the
    desugared record; the constraints are what free values (inputs, oracles,
    undefined outputs, free constants and quantified variables) are subject
    to. *)
val mk_canonical_exprs :
  TypeCheckerContext.tc_context ->
  adt_map ->
  Lib.position ->
  LustreAst.expr ->
  LustreAst.lustre_type ->
  LustreAst.expr list

(** The constructor whose payload field has the given internal record field
    name, if any *)
val ctor_of_payload_field : adt_info -> HString.t -> HString.t option

(** The ADT underlying a type, through type synonyms and refinement types *)
val adt_info_of_type :
  TypeCheckerContext.tc_context -> adt_map -> LustreAst.lustre_type -> adt_info option

val build_adt_map : LustreAst.declaration list -> adt_map
(** Collect all ADT type declarations from a program into an [adt_map],
    without performing any desugaring. Exposed so that passes needing
    [is_recursive] classification (e.g. [LustreCheckADTDecreases]) can run
    before [desugar_adts] eliminates [Match]/[ADTTerm] from the AST. *)

val desugar_adts :
  TypeCheckerContext.tc_context ->
  LustreAst.declaration list ->
  LustreAst.declaration list ->
  LustreAst.declaration list * LustreAst.declaration list * TypeCheckerContext.tc_context * adt_map

(* Canonical string key of a refinement type, or None if it is not one.  Used to
   build the [ref_type_names] map passed to [string_of_expr_as_source]: the key of
   a named refinement synonym's flattened definition maps to the synonym name. *)
val ref_type_canonical_key : LustreAst.lustre_type -> string option

(* [ref_type_names] maps refinement-type canonical keys to synonym names so that a
   quantified refinement type prints as the synonym name rather than its expansion. *)
val string_of_expr_as_source :
  ?ref_type_names:(string * HString.t) list -> adt_map -> LustreAst.expr -> string
