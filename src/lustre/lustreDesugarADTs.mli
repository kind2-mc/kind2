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
}

type adt_map = adt_info HStringMap.t

val desugar_adts :
  TypeCheckerContext.tc_context ->
  LustreAst.declaration list ->
  LustreAst.declaration list ->
  LustreAst.declaration list * LustreAst.declaration list * TypeCheckerContext.tc_context * adt_map

val string_of_expr_as_source : adt_map -> LustreAst.expr -> string
