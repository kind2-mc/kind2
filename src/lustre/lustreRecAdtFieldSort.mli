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

(** The SMT sorts of the fields of a recursive datatype.

    A recursive datatype is a native SMT datatype, each of whose fields has a
    single sort. A field whose compiled Lustre type is not one gets a datatype
    sort of its own: an enum, whose integer encoding would let a value outside
    the enum be read out of a field, has one nullary constructor per value; a
    tuple or record has a single constructor with one argument per component;
    a non-recursive datatype, desugared to a record by then, has its own
    constructors with their payloads. A nested type is a nested sort. Values
    are converted where a field is built ({!encode}) and where one is read
    ({!decode}).

    @author Rob Lorch *)

(** SMT symbol of a datatype's name, with any character that is not legal in
    an SMT-LIB simple symbol mangled to ['$'] *)
val smt_name_of_adt_name : string -> string

(** [field_sort dt ctor field ty] is the sort of the field [field] of the
    constructor [ctor] of the recursive datatype of SMT name [dt], given the
    compiled type [ty] of the field's source type. A single sort other than
    an enum is its own; any other gets a sort derived from [dt], [ctor] and
    [field], whose constructors are all declared.

    @raise Invalid_argument if [ty] holds an array *)
val field_sort : string -> string -> string -> Type.t LustreIndex.t -> Type.t

(** [encode sort e] is the value of the field sort [sort] that the compiled
    expression [e] of the field's source type denotes *)
val encode : Type.t -> LustreExpr.t LustreIndex.t -> LustreExpr.t

(** [decode default sort e] is the compiled expression of the field's source
    type that the value [e] of the field sort [sort] holds. A non-recursive
    datatype comes out in canonical form: the payloads of its inactive
    constructors hold the default value of their type, which [default] gives
    for a type that is not a datatype. *)
val decode :
  (Type.t -> LustreExpr.t) -> Type.t -> LustreExpr.t -> LustreExpr.t LustreIndex.t

(** [declaration_order declared dt] is [declared] followed by the field sorts
    the datatype [dt] reaches that are not in [declared] and by [dt], each
    after the sorts its own fields have *)
val declaration_order : Type.t list -> Type.t -> Type.t list
