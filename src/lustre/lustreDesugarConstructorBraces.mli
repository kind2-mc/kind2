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

(** Desugars ADT constructors written with curly braces and named fields,
    [Cons { tl = Nil; hd = 3 }], to constructor applications with the arguments
    in declaration order.

    The parser builds the same expression for a record and for a constructor,
    so this pass runs before any other, resolving each [RecordExpr] by its name.
    A constructor may therefore not share its name with a type other than the
    datatype declaring it.

    @author Kind 2 development team *)

type error_kind =
  | ConstructorNamedAsType of HString.t
  | MissingConstructorField of HString.t * HString.t
  | UnknownConstructorField of HString.t * HString.t
  | RepeatedConstructorField of HString.t * HString.t

val error_message : error_kind -> string

type error = [
  | `LustreDesugarConstructorBracesError of Lib.position * error_kind
]

(** Rejects a constructor named as a type other than its own datatype, then
    replaces every [RecordExpr] named after a constructor by a constructor
    application. Each other [RecordExpr] is left as is. *)
val desugar_constructor_braces : LustreAst.t -> (LustreAst.t, [> error]) result
