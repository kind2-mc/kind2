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

(** Desugars the [last] operator (only allowed within frame blocks).

    @author Kind 2 development team *)

type error_kind =
  | MisplacedLastError of HString.t
  | UnknownIdentifier of HString.t

val error_message : error_kind -> string

type error = [
  | `LustreDesugarLastError of Lib.position * error_kind
]

(** Replaces each [last x] occurring in a frame block with a fresh local
    variable initialized by the frame and equal to [pre x] afterwards. Returns
    an error if [last] is used outside of a frame block. *)
val desugar_last : LustreAst.t -> (LustreAst.t, [> error]) result
