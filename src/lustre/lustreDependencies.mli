(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

module I = LustreIdent
module ISet = I.Set
module IMap = I.Hashtbl

module A = LustreAst

(** Enum over declaration types. *)
type decl =
| NodeOrFun | Type | Contract | Const

(** Reference to an unknown declaration. *)
exception Unknown_decl of decl * I.t * Lib.position

(** Pretty printer for declarations. *)
val pp_print_decl : Format.formatter -> decl -> unit

(** A dependency context. *)
type t

(** Empty dependency context. *)
val empty : t

(** Adds a dependency in a dependency context. *)
val add : t -> (
  decl * LustreIdent.t
) -> (
  decl * LustreIdent.t
) -> unit

(** Checks if a declaration depends on another. *)
val mem : t -> (
  decl * LustreIdent.t
) -> (
  decl * LustreIdent.t
) -> bool



(** Identifier corresponding to a declaration. *)
val info_of_decl : LustreAst.declaration -> (
  Lib.position * LustreIdent.t * decl
)

(** Inserts a declaration in a list of declarations, after the one with name
[f_ident]. *)
val insert_decl : LustreAst.declaration -> (
  decl * LustreIdent.t
) -> LustreAst.declaration list -> LustreAst.declaration list





(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
