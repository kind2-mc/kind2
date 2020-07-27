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

open Lib
open LustreAst

(** {1 Helpers} *)

(** Returns the position of an expression *)
val pos_of_expr : expr -> Lib.position

(** Returns true if the expression has unguareded pre's *)
val has_unguarded_pre : expr -> bool

(** Returns true if the expression has a `pre` or a `->`. *)
val has_pre_or_arrow : expr -> Lib.position option

(** Returns true iff a contract mentions a `pre` or a `->`.
    Does not (cannot) check contract calls recursively, checks only inputs and
    outputs. *)
val contract_has_pre_or_arrow : contract -> Lib.position option

(** Checks whether a node local declaration has a `pre` or a `->`. *)
val node_local_decl_has_pre_or_arrow : node_local_decl -> Lib.position option

(** Checks whether a node equation has a `pre` or a `->`. *)
val node_item_has_pre_or_arrow : node_item -> Lib.position option

(** [replace_lasts allowed prefix acc e] replaces [last x] expressions in AST
    [e] by abstract identifiers prefixed with [prefix]. Only identifiers that
    appear in the list [allowed] are allowed to appear under a last. It returns
    the new AST expression and a set of identifers for which the last
    application was replaced. *)
val replace_lasts : string list -> string -> SI.t -> expr -> expr * SI.t

(** returns all the [ident] that appear in the expr ast*)
val vars: expr -> SI.t

(** Return an ast that adds two expressions*)
val addExp: Lib.position -> expr -> expr -> expr

(** returns an ast which is the absolute difference of two expr ast*)
val abs_diff: Lib.position -> expr -> expr -> expr
