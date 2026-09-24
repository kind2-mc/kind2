(* This file is part of the Kind 2 model checker.

   Copyright (c) 2024 by the Board of Trustees of the University of Iowa

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

 (** @author Rob Lorch *)

module A = LustreAst
module NI = NodeId
module Ctx = TypeCheckerContext
module GI = GeneratedIdentifiers

(** [instantiate_polymorphic_adts ctx gids type_decls decls] declares every
    ground instantiation of a polymorphic datatype the program uses, and rewrites
    each use to name the declaration of its instantiation, so that no later pass
    has to resolve one. Fails when an instantiation's field types break a
    restriction that only a concrete type can break. *)
val instantiate_polymorphic_adts :
  Ctx.tc_context -> GI.t NI.Map.t -> A.declaration list -> A.declaration list ->
  (Ctx.tc_context * GI.t NI.Map.t * A.declaration list * A.declaration list,
   [> LustreTypeChecker.error ]) result

val instantiate_polymorphic_nodes :
  Ctx.tc_context -> GI.t NI.Map.t  -> A.declaration list -> Ctx.tc_context * GI.t NI.Map.t * A.declaration list
