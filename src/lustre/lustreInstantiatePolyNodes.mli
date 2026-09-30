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

(** [instantiate_scc_map scc_map gids decls] returns the map from the internal
    name of each (possibly mutually) recursive function in the normalized
    declarations [decls], with generated identifiers [gids], to the identifier
    of its recursive group, given [scc_map], the map computed before the
    instantiation of polymorphic functions. An instantiation of a recursive
    function need not be in a recursive group with the instantiations of the
    other members of the group of that function, so the groups are computed
    again, from the calls in [gids], when there is such an instantiation. *)
val instantiate_scc_map :
  int HString.HStringMap.t -> GI.t NI.Map.t -> A.declaration list ->
  int HString.HStringMap.t
