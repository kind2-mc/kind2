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

val inlinable_functions :
  TypeCheckerContext.tc_context ->
  LustreAst.declaration list ->
  NodeId.Set.t

(** The recursive functions whose functional symbols can be given a
    definition at the SMT level in every analysis of the run (see
    {!LustreFunDefs}), and which a call applied to quantified variables can
    therefore be compiled to an application of, rather than to a node
    instance. As for the functions that can be inlined, and whatever the
    analysis, a function with an effective contract is left out unless it is
    transparent, and so is a function with an assertion, an output or local
    of a type that contains an array, or an output or local that no equation
    defines. A function is also left out if it calls a function that can
    neither be inlined nor is in the set: the set is the greatest one closed
    under calls. The conditions that are only known once the nodes are
    compiled are not checked, and {!LustreTransSys} warns about them
    instead. *)
val uf_callable_functions :
  TypeCheckerContext.tc_context ->
  LustreAst.declaration list ->
  NodeId.Set.t

(** [uf_callable_instance ctx decls ~caller_ty_params id ty_args] is [true]
    if the instantiation of the function [id] of [decls] with the type
    arguments [ty_args] has no output of a refinement type (unless the
    function is transparent) and no output or local variable of a type that
    contains an array, or if [ty_args] is empty. {!uf_callable_functions}
    checks a polymorphic function with its type parameters as they are. The
    type parameters [caller_ty_params] of the node that makes the call, which
    [ty_args] may mention, are taken to be array types. *)
val uf_callable_instance :
  TypeCheckerContext.tc_context ->
  LustreAst.declaration list ->
  caller_ty_params:HString.t list ->
  NodeId.t ->
  LustreAst.lustre_type list ->
  bool
