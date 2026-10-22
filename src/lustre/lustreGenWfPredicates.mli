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
  Generation of well-formedness predicates for recursive ADTs.

  A refinement type on a field of a recursive ADT constrains infinitely many
  values, so it cannot be expanded into a finite conjunction the way a record
  or a non-recursive ADT can. Each such type instead gets a generated
  [function rec] predicate, named by {!LustreDesugarADTs.wf_pred_id}, which
  the normalizer emits as an ordinary refinement-type constraint.

  @author Rob Lorch
*)

val gen_wf_predicates :
  TypeCheckerContext.tc_context ->
  LustreDesugarADTs.adt_map ->
  LustreAst.declaration list ->
  TypeCheckerContext.tc_context * LustreAst.declaration list
(** [gen_wf_predicates ctx adt_map decls] returns one function declaration for
    each monomorphic recursive ADT declared in [decls] that carries a
    refinement type, in the order of [decls], with the context extended with
    their signatures. It expects polymorphic datatypes to be instantiated
    already, and returns declarations in the desugared form of that point of
    the pipeline. *)
