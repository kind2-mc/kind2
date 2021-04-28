(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020 by the Board of Trustees of the University of Iowa

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
(** Normalize a Lustre AST to ease in translation to a transition system

  The two main requirements of this normalization are to:
    1. Guard any unguarded pre expressions 
    2. Generate any needed local identifiers or oracles

  Identifiers are constructed with a numeral prefix followed by a type suffix.
  e.g. 2_glocal or 6_oracle. These are not valid lustre identifiers and are
  expected to be transformed into indexes with the numeral as a branch and the
  suffix type as the leaf.

  Generated locals/oracles are referenced inside the AST via an Ident expression
  but the actual definition is not added to the AST. Instead it is recoreded in
  the generated_identifiers record.

  pre operators are explicitly guarded in the AST by an oracle variable
  if they were originally unguarded
    e.g. pre expr => oracle -> pre expr

  The following parts of the AST are abstracted by locals:

  1. Arguments to node calls that are not identifiers
    e.g.
      Node expr1 expr2 ... exprn
      =>
      Node l1 l2 ... ln
    where each li is a local variable and li = expri

  2. Arguments to the pre operator that are not identifiers
    e.g.
      pre expr => pre l
    where l = expr

     @author Andrew Marmaduke *)

module StringMap : sig
  include (Map.S with type key = string)
  val keys: 'a t -> key list
end

type generated_identifiers = {
    node_args : (string * LustreAst.expr) list;
    pre_args : (string * LustreAst.expr) list;
    oracles : (LustreAst.ident * LustreAst.expr) list;
    calls : (Lib.position (* node call position *)
      * (string list) (* abstraction variables *)
      * LustreAst.expr (* condition expression *)
      * LustreAst.expr (* restart expression *)
      * string (* node name *)
      * (LustreAst.expr list) (* node arguments *)
      * (LustreAst.expr list option)) (* node argument defaults *)
      list
}

val normalize : TypeCheckerContext.tc_context
  -> LustreAst.t
  -> (LustreAst.t * generated_identifiers StringMap.t, Lib.position * string) result

val pp_print_generated_identifiers : Format.formatter -> generated_identifiers -> unit
