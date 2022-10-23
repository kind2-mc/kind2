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
  Note that oracles are _propagated_ in node calls. If a node `n1` has an oracle
  and is called by another node `n2`, then `n2` will inherit a propagated oracle

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

  3. Node calls
    e.g.
      x1, ..., xn = ... op node_call(a, b, c) op ...
      => x1, ..., xn = ... op (l1, ..., ln) op ...
    where (l1, ..., ln) is a group (list) expression
      and each li corresponds to an output of the node_call
      If node_call has only one output, it is instead just an ident expression
    (Note that there is no generated equality here, how the node call is
      referenced at the stage of a LustreNode is by the node_call record where
      the output holds the state variables produced by the node call)

  4. Properties checked expression
  5. Assertions checked expression
  6. Condition of node calls (if it is not equivalent to true)
  7. Restarts of node calls (if it is not a constant)

     @author Andrew Marmaduke *)

module StringMap : sig
  include (Map.S with type key = HString.t)
  val keys: 'a t -> key list
end

module StringSet : sig
  include (Set.S with type elt = HString.t)
end

type source = Local | Input | Output | Ghost

type generated_identifiers = {
  node_args : (HString.t (* abstracted variable name *)
    * bool (* whether the variable is constant *)
    * LustreAst.lustre_type
    * LustreAst.expr)
    list;
  array_constructors :
    (LustreAst.lustre_type
    * LustreAst.expr
    * LustreAst.expr)
    StringMap.t;
  locals : (bool (* whether the variable is ghost *)
    * LustreAst.lustre_type
    * LustreAst.expr (* abstracted expression *)
    * LustreAst.expr) (* original expression *)
    StringMap.t;
  contract_calls :
    (Lib.position
    * (Lib.position * HString.t) list (* contract scope *)
    * LustreAst.contract_node_equation list)
    StringMap.t;
  warnings : (Lib.position * LustreAst.expr) list;
  oracles : (HString.t * LustreAst.lustre_type * LustreAst.expr) list;
  ib_oracles : (HString.t * LustreAst.lustre_type) list;
  propagated_oracles : (HString.t * HString.t) list;
  calls : (Lib.position (* node call position *)
    * (HString.t list) (* oracle inputs *)
    * HString.t (* abstracted output *)
    * LustreAst.expr (* condition expression *)
    * LustreAst.expr (* restart expression *)
    * HString.t (* node name *)
    * (LustreAst.expr list) (* node arguments *)
    * (LustreAst.expr list option)) (* node argument defaults *)
    list;
  subrange_constraints : (source
    * bool (* true if the type used for the subrange is the original type *)
    * Lib.position
    * HString.t (* Generated name for Range Expression *)
    * LustreAst.expr) (* Computed ranged expr *)
    list;
  expanded_variables : StringSet.t;
  equations :
    (LustreAst.typed_ident list (* quantified variables *)
    * (Lib.position * HString.t) list (* contract scope  *)
    * LustreAst.eq_lhs
    * LustreAst.expr)
    list;
}

type error = [
  | `LustreAstNormalizerError
]

val empty : unit -> generated_identifiers

val union : generated_identifiers -> generated_identifiers -> generated_identifiers


type info = {
  context : TypeCheckerContext.tc_context;
  abstract_interp_context : LustreAbstractInterpretation.context;
  inductive_variables : LustreAst.lustre_type StringMap.t;
  quantified_variables : LustreAst.typed_ident list;
  node_is_input_const : (bool list) StringMap.t;
  contract_calls_info : LustreAst.contract_node_decl StringMap.t;
  contract_scope : (Lib.position * HString.t) list;
  contract_ref : HString.t;
  interpretation : HString.t StringMap.t;
  local_group_projection : int
}

val mk_fresh_local : bool ->
  info ->
  Lib.position ->
  bool ->
  'a StringMap.t ->
  LustreAst.lustre_type -> LustreAst.expr -> LustreAst.expr -> LustreAst.expr * generated_identifiers

val normalize : TypeCheckerContext.tc_context
  -> LustreAbstractInterpretation.context
  -> LustreAst.t
  -> generated_identifiers StringMap.t
  -> (LustreAst.t * generated_identifiers StringMap.t,
      [> error]) result

val pp_print_generated_identifiers : Format.formatter -> generated_identifiers -> unit

val get_warnings : generated_identifiers StringMap.t -> (Lib.position * LustreAst.expr) list
