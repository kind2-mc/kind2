(* This file is part of the Kind 2 model checker.

   Copyright (c) 2022 by the Board of Trustees of the University of Iowa

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
  @author Andrew Marmaduke 
  *)   

module StringMap = HString.HStringMap
module StringSet = HString.HStringSet

type source =
  | Local
  | Input
  | Output
  | Ghost
  | ClockedOutput of LustreAst.expr
  (** Output of an equation pulled out of a when-block branch; the expression is
      the (polarity-adjusted) conjunction of the enclosing when-block guards.
      Node calls in such an equation must be activated on that clock. *)

type t = {
  node_args : (HString.t (* abstracted variable name *)
    * bool (* whether the variable is constant *)
    * LustreAst.lustre_type
    * LustreAst.expr)
    list;
  locals : 
  (LustreAst.lustre_type)
    StringMap.t;
  free_constants: (HString.t * LustreAst.lustre_type) list;
  contract_calls :
    (Lib.position
    * (Lib.position * NodeId.t) list (* contract scope *)
    * LustreAst.contract_node_equation list)
    StringMap.t;
  oracles : (HString.t * LustreAst.lustre_type * LustreAst.expr) list;
  ib_oracles : (HString.t * LustreAst.lustre_type) list;
  calls : (Lib.position (* node call position *)
    * HString.t (* abstracted output *)
    * LustreAst.expr (* condition expression *)
    * LustreAst.expr (* restart expression *)
    * HString.t option (* boolean variable representing call context *)
    * NodeId.t (* node name *)
    * (LustreAst.expr list) (* node arguments *)
    * (LustreAst.expr list option) (* node argument defaults *)
    * bool) (* Was call inlined? *)
    list;
  refinement_type_constraints: (source
    * Lib.position
    * HString.t (* Generated name for refinement type constraint *)
    * LustreAst.expr
    * NodeId.t option) (* Node ID for type ascription substitution *)
    list;
  empty_maps: (HString.t * LustreAst.lustre_type * LustreAst.lustre_type) list;
  empty_sets: (HString.t * LustreAst.lustre_type) list;
  map_element_updates: (HString.t * 
    LustreAst.expr * 
    LustreAst.expr * 
    LustreAst.expr * 
    HString.t * 
    LustreAst.lustre_type * 
    LustreAst.lustre_type) list;
  map_subtractions: (HString.t *
    LustreAst.expr *
    LustreAst.expr *
    HString.t *
    LustreAst.lustre_type *
    LustreAst.lustre_type) list;
  set_insertions: (HString.t *
    LustreAst.expr * 
    LustreAst.expr * 
    HString.t * 
    LustreAst.lustre_type) list;
  set_binops: (HString.t * 
    LustreAst.expr * 
    LustreAst.expr * 
    HString.t *
    LustreAst.binary_operator * 
    LustreAst.lustre_type) list;
  expanded_variables : StringSet.t;
  equations :
    (LustreAst.typed_ident list (* quantified variables *)
    * (Lib.position * NodeId.t) list (* contract scope  *)
    * LustreAst.eq_lhs
    * LustreAst.expr
    * source option) (* Record the source of the equation if generated before normalization step *)
    list;
  nonvacuity_props: StringSet.t;
  clocked_call_ties:
    (HString.t * HString.t option * HString.t * HString.t) list;
  (** Tuples [(tie, init_tie, t, x)] where [x] is a when-block variable whose
      off-branch holds its previous value, [t] is the local bound to the
      output of the node call activated on the when-block guard, [tie] is a
      generated boolean local defined as [x = t], and [init_tie], if any, is a
      generated boolean local defined as [x = init], where [init] is the
      initial value of [x]. Used to generate candidate invariants tying the
      held variable to the (frozen) call output. *)
  array_literal_vars: StringSet.t; (* Variables equal to an array literal *)
  expr_source_map: LustreAst.expr StringMap.t;
  type_ascription_exprs: LustreAst.expr NodeId.Map.t;
  history_vars: HString.t StringMap.t;
}

(* String constant used in lustreDesugarIfBlocks.ml and lustreDesugarFrameBlocks.ml
   that is used for if block oracle variable names. *)
val iboracle : string

(* String constant used for counter variables generated for instrumentation
of reachability queries with timestep bounds. *)
val ctr_id : HString.t

(** Checks if a variable name corresponds to an iboracle *)
val var_is_iboracle: HString.t -> bool

(* String constant used as the suffix of fresh locals capturing the discarded
   results of a call statement (see lustreNameCalls.ml). *)
val discarded_output : string

(** Checks if a variable name corresponds to a discarded call-statement result *)
val var_is_discarded_output: HString.t -> bool

(* String constant used as a segment of fresh locals introduced to desugar the
   'last' operator (see lustreDesugarLast.ml). *)
val last_local : string

(** Checks if a variable name corresponds to a 'last'-operator local *)
val var_is_last_local: HString.t -> bool

(* String constant used as the suffix of fresh locals capturing the output of
   a node call in a when-block branch (see lustreDesugarIfBlocks.ml). *)
val clocked_call_output : string

(* String constant used as the suffix of the fresh boolean locals stating that
   a when-block variable agrees with the output of the node call activated on
   the when-block guard (see lustreDesugarIfBlocks.ml). *)
val clocked_call_tie : string

val empty : unit -> t

val union : t -> t -> t

val union_keys : 'a -> 'b option -> 'b option -> 'b option

val union_keys2 : 'a -> t option -> t option -> t option
