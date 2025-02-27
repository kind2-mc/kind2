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

type source = Local | Input | Output | Ghost

type t = {
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
  locals : 
  (LustreAst.lustre_type)
    StringMap.t;
  asserts : (Lib.position * LustreAst.expr) list;
  contract_calls :
    (Lib.position
    * (Lib.position * LustreAst.node_name) list (* contract scope *)
    * LustreAst.contract_node_equation list)
    StringMap.t;
  oracles : (HString.t * LustreAst.lustre_type * LustreAst.expr) list;
  ib_oracles : (HString.t * LustreAst.lustre_type) list;
  calls : (Lib.position (* node call position *)
    * HString.t (* abstracted output *)
    * LustreAst.expr (* condition expression *)
    * LustreAst.expr (* restart expression *)
    * LustreAst.node_name (* node name *)
    * (LustreAst.expr list) (* node arguments *)
    * (LustreAst.expr list option) (* node argument defaults *)
    * bool) (* Was call inlined? *)
    list;
  subrange_constraints : (source
    * (Lib.position * LustreAst.node_name) list (* contract scope  *)
    * bool (* true if the type used for the subrange is the original type *)
    * Lib.position
    * HString.t (* Generated name for Range Expression *)
    * LustreAst.expr) (* Computed ranged expr *)
    list;
  refinement_type_constraints: (source
    * Lib.position
    * HString.t (* Generated name for refinement type constraint *)
    * LustreAst.expr) 
    list;
  expanded_variables : StringSet.t;
  equations :
    (LustreAst.typed_ident list (* quantified variables *)
    * (Lib.position * LustreAst.node_name) list (* contract scope  *)
    * LustreAst.eq_lhs
    * LustreAst.expr
    * source option) (* Record the source of the equation if generated before normalization step *)
    list;
  nonvacuity_props: StringSet.t;
  array_literal_vars: StringSet.t; (* Variables equal to an array literal *)
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

val empty : unit -> t

val union : t -> t -> t

val union_keys : 'a -> 'b option -> 'b option -> 'b option

val union_keys2 : 'a -> t option -> t option -> t option
