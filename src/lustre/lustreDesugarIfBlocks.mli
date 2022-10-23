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
   Code for desugaring imperative-style if blocks to functional ITEs.

   The code has a few steps.
    1. Remove multiple assignment from if blocks using temp variables.
    2. Parse the if block and create a map of trees, one for each variable
    3. Fill in oracles in the trees for missing values.
    4. Remove redundancy from the trees.
    5. Convert the trees to ITE expressions. 

   @author Rob Lorch
 *)



type error_kind = Unknown of string
  | MisplacedNodeItemError of LustreAst.node_item

val error_message : error_kind -> string

type error = [
(*   | `LustreTypeCheckerError of Lib.position * LustreTypeChecker.error_kind
  | `LustreSyntaxChecksError of Lib.position * LustreSyntaxChecks.error_kind
  | `LustreAstInlineConstantsError of Lib.position * LustreAstInlineConstants.error_kind *)
  | `LustreDesugarIfBlocksError of Lib.position * error_kind 
]


module LhsMap : sig
    type key
    type 'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : key -> 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
    val singleton : key -> 'a -> 'a t
    val remove : key -> 'a t -> 'a t
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val filter : (key -> 'a -> bool) -> 'a t -> 'a t
    val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t
    val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal : 'a t -> int
    val bindings : 'a t -> (key * 'a) list
    val min_binding : 'a t -> key * 'a
    val min_binding_opt : 'a t -> (key * 'a) option
    val max_binding : 'a t -> key * 'a
    val max_binding_opt : 'a t -> (key * 'a) option
    val choose : 'a t -> key * 'a
    val choose_opt : 'a t -> (key * 'a) option
    val split : key -> 'a t -> 'a t * 'a option * 'a t
    val find : key -> 'a t -> 'a
    val find_opt : key -> 'a t -> 'a option
    val find_first : (key -> bool) -> 'a t -> key * 'a
    val find_first_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val find_last : (key -> bool) -> 'a t -> key * 'a
    val find_last_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val to_seq : 'a t -> (key * 'a) Seq.t
    val to_rev_seq : 'a t -> (key * 'a) Seq.t
    val to_seq_from : key -> 'a t -> (key * 'a) Seq.t
    val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t
    val of_seq : (key * 'a) Seq.t -> 'a t
  end


val get_node_ctx : TypeCheckerContext.tc_context ->
  'a * 'b * 'c * LustreAst.const_clocked_typed_decl list * LustreAst.clocked_typed_decl list *
  LustreAst.node_local_decl list * 'd * 'e -> TypeCheckerContext.tc_context

val remove_mult_assign_from_ni : 
TypeCheckerContext.tc_context ->
  LustreAst.node_item ->
    (LustreAst.node_item list * LustreAst.node_item list * LustreAst.node_local_decl list *
    TypeCheckerContext.tc_context list,
    [> error ])
    result

val desugar_if_blocks : 
TypeCheckerContext.tc_context ->
  LustreAst.declaration list ->
  (LustreAst.declaration list * LustreAstNormalizer.generated_identifiers LustreAstNormalizer.StringMap.t,
   [> `LustreDesugarIfBlocksError of Lib.position * error_kind ])
  result
