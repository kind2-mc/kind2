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

module StringMap : sig
  include (Map.S with type key = HString.t)
  val keys: 'a t -> key list
end

module StringSet : sig
  include (Set.S with type elt = HString.t)
end

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

val empty : unit -> t

val union : t -> t -> t

val union_keys : 'a -> 'b option -> 'b option -> 'b option