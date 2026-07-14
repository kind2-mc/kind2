(* This file is part of the Kind 2 model checker.

   Copyright (c) 2025 by the Board of Trustees of the University of Iowa

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

type node_type = Component | Contract | Environment | Type | Any | Choose | TypeAscription | ClockedExpr | DefinedConstant | FreeConstant

type t

(* Required HString.t arg is the node's input name *)
val mk_node_id: ?node_type:node_type -> ?monomorphization:int list -> ?user_name:HString.t -> HString.t -> t
val pp_print_node_id_input_name: Format.formatter -> t -> unit
val pp_print_node_id_user_name: Format.formatter -> t -> unit
val pp_print_node_id_internal_name: Format.formatter -> t -> unit
val hash: t -> int 
val equal: t -> t -> bool 
val compare: t -> t -> int
val get_name: t -> HString.t
val get_user_name: t -> HString.t 
val get_internal_name: t -> HString.t
val get_node_type: t -> node_type
val get_monomorphization: t -> int list

module Map : Map.S with type key = t

module Set: sig
  include (Set.S with type elt = t)
  val flatten: t list -> t
end

module Hashtbl : Hashtbl.S with type key = t
