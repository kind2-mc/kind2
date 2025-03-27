(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

(** @author: Rob Lorch *)

type node_type = Component | Contract | Environment | Type
type node_id = {
  name : HString.t;
  node_type : node_type;
  monomorphization : int option;
}

val mk_node_id: ?node_type:node_type -> ?monomorphization:int option ->  HString.t -> node_id
val pp_print_node_id: Format.formatter -> node_id -> unit
val internal_string_of_node_id: node_id -> string
val node_id_hash: node_id -> int 
val eq_node_ids: node_id -> node_id -> bool 

module NodeIdMap : Map.S with type key = node_id

module NodeIdSet: sig
  include (Set.S with type elt = node_id)
  val flatten: t list -> t
end

module NodeIdHashtbl : Hashtbl.S with type key = node_id