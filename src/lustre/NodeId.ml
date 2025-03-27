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

type node_type = 
  | Component (* Standard node from user input *)
  | Contract (* Generated imported node for contract realizability checking *)
  | Environment (* Generated imported node for environment realizability checking *)
  | Type (* Generated imported node for refinement type realizability checking *)
 
type node_id = {
  name : HString.t;
  node_type : node_type;
  monomorphization : int option; (* Instantiation of a polymorphic node. The int is a unique ID. *) 
}

let mk_node_id ?(node_type=Component) ?(monomorphization=None) name = 
  { name; node_type; monomorphization }

let pp_print_node_type ppf node_type = 
  Format.fprintf ppf "%s"
    (match node_type with 
      | Component -> ""
      | Environment -> ".env_"
      | Contract -> ".contract_"
      | Type -> ".type_")

let pp_print_monomorphization ppf monomorphization = 
  Format.fprintf ppf "%s"
    (match monomorphization with 
      | Some i ->  ".poly_" ^ (string_of_int i)
      | None -> "")

let internal_string_of_node_id { name; node_type; monomorphization; } = 
  Format.asprintf "%a%a%a"
    HString.pp_print_hstring name
    pp_print_node_type node_type 
    pp_print_monomorphization monomorphization

let pp_print_node_id ppf { name; } = 
  Format.fprintf ppf "%a" HString.pp_print_hstring name

let compare_node_ids: node_id -> node_id -> int 
= fun { name = name1; node_type = type1; monomorphization = mono1 } 
      { name = name2; node_type = type2; monomorphization = mono2 }  ->
  let c1 = HString.compare name1 name2 in 
  if c1 <> 0 then c1 else 
  let c2 = Stdlib.compare type1 type2 in 
  if c2 <> 0 then c2 else 
  Stdlib.compare mono1 mono2 

let eq_node_ids: node_id -> node_id -> bool 
= fun id1 id2 -> compare_node_ids id1 id2 = 0

let node_id_hash: node_id -> int 
= fun { name; node_type; monomorphization } ->
  Hashtbl.hash (HString.hash name, Hashtbl.hash node_type, Hashtbl.hash monomorphization) 

module NodeIdHashtbl = Hashtbl.Make(struct
  type t = node_id
  let equal = (=)
  let hash = node_id_hash
end)

module NodeIdMap = Map.Make(struct
    type t = node_id
    let compare = compare_node_ids
end)
  
module NodeIdSet = struct
  include (Set.Make (struct
                type t = node_id
                let compare = compare_node_ids
              end))
  let flatten: t list -> t = fun sets ->
    List.fold_left union empty sets
end 