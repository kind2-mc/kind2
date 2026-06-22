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
  | Any (* Generated for node corresponding to an 'any' operator *)
  | Choose (* Generated for node corresponding to a 'choose' operator *)
  | TypeAscription (* Generated for node corresponding to a type ascription operator *)
  | ClockedExpr (* Generated for a temporal expression abstracted out of a when branch *)
  | DefinedConstant (* Defined global constant converted to function without args *)
  | FreeConstant (* Free global constant converted to function without args *)
 
type t = {
  name : HString.t; (* Input name, probably not used *)
  user_name : HString.t; (* For printing to the user (distinguishes monomorphizations) *)
  internal_name : HString.t; (* For a unique ID that is an HString *)
  node_type : node_type;
  (* Instantiation of a polymorphic node. The ints comprise a unique ID. 
     Have a list because a monomorphization can be further monomorphized. *)
  monomorphization : int list; 
}

let pp_print_node_type ppf node_type = 
  Format.fprintf ppf "%s"
    (match node_type with 
      | Component -> ""
      | Environment -> ".env_"
      | Contract -> ".contract_"
      | Type -> ".type_"
      | Any -> ".any_"
      | TypeAscription -> ".type_ascription_"
      | ClockedExpr -> ".clocked_expr_"
      | FreeConstant -> ".free_constant_"
      | DefinedConstant -> ".def_constant_"
      | Choose -> ".choose_")

let rec pp_print_monomorphization ppf monomorphization = 
  match monomorphization with 
    | hd :: tl ->  
      Format.fprintf ppf ".poly_%d%a"
        hd 
        pp_print_monomorphization tl
    | [] -> ()

let pp_print_node_id_input_name ppf { name; } = 
  Format.fprintf ppf "%a" HString.pp_print_hstring name

let pp_print_node_id_user_name ppf { user_name; } = 
  Format.fprintf ppf "%a" HString.pp_print_hstring user_name

let pp_print_node_id_internal_name ppf { internal_name; } =
  Format.fprintf ppf "%a" HString.pp_print_hstring internal_name

let mk_node_id ?(node_type=Component) ?(monomorphization = []) ?user_name name = 
  let user_name = Option.value user_name ~default:name in
  let internal_name = 
    Format.asprintf "%a%a%a"
      HString.pp_print_hstring name
      pp_print_node_type node_type 
      pp_print_monomorphization monomorphization |> HString.mk_hstring
  in
  { name; user_name; internal_name; node_type; monomorphization; }

let get_name node_id = node_id.name 

let get_user_name node_id = node_id.user_name 

let get_internal_name node_id = node_id.internal_name 

let get_node_type node_id = node_id.node_type 

let get_monomorphization node_id = node_id.monomorphization

let compare: t -> t -> int 
= fun { name = name1; node_type = type1; monomorphization = mono1 } 
      { name = name2; node_type = type2; monomorphization = mono2 }  ->
  let c1 = HString.compare name1 name2 in 
  if c1 <> 0 then c1 else 
  let c2 = Stdlib.compare type1 type2 in 
  if c2 <> 0 then c2 else 
  Stdlib.compare mono1 mono2 

let equal: t -> t -> bool 
= fun id1 id2 -> compare id1 id2 = 0

let hash: t -> int 
= fun { name; node_type; monomorphization } ->
  Hashtbl.hash (HString.hash name, Hashtbl.hash node_type, Hashtbl.hash monomorphization) 

module Hashtbl = Hashtbl.Make(struct
  type z = t (* This t is NodeId.t *)
  type t = z (* This t is Hashtbl.t *)
  let equal = equal
  let hash = hash
end)

module Map = Map.Make(struct
    type z = t (* This t is NodeId.t *)
    type t = z (* This t is Map.t *)
    let compare = compare
end)
  
module Set = struct
  include (Set.Make (struct
    type z = t (* This t is NodeId.t *)
    type t = z (* This t is Set.t *)
    let compare = compare
  end))
  let flatten: t list -> t = fun sets ->
    List.fold_left union empty sets
end 
