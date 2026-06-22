(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

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

type 'a t = {
  (* Name of the system as a scope. *)
  scope: Scope.t ;

  (* Original input. *)
  source : 'a ;

  (* Whether the system should be always abstracted by its contract, never, or sometimes. *)
  opacity : Opacity.t ;

  (* System has a contract. *)
  has_contract : bool ;

  (* System has modes. *)
  has_modes : bool ;

  (* System has an implementation. *)
  has_impl : bool ;

  map : 'a t Scope.Hashtbl.t ;

  (* Direct sub-systems. *)
  subsystems : Scope.t list ;
}

(* Strategy info of a subsystem. *)
let strategy_info_of {
  opacity; has_contract ; has_modes ; has_impl
} = {
  Strategy.opacity ;
  Strategy.has_contract ;
  Strategy.has_modes ;
  Strategy.has_impl;

}


(* Add all subsystems of the systems in the second argument to the accumulator
   in topological order with the top system at the head of the list. *)
let rec all_subsystems' accum = function

(* All subsystems added, return. *)
| [] -> accum

(* First system on the stack is already in the accumulator. *)
| { scope } :: tl when accum |> List.exists (
  fun { scope = s } -> scope = s
) ->
  (* Skip altogether, subsystems have already been added. *)
  all_subsystems' accum tl

(* First system on the stack. *)
| { scope = top; map; subsystems } as h :: tl -> 

  (* Subsystems that are not in the accumulator. *)
  let tl' =
    subsystems |> List.fold_left (fun tl' scope ->
      if
       (* System of the same name is in the stack? *)
       scope = top
       || List.exists (fun { scope = s } -> scope = s) tl
       (* System of the same name is in the accumulator? *)
       || List.exists
         (fun { scope = s } -> scope = s)
         accum
      then (* Do not add twice. *)
       tl'
      else (* First get subsystems of this system. *)
       Scope.Hashtbl.find map scope :: tl'
    ) []
  in

  (* Are all subsystems in the accumulator? *)
  match tl' with

  (* Now add this system. *)
  | [] -> all_subsystems' (h :: accum) tl

  (* First add all subsystems. *)
  | _ -> all_subsystems' accum (tl' @ h :: tl)


(* Return all subsystems in topological order with the top system at the head
   of the list. *)
let all_subsystems s = all_subsystems' [] [s]

let all_subsystems_of_list l = all_subsystems' [] l

(* Return the subsystem of the given scope.

   Raise [Not_found] if there is no subsystem of that scope. *)
let find_subsystem { map } scope = Scope.Hashtbl.find map scope

let find_subsystem_of_list subsystems scope =
  let res =
    List.find_map (fun { map } -> Scope.Hashtbl.find_opt map scope) subsystems
  in
  match res with
  | Some sub -> sub
  | None -> raise Not_found

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
