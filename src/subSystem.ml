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

  (* System can be abstracted to its contract. *)
  has_contract : bool ;

  (* System has modes. *)
  has_modes : bool ;

  (* System can be refined to its implementation. *)
  has_impl : bool ;

  (* Direct sub-systems. *)
  subsystems : 'a t list ;
}

(* Strategy info of a subsystem. *)
let strategy_info_of {
  has_contract ; has_modes ; has_impl
} = {
  Strategy.can_refine = has_impl ;
  Strategy.has_contract ;
  Strategy.has_modes ;
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
| { subsystems } as h :: tl -> 

  (* Subsystems that are not in the accumulator. *)
  let tl' =
    subsystems |> List.fold_left (fun tl' ({ scope } as subsystem) ->
      if
       (* System of the same name is in the accumulator? *)
       List.exists
         (fun { scope = s } -> scope = s)
         accum
      then (* Do not add twice. *)
       tl'
      else (* First get subsystems of this system. *)
       subsystem :: tl'
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

(* Search depth-first for the subsystem in the list of subsystems, skip over
   systems already visited. *)
let rec find_subsystem' scope visited = function 

(* Stack is empty, scope not found. *)
| [] -> raise Not_found 

(* Take first element from stack. *)
| ({ scope = scope'; subsystems } as subsystem) :: tl -> 

  (* Return subsystem if scope matches. *)
  if scope = scope' then subsystem else 

    (* System already seen? *)
    if List.mem scope' visited then 

      (* Continue with rest of stack. *)
      find_subsystem' scope visited tl

    else

      (* Push subsystems of this system to stack. *)
      find_subsystem' scope (scope' :: visited) (subsystems @ tl)
        
    
(* Return the subsystem of the given scope.

   Raise [Not_found] if there is no subsystem of that scope. *)
let find_subsystem subsystem scope = find_subsystem' scope [] [subsystem]

let find_subsystem_of_list subsystems scope = find_subsystem' scope [] subsystems

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
