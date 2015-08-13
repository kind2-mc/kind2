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

module A = Analysis
module Sys = TransSys

(* Merges two abstractions with the following semantics. First abstraction is
   the one from the previous analysis, second is the abstraction used to prove
   correct the node we are refining. *)
let merge_abstractions =
  Scope.Map.merge (fun _ lft rgt -> match lft, rgt with
    (* System was previously abstracted, now is concrete. *)
    | Some b, Some b' -> Some (b && b')
    (* Other cases are unreachable. *)
    | _ -> assert false
  )

(* Looks for the first refineable subsystem of the system [result] corresponds
   to. Traversal of the subsystems is breadth first. Returns an option of the
   scope of the system refined, the new abstraction, and the new assumptions.
   (New assumptions is an augmentation of the one in result.) *)
let get_params results subs_of_scope result =
  let sys = result.A.param.top in
  let subs = subs_of_scope sys in

  match result.A.requirements_valid with
  | Some false -> (* Requirements could not be proved, aborting. *)
    (* Event.log L_info
      "Cannot refine %a, some requirements could not be proved."
      Scope.pp_print_scope sys ; *)
    None
  | _ -> (
    let abstraction, assumptions =
      result.A.param.A.abstraction_map, result.A.param.A.assumptions
    in

    (* Input is a list of list of scope / whatever pairs. Initially input
       only contains [subs]. Function looks at them as candidates and
       returns the first refineable system from [subs], more precisely the
       [result] corresponding to the system. When a non-refineable system
       is encountered, it is discarded and its subsystems are appended to
       the input. If no refineable system is found in [subs] function goes
       looks at the subsystems previously appended to the input
       recursively. *)
    let rec loop = function
      | ( (candidate, _) :: tail ) :: lower -> (
        (* Is candidate currently abstracted? *)
        if Scope.Map.find candidate abstraction then
          (* Is candidate refineable? *)
          match A.results_find candidate results with
          | result :: _ ->
            (* It is if everything was proved in the last analysis. *)
            if A.result_is_all_proved result then Some result
            (* Otherwise keep going. *)
            else tail :: lower |> loop
          | [] -> failwith "unreachable"
        else (* Candidate is not abstracted, remembering its subsystems and
                looping. *)
          (tail :: lower) @ [ subs_of_scope candidate ] |> loop
      )
      | [] :: lower -> loop lower
      | [] -> None
    in

    match loop [ subs ] with
    (* No refinement possible. *)
    | None -> None
    | Some ({ A.param } as result) -> (* Refinement found, need to update
                                         abstraction and lift invariants.
                                         *)
      let sub = param.A.top in
      (* System is now concrete. *)
      let abstraction = Scope.Map.add sub false abstraction in
      (* Updating with the abstraction used to prove [sub]. *)
      let abstraction =
        merge_abstractions abstraction param.A.abstraction_map
      in
      (* Lifting invariants from previous result. *)
      let nu_assumptions =
        TransSys.invars_of_bound result.A.sys Numeral.zero
        |> List.map (fun t -> sub, t)
      in

      Some (sub, abstraction, List.rev_append nu_assumptions assumptions)
  )

let first_param_of results all_nodes scope =

  let rec loop abstraction assumptions = function
    | (sys, abstractable) :: tail -> (
      (* Can/should we abstract this system? *)
      let is_abstract =
        (sys = scope |> not) && abstractable && (Flags.compositional ())
      in
      let abstraction = Scope.Map.add sys is_abstract abstraction in
      if is_abstract then
        (* Sys is abstract, no assumptions, don't care if it's correct. *)
        loop abstraction assumptions tail
      else ( (* Sys is not abstract, making sure it's correct and lifting
                invariants. *)
        try (
        (* What do we know about this system? *)
        match A.results_find sys results with
        | [] -> assert false
        | result :: _ ->
          if A.result_is_all_proved result then
            (* System is correct, lifting invariants and looping. *)
            let nu_assumptions =
              TransSys.invars_of_bound result.A.sys Numeral.zero
              |> List.map (fun t -> result.A.param.A.top, t)
            in
            loop abstraction (List.rev_append nu_assumptions assumptions) tail
          else None (* System is not correct, no need to keep going. *)
        ) with Not_found ->
          (* We know nothing about this sys. *)
          loop abstraction assumptions tail
      )
    )
    | [] -> Some (abstraction, assumptions)
  in

  match loop Scope.Map.empty [] all_nodes with
  | None -> None
  | Some (abstraction, assumptions) -> Some {
    A.top = scope ;
    A.abstraction_map = abstraction ;
    A.assumptions = assumptions ;
  }

module type Strategy = sig
  val next_analysis:
    A.results -> (Scope.t -> (Scope.t * bool) list) -> (Scope.t * bool) list ->
    A.param option
end

module MonolithicStrategy : Strategy = struct
  let next_analysis results subs_of_scope all_nodes = match all_nodes with
    | (top,_) :: tail -> (
      try (
        match A.results_find top results with
        | [] -> assert false
        (* Not the first analysis, done. *)
        | _ -> None
      ) with Not_found ->
        first_param_of results all_nodes top
      (* Some { (* First analysis, creating [A.param]. *)
        (* We will analyze the top node. *)
        A.top = top ;
        (* All sub-systems are concrete. *)
        A.abstraction_map = tail |> List.fold_left (fun map (scope,_) ->
          Scope.Map.add scope false map
        ) (Scope.Map.empty) ;
        (* No assumption. *)
        A.assumptions = [] ;
      } *)
    )
    | [] -> failwith "[strategy] \
      no system to analyze (empty list of scopes)\
    "
end


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
