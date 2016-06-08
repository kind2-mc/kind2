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

open Lib

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
  let info = A.info_of_param result.A.param in
  let sys = info.A.top in
  let subs = subs_of_scope sys in

  match result.A.requirements_valid with
  | Some false -> (* Requirements could not be proved, aborting. *)
    (* Event.log L_info
      "Cannot refine %a, some requirements could not be proved."
      Scope.pp_print_scope sys ; *)
    None
  | _ -> (
    let abstraction, assumptions =
      info.A.abstraction_map, info.A.assumptions
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
      | ( (candidate, _, _) :: tail ) :: lower -> (
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
    | Some ({ A.param } as result) ->
      (* Refinement found, need to update abstraction and lift invariants. *)
      let info = A.info_of_param param in
      let sub = info.A.top in
      (* System is now concrete. *)
      let abstraction = Scope.Map.add sub false abstraction in
      (* Updating with the abstraction used to prove [sub]. *)
      let abstraction =
        merge_abstractions abstraction info.A.abstraction_map
      in
      (* Lifting invariants from previous result. *)
      let nu_assumptions =
        TransSys.invars_of_bound result.A.sys Numeral.zero
        |> List.map (fun t -> sub, t)
      in

      Some (sub, abstraction, List.rev_append nu_assumptions assumptions)
  )

(* Returns an option of the parameter for the first analysis of a system. *)
let first_param_of results all_nodes scope =

  let rec loop abstraction assumptions = function
    | (sys, abstractable, has_modes) :: tail -> (
      (* Can/should we abstract this system? *)
      let is_abstract =
        if sys = scope then 
          has_modes && (Flags.Contracts.check_modes ())
        else
          abstractable && (Flags.Contracts.compositional ())
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
          if A.result_is_some_falsified result |> not then
            (* System has not been proved unsafe, lifting invariants and
               looping. *)
            let nu_assumptions =
              TransSys.invars_of_bound result.A.sys Numeral.zero
              |> List.map (fun t -> (A.info_of_param result.A.param).A.top, t)
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
  | Some (abstraction, assumptions) ->
    let info =
      { A.top = scope ;
        A.uid = A.results_length results ;
        A.abstraction_map = abstraction ;
        A.assumptions = assumptions }
    in
    if Scope.Map.find scope abstraction then
      (* Top level is abstract, we're checking its contract. *)
      Some (A.ContractCheck info)
    else
      (* Top level is not abstract, first analysis. *)
      Some (A.First info)

let first_analysis_of_contract_check top (
  { A.uid ; A.abstraction_map } as info
) = function
| None -> failwith "unreachable"
| Some true -> (* Modes are complete. *)
  Some (
    A.First {
      info with
        A.uid = uid + 1 ;
        A.abstraction_map = Scope.Map.add top false abstraction_map ;
    }
  )
| Some false -> (* Modes are incomplete, done. *)
  None



(* Using modules is kind of useless here, however it compartments the code and
   maybe in the future will have functors building the strategies. *)

module type Strategy = sig
  val next_analysis:
    A.results ->
    (Scope.t -> (Scope.t * bool * bool) list) ->
    (Scope.t * bool * bool) list ->
    A.param option
end

module MonolithicStrategy : Strategy = struct
  let next_analysis results subs_of_scope all_syss = match all_syss with
    | [] -> failwith "[strategy] \
      no system to analyze (empty list of scopes)\
    "
    | (top,_,_) :: tail -> try (
      match A.results_find top results with
      | [] -> failwith "unreachable"
      | [ {
        A.param = A.ContractCheck info ;
        A.contract_valid ;
      } ] when Flags.Contracts.check_implem () ->
        first_analysis_of_contract_check top info contract_valid
      (* Not the first analysis, done. *)
      | _ -> None
    ) with Not_found ->
      first_param_of results all_syss top
end

module ModularStrategy : Strategy = struct
  let next_analysis results subs_of_scope = function
  | [] -> failwith "[strategy] \
    no system to analyze (empty list of scopes)\
  "
  | all_syss ->

    (* Returns the param for the first analysis of the first system in the
       input list that can be analyzed. Returns [None] if none.

       Assumes no system in the input list has already been analyzed. See
       [go_down]. *)
    let rec go_up = function
      | [] -> None
      | sys :: tail -> (
        (* Format.printf "|up %a@." Scope.pp_print_scope sys ; *)
        try (
          match A.results_find sys results with
          | _ -> Format.asprintf "[strategy.go_up] \
            called with already analyzed system %a
          " Scope.pp_print_scope sys |> failwith
        ) with Not_found -> (
          match first_param_of results all_syss sys with
          | None ->
            (* Format.printf "|> no first param@." ; *)
            go_up tail
          | res -> res
        )
      )
    in

    (* Finds the system that's been analyzed last by going down [all_syss].
       Returns the params of the next analysis for that system if any, calls
       [go_up] on the systems before that system otherwise. *)
    let rec go_down prefix = function
      | (sys, _, _) :: tail -> (
        try (
          (* Format.printf "| %a@." Scope.pp_print_scope sys ; *)
          match A.results_find sys results with
          | [] -> assert false
          | _ when Flags.Contracts.check_implem () |> not -> go_up prefix
          | [ {
            A.param = A.ContractCheck info ;
            A.contract_valid ;
          } ] -> first_analysis_of_contract_check sys info contract_valid
          | result :: _ ->
            if A.result_is_all_proved result then (
              (* Format.printf "|> all proved, going up@." ; *)
              (* Going up. *)
              go_up prefix
            ) else if Flags.Contracts.refinement () then (
              match get_params results subs_of_scope result with
              | None -> (* Cannot refine, going up. *)
                (* Format.printf "Cannot refine for %a@."
                  Scope.pp_print_scope sys ; *)
                go_up prefix
              | Some (sub, abs, ass) -> (* Refinement found. *)
                (* Format.printf "Refined %a for %a@."
                  Scope.pp_print_scope sub
                  Scope.pp_print_scope sys ; *)
                Some (
                  A.Refinement (
                    { A.top = sys ;
                      A.uid = A.results_length results ;
                      A.abstraction_map = abs ;
                      A.assumptions = ass ; },
                    result
                  )
                )
            ) else go_up prefix
        ) with Not_found ->
          (* Format.printf "|> not the last system, going down@." ; *)
          (* Not the last system analyzed, going down. *)
          go_down (sys :: prefix) tail
      )
      | [] ->
        (* We just started, going up. *)
        go_up prefix
    in

    go_down [] all_syss

end

let next_analysis results subs_of_scope all_syss = (
  (* Calling the right function. *)
  if Flags.modular () then ModularStrategy.next_analysis
  else MonolithicStrategy.next_analysis
) results subs_of_scope all_syss


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
