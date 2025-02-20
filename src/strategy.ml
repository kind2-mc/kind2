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
module O = Opacity

(** Information used by the strategy module. *)
type info = {
  opacity: Opacity.t ; (** Whether the node should be always abstracted by its contract, never, or sometimes *)
  has_contract: bool ; (** Does the system have a contract? *)
  has_impl: bool ;     (** Does the system have an implementation? *)
  has_modes: bool ;    (** Does the system have modes? *)
}

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

(* Try to refine every refineable subsystem of the system [result] corresponds
   to. Traversal of the subsystems is breadth first. Return an option of the
   the new abstraction, if any, or [None] otherwise. *)
let get_reachability_abstraction results subs_of_scope result =

  (* Input is a list of list of scope / whatever pairs. Initially input
     only contains [subs]. Function refines every refineable system from [subs],
     more precisely the [result] corresponding to the system recursively.
     In addition, appends the subsystems of all refined systems and
     not abstracted systems to the input. The function looks at
     the subsystems previously appended to the input recursively. *)
  let rec loop refined abstraction = function
  | ( (system, { opacity } ) :: tail ) :: lower -> (
    (* Is system currently abstracted? *)
    if Scope.Map.find system abstraction then
      (* Is system refineable? *)
      if (opacity <> Opaque) then (
        try match A.results_find system results with
        | ({ A.param } as result) :: _ ->
          (* It is if everything was proved in the last analysis. *)
          if A.result_is_all_inv_proved result then (
            let info = A.info_of_param param in
            let sub = info.A.top in
            (* System is now concrete. *)
            let abstraction = Scope.Map.add sub false abstraction in
            (* Updating with the abstraction used to prove [sub]. *)
            let abstraction =
              merge_abstractions abstraction info.A.abstraction_map
            in
            (tail :: lower) @ [ subs_of_scope system ]
            |> loop true abstraction
          )
          (* Otherwise keep going. *)
          else tail :: lower |> loop refined abstraction
        | [] -> failwith "unreachable"
        with Not_found -> (* Case of imported nodes (they have no result) *)
          tail :: lower |> loop refined abstraction
      )
      else (
        tail :: lower |> loop refined abstraction
      )
    else (* System is not abstracted, remembering its subsystems and
            looping. *)
      (tail :: lower) @ [ subs_of_scope system ]
      |> loop refined abstraction
  )
  | [] :: lower -> loop refined abstraction lower
  | [] -> if refined then Some abstraction else None
  in

  if Flags.Contracts.refinement () && A.result_is_some_reach_proved result then
  (  
    let info = A.info_of_param result.A.param in
    let sys = info.A.top in
    let subs = subs_of_scope sys in
    let abstraction = info.A.abstraction_map in

    loop false abstraction [ subs ]
  )
  else
    None

(* Looks for the first refineable subsystem of the system [result] corresponds
   to. Traversal of the subsystems is breadth first. Returns an option of the
   scope of the system refined, and the new abstraction. *)
let get_refinement_abstraction results subs_of_scope result =
  let info = A.info_of_param result.A.param in
  let sys = info.A.top in
  let subs = subs_of_scope sys in

  match result.A.requirements_valid with
  | Some false -> (* Requirements could not be proved, aborting. *)
    None
  | _ -> (
    let abstraction = info.A.abstraction_map in

    (* Input is a list of list of scope / whatever pairs. Initially input
       only contains [subs]. Function looks at them as candidates and
       returns the first refineable system from [subs], more precisely the
       [result] corresponding to the system. When a non-refineable system
       is encountered, it is discarded and its subsystems are appended to
       the input. If no refineable system is found in [subs] function goes
       looks at the subsystems previously appended to the input
       recursively. *)
    let rec loop = function
      | ( (candidate, { opacity }) :: tail ) :: lower -> (
        (* Is candidate currently abstracted? *)
        if Scope.Map.find candidate abstraction then
          (* Is candidate refineable? *)
          if (opacity <> O.Opaque) then (
            try match A.results_find candidate results with
            | result :: _ ->
              (* It is if everything was proved in the last analysis. *)
              if A.result_is_all_inv_proved result then Some result
              (* Otherwise keep going. *)
              else tail :: lower |> loop
            | [] -> failwith "unreachable"
            with Not_found -> (* Case of imported nodes (they have no result) *)
              tail :: lower |> loop
          )
          else (
            tail :: lower |> loop
          )
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
    | Some { A.param } ->
      (* Refinement found, need to update abstraction and lift invariants. *)
      let info = A.info_of_param param in
      let sub = info.A.top in
      (* System is now concrete. *)
      let abstraction = Scope.Map.add sub false abstraction in
      (* Updating with the abstraction used to prove [sub]. *)
      let abstraction =
        merge_abstractions abstraction info.A.abstraction_map
      in

      Some (sub, abstraction)
  )

let is_candidate_for_analysis { has_impl ; has_modes } =
  (has_modes && Flags.Contracts.check_modes ()) || has_impl

(* Returns an option of the parameter for the first analysis of a system. *)
let first_param_of in_sys ass _results all_nodes scope =

  let rec loop abstraction = function
    | (sys, { opacity; has_impl ; has_contract ; has_modes }) :: tail -> (
      (* Can/should we abstract this system? *)
      let is_abstract =
        if sys = scope then 
          has_modes && (Flags.Contracts.check_modes ())
        else
          (not has_impl) || (has_contract &&
            (opacity=O.Opaque ||
             (Flags.Contracts.compositional() && opacity<>O.Transparent)
            )
          )
      in
      let abstraction = Scope.Map.add sys is_abstract abstraction in
      loop abstraction tail
      (*if is_abstract then
        (* Sys is abstract, don't care if it's correct. *)
        loop abstraction tail
      else ( (* Sys is not abstract, making sure it's correct and lifting
                invariants. *)
        try (
        (* What do we know about this system? *)
        match A.results_find sys results with
        | [] -> assert false
        | result :: _ ->
          if A.result_is_some_inv_falsified result |> not then
            (* System has not been proved unsafe. *)
            loop abstraction tail
          else None (* System is not correct, no need to keep going. *)
        ) with Not_found ->
          (* We know nothing about this sys. *)
          loop abstraction tail
      )*)
    )
    | [] -> Some (abstraction)
  in

  let has_first_analysis =
    try (
      is_candidate_for_analysis (List.assoc scope all_nodes)
    ) with Not_found ->
      let node = InputSystem.get_lustre_node in_sys scope |> Option.get in
      Format.asprintf "Unreachable: could not find info of system %a"
        (LustreIdent.pp_print_ident true) node.name
      |> failwith
  in

  if has_first_analysis then (
    match loop Scope.Map.empty all_nodes with
    | None -> None
    | Some (abstraction) ->
      let info =
        { A.top = scope ;
          A.uid = A.get_uid () ;
          A.abstraction_map = abstraction ;
          A.assumptions = ass }
      in
      if Scope.Map.find scope abstraction then
        (* Top level is abstract, we're checking its contract. *)
        Some (A.ContractCheck info)
      else
        (* Top level is not abstract, first analysis. *)
        Some (A.First info)
  ) else None

(** First analysis after the mode consistency analysis, if any. *)
let first_analysis_of_contract_check ass top (
  { A.abstraction_map } as info
) = function
| None -> failwith "unreachable"
(* Next analysis is performed independently of previous result *)
| Some _ ->
  Some (
    A.First {
      info with
        A.uid = A.get_uid () ;
        A.abstraction_map = Scope.Map.add top false abstraction_map ;
        A.assumptions = ass ;
    }
  )
(* Next analysis is only performed if modes are complete *)
(*
| Some true -> (* Modes are complete. *)
  Some (
    A.First {
      info with
        A.uid = A.get_uid () ;
        A.abstraction_map = Scope.Map.add top false abstraction_map ;
        A.assumptions = ass ;
    }
  )
| Some false -> (* Modes are incomplete, done. *)
  None
*)


let next_monolithic_analysis in_sys results main_syss = function
  | [] -> failwith "[strategy] \
      no system to analyze (empty list of scopes)\
    "
  | all_syss -> (
    
    let check_sys ( top, { has_impl } ) =
      try (
        match A.results_find top results with
        | [] -> failwith "unreachable"
        | [ {
          A.param = A.ContractCheck info ;
          A.contract_valid ;
        } ] when Flags.Contracts.check_implem () ->
          if has_impl then
            (* Invariants generated during ContractCheck analysis are discarded.
              They were generated assuming the contract! *)
            let ass = A.assumptions_empty in
            first_analysis_of_contract_check ass top info contract_valid
          else None
        (* Not the first analysis, done. *)
        | _ -> None
      ) with Not_found ->
        first_param_of in_sys A.assumptions_empty results all_syss top
    in

    Lib.find_map check_sys main_syss

  )


(* Last transition system analyzed. *)
let last_trans_sys = ref None
  
(* Assumptions corresponding to the last system analyzed. *)
let last_assumptions () =
  match ! last_trans_sys with
  | None -> A.assumptions_empty
  | Some sys -> A.assumptions_of_sys sys

let next_modular_analysis in_sys results subs_of_scope = function
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
        try (
          match A.results_find sys results with
          | _ -> None
        ) with Not_found -> (
          match first_param_of in_sys (last_assumptions ()) results all_syss sys with
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
      | (sys, { has_impl }) :: tail -> (
        try (
          match A.results_find sys results with
          | [] -> assert false
          | _ when Flags.Contracts.check_implem () |> not ||
              not has_impl -> go_up prefix
          | [ {
            A.param = A.ContractCheck info ;
            A.contract_valid ;
            (* A.sys = trans_sys ; *)
          } ] ->
            (* last_trans_sys := Some trans_sys ; *)
            (* ^^-- Invariants generated during ContractCheck analysis are discarded.
               They were generated assuming the contract! *)
            first_analysis_of_contract_check
              (last_assumptions ()) sys info contract_valid
          | result :: _ ->
            last_trans_sys := Some result.A.sys ;
            if A.result_is_all_inv_proved result then (
              match get_reachability_abstraction results subs_of_scope result with
              | None -> (
                (* Format.printf "|> all proved, going up@." ; *)
                (* Going up. *)
                go_up prefix
              )
              | Some abs -> (
                Some (
                  A.Refinement (
                    { A.top = sys ;
                      A.uid = A.get_uid () ;
                      A.abstraction_map = abs ;
                      A.assumptions = last_assumptions () ; },
                    result
                  )
                )
              )
            ) else if Flags.Contracts.refinement () then (
              match get_refinement_abstraction results subs_of_scope result with
              | None -> (* Cannot refine, going up. *)
                go_up prefix
              | Some (_, abs) -> (* Refinement found. *)
                Some (
                  A.Refinement (
                    { A.top = sys ;
                      A.uid = A.get_uid () ;
                      A.abstraction_map = abs ;
                      A.assumptions = last_assumptions () ; },
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


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
