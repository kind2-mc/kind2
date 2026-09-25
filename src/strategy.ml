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
  rec_group: int option ; (** The recursive group of a recursive function *)
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

(* A recursive function a compositional analysis abstracts by its contract
   is refined in steps, when the analysis of the function itself proved its
   contract: its body is unrolled once, its recursive calls abstracted by the
   contract; then one more time up to the limit below; then the function is
   defined at the SMT level (see [LustreFunDefs]). [Analysis.info.unrollings]
   holds the current number of unrollings of each function so refined; a
   concrete recursive function that is not in it is defined. The top system
   and the functions of its recursive group are never in it: their recursive
   calls keep the contract as the induction hypothesis of the recursion, and
   they are never defined. *)

(* The number of unrollings a refinement tries before defining the
   function *)
let unrolling_limit () = Flags.Contracts.rec_unrollings ()

(* Merges the unrollings of the previous analysis with those of the analysis
   that proved the refined system, given the abstractions they go with: a
   function defined in either (concrete, with no unrollings) is defined, and
   one unrolled in both keeps the larger number of unrollings *)
let merge_unrollings (abs_1, unr_1) (abs_2, unr_2) =
  let defined abstraction unrollings scope =
    Scope.Map.find_opt scope abstraction = Some false
    && not (Scope.Map.mem scope unrollings)
  in
  Scope.Map.merge (fun scope n_1 n_2 ->
    if defined abs_1 unr_1 scope || defined abs_2 unr_2 scope then None
    else match n_1, n_2 with
      | Some n, None | None, Some n -> Some n
      | Some n, Some n' -> Some (max n n')
      | None, None -> None
  ) unr_1 unr_2

(* The functions of the recursive group of [scope], reached through the
   subsystems of one another *)
let group_members subs_of_scope scope group =
  let rec collect seen = function
    | [] -> Scope.Set.elements seen
    | s :: rest when Scope.Set.mem s seen -> collect seen rest
    | s :: rest ->
      let subs =
        subs_of_scope s |> List.filter_map (fun (s', { rec_group }) ->
          if rec_group = Some group then Some s' else None)
      in
      collect (Scope.Set.add s seen) (subs @ rest)
  in
  collect Scope.Set.empty [ scope ]

(* The unrollings after refining the concrete recursive function [scope] one
   step further: one more unrolling up to the limit, then, once every
   function of its group is concrete and at the limit, the definition of the
   group, whose functions are removed from the map. [None] if the function
   cannot be refined further: it is defined already, it is the top system or
   a function of its group, or a function of its group is not at the limit
   (its contract was not proved, or the top system is one of them). *)
let next_unrollings subs_of_scope abstraction unrollings scope group =
  match Scope.Map.find_opt scope unrollings with
  | None -> None
  | Some n when n < unrolling_limit () ->
    Some (Scope.Map.add scope (n + 1) unrollings)
  | Some _ ->
    let at_limit s =
      Scope.Map.find_opt s abstraction = Some false
      && (match Scope.Map.find_opt s unrollings with
          | Some n -> n >= unrolling_limit ()
          | None -> false)
    in
    let members = group_members subs_of_scope scope group in
    if List.for_all at_limit members then
      Some (List.fold_left (fun unr s -> Scope.Map.remove s unr) unrollings members)
    else None

(* Whether the last analysis of [scope] proved its contract, i.e. its
   contract holds of its implementation (see [A.result_is_contract_proved]).
   A refinement keeps what was proved under the abstraction of [scope], and
   the checks of its body and the other properties of its analysis are not
   what the abstraction assumed. An imported node has no analysis. *)
let proved_correct results scope =
  match A.results_find scope results with
  | result :: _ -> A.result_is_contract_proved result
  | [] -> failwith "unreachable"
  | exception Not_found -> false

(* Makes the abstract system [scope] concrete: the abstraction and the
   unrollings are updated with those its own analysis proved it under, and a
   recursive function gets one unrolling *)
let make_concrete results (abstraction, unrollings) scope rec_group =
  let info = A.info_of_param (A.results_last scope results).A.param in
  let abstraction' = Scope.Map.add scope false abstraction in
  (* Updating with the abstraction used to prove [scope]. *)
  let abstraction' = merge_abstractions abstraction' info.A.abstraction_map in
  let unrollings' =
    merge_unrollings
      (abstraction, unrollings) (info.A.abstraction_map, info.A.unrollings)
  in
  let unrollings' =
    if rec_group <> None then Scope.Map.add scope 1 unrollings' else unrollings'
  in
  abstraction', unrollings'

(* Try to refine every refineable subsystem of the system [result] corresponds
   to. Traversal of the subsystems is breadth first. Return an option of the
   the new abstraction and unrollings, if any, or [None] otherwise. *)
let get_reachability_abstraction results subs_of_scope result =

  (* Input is a list of list of scope / whatever pairs. Initially input
     only contains [subs]. Function refines every refineable system from [subs],
     more precisely the [result] corresponding to the system recursively.
     In addition, appends the subsystems of all refined systems and
     not abstracted systems to the input. The function looks at
     the subsystems previously appended to the input recursively. *)
  let rec loop seen refined ((abstraction, unrollings) as maps) = function
  | ( (system, { opacity ; rec_group } ) :: tail ) :: lower -> (
    (* A system reached before, through another caller or through a
       recursive call of itself, has been looked at already; without this
       the traversal never ends on a recursive function, whose subsystems
       include itself *)
    if Scope.Set.mem system seen then
      tail :: lower |> loop seen refined maps
    else
    let seen = Scope.Set.add system seen in
    (* Is system currently abstracted? *)
    if Scope.Map.find system abstraction then
      (* It is refineable if it is not opaque and its contract was proved in
         its last analysis. *)
      if opacity <> Opaque && proved_correct results system then
        (tail :: lower) @ [ subs_of_scope system ]
        |> loop seen true (make_concrete results maps system rec_group)
      (* Otherwise keep going. *)
      else tail :: lower |> loop seen refined maps
    else (* System is not abstracted: a recursive function may be refined a
            step further; remembering its subsystems and looping. *)
      let refined, maps =
        match rec_group with
        | Some group when opacity <> Opaque && proved_correct results system -> (
          match
            next_unrollings subs_of_scope abstraction unrollings system group
          with
          | Some unrollings -> true, (abstraction, unrollings)
          | None -> refined, maps
        )
        | _ -> refined, maps
      in
      (tail :: lower) @ [ subs_of_scope system ]
      |> loop seen refined maps
  )
  | [] :: lower -> loop seen refined maps lower
  | [] -> if refined then Some maps else None
  in

  if Flags.Contracts.refinement () && A.result_is_some_reach_proved result then
  (  
    let info = A.info_of_param result.A.param in
    let sys = info.A.top in
    let subs = subs_of_scope sys in

    loop
      (Scope.Set.singleton sys) false
      (info.A.abstraction_map, info.A.unrollings) [ subs ]
  )
  else
    None

(* Looks for the first refineable subsystem of the system [result] corresponds
   to. Traversal of the subsystems is breadth first. Returns an option of the
   scope of the system refined, and the new abstraction and unrollings. *)
let get_refinement_abstraction results subs_of_scope result =
  let info = A.info_of_param result.A.param in
  let sys = info.A.top in
  let subs = subs_of_scope sys in

  (* A refinement is attempted even when the assumptions of some callee could
     not be proved. The guarantees of an abstracted callee are only asserted
     while its assumptions have held so far (its "sofar" flag), and the
     properties proved in the analysis of a concrete callee are asserted
     under the same flag. What was proved under the abstraction therefore
     holds of the implementation of a callee that was proved correct, even on
     a trace that violates its assumptions, and it can be kept after the
     refinement. A refinement can also prove the assumptions themselves: a
     callee abstracted by a contract too weak to establish them may establish
     them once it is concrete. *)
  let abstraction = info.A.abstraction_map in
  let unrollings = info.A.unrollings in

  (* Input is a list of list of scope / whatever pairs. Initially input
     only contains [subs]. Function looks at them as candidates and
     returns the first one [pick] refines, with the new abstraction and
     unrollings. When a candidate is not refined, it is discarded if it is
     abstract, and its subsystems are appended to the input otherwise. If no
     candidate is refined in [subs] function goes looks at the subsystems
     previously appended to the input recursively. *)
  let rec loop pick seen = function
    | ( (candidate, sinfo) :: tail ) :: lower -> (
      (* A candidate reached before, through another caller or through a
         recursive call of itself, has been looked at already; without
         this the traversal never ends on a recursive function, whose
         subsystems include itself *)
      if Scope.Set.mem candidate seen then
        tail :: lower |> loop pick seen
      else
      let seen = Scope.Set.add candidate seen in
      match pick candidate sinfo with
      | Some maps -> Some (candidate, maps)
      | None ->
        if Scope.Map.find candidate abstraction then
          tail :: lower |> loop pick seen
        else
          (tail :: lower) @ [ subs_of_scope candidate ] |> loop pick seen
    )
    | [] :: lower -> loop pick seen lower
    | [] -> None
  in

  (* An abstract system that is not opaque and was proved correct is made
     concrete *)
  let pick_abstract candidate { opacity ; rec_group } =
    if Scope.Map.find candidate abstraction
       && opacity <> O.Opaque && proved_correct results candidate
    then Some (make_concrete results (abstraction, unrollings) candidate rec_group)
    else None
  in
  (* A concrete recursive function that was proved correct is refined a step
     further, if it can be *)
  let pick_unrolled candidate { opacity ; rec_group } =
    match rec_group with
    | Some group
      when not (Scope.Map.find candidate abstraction)
           && opacity <> O.Opaque && proved_correct results candidate -> (
      match
        next_unrollings subs_of_scope abstraction unrollings candidate group
      with
      | Some unrollings -> Some (abstraction, unrollings)
      | None -> None
    )
    | _ -> None
  in

  (* The abstract systems first: making one concrete is the cheaper step,
     and it may be what the properties need. Only when every system is as
     concrete as it can be is a recursive function unrolled further. *)
  match loop pick_abstract (Scope.Set.singleton sys) [ subs ] with
  | Some _ as refinement -> refinement
  | None -> loop pick_unrolled (Scope.Set.singleton sys) [ subs ]

(* The invariants that the last analysis of each system a refinement makes
   concrete, or refines a step further, established, to be assumed in the
   refinement.

   The assumptions of an analysis are the invariants of the analysis before
   it (see [last_assumptions]). The one before a refinement is the analysis
   of the same system in which the refined systems were abstract, and an
   abstract system is given no assumptions: the invariants established by
   the analysis of a refined system, its guarantees among them, are not
   passed on. The invariants of a contract check are left out, as they were
   established assuming the contract. *)
let assumptions_of_refined results (prev_abstraction, prev_unrollings) (abstraction, unrollings) =
  Scope.Map.fold (fun scope is_abstract acc ->
    let was_abstract =
      match Scope.Map.find_opt scope prev_abstraction with
      | Some b -> b
      | None -> false
    in
    let unrolled_further =
      Scope.Map.find_opt scope unrollings
      <> Scope.Map.find_opt scope prev_unrollings
    in
    if is_abstract || not (was_abstract || unrolled_further) then acc
    else
      match A.results_find scope results with
      | { A.param = A.First _ | A.Refinement _ ; A.sys } :: _ ->
        A.assumptions_merge (A.assumptions_of_sys sys) acc
      | _ -> acc
      | exception Not_found -> acc
  ) abstraction A.assumptions_empty

let is_candidate_for_analysis { has_impl ; has_modes } =
  (has_modes && Flags.Contracts.check_modes ()) || has_impl

(* Returns an option of the parameter for the first analysis of a system. *)
let first_param_of ass _results all_nodes scope =

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
      Format.asprintf "Unreachable: could not find info of system %a"
        (Scope.pp_print_scope_internal) scope
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
          A.unrollings = Scope.Map.empty ;
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


let next_monolithic_analysis results main_syss = function
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
        first_param_of A.assumptions_empty results all_syss top
    in

    List.find_map check_sys main_syss

  )


(* Last transition system analyzed. *)
let last_trans_sys = ref None
  
(* Assumptions corresponding to the last system analyzed. *)
let last_assumptions () =
  match ! last_trans_sys with
  | None -> A.assumptions_empty
  | Some sys -> A.assumptions_of_sys sys

(* The parameter of the refinement of [sys] with the abstraction and
   unrollings [maps], after [result] *)
let refinement_of results sys result (abstraction, unrollings) =
  let prev = A.info_of_param result.A.param in
  A.Refinement (
    { A.top = sys ;
      A.uid = A.get_uid () ;
      A.abstraction_map = abstraction ;
      A.unrollings = unrollings ;
      A.assumptions =
        A.assumptions_merge
          (assumptions_of_refined results
            (prev.A.abstraction_map, prev.A.unrollings)
            (abstraction, unrollings))
          (last_assumptions ()) ; },
    result
  )

let next_modular_analysis results subs_of_scope = function
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
          match first_param_of (last_assumptions ()) results all_syss sys with
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
              | Some maps -> Some (refinement_of results sys result maps)
            ) else if Flags.Contracts.refinement () then (
              match get_refinement_abstraction results subs_of_scope result with
              | None -> (* Cannot refine, going up. *)
                go_up prefix
              | Some (_, maps) -> (* Refinement found. *)
                Some (refinement_of results sys result maps)
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
