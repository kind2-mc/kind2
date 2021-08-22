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

let uid_cnt = ref 0
let get_uid () =
  let res = ! uid_cnt in
  uid_cnt := 1 + !uid_cnt ;
  res

(** Type of scope-wise assumptions. *)
type assumptions = Invs.t Scope.Map.t

(** Empty assumptions. *)
let assumptions_empty = Scope.Map.empty

(** Merges two assumptions. *)
let assumptions_merge a_1 a_2 =
  a_1 |> Scope.Map.fold (
    fun scope invs map ->
      let invs =
        try map |> Scope.Map.find scope |> Invs.merge invs
        with Not_found -> invs
      in
      Scope.Map.add scope invs map
  ) a_2

(** Assumptions of a transition system. *)
let assumptions_of_sys =
  TransSys.get_all_invariants

(** Fold over assumptions. *)
let assumptions_fold f init ass =
  Scope.Map.fold (fun k v a -> f a k v) ass init

(** Information for the creation of a transition system *)
type info = {
  top : Scope.t ;
  (** The top system for the analysis run *)

  uid : int ;
  (** UID for the analysis. *)

  abstraction_map : bool Scope.Map.t ;
  (** Systems flagged [true] are to be represented abstractly, those flagged
      [false] are to be represented by their implementation. *)

  assumptions : assumptions ;
  (** Properties that can be assumed invariant in subsystems *)

  (* refinement_of : result option *)
  (* Result of the previous analysis of the top system if this analysis is a
      refinement. *)
}

(** Shrinks an abstraction map to the subsystems of a system. *)
let shrink_info_to_sys ({ abstraction_map } as info) sys =
  let abstraction_map =
    TransSys.fold_subsystems ?include_top:(Some false) (
      fun map sys ->
        let scope = TransSys.scope_of_trans_sys sys in
        try Scope.Map.add scope (Scope.Map.find scope abstraction_map) map
        with Not_found -> Scope.Map.add scope false map
    ) Scope.Map.empty sys
  in
  { info with abstraction_map }

(** Parameter of an analysis. *)
type param =
  (* Simulation of a system *)
  | Interpreter of info
  (* Analysis of the contract of a system. *)
  | ContractCheck of info
  (* First analysis of a system. *)
  | First of info
  (* Refinement of a system. Store the result of the previous analysis. *)
  | Refinement of info * result


(** Result of analysing a transistion system *)
and result = {
  param : param ;
  (** Parameters of the analysis. *)

  time: float ;
  (** Total time of the analysis. *)

  sys : TransSys.t ;
  (** System analyzed, contains property statuses and invariants. *)

  contract_valid : bool option ;
  (** [None] if system analyzed has not contracts,
      [Some true] if it does and they have been proved correct,
      [Some false] if it does and some are unknown / falsified. *)

  requirements_valid : bool option ;
  (** [None] if system analyzed has not sub-requirements,
      [Some true] if it does and they have been proved correct,
      [Some false] if it does and some are unknown / falsified. *)
}

(* Clones an [info], only changes its [uid]. *)
let info_clone info = { info with uid = get_uid () } 

(* Clones a [param], only changes its [uid]. *)
let param_clone = function
| Interpreter info -> Interpreter (info_clone info)
| ContractCheck info -> ContractCheck (info_clone info)
| First info -> First (info_clone info)
| Refinement (info, res) -> Refinement (info_clone info, res)

(* The info or a param. *)
let info_of_param = function
| Interpreter info -> info
| ContractCheck info -> info
| First info -> info
| Refinement (info,_) -> info

(** Shrinks a param to a system. *)
let shrink_param_to_sys param sys = match param with
| Interpreter info -> Interpreter (shrink_info_to_sys info sys)
| ContractCheck info -> ContractCheck (shrink_info_to_sys info sys)
| First info -> First (shrink_info_to_sys info sys)
| Refinement (info, res) -> Refinement ( (shrink_info_to_sys info sys), res )

(* Retrieve the assumptions of a [scope] from a [param]. *)
let param_assumptions_of_scope param scope =
  let { assumptions } = info_of_param param in
  try assumptions |> Scope.Map.find scope
  with Not_found -> Invs.empty ()

(* Return [true] if a scope is flagged as abstract in the [abstraction_map] of
   a [param]. Default to [false] if the node is not in the map. *)
let param_scope_is_abstract param scope =
  let { abstraction_map } = info_of_param param in
  try
    (* Find node in abstraction map by name *)
    Scope.Map.find scope abstraction_map
  (* Assume node to be concrete if not in map *)
  with Not_found -> false

let no_system_is_abstract param =
  let { abstraction_map } = info_of_param param in
  abstraction_map |> Scope.Map.for_all (fun _ v -> not v)

(* Abstraction of a property source. *)
(* type prop_kind = | Contract | Subreq | Prop *)

(* Creates a [result] from a [param], a [t] and an analysis time. *)
let mk_result param sys time =

  let valid, invalid, unknown = TransSys.get_split_properties sys in

  let rec find c r valid = function
    | p :: tail -> (
      match p.Property.prop_source with
      | Property.Assumption _ -> find c (Some valid) valid tail
      | Property.Guarantee _
      | Property.GuaranteeOneModeActive _
      | Property.GuaranteeModeImplication _ -> find (Some valid) r valid tail
      | _ -> find c r valid tail
    )
    | [] -> c, r
  in

  let c_valid, r_valid = find None None true valid in
  let c_valid, r_valid = find c_valid r_valid false invalid in
  let contract_valid, requirements_valid =
    find c_valid r_valid false unknown
  in

  { param ; time ; sys ; contract_valid ; requirements_valid }

(** Returns true if all properties in the system in a [result] have been
    proved. *)
let result_is_all_proved { sys } =
  TransSys.get_prop_status_all_nocands sys |>
  List.for_all (function
    | _, Property.PropInvariant _ -> true
    | _ -> false
  )

(** Returns true if some properties in the system in a [result] have been
    falsified. *)
let result_is_some_falsified { sys } =
  TransSys.get_prop_status_all_nocands sys |>
  List.exists (function
      | _, Property.PropFalse _ -> true
      | _ -> false
    )



(** Map from [Scope.t] to [result list] storing the results found this far. *)
type results = (result list) Scope.Map.t

(** Creates a new [results]. *)
let mk_results () = Scope.Map.empty

(** Adds a [result] to a [results]. *)
let results_add result results =
  (* The key is the top scope of the result. *)
  let key = (info_of_param result.param).top in
  (* Building updated value for [key]. *)
  let value = result :: (
      (* Retrieving current value. *)
      try Scope.Map.find key results with Not_found -> []
    )
  in
  (* Updating map. *)
  Scope.Map.add key value results

(** Returns the list of results for a top scope.

    Raises [Not_found] if not found. *)
let results_find = Scope.Map.find

(** Returns the last result corresponding to a scope. *)
let results_last scope results =
  match results_find scope results with
  | head :: _ -> head
  | [] -> raise Not_found

(** Returns the total number of analyzed systems so far *)
let results_size results = Scope.Map.cardinal results

(** Returns the total number of results stored in a [results]. Used to
    generate UIDs for [param]s. *)
let results_length results =
  Scope.Map.fold (fun _ l sum ->
    (List.length l) + sum
  ) results 0

(** Returns [None] if no properties were falsified but some could not be
    proved, [Some true] if all properties were proved, and [Some false] if
    some were falsified. *)
let results_is_safe results = Scope.Map.fold (fun _ -> function
  | head :: _ -> (
    (* If system is safe, propagate previous result if any. *)
    if result_is_all_proved head then fun opt -> opt
    (* If it's not then result is false. *)
    else if result_is_some_falsified head then fun _ -> Some false
    (* In case of a timeout, propagate false result, none otherwise. *)
    else function | (Some false) as opt -> opt | _ -> None
  )
  | [] -> assert false
) results (Some true)

(** Cleans the results by removing nodes that don't have any property or
contract. *)
let results_clean = Scope.Map.filter (
  fun _ -> function
  | res :: _ -> TransSys.props_list_of_bound res.sys Numeral.zero <> []
  | [] -> failwith "unreachable"
)














let pp_print_param verbose fmt param =
  let { top ; abstraction_map ; assumptions } = info_of_param param in
  let abstract, concrete =
    abstraction_map |> Scope.Map.bindings |> List.fold_left (
      fun (abs,con) (s,b) -> if b then s :: abs, con else abs, s :: con
    ) ([], [])
  in
  Format.fprintf fmt "%s @[<v>top: '%a'%a%a@]"
    ( match param with
      | Interpreter _ -> "Interpreter"
      | ContractCheck _ -> "ContractCheck"
      | First _ -> "First"
      | Refinement _ -> "Refinement")
    Scope.pp_print_scope top

    (fun fmt -> function
      | [], [] ->
        Format.fprintf fmt " (no subsystems)"
      | concrete, abstract ->
        Format.fprintf fmt "@ subsystems@   @[<v>" ;
        ( match concrete with
          | [] -> ()
          | concrete ->
            Format.fprintf fmt "| concrete: @[<hov>%a@]"
              (pp_print_list Scope.pp_print_scope ",@ ") concrete ;
            if abstract = [] |> not then Format.fprintf fmt "@ " ) ;
        ( match abstract with
          | [] -> ()
          | abstract ->
            Format.fprintf fmt "| abstract: @[<hov>%a@]"
          (pp_print_list Scope.pp_print_scope ",@ ") abstract) ;
        Format.fprintf fmt "@]")
    (concrete, abstract)

    (fun fmt -> function
      | [] -> ()
      | assumptions ->
        assumptions |> List.filter (
          fun (_, invs) -> Invs.is_empty invs |> not
        )
        |> Format.fprintf fmt "@ assumptions:@   @[<v>%a@]"
          (pp_print_list
            (fun fmt (s, invs) ->
              let os, ts = Invs.len invs in
              if os + ts > 0 then (
                Format.fprintf fmt "%a: "
                  Scope.pp_print_scope s ;
                if verbose then
                  Format.fprintf fmt "%a" Invs.fmt invs
                else (
                  Format.fprintf fmt "%d one-state, %d two-state" os ts
                )
              )
            )
            "@ "
          )
    )
    (Scope.Map.bindings assumptions)

let split_properties_nocands sys =
  let valid, invalid, unknown = TransSys.get_split_properties sys in
  let remove_cands l =
    List.filter (
      function
      | { Property.prop_source = Property.Candidate _ } -> false
      | _ -> true
    ) l
    |> List.rev in
  remove_cands valid, remove_cands invalid, remove_cands unknown

let pp_print_param_of_result fmt { param ; sys } =
  let param = shrink_param_to_sys param sys in
  match param with
  | Interpreter _ -> Format.fprintf fmt "simulating system"
  | ContractCheck _ -> Format.fprintf fmt "checking mode exhaustiveness"
  | First { abstraction_map } ->
    let count =
      Scope.Map.fold (
        fun _ is_abs acc ->
          if is_abs then acc + 1 else acc
      ) abstraction_map 0
    in
    Format.fprintf
      fmt "without refinement: %d abstract system%s" count (
        if count = 1 then "" else "s"
      )
  | Refinement ( { abstraction_map }, { param = pre_param } ) ->
    let { abstraction_map = pre_abs_map } = info_of_param pre_param in
    let count =
      Scope.Map.fold (
        fun _ is_abs acc ->
          if is_abs then acc + 1 else acc
      ) abstraction_map 0
    in
    let refined =
      Scope.Map.fold (
        fun scope is_abs acc ->
          if not is_abs then try (
            if Scope.Map.find scope pre_abs_map then scope :: acc else acc
          ) with Not_found -> (
            Format.asprintf
              "could not find system %a \
              in abstraction map of previous result"
              Scope.pp_print_scope scope
            |> failwith
          ) else acc
      ) abstraction_map []
    in
    Format.fprintf
      fmt
      "with %d abstract system%s@ \
      but after refining %d system%s:@   \
      @[<hov>%a@]"
      count
      (if count = 1 then "" else "s")
      (List.length refined)
      (if (List.length refined) = 1 then "" else "s")
      (pp_print_list
        Scope.pp_print_scope
        ",@ "
      ) refined

let pp_print_result_quiet fmt ({ time ; sys } as res) =
  match split_properties_nocands sys with
  | valid, [], [] ->
    Format.fprintf fmt "%a:@   @[<v>\
        @{<green>safe@} in %.3fs@ \
        %a@ \
        %d propert%s\
      @]"
      Scope.pp_print_scope (TransSys.scope_of_trans_sys sys)
      time
      pp_print_param_of_result res
      (List.length valid)
      ( match valid with
        | [ _ ] -> "y"
        | _ -> "ies" )
  | valid, [], unknown ->
    Format.fprintf fmt "%a:@   @[<v>\
        @{<red>timeout@}@ \
        %a@ \
        @{<yellow>unknown@}: [ @[<hov>%a@] ]@ \
        @{<green>valid@}:   [ @[<hov>%a@] ]\
      @]"
      Scope.pp_print_scope (TransSys.scope_of_trans_sys sys)
      pp_print_param_of_result res
      (pp_print_list Property.pp_print_prop_quiet ",@ ") unknown
      (pp_print_list Property.pp_print_prop_quiet ",@ ") valid
  | valid, invalid, unknown ->
    Format.fprintf fmt "%a:@   @[<v>\
        @{<red>unsafe@} in %.3fs@ \
        %a@ \
        @{<red>invalid@}: [ @[<hov>%a@] ]@ \
        @{<yellow>unknown@}: [ @[<hov>%a@] ]@ \
        @{<green>valid@}:   [ @[<hov>%a@] ]\
      @]"
      Scope.pp_print_scope (TransSys.scope_of_trans_sys sys)
      time
      pp_print_param_of_result res
      (pp_print_list Property.pp_print_prop_quiet ",@ ") invalid
      (pp_print_list Property.pp_print_prop_quiet ",@ ") unknown
      (pp_print_list Property.pp_print_prop_quiet ",@ ") valid

let pp_print_result fmt {
  param ; sys ; contract_valid ; requirements_valid
} =
  let pp_print_prop_list pref = fun fmt props ->
    Format.fprintf fmt
      "%s: @[<v>%a@]@ "
      pref
      (pp_print_list Property.pp_print_prop_quiet "@ ")
      props
  in
  let pp_print_skip _ _ = () in
  let valid, invalid, unknown = split_properties_nocands sys in
  Format.fprintf fmt "@[<v>\
      config: %a@ - %s@ - %s@ \
      %a%a%a@ \
    @]"
    (pp_print_param true) param
    ( match contract_valid with
      | None -> "no contracts"
      | Some true -> "contract is valid"
      | Some false -> "contract is not valid" )
    ( match requirements_valid with
      | None -> "no sub-assumptions"
      | Some true -> "sub-assumptions are valid"
      | Some false -> "sub-assumptions are not valid" )
    ( match valid with
      | [] -> pp_print_skip
      | _ -> (pp_print_prop_list "valid") )
    valid
    ( match invalid with
      | [] -> pp_print_skip
      | _ -> (pp_print_prop_list "invalid") )
    invalid
    ( match unknown with
      | [] -> pp_print_skip
      | _ -> (pp_print_prop_list "unknown") )
    unknown


(*
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End:
*)
