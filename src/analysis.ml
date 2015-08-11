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

(** Parameters for the creation of a transition system *)
type param = {
    (** The top system for the analysis run *)
    top : Scope.t ;

    (** Systems flagged [true] are to be represented abstractly, those flagged
        [false] are to be represented by their implementation. *)
    abstraction_map : bool Scope.Map.t ;

    (** Properties that can be assumed invariant in subsystems *)
    assumptions : (Scope.t * Term.t) list ;
}

(** Result of analysing a transistion system *)
type result = {
    (** Parameters of the analysis. *)
    param : param ;

    (** System analyzed, contains property statuses and invariants. *)
    sys : TransSys.t ;

    (** [None] if system analyzed has not contracts,
        [Some true] if it does and they have been proved correct,
        [Some false] if it does and some are unknown / falsified. *)
    contract_valid : bool option ;

    (** [None] if system analyzed has not sub-requirements,
        [Some true] if it does and they have been proved correct,
        [Some false] if it does and some are unknown / falsified. *)
    requirements_valid : bool option ;
}

let pp_print_param fmt { top ; abstraction_map ; assumptions } =
  let abstract, concrete =
    abstraction_map |> Scope.Map.bindings |> List.fold_left (
      fun (abs,con) (s,b) -> if b then s :: abs, con else abs, s :: con
    ) ([], [])
  in
  Format.fprintf fmt "@[<v>\
      top: \"%a\"@ \
      subsystems @[<v>| concrete: [@[<hov>%a@]]@ \
                      | abstract: [@[<hov>%a@]]@]@ \
      assumptions: [@[<v>%a@]]@ \
    @]"
    Scope.pp_print_scope top
    (pp_print_list Scope.pp_print_scope ",@ ") concrete
    (pp_print_list Scope.pp_print_scope ",@ ") abstract
    (pp_print_list
      ( fun fmt (s,t) ->
        Format.fprintf fmt "%a: %a"
          Scope.pp_print_scope s
          Term.pp_print_term t )
      "@ ")
    assumptions

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
  let valid, invalid, unknown = TransSys.get_split_properties sys in
  Format.fprintf fmt "@[<v>\
      config: %a@ - %s@ - %s@ \
      %a%a%a@ \
    @]"
    pp_print_param param
    ( match contract_valid with
      | None -> "no contracts"
      | Some true -> "contract is valid"
      | Some false -> "contract is not valid" )
    ( match requirements_valid with
      | None -> "no sub-requirements"
      | Some true -> "sub-requirements are valid"
      | Some false -> "sub-requirements are not valid" )
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


(* Return [true] if the scope is flagged as abstract in
   [abstraction_map]. Default to [false] if the node is not in the
   map. *)
let scope_is_abstract { abstraction_map } scope =
  try
    (* Find node in abstraction map by name *)
    Scope.Map.find scope abstraction_map 
  (* Assume node to be concrete if not in map *)
  with Not_found -> false


(* Return assumptions of scope *)
let assumptions_of_scope { assumptions } scope =
  assumptions |> List.fold_left (fun a (s, t) -> 
     if Scope.equal s scope then t :: a else a
  ) []

(* Abstraction of a property source. *)
type prop_kind = | Contract | Subreq | Prop

(* Creates a [result] from a [param] and a [t]. *)
let result_of param sys =

  let valid, invalid, unknown = TransSys.get_split_properties sys in

  let rec find c r valid = function
    | p :: tail -> (
      match p.Property.prop_source with
      | Property.Contract _ -> find (Some valid) r valid tail
      | Property.Requirement _ -> find c (Some valid) valid tail
      | _ -> find c r valid tail
    )
    | [] -> c, r
  in

  let c_valid, r_valid = find None None true valid in
  let c_valid, r_valid = find c_valid r_valid false invalid in
  let contract_valid, requirements_valid =
    find c_valid r_valid false unknown
  in

  { param ; sys ; contract_valid ; requirements_valid }


(** Run one analysis *)
let run _ = assert false


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  

