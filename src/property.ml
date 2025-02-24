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


(* Current status of a property *)
type prop_status =

  (* Status of property is unknown *)
  | PropUnknown

  (* Property is true for at least k steps *)
  | PropKTrue of int

  (* Property is true in all reachable states *)
  | PropInvariant of Certificate.t

  (* Property is false at some step *)
  | PropFalse of (StateVar.t * Model.value list) list

type prop_bound =
  | From of int
  | Within of int
  | At of int
  | FromWithin of int * int

type prop_kind =
  | Invariant
  | Reachable of prop_bound option

(* A property of a transition system *)
type t = 

  { 

    (* Identifier for the property *)
    prop_name : string;

    (* Source of the property *)
    prop_source : prop_source;

    (* Kind of property (do we wish to prove it invariant or reachable) *)
    prop_kind : prop_kind ;

    (* Term with variables at offsets [prop_base] and [prop_base - 1] *)
    prop_term : Term.t;

    (* Current status *)
    mutable prop_status : prop_status 

  }

(* Source of a property *)
and prop_source =

  (* Property is from an annotation *)
  | PropAnnot of position

  (* Property was generated, for example, from a subrange constraint *)
  | Generated of position option * StateVar.t list

  (* Property is an instance of a property in a called node.

     Reference the instantiated property by the [scope] of the subsystem and
     the name of the property *)
  | Instantiated of Scope.t * t

  (* Contract assumption that a caller has to prove.

     Reference the assumption by its position, the scope of the subsystem,
     and the position of the node call *)
  | Assumption of position * (Scope.t * position)

  (* Contract guarantees. *)
  | Guarantee of (position * Scope.t)
  (* Contract: at least one mode active. *)
  | GuaranteeOneModeActive of (position * Scope.t)
  (* Contract: mode implication. *)
  | GuaranteeModeImplication of (position * Scope.t)
  (* Non-vacuity check *)
  | NonVacuityCheck of (position * Scope.t)

  (* Property is only a candidate invariant here to help prove other
     properties *)
  | Candidate of prop_source option

let is_candidate = function 
| Candidate _ -> true
| PropAnnot _ | Generated _ | Instantiated _ | Assumption _ 
| Guarantee _ | GuaranteeOneModeActive _ | GuaranteeModeImplication _
| NonVacuityCheck _ -> false

let copy t = { t with prop_status = t.prop_status }

(* Return the length of the counterexample *)
let length_of_cex = function 

  (* Empty counterexample has length zero *)
  | [] -> 0

  (* Length of counterexample from first state variable *)
  | (_, l) :: _ -> List.length l


let pp_print_prop_status_pt ppf = function 
  | PropUnknown -> Format.fprintf ppf "unknown"
  | PropKTrue k -> Format.fprintf ppf "true-for %d steps" k
  | PropInvariant (k, _) -> Format.fprintf ppf "invariant at %d" k
  | PropFalse [] -> Format.fprintf ppf "false"
  | PropFalse cex -> Format.fprintf ppf "false-at %d" (length_of_cex cex)


let pp_print_prop_status = pp_print_prop_status_pt

let pp_print_prop_source ppf = function
  | PropAnnot pos ->
     Format.fprintf
       ppf "%a" pp_print_position pos
  | Generated (_, []) ->
     Format.fprintf ppf "generated"
  | Generated _ ->
     Format.fprintf ppf "subrange constraint"
  | Candidate _ ->
     Format.fprintf ppf "candidate invariant"
  | Instantiated (scope,_) ->
     Format.fprintf
       ppf
       "instantiated from %s"
              (String.concat "." scope)

  | Assumption (_, (scope, _)) ->
    Format.fprintf ppf "assumption of %s" (String.concat "." scope)
  | Guarantee (_, scope) ->
    Format.fprintf ppf "guarantee (%a)" Scope.pp_print_scope_internal scope
  | GuaranteeOneModeActive (_, scope) ->
    Format.fprintf ppf "one mode active (%a)" Scope.pp_print_scope_internal scope
  | GuaranteeModeImplication (_, scope) ->
    Format.fprintf ppf "mode implication %a" Scope.pp_print_scope_internal scope
  | NonVacuityCheck (_, scope) ->
    Format.fprintf ppf "non-vacuity check (%a)" Scope.pp_print_scope_internal scope

let pp_print_prop_quiet ppf { prop_name ; prop_source } =
  Format.fprintf ppf
    "'%s': %a"
    prop_name
    pp_print_prop_source prop_source

let pp_print_prop_source ppf = function 
  | PropAnnot _ -> Format.fprintf ppf ":user"
  | Generated _ -> Format.fprintf ppf ":generated"
  | Candidate _ -> Format.fprintf ppf ":candidate"
  | Instantiated _ -> Format.fprintf ppf ":subsystem"
  | Assumption _ -> Format.fprintf ppf ":assumption"
  | Guarantee _ -> Format.fprintf ppf ":guarantee"
  | GuaranteeOneModeActive _ -> Format.fprintf ppf ":one_mode_active"
  | GuaranteeModeImplication _ -> Format.fprintf ppf ":mode_implication"
  | NonVacuityCheck _ -> Format.fprintf ppf ":non_vacuity_check"

let pp_print_property ppf { prop_name; prop_source; prop_term; prop_status } = 

  Format.fprintf 
    ppf
    "@[<hv 1>(%s@ %a@ %a@ %a)@]"
    prop_name
    Term.pp_print_term prop_term
    pp_print_prop_source prop_source
    pp_print_prop_status_pt prop_status

(* Property status is known? *)
let prop_status_known = function 

  (* Property may become invariant or false *)
  | PropUnknown
  | PropKTrue _ -> false

  (* Property is invariant or false *)
  | PropInvariant _
  | PropFalse _ -> true


(* Mark property as invariant *)
let set_prop_invariant p cert =

  (* Modify status *)
  p.prop_status <- 

    (* Check current status *)
    match p.prop_status with

      (* Mark as k-true if it was unknown *)
      | PropKTrue _
      | PropInvariant _
      | PropUnknown -> PropInvariant cert

      (* Fail if property was l-false for l <= k *)
      | PropFalse _ -> 
        let msg =
          Format.sprintf "Falsified property '%s' was proven invariant too!"
            p.prop_name
        in
        failwith msg


(* Mark property as k-false *)
let set_prop_false p cex =

  (* Modify status *)
  p.prop_status <- 

    (* Check current status *)
    match p.prop_status with

      (* Mark property as k-false if it was unknown, l-true for l <
         k or invariant *)
      | PropUnknown -> PropFalse cex

      (* Fail if property was invariant *)
      | PropInvariant _ -> 
        let msg =
          Format.sprintf "Property '%s' proven invariant was falsified too!"
            p.prop_name
        in
        failwith msg

      (* Fail if property was l-true for l >= k *)
      | PropKTrue l when l > (length_of_cex cex) -> 
        let msg =
          Format.sprintf "Property '%s' proven %d-true before, now falsified with cex of length %d!"
            p.prop_name l (length_of_cex cex)
        in
        failwith msg

      (* Mark property as false if it was l-true for l < k *)
      | PropKTrue _ -> PropFalse cex

      (* Keep if property was l-false for l <= k *)
      | PropFalse cex' when (length_of_cex cex') <= (length_of_cex cex) -> 
        p.prop_status

      (* Mark property as k-false *)
      | PropFalse _ -> PropFalse cex


(* Mark property as k-true *)
let set_prop_ktrue p k =

  (* Modify status *)
  p.prop_status <- 

    (* Check current status *)
    match p.prop_status with

      (* Mark as k-true if it was unknown *)
      | PropUnknown -> PropKTrue k

      (* Keep if it was l-true for l > k *)
      | PropKTrue l when l > k -> p.prop_status

      (* Mark as k-true if it was l-true for l <= k *)
      | PropKTrue _ -> PropKTrue k

      (* Keep if it was invariant *)
      | PropInvariant _ -> p.prop_status

      (* Keep if property was l-false for l > k *)
      | PropFalse cex when (length_of_cex cex) > k -> p.prop_status

      (* Fail if property was l-false for l <= k *)
      | PropFalse cex ->
        let msg =
          Format.sprintf "Falsified property '%s' (l=%d) was proven %d-true too!"
            p.prop_name (length_of_cex cex) k
        in
        failwith msg


(* Mark property status *)
let set_prop_status p = function

  | PropUnknown -> ()

  | PropKTrue k -> set_prop_ktrue p k 

  | PropInvariant cert -> set_prop_invariant p cert

  | PropFalse c -> set_prop_false p c

let set_prop_unknown p =
  p.prop_status <- PropUnknown

(* Get property status *)
let get_prop_status { prop_status } = prop_status

let rec get_prop_original_source { prop_source } =
  match prop_source with
  | Instantiated (_, p) -> get_prop_original_source p
  | _ -> prop_source


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
