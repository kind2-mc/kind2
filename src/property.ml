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
  | PropInvariant 

  (* Property is false at some step *)
  | PropFalse of (StateVar.t * Model.term_or_lambda list) list


(* Source of a property *)
type prop_source =

  (* Property is from an annotation *)
  | PropAnnot of position

  (* Property is part of a contract *)
  | Contract of position * string

  (* Property was generated, for example, from a subrange
     constraint *)
  | Generated of StateVar.t list

  (* Property is a requirement of a subnode. The list of state
     variables are the guarantees proving the requirement yields. *)
  | Requirement of position * string list * StateVar.t list

  (* Property is a mode contract implication. *)
  (* | ModeContract of position * string *)

  (* Property is a global contract. *)
  (* | GlobalContract of position * string *)

  (* Property is an instance of a property in a called node

     Reference the instantiated property by the [scope] of the
     subsystem and the name of the property *)
  | Instantiated of string list * string 


(* A property of a transition system *)
type t = 

  { 

    (* Identifier for the property *)
    prop_name : string;

    (* Source of the property *)
    prop_source : prop_source;

    (* Term with variables at offsets [prop_base] and [prop_base - 1] *)
    prop_term : Term.t;

    (* Current status *)
    mutable prop_status : prop_status 

  }


(* Return the length of the counterexample *)
let length_of_cex = function 

  (* Empty counterexample has length zero *)
  | [] -> 0

  (* Length of counterexample from first state variable *)
  | (_, l) :: _ -> List.length l


let pp_print_prop_status_pt ppf = function 
  | PropUnknown -> Format.fprintf ppf "unknown"
  | PropKTrue k -> Format.fprintf ppf "true-for %d steps" k
  | PropInvariant -> Format.fprintf ppf "invariant"
  | PropFalse [] -> Format.fprintf ppf "false"
  | PropFalse cex -> Format.fprintf ppf "false-at %d" (length_of_cex cex)




let pp_print_prop_source ppf = function

  | PropAnnot pos ->
     Format.fprintf
       ppf "%a" pp_print_position pos
  | Contract (pos, name) ->
     Format.fprintf
       ppf "contract %s at %a" name pp_print_position pos
  | Requirement (pos, scope, _) ->
     Format.fprintf
       ppf
       "requirement of %s for call at %a"
       (String.concat "." scope)
       pp_print_position pos
  | Generated _ ->
     Format.fprintf ppf "subrange constraint"
  | Instantiated (scope,_) ->
     Format.fprintf
       ppf
       "instantiated from %s"
              (String.concat "." scope)

let pp_print_prop_source ppf = function 
  | PropAnnot _ -> Format.fprintf ppf ":user"
  | Contract _ -> Format.fprintf ppf ":contract"
  | Requirement _ -> Format.fprintf ppf ":requirement"
  | Generated p -> Format.fprintf ppf ":generated"
  | Instantiated _ -> Format.fprintf ppf ":subsystem"

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
  | PropInvariant
  | PropFalse _ -> true




(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
