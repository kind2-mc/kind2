(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

module I = LustreIdent
module SVar = StateVar

module SVarSet = SVar.StateVarSet

type svar = {
  pos: position ;
  num: int ;
  name: string option;
  svar: SVar.t ;
  scope: (position * string) list ;
}

let mk_svar pos num name svar scope = {
  pos ; num ; name ; svar ; scope
}

(* Quiet pretty printer for non dummy positions. *)
let pprint_pos fmt pos =
  let f,l,c = file_row_col_of_pos pos in
  let f = if f = "" then "" else f ^ "|" in
  Format.fprintf fmt "%sl%dc%d" f l c

let prop_name_of_svar { pos ; num ; name = s; scope } kind name =
  match s with
  | Some n ->
    Format.asprintf "%a%s[%d]" (
      pp_print_list (
        fun fmt (pos, call) ->
          Format.fprintf fmt "%s[%a]." call pprint_pos pos
      ) ""
    ) scope n num
    
  | None ->
    Format.asprintf "%a%s%s[%a][%d]" (
      pp_print_list (
        fun fmt (pos, call) ->
          Format.fprintf fmt "%s[%a]." call pprint_pos pos
      ) ""
    ) scope kind name pprint_pos pos num


type mode = {
  name: I.t ;
  pos: position ;
  path: string list ;
  requires: svar list ;
  ensures: svar list ;
  candidate: bool ;
}

let mk_mode name pos path requires ensures candidate = {
  name ; pos ; path ; requires ; ensures ; candidate
}

type t = {
  assumes: svar list ;
  sofar_assump: StateVar.t ;
  guarantees: (svar * bool) list ;
  modes: mode list ;
}


let mk assumes sofar_assump guarantees modes = {
  assumes ; sofar_assump ; guarantees ; modes
}


let add_ass t assumes = {
  t with
    assumes = t.assumes @ assumes ;
}

let add_gua t guarantees = {
  t with
    guarantees = t.guarantees @ guarantees ;
}


let add_modes t modes = { t with modes = t.modes @ modes }


let svars_of_list l set = l |> List.fold_left (
  fun set { svar } -> SVarSet.add svar set
) set

let svars_of_plist l set = l |> List.fold_left (
  fun set ({ svar }, _) -> SVarSet.add svar set
) set


let svars_of_modes modes set = modes |> List.fold_left (
  fun set { requires ; ensures } ->
    svars_of_list requires set
    |> svars_of_list ensures
) set


let svars_of { assumes ; sofar_assump ; guarantees ; modes } =
  let initial_set =
    if assumes <> [] then
      SVarSet.singleton sofar_assump
    else
      SVarSet.empty
  in
  svars_of_list assumes initial_set
  |> svars_of_plist guarantees
  |> svars_of_modes modes


(* Output a space if list is not empty *)
let space_if_nonempty = function
| [] -> (function _ -> ())
| _ -> (function ppf -> Format.fprintf ppf "@ ")

let pp_print_svar fmt { pos ; num ; svar } =
  Format.fprintf fmt "[%d] %a (%a)"
    num pp_print_pos pos SVar.pp_print_state_var svar

let pp_print_mode safe fmt { name ; pos ; requires ; ensures } =
  Format.fprintf fmt "@[<v 2>mode %a (%a) (@ %a@ %a@ ) ;@]"
    (I.pp_print_ident safe) name pp_print_pos pos (
      pp_print_list (
        fun fmt req ->
          Format.fprintf fmt "  require%a" pp_print_svar req
      ) "@,"
    ) requires (
      pp_print_list (
        fun fmt ens ->
          Format.fprintf fmt "  ensure%a" pp_print_svar ens
      ) "@,"
    ) ensures

let pp_print_contract safe fmt { assumes ; guarantees ; modes } =
  Format.fprintf fmt "@[<v 2>(*@contract@ %a@ %a@ %a@]@ *)" (
      pp_print_list (
        fun fmt ass ->
          Format.fprintf fmt "  assume%a" pp_print_svar ass
      ) "@ "
    ) assumes (
      pp_print_list (
        fun fmt (gua, _) ->
          Format.fprintf fmt "  guarantee%a" pp_print_svar gua
      ) "@ "
    ) guarantees (
      pp_print_list (
        fun fmt mode -> Format.fprintf fmt "  %a" (pp_print_mode safe) mode
      ) "@ "
    ) modes


(* This module contains the stuff allowing to construct a hierarchical version
of a trace of mode paths. The goal is to construct a tree representing the
scopes defined by the contract imports for a node, and the modes active for
these scopes.

This is only used for XML output. *)
module ModeTrace = struct

  (* ADT for scoped mode trees.
  Semantics of the triplet's elements:
    - contract name
    - modes for this contract
    - sub contracts.
  *)
  type mode_tree_rec =
  | Contract of string * string list * mode_tree_rec list

  (* Wraps an ADT to represent a complete mode tree.
  Semantics of the pair's elements:
    - modes directly attached to the node
    - contract imported for the node.
  *)
  type mode_tree = string list * mode_tree_rec list

  let empty_tree = [], []

  (* Inserts a mode path into a mode tree. *)
  let insert (top_modes, subs) path =
    (* Splits a list of contracts at the first contract with name
    [contract]. *)
    let split_at contract =
      let rec loop pref = function
        | (Contract (c, ms, subs)) as head :: tail ->
          if c = contract then pref, (c, ms), subs, tail
          else loop (head :: pref) tail
        | [] -> pref, (contract, []), [], []
      in
      loop []
    in
    (* Zips up a zipper created by [zipper] below.
    ASSUMES [zipper] is not empty. *)
    let zip_up zipper trees mode =
      let rec loop subs = function
        | (pref, (contract, modes), suff) :: tail ->
          let subs =
            Contract (contract, modes, subs) :: suff
            |> List.rev_append pref
          in
          loop subs tail
        | [] -> subs
      in
      match zipper with
      | (pref, (contract, modes), suff) :: tail ->
        loop trees ( (pref, (contract, mode :: modes), suff) :: tail )
      | _ -> failwith "unreachable (zipper cannot be empty)"
    in
    (* Goes down some [trees], following [path], creating trees if needed.
    Creates a zipper to re-assemble the final tree using [zip_up]. *)
    let rec loop zipper path trees = match path with
      | [] -> failwith "unreachable (empty mode path, recursive case)"
      | [ mode ] -> zip_up zipper trees mode
      | contract :: path ->
        let pref, contract, subs, suff = split_at contract trees in
        loop ( (pref, contract, suff) :: zipper ) path subs
    in
    match path with
    | [] -> failwith "unreachable (empty mode path)"
    | [ mode ] -> (mode :: top_modes), subs
    | _ -> top_modes, loop [] path subs

  (** Turns a list of mode paths into a mode tree. *)
  let mode_paths_to_tree paths =
    paths
    |> List.map (fun { path } -> path)
    |> List.fold_left insert empty_tree

  (** Turns a trace of lists of mode paths into a trace of trees. *)
  let mode_trace_to_tree = List.map mode_paths_to_tree

  (** Formats a tree as a cex step in xml. *)
  let fmt_as_cex_step_xml fmt (top_mods, trees) =
    (* Goes down the tree and prints stuff. Constructs [right], which is
    basically the right part of a zipper over the tree structure. It is
    used by [go_up] to print contract trailers and go down in the next
    branch. *)
    let rec loop right = function
      | (Contract (name, modes, subs)) :: tail ->
        Format.fprintf fmt "  @[<v><Contract name=\"%s\">@ " name ;
        List.iter (Format.fprintf fmt "<Mode>%s</Mode>@ ") modes ;
        loop (tail :: right) subs
      | [] -> go_up right
    (* Goes up the "right zipper" constructed by [loop]. Prints contract
    trailers and runs loop on the next branch, if any. *)
    and go_up = function
      | head :: tail -> (
        Format.fprintf fmt "</Contract>@]@ " ;
        match head with
        | [] -> go_up tail
        | _ -> loop tail head
      )
      | [] -> ()
    in

    top_mods |> List.iter (
      Format.fprintf fmt "<Mode name=\"%s\"/>"
    ) ;

    loop [] trees

  (** Formats a tree as a cex step in JSON *)
  let fmt_as_cex_step_json fmt (top_mods, contract_modes) =

    let pp_print_qstring ppf s =
      Format.fprintf ppf "\"%s\"" s
    in

    let pp_print_mode_list pp ppf = function
      | [] -> Format.fprintf ppf " []"
      | lst -> Format.fprintf ppf
        "@,[@[<v 1>@,%a@]@,]" (pp_print_list pp ",@,") lst
    in

    let rec pp_contract_modes ppf (Contract (name, modes, subs)) =
      Format.fprintf fmt
          "{@[<v 1>@,\
            \"contract\" : \"%s\",@,\
            \"modes\" :%a,@,\
            \"subcontractModes\" :%a\
           @]@,}\
          "
          name (pp_print_mode_list pp_print_qstring) modes
          pp_print_contract_modes_list subs
    and
      pp_print_contract_modes_list ppf = function
      | [] -> Format.fprintf ppf " []"
      | lst -> Format.fprintf ppf
        "@,[@[<v 1>@,%a@]@,]" (pp_print_list pp_contract_modes ",@,") lst
    in

    Format.fprintf fmt
      "\"topModes\" :%a,@,\
       \"contractModes\" :%a\
      "
      (pp_print_mode_list pp_print_qstring) top_mods
      pp_print_contract_modes_list contract_modes

end



(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
