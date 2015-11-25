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
  svar: SVar.t ;
  scope: (position * string) list ;
}

let mk_svar pos num svar scope = {
  pos ; num ; svar ; scope
}

(* Quiet pretty printer for non dummy positions. *)
let pprint_pos fmt pos =
  let f,l,c = file_row_col_of_pos pos in
  let f = if f = "" then "" else f ^ "@" in
  Format.fprintf fmt "%sl%dc%d" f l c

let prop_name_of_svar { pos ; num ; scope } kind name =
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
}

let mk_mode name pos path requires ensures = {
  name ; pos ; path ; requires ; ensures
}

type t = {
  assumes: svar list ;
  guarantees: svar list ;
  modes: mode list ;
}

let empty () = {
  assumes = [] ; guarantees = [] ; modes = []
}

let mk assumes guarantees modes = {
  assumes ; guarantees ; modes
}

let add_ass_gua t assumes guarantees = {
  t with
    assumes = assumes @ t.assumes ;
    guarantees = guarantees @ t.guarantees ;
}

let add_modes t modes = { t with modes = modes @ t.modes }

let svars_of_list l set = l |> List.fold_left (
  fun set { svar } -> SVarSet.add svar set
) set

let svars_of_modes modes set = modes |> List.fold_left (
  fun set { requires ; ensures } ->
    svars_of_list requires set
    |> svars_of_list ensures
) set

let svars_of { assumes ; guarantees ; modes } =
  svars_of_list assumes SVarSet.empty
  |> svars_of_list guarantees
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
        fun fmt gua ->
          Format.fprintf fmt "  guarantee%a" pp_print_svar gua
      ) "@ "
    ) guarantees (
      pp_print_list (
        fun fmt mode -> Format.fprintf fmt "  %a" (pp_print_mode safe) mode
      ) "@ "
    ) modes

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
