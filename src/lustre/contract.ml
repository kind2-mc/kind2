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

type svar = {
  pos: position ;
  num: int ;
  svar: StateVar.t ;
}

let mk_svar pos num svar = {
  pos ; num ; svar
}

type mode = {
  name: I.t ;
  pos: position ;
  requires: svar list ;
  ensures: svar list ;
}

let mk_mode name pos requires ensures = { name ; pos ; requires ; ensures }

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

let svars_of_list l acc = l |> List.fold_left (
  fun acc { svar } -> svar :: acc
) acc

let svars_of_modes modes acc = modes |> List.fold_left (
  fun acc { requires ; ensures } ->
    svars_of_list requires acc
    |> svars_of_list ensures
) acc

let svars_of { assumes ; guarantees ; modes } =
  svars_of_list assumes []
  |> svars_of_list guarantees
  |> svars_of_modes modes
  |> StateVar.StateVarSet.of_list

(* Output a space if list is not empty *)
let space_if_nonempty = function
| [] -> (function _ -> ())
| _ -> (function ppf -> Format.fprintf ppf "@ ")

let pp_print_svar fmt { pos ; num ; svar } =
  Format.fprintf fmt "[%d] %a (%a)"
    num pp_print_pos pos StateVar.pp_print_state_var svar

let pp_print_mode safe fmt { name ; pos ; requires ; ensures } =
  Format.fprintf fmt "@[<v 2>mode %a (%a) (%a%a@ ) ;@]"
    (I.pp_print_ident safe) name pp_print_pos pos (
      pp_print_list (
        fun fmt req -> Format.fprintf fmt "  require%a" pp_print_svar req
      ) "@ "
    ) requires (
      pp_print_list (
        fun fmt ens -> Format.fprintf fmt "  ensure%a" pp_print_svar ens
      ) "@ "
    ) ensures

let pp_print_contract safe fmt { assumes ; guarantees ; modes } =
  Format.fprintf fmt "@[<v 2>(*@contract@ %a%a%a@]@ *)" (
      pp_print_list (
        fun fmt ass -> Format.fprintf fmt "  assume%a" pp_print_svar ass
      ) "@ "
    ) assumes (
      pp_print_list (
        fun fmt gua -> Format.fprintf fmt "  guarantee%a" pp_print_svar gua
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
  
