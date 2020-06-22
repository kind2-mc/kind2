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

(** Invariants are stored in two hash tables mapping them to their certificate.
One table is for one-state invariants, the other is for two-state invariants.
*)

open Lib

module TMap = Term.TermHashtbl
module Cert = Certificate

let fmt_term = Term.pp_print_term

(** Stores invariants. *)
type t = {
  (** One-state invariants. *)
  os: Cert.t TMap.t ;
  (** Two-state invariants. *)
  ts: Cert.t TMap.t ;
}

let copy { os ; ts } =
  { os = TMap.copy os ; ts = TMap.copy ts }

(** The empty collection of invariants. *)
let empty () = {
  os = TMap.create 107 ;
  ts = TMap.create 107 ;
}

(** True if no invariants. *)
let is_empty { os ; ts } =
  TMap.length os = 0 && TMap.length ts = 0

(** Number of invariants. *)
let len { os ; ts } =
  TMap.length os, TMap.length ts

(** Bumps invariants. *)
let of_bound { os ; ts } include_two_state offset =
  let bump_add inv _ acc = Term.bump_state offset inv :: acc in
  TMap.fold bump_add os [] |> (
    if include_two_state then
      TMap.fold bump_add ts
    else
      identity
  )

(** Filters some invariants. *)
let filter f { os ; ts } =
  let res = empty () in
  TMap.iter (
    fun inv cert ->
      if f false inv cert then TMap.add res.os inv cert
  ) os ;
  TMap.iter (
    fun inv cert ->
      if f true inv cert then TMap.add res.ts inv cert
  ) ts ;
  res

(** Adds a one-state invariant.

Removes it from two-state invariants if it was there. *)
let add_os { os ; ts } inv cert =
  TMap.remove ts inv ;
  if TMap.mem os inv |> not then TMap.add os inv cert
(** Adds a two-state invariant.

Does not add it if it is already known as a one-state invariant. *)
let add_ts { os ; ts } inv cert =
  if (
    TMap.mem os inv |> not &&
    TMap.mem ts inv |> not
  ) then TMap.add ts inv cert

(** Remove all the invariants. *)
let clear { os ; ts } =
  TMap.clear os ; TMap.clear ts

(** The one-state invariants. *)
let get_os { os } = TMap.fold (
  fun inv _ acc -> Term.TermSet.add inv acc
) os Term.TermSet.empty
(** The two-state invariants. *)
let get_ts { ts } = TMap.fold (
  fun inv _ acc -> Term.TermSet.add inv acc
) ts Term.TermSet.empty

(** Checks if a term is a known invariant. *)
let mem { os ; ts } term =
  TMap.mem os term || TMap.mem ts term

(** Returns [Some cert] if [term] is a known invariant, or [None] otherwise. *)
let find { os ; ts } term =
  try
    Some (TMap.find os term)
  with Not_found -> (
    try
      Some (TMap.find ts term)
    with Not_found ->
      None
  )

(** **Temporary.** Flattens some invariants into a list. *)
let flatten { os ; ts } =
  let f inv cert tail = (inv, cert) :: tail in
  TMap.fold f os [] |> TMap.fold f ts

(** Merges two collections of invariants (non-destructive). *)
let merge t_1 t_2 =
  let res = { os = TMap.copy t_1.os ; ts = TMap.copy t_2.os } in
  TMap.iter (add_os res) t_2.os ;
  TMap.iter (add_ts res) t_2.ts ;
  res

(** Formats some invariants. *)
let fmt fmt { os ; ts } =
  let os_empty, ts_empty =
    TMap.length os = 0, TMap.length ts = 0
  in
  if not os_empty || not ts_empty then (
    Format.fprintf fmt "@[<v>" ;
    if not os_empty then (
      Format.fprintf fmt "one state:" ;
      os |> TMap.iter (
        fun inv _ -> Format.fprintf fmt "@   %a" fmt_term inv
      ) ;
      if not ts_empty then
        Format.fprintf fmt "@ "
    ) ;
    if not ts_empty then (
      Format.fprintf fmt "two state:" ;
      ts |> TMap.iter (
        fun inv _ -> Format.fprintf fmt "@   %a" fmt_term inv
      ) ;
    ) ;
    Format.fprintf fmt "@]"
  )


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
