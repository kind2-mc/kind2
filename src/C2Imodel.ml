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


(** We need to store sets of models. Very inefficient, investigate ZDD.

    Also, not sure the way to deal with partial models makes that much sense.
    See [model_equal]. *)


open Lib
open Actlit

(** |===| Shorthand for modules, types and functions. *)

(** Modules. *)
module Candidate = C2ICandidate
module Solver = SMTSolver
module Sys = TransSys
module VHT = Var.VarHashtbl

(** Types. *)
type model = Model.t

(** Functions. *)
let offset_of = Var.offset_of_state_var_instance
let set_offset = Var.set_offset_of_state_var_instance
let is_const = Var.is_const_state_var
let mk_vht = VHT.create
let vht_add = VHT.add


(** Iterates over a [model] for variables at 0 and possibly at 1. Returns two
    models (hashtables): one containing the bindings for the variables at 0 and
    another with the bindings for the variables at 1 with the offset of these
    variables changed to 0.

    Argument [n] is the capacity new hash tables are created with. Should be
    the number of state variables in the system. *)
let model_split n model =
  (** Creating result hash tables. *)
  let m0, m1 = mk_vht n, mk_vht n in
  (** Filling them with bindings. *)
  model |> VHT.iter (fun var va1 ->
    if is_const var then ( vht_add m0 var va1 ; vht_add m1 var va1 )
    else match offset_of var |> Numeral.to_int with
    | -1 -> ()
    | 0 -> vht_add m0 var va1
    | 1 -> let var = set_offset var Numeral.zero in vht_add m1 var va1
    | n -> Format.sprintf "unexpected offset of variable %d > 1" n |> failwith
  ) ;
  (** Returning split models. *)
  m0, m1

(** Exception used by [model_equal] to break out of the iteration. *)
exception Not_equal

(** Checks if two models are equal. *)
let model_equal lhs rhs =
  try
    lhs |> VHT.iter (fun var va1 ->
      try if (VHT.find rhs var) == va1 then () else raise Not_equal
      (** [rhs] does not feature rhs. *)
      with Not_found -> raise Not_equal
    ) ;
    true
  with Not_equal -> false

(** Checks if a model is in a list of models. *)
let contains model models = List.exists (model_equal model) models

(** Raised by update colors if [white] intersects [black] by transitivity. *)
exception PropIsFalse

(** Updates the white, grey and black model lists.
    
    In theory thanks to the cost function the intersetion between the new sets
    and the old ones is empty. *)
let update_colors n white grey black nu_white nu_grey nu_black =
  (** Updating white. *)
  let white =
    nu_white |> List.fold_left (fun white w ->
      (model_split n w |> fst) :: white
    ) white
  in

  (** Updating black. *)
  let black =
    nu_black |> List.fold_left (fun black b ->
      (model_split n b |> fst) :: black
    ) black
  in

  (* Updating white, grey and black with the new grey models. *)
  nu_grey |> List.fold_left (fun (white, grey, black) g ->
    let m0, m1 = model_split n g in

    match contains m0 white, contains m1 black with
    | true, false ->
      (** [m0] is white, so is [m1]. *)
      m1 :: white, grey, black
    | false, true ->
      (** [m1] is black, so is [m0]. Still adding to grey, because black
          might be reset later. *)
      white, (m0, m1) :: grey, m0 :: black
    | false, false ->
      (** None of the above, adding to grey. *)
      white, (m0, m1) :: grey, black
    | _ ->
      (** Property is invalid. *)
      raise PropIsFalse
  ) (white, grey, black)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
