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

   This module is adapted from the model checker Cubicle
   http://cubicle.lri.fr

*)

open Format

(** Functions for pretty ascii output (colors, etc.)

    @author Alain Mebsout
 *)


(** {1 Pretty colors} *)

(** Width of the virtual terminal (80 if cannot be detected) *)
val vt_width : int

(** prints separating line *)
val print_line : formatter -> unit -> unit

(** prints separating double line *)
val print_double_line : formatter -> unit -> unit

(** add color tags to a formatter *)
val add_colors : formatter -> unit


(** {1 Event tags} *)

(** Timeout tag. *)
val timeout_tag : Format.formatter -> unit

(** Success tag. *)
val success_tag : Format.formatter -> unit

(** Failure tag. *)
val failure_tag : Format.formatter -> unit

(** Error tag. *)
val error_tag : Format.formatter -> unit

(** Warning tag. *)
val warning_tag : Format.formatter -> unit

(** Interruption tag. *)
val interruption_tag : Format.formatter -> unit

(** Done tag. *)
val done_tag : Format.formatter -> unit

val tag_of_level : formatter -> Lib.log_level -> unit
