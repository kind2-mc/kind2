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

(** Functions for pretty ascii output (colors, etc.)

    By default a set of tags are added to stdout and stderr. To activate them
    call [Format.pp_set_tags fmt true]. Colors can be added to another formatter with the function {!add_colors}.

Tags must be added to the format string with [@{<tag> what you want@}]. They can be arbitrarily nested. For instance to print a string in red with part of it bold do
{[
Format.printf "@{<red>I'm red. @{<b> I'm bold red.@}@}"
]}

The font tags available are:
- [n] : normal
- [b] : bold
- [/b] : cancel bold
- [dim] : dimmer color
- [u] : underline
- [/u] : cancel underline
- [i] : italicize
- [/i] : cancel italicize
- [/bl] : cancel blinking

The color (foreground) tags are: 
- [black]
- [red]
- [green]
- [yellow]
- [blue]
- [magenta]
- [cyan]
- [gray]
- [default]
- [c:0-255] give directly the color number on 256 colors terminals

And their bright version
- [black_b]
- [red_b]
- [green_b]
- [yellow_b]
- [blue_b]
- [magenta_b]
- [cyan_b]
- [gray_b]
- [default_b]


The background color tags are: 
- [bg_black]
- [bg_red]
- [bg_green]
- [bg_yellow]
- [bg_blue]
- [bg_magenta]
- [bg_cyan]
- [bg_gray]
- [bg_default]

And their bright version
- [bg_black_b]
- [bg_red_b]
- [bg_green_b]
- [bg_yellow_b]
- [bg_blue_b]
- [bg_magenta_b]
- [bg_cyan_b]
- [bg_gray_b]
- [bg_default_b]


    @author Alain Mebsout
*)


open Format


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
