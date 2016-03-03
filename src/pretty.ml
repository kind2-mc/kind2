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

(* Captures the output and exit status of a unix command : aux func *)
let syscall cmd =
  let ic, oc = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  ignore(Unix.close_process (ic, oc));
  Buffer.contents buf

(* Set width of pretty printing boxes to number of columns *)
let vt_width =
  try
    let scol = syscall "tput cols" in
    let w = int_of_string (String.trim scol) in
    set_margin w;
    w
  with Not_found | Failure _ -> 80

let print_line = 
  let s = String.make vt_width '-' in
  fun fmt () -> fprintf fmt "%s@\n" s

let print_double_line = 
  let s = String.make vt_width '=' in
  fun fmt () -> fprintf fmt "%s@\n" s


let print_title fmt s =
  printf "%a" print_double_line ();
  printf "* @{<b>%s@}@\n" s;
  printf "%a" print_line ()


let rec print_list print sep fmt = function
  | [] -> ()
  | [e] -> print fmt e
  | e :: l ->
    print fmt e;
    fprintf fmt sep;
    print_list print sep fmt l


type style =
  | User of int
  | Normal
  | Bold
  | Bold_off
  | Dim
  | Underline
  | Underline_off
  | Inverse
  | Inverse_off
  | Blink_off
  | FG_Black
  | FG_Red
  | FG_Green
  | FG_Yellow
  | FG_Blue
  | FG_Magenta
  | FG_Cyan
  | FG_Gray
  | FG_Default
  | BG_Black
  | BG_Red
  | BG_Green
  | BG_Yellow
  | BG_Blue
  | BG_Magenta
  | BG_Cyan
  | BG_Gray
  | BG_Default
  | FG_Black_B
  | FG_Red_B
  | FG_Green_B
  | FG_Yellow_B
  | FG_Blue_B
  | FG_Magenta_B
  | FG_Cyan_B
  | FG_Gray_B
  | FG_Default_B
  | BG_Black_B
  | BG_Red_B
  | BG_Green_B
  | BG_Yellow_B
  | BG_Blue_B
  | BG_Magenta_B
  | BG_Cyan_B
  | BG_Gray_B
  | BG_Default_B


let assoc_style =  function
  | User i  -> "38;5;" ^ string_of_int i (* 256 colors *)
  | Normal -> "0"
  | Bold -> "1"
  | Bold_off -> "22"
  | Dim ->  "2"
  | Underline -> "4"
  | Underline_off -> "24"
  | Inverse -> "7"
  | Inverse_off -> "27"
  | Blink_off -> "22"
  | FG_Black -> "30"
  | FG_Red -> "31"
  | FG_Green -> "32"
  | FG_Yellow -> "33"
  | FG_Blue -> "34"
  | FG_Magenta -> "35"
  | FG_Cyan -> "36"
  | FG_Gray -> "37"
  | FG_Default -> "39"
  | BG_Black -> "40"
  | BG_Red -> "41"
  | BG_Green -> "42"
  | BG_Yellow -> "43"
  | BG_Blue -> "44"
  | BG_Magenta -> "45"
  | BG_Cyan -> "46"
  | BG_Gray -> "47"
  | BG_Default -> "49"
  | FG_Black_B -> "90"
  | FG_Red_B -> "91"
  | FG_Green_B -> "92"
  | FG_Yellow_B -> "93"
  | FG_Blue_B -> "94"
  | FG_Magenta_B -> "95"
  | FG_Cyan_B -> "96"
  | FG_Gray_B -> "97"
  | FG_Default_B -> "99"
  | BG_Black_B -> "100"
  | BG_Red_B -> "101"
  | BG_Green_B -> "102"
  | BG_Yellow_B -> "103"
  | BG_Blue_B -> "104"
  | BG_Magenta_B -> "105"
  | BG_Cyan_B -> "106"
  | BG_Gray_B -> "107"
  | BG_Default_B -> "109"


let style_of_tag = function
  | "n" -> Normal
  | "b" -> Bold
  | "/b" -> Bold_off
  | "dim" -> Dim
  | "u" -> Underline
  | "/u" -> Underline_off
  | "i" -> Inverse
  | "/i" -> Inverse_off
  | "/bl" -> Blink_off
  | "black" -> FG_Black
  | "red" -> FG_Red
  | "green" -> FG_Green
  | "yellow" -> FG_Yellow
  | "blue" -> FG_Blue
  | "magenta" -> FG_Magenta
  | "cyan" -> FG_Cyan
  | "gray" -> FG_Gray
  | "default" -> FG_Default
  | "bg_black" -> BG_Black
  | "bg_red" -> BG_Red
  | "bg_green" -> BG_Green
  | "bg_yellow" -> BG_Yellow
  | "bg_blue" -> BG_Blue
  | "bg_magenta" -> BG_Magenta
  | "bg_cyan" -> BG_Cyan
  | "bg_gray" -> BG_Gray
  | "bg_default" -> BG_Default
  | "black_b" -> FG_Black_B
  | "red_b" -> FG_Red_B
  | "green_b" -> FG_Green_B
  | "yellow_b" -> FG_Yellow_B
  | "blue_b" -> FG_Blue_B
  | "magenta_b" -> FG_Magenta_B
  | "cyan_b" -> FG_Cyan_B
  | "gray_b" -> FG_Gray_B
  | "default_b" -> FG_Default_B
  | "bg_black_b" -> BG_Black_B
  | "bg_red_b" -> BG_Red_B
  | "bg_green_b" -> BG_Green_B
  | "bg_yellow_b" -> BG_Yellow_B
  | "bg_blue_b" -> BG_Blue_B
  | "bg_magenta_b" -> BG_Magenta_B
  | "bg_cyan_b" -> BG_Cyan_B
  | "bg_gray_b" -> BG_Gray_B
  | "bg_default_b" -> BG_Default_B
  | t ->
    try Scanf.sscanf t "c:%d" (fun x -> User x)
    with Scanf.Scan_failure _ | End_of_file ->
      eprintf "tag : %s@." t;
      raise Not_found


let start_tag t = 
  try Printf.sprintf "[%sm" (assoc_style (style_of_tag t))
  with Not_found -> ""

let stop_tag t =
  (* try *)
    let st = match style_of_tag t with
      | Bold -> Bold_off
      | Underline -> Underline_off
      | Inverse -> Inverse_off

      | FG_Black | FG_Red | FG_Green | FG_Yellow | FG_Blue
      | FG_Magenta | FG_Cyan | FG_Gray | FG_Default -> FG_Default

      | BG_Black | BG_Red | BG_Green | BG_Yellow | BG_Blue 
      | BG_Magenta | BG_Cyan | BG_Gray | BG_Default -> BG_Default

      | FG_Black_B | FG_Red_B | FG_Green_B | FG_Yellow_B | FG_Blue_B 
      | FG_Magenta_B | FG_Cyan_B | FG_Gray_B | FG_Default_B -> FG_Default

      | BG_Black_B | BG_Red_B | BG_Green_B | BG_Yellow_B | BG_Blue_B
      | BG_Magenta_B | BG_Cyan_B | BG_Gray_B | BG_Default_B -> BG_Default

      | _ -> Normal
    in
    Printf.sprintf "[%sm" (assoc_style st)
  (* with Not_found -> eprintf "didnr find %s@." t; raise Not_found  *)


let add_colors formatter =
  (* pp_set_tags formatter true; *)
  let old_fs = pp_get_formatter_tag_functions formatter () in
  pp_set_formatter_tag_functions formatter
    { old_fs with
      mark_open_tag = start_tag;
      mark_close_tag = stop_tag }

let _ =
  add_colors std_formatter;
  add_colors err_formatter;
  add_colors !Lib.log_ppf;
  pp_set_margin std_formatter vt_width;
  pp_set_margin err_formatter vt_width



(* ********************************************************************** *)
(* Event tags used when outputting info.                                  *)
(* ********************************************************************** *)

type event_tag =
  | Timeout
  | Success
  | Failure
  | Warning
  | Error
  | Interruption
  | Done

(* Formats a string to construct a tag. *)
let tagify fmt s = Format.fprintf fmt ("@{<b><" ^^ s ^^ ">@}")

let print_event_tag fmt = function
  | Timeout -> tagify fmt "@{<magenta>Timeout}"
  | Success -> tagify fmt "@{<green_b>Success@}"
  | Failure -> tagify fmt "@{<red_b>Failure@}"
  | Warning -> tagify fmt "@{<yellow>Warning@}"
  | Error ->  tagify fmt "@{<magenta_b>Error@}"
  | Interruption -> tagify fmt "@{<magenta>Interruption@}"
  | Done -> tagify fmt "@{<green>Done@}"


let timeout_tag fmt = print_event_tag fmt Timeout
let success_tag fmt = print_event_tag fmt Success
let failure_tag fmt = print_event_tag fmt Failure
let error_tag fmt = print_event_tag fmt Error
let warning_tag fmt = print_event_tag fmt Warning
let interruption_tag fmt = print_event_tag fmt Interruption
let done_tag fmt = print_event_tag fmt Done


let tag_of_level fmt = let open Lib in function
| L_fatal | L_error -> print_event_tag fmt Error
| L_warn -> print_event_tag fmt Warning
| _ -> ()


