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

open Format
open Lib
open Log

(* A position in a file

  The column is the actual colum number, not an offset from the
  beginning of the file as in Lexing.position *)
  type position =
  { pos_fname : string; pos_lnum: int; pos_cnum: int }


let equal_pos
  { pos_fname = p1; pos_lnum = l1; pos_cnum = c1 }
  { pos_fname = p2; pos_lnum = l2; pos_cnum = c2 } =

  l1=l2 && c1=c2 && String.equal p1 p2

(* Lexicographic comparison of pairs *)
let compare_pairs cmp_a cmp_b (a1, b1) (a2, b2) =
  let c_a = cmp_a a1 a2 in if c_a = 0 then cmp_b b1 b2 else c_a

(* Comparision on positions *)
let compare_pos 
    { pos_fname = p1; pos_lnum = l1; pos_cnum = c1 }  
    { pos_fname = p2; pos_lnum = l2; pos_cnum = c2 } =

  compare_pairs 
    String.compare
    (compare_pairs Int.compare Int.compare)
    (p1, (l1, c1)) 
    (p2, (l2, c2)) 


(* A dummy position, different from any valid position *)
let dummy_pos = { pos_fname = ""; pos_lnum = 0; pos_cnum = -1 }

(*
(* A dummy position in the specified file *)
let dummy_pos_in_file fname = 
  { pos_fname = fname; pos_lnum = 0; pos_cnum = -1 }
*)

(* Pretty-print a position *)
let pp_print_position ppf (
  { pos_fname; pos_lnum; pos_cnum } as pos
) =

  if pos = dummy_pos then 

    fprintf ppf "(unknown)"

  else if pos_lnum = 0 && pos_cnum = -1 then

    fprintf ppf "%s" pos_fname

  else

    let fname =
      if pos_fname = "" then Flags.fake_filename () else pos_fname
    in

    fprintf ppf "%s:%d:%d" fname pos_lnum pos_cnum


(** Pretty-print line and column *)
let pp_print_line_and_column ppf { pos_lnum; pos_cnum } =

  if pos_lnum >= 0 && pos_cnum >= 0 then

    fprintf ppf "[l%dc%d]" pos_lnum pos_cnum

  else

    fprintf ppf "[unknown]"

let pp_print_lines_and_columns ppf positions =
  pp_print_list pp_print_line_and_column ", " ppf positions

(* Convert a position from Lexing to a position *)
let position_of_lexing 
    { Lexing.pos_fname;
      Lexing.pos_lnum;
      Lexing.pos_bol;
      Lexing.pos_cnum } = 

  (* Colum number is relative to the beginning of the file *)
  { pos_fname = pos_fname; 
    pos_lnum = pos_lnum; 
    pos_cnum = pos_cnum - pos_bol + 1}


(* Return true if position is a dummy position *)
let is_dummy_pos = function 
  | { pos_cnum = -1 } -> true 
  | _ -> false


(* Return the file, line and column of a position; fail if the
  position is a dummy position *)
let file_row_col_of_pos = function 

  (* Fail if position is a dummy position *)
  | p when is_dummy_pos p -> raise (Invalid_argument "file_row_col_of_pos")

  (* Return tuple of filename, line and column *)
  | { pos_fname; pos_lnum; pos_cnum } -> (pos_fname, pos_lnum, pos_cnum)

(* Return the file of a position *)
let file_of_pos { pos_fname } = pos_fname

(* Return the line and column of a position; fail if the
  position is a dummy position *)
let row_col_of_pos = function

  (* Fail if position is a dummy position *)
  | p when is_dummy_pos p -> raise (Invalid_argument "row_col_of_pos")

  (* Return tuple of line and column *)
  | { pos_lnum; pos_cnum } -> (pos_lnum, pos_cnum)

let pos_of_file_row_col (pos_fname, pos_lnum, pos_cnum) =
{ pos_fname; pos_lnum; pos_cnum }

let parse_log_xml level pos msg =
  let pp_print_fname ppf fname =
    if fname = "" then () else
    Format.fprintf ppf " file=\"%s\"" fname
  in
  let pp_print_line_col ppf pos =
    try
      let lnum, cnum = row_col_of_pos pos in
      Format.fprintf ppf " line=\"%d\" column=\"%d\"" lnum cnum
    with Invalid_argument _ -> ()
  in
  let file = file_of_pos pos in
  (ignore_or_fprintf level)
    !log_ppf
    "@[<hv 2><Log class=\"%a\" source=\"parse\"%a%a>\
    @,@[<hov>%s@]@;<0 -2></Log>@]@."
    pp_print_level_xml_cls level pp_print_line_col pos pp_print_fname file
    (Lib.escape_xml_string msg)

let parse_log_json level pos msg =
  let pp_print_fname ppf fname =
    if fname = "" then () else
    Format.fprintf ppf "\"file\" : \"%s\",@," fname
  in
  let pp_print_line_col ppf pos =
    try
      let lnum, cnum = row_col_of_pos pos in
      Format.fprintf ppf
        "\"line\" : %d,@,\"column\" : %d,@," lnum cnum
    with Invalid_argument _ -> ()
  in
  let file = file_of_pos pos in
  (ignore_or_fprintf level)
    !log_ppf
    ( (if !first_log_flag then
          (first_log_flag := false; "")
        else
          ",@."
      ) ^^
      "{@[<v 1>@,\
        \"objectType\" : \"log\",@,\
        \"level\" : \"%s\",@,\
        \"source\" : \"parse\",@,\
        %a\
        %a\
        \"value\" : @[<h>\"%s\"@]\
        @]@.}@.\
      "
    )
    (string_of_log_level level)
    pp_print_fname file
    pp_print_line_col pos (Lib.escape_json_string msg)