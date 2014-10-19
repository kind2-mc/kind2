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

open Printf

module Cursor = struct

  let escape s = sprintf "\x1b[%s" s
  let escape_normal = "\x1b[0m"

  let escape_print s = escape s |> printf "%s"

  let go_to (row, col) =
    sprintf "%i;%if" row col |> escape_print

  let save () = escape_print "s"

  let restore () = escape_print "u"

  let go_up n =
    sprintf "%iA" n |> escape_print
  let go_down n =
    sprintf "%iB" n |> escape_print
  let go_right n =
    sprintf "%iC" n |> escape_print
  let go_left n =
    sprintf "%iD" n |> escape_print

  let go_to_relative (row,col) =
    go_up row ; go_right col

end

type t = {
  col_count: int  ;
  row_count: int  ;
  col_width: int  ;
  row_height: int ;
  log_height: int ;
  mutable log: string list
}

let create_table (col_count, row_count)
		 (col_width, row_height)
		 log_height =
  { col_count = col_count   ;
    row_count = row_count   ;
    col_width = col_width   ;
    row_height = row_height ;
    log_height = log_height ;
    log = []                }

let create_default_table () =
  { col_count = 2  ;
    row_count = 3  ;
    col_width = 40 ;
    row_height = 7 ;
    log_height = 7 ;
    log = []       }

let get_col_count { col_count } = col_count
let get_row_count { row_count } = row_count
let get_col_width { col_width } = col_width
let get_row_height { row_height } = row_height
let get_log_height { log_height } = log_height
let get_log { log } = log

let real_width { col_count ; col_width } =
  (col_width * col_count) + col_count + 1

let real_height { row_count ; row_height ; log_height } =
  (row_height * row_count) + row_count + log_height + 2

let cell_title_offset = 1
let cell_line_offset = 2

let vert_sep, hori_sep = '|', '-'
let no_sep, ne_sep, se_sep, so_sep = '/', '\\', '/', '\\'
let char_to_string c = sprintf "%c" c
let vert_sep_string,
    hori_sep_string,
    no_sep_string,
    ne_sep_string,
    se_sep_string,
    so_sep_string = char_to_string vert_sep,
                    char_to_string hori_sep,
                    char_to_string no_sep,
                    char_to_string ne_sep,
                    char_to_string se_sep,
                    char_to_string so_sep

let log_width table = (real_width table) - 2
let log_offset = 1
let south_west_of_log = 1, 1 + log_offset
let north_west_of_log { log_height } =
  1 + log_height, 1 + log_offset

let rec repeat_char prefix suffix n c =
  if n <= 0 then sprintf "%s%s" prefix suffix
  else repeat_char (sprintf "%s%c" prefix c) suffix (n-1) c

let rec repeat_string prefix suffix n s =
  if n <= 0 then sprintf "%s%s" prefix suffix
  else repeat_string (sprintf "%s%s" prefix s) suffix (n-1) s

let top_top_line table =
  repeat_char
    (sprintf " %c" no_sep)
    ne_sep_string
    ((real_width table) - 1)
    hori_sep

let top_line table =
  repeat_char
    no_sep_string
    ne_sep_string
    ((real_width table) - 2)
    hori_sep

let sep_line { col_count ; col_width } =
  repeat_string
    ""
    vert_sep_string
    col_count
    ( repeat_char
        vert_sep_string
        ""
        col_width
        hori_sep )

let full_sep_line table =
  repeat_char
    vert_sep_string
    vert_sep_string
    ((real_width table) - 2)
    hori_sep

let bot_line table =
  repeat_char
    so_sep_string
    se_sep_string
    ((real_width table) - 2)
    hori_sep
    

let empty_line { col_count ; col_width } =
  let col =
    sprintf "%c%s"
            vert_sep
            (repeat_char "" "" col_width ' ')
  in

  repeat_string
    "" vert_sep_string col_count col
                

let empty_log_line table =
  repeat_char
    vert_sep_string
    vert_sep_string
    ((real_width table) - 2)
    ' '

let rec do_n_times n f =
  if n <= 0 then ()
  else (f () ; do_n_times (n-1) f)

let println s = printf "%s\n" s

open Cursor

let draw_table ({ col_count ;
		  row_count ;
		  col_width ;
		  row_height ;
		  log_height }
		as table) =
  println (top_top_line table) ;
  println (top_line table) ;

  let empty_line = empty_line table in
  let sep_line = sep_line table in
  let full_sep_line = full_sep_line table in
  let empty_log_line = empty_log_line table in
  let bot_line = bot_line table in

  do_n_times
    row_height
    (fun () -> println empty_line) ;

  do_n_times
    (row_count - 1)
    ( fun () ->
      println sep_line ;
      do_n_times
        row_height
        (fun () -> println empty_line)
    ) ;

  println full_sep_line ;
  do_n_times
    log_height
    ( fun () -> println empty_log_line ) ;
  println bot_line ;
  save () ;

  restore () ;
  go_to_relative (real_height table,
		  (real_width table) + 1) ;

  do_n_times
    ((real_height table) - 3)
    ( fun () ->
      printf "%c" vert_sep ;
      go_left 1 ; go_down 1 ) ;

  printf "%c" se_sep ;
  go_left 2 ; go_down 1 ;
  printf "%c" se_sep ;
  restore ()

let clamp_line_fill_rev width char line =

  let rec loop l res =
    let length = String.length l in
    if length == width
    then l :: res
    else if length < width
    then loop (sprintf "%s%c" l char) res
    else
      let pre, suf =
        String.sub l 0 width,
        String.sub l width (length - width)
      in
      loop suf (pre :: res)
  in

  loop line []

let index_to_cell { col_count ; row_count } n =
  assert ( (0 <= n) && (n <= col_count * row_count) ) ;
  (n-1) / col_count + 1, ((n-1) mod col_count) + 1

let north_west_of_cell { col_count ;
			 row_count ;
			 col_width ;
			 row_height ;
			 log_height }
		       (row,col) =
  assert ((0 <= row) && (row <= row_count) &&
            (0 <= col) && (col <= col_count) ) ;
  log_height + 1 + (row_count - row + 1) * (row_height+1),
  1 + (col - 1) * (col_width + 1)

let north_east_of_cell { col_count ;
			 row_count ;
			 col_width ;
			 row_height ;
			 log_height }
		       (row,col) =
  assert ((0 <= row) && (row <= row_count) &&
            (0 <= col) && (col <= col_count) ) ;
  log_height + 1 + (row_count - row + 1) * (row_height+1),
  col * (col_width + 1) - 1

let title_of_cell table cell =
  let row,col = north_west_of_cell table cell in
  row, col + cell_title_offset

let line_of_cell ({ row_height } as table) cell line =
  assert ( (0 <= line) && (line <= row_height - 1) ) ;
  let row,col = title_of_cell table cell in
  row - line, col + cell_line_offset

let set_title_pair table cell title =
  restore () ;
  title_of_cell table cell |> go_to_relative ;
  printf "%s%s%s" (escape "1m") title escape_normal ;
  restore ()
let set_title ({ col_width } as table)
	      cell_index
	      title =
  match List.rev
          (clamp_line_fill_rev
             (col_width - cell_title_offset)
             ' '
             title)
  with
  | clamped :: t ->
     set_title_pair
       table
       (index_to_cell table cell_index)
       clamped
  | [] -> assert false

let update_line_pair table cell line_index line =
  restore () ;
  line_of_cell table cell line_index |> go_to_relative ;
  printf "%s" line ;
  restore ()
let update_line ({ col_width } as  table )
		cell_index
		line_index
		line =
  match List.rev
          (clamp_line_fill_rev
             (col_width -
                cell_line_offset -
                cell_title_offset)
             ' '
             line)
  with
  | clamped :: t ->
     update_line_pair
       table
       (index_to_cell table cell_index)
       line_index
       clamped
  | [] -> assert false


let clamp_log table =
  let rec loop n res = function
    | head :: tail when n > 0 ->
       loop (n-1) (head :: res) tail
    | _ -> List.rev res
  in
  table.log <- loop table.log_height [] table.log

let draw_log table =
  clamp_log table ;
  restore () ;
  let back_to_top () =
    restore () ;
    go_to_relative (north_west_of_log table)
  in

  table.log
  |> List.rev
  |> List.fold_left
       ( fun down l -> back_to_top () ;
                       if down > 0 then go_down down ;
                       printf "%s" l ;
                       down + 1 )
       0
  |> ignore ;
  restore ()

let log_add_line table line =
  let lines_rev =
    clamp_line_fill_rev
      ((log_width table) - log_offset)
      ' '
      line
  in
  table.log <- List.concat [ lines_rev ; table.log ] ;
  clamp_log table ;
  draw_log table





(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

