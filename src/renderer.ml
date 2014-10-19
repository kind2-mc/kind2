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

open Lib


(*
_/\\\________/\\\_____________________________/\\\_______________/\\\\\\\\\_____________
_\/\\\_____/\\\//_____________________________\/\\\_____________/\\\///////\\\__________
__\/\\\__/\\\//______/\\\______________________\/\\\____________\///______\//\\\________
___\/\\\\\\//\\\_____\///___/\\/\\\\\\__________\/\\\______________________/\\\/________
____\/\\\//_\//\\\_____/\\\_\/\\\////\\\____/\\\\\\\\\___________________/\\\//_________
_____\/\\\____\//\\\___\/\\\_\/\\\__\//\\\__/\\\////\\\________________/\\\//___________
______\/\\\_____\//\\\__\/\\\_\/\\\___\/\\\_\/\\\__\/\\\______________/\\\/_____________
_______\/\\\______\//\\\_\/\\\_\/\\\___\/\\\_\//\\\\\\\/\\____________/\\\\\\\\\\\\\\\__
________\///________\///__\///__\///____\///___\///////\//____________\///////////////__
*)

let header_lines_3D =
  [ "_/\\\\\\________/\\\\\\_____________________________/\\\\\\_______________/\\\\\\\\\\\\\\\\\\_____________" ;
    "_\\/\\\\\\_____/\\\\\\//_____________________________\\/\\\\\\_____________/\\\\\\///////\\\\\\__________" ;
    "__\\/\\\\\\__/\\\\\\//______/\\\\\\______________________\\/\\\\\\____________\\///______\\//\\\\\\________" ;
    "___\\/\\\\\\\\\\\\//\\\\\\_____\\///___/\\\\/\\\\\\\\\\\\__________\\/\\\\\\______________________/\\\\\\/________" ;
    "____\\/\\\\\\//_\\//\\\\\\_____/\\\\\\_\\/\\\\\\////\\\\\\____/\\\\\\\\\\\\\\\\\\___________________/\\\\\\//_________" ;
    "_____\\/\\\\\\____\\//\\\\\\___\\/\\\\\\_\\/\\\\\\__\\//\\\\\\__/\\\\\\////\\\\\\________________/\\\\\\//___________" ;
    "______\\/\\\\\\_____\\//\\\\\\__\\/\\\\\\_\\/\\\\\\___\\/\\\\\\_\\/\\\\\\__\\/\\\\\\______________/\\\\\\/_____________" ;
    "_______\\/\\\\\\______\\//\\\\\\_\\/\\\\\\_\\/\\\\\\___\\/\\\\\\_\\//\\\\\\\\\\\\\\/\\\\____________/\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\__" ;
    "________\\///________\\///__\\///__\\///____\\///___\\///////\\//____________\\///////////////__" ;
  ]


(*
            _  __     _                _     ___   
     o O O | |/ /    (_)    _ _     __| |   |_  )  
    o      | ' <     | |   | ' \   / _` |    / /   
   TS__[O] |_|\_\   _|_|_  |_||_|  \__,_|   /___|  
  {======|_|"""""|_|"""""|_|"""""|_|"""""|_|"""""| 
 ./o--000'"`-0-0-'"`-0-0-'"`-0-0-'"`-0-0-'"`-0-0-'
*)

let header_train =
  [ "            _  __     _                _     ___   " ;
    "     o O O | |/ /    (_)    _ _     __| |   |_  )  " ;
    "    o      | ' <     | |   | ' \\   / _` |    / /   " ;
    "   TS__[O] |_|\\_\\   _|_|_  |_||_|  \\__,_|   /___|  " ;
    "  {======|_|\"\"\"\"\"|_|\"\"\"\"\"|_|\"\"\"\"\"|_|\"\"\"\"\"|_|\"\"\"\"\"| " ;
    " ./o--000'\"`-0-0-'\"`-0-0-'\"`-0-0-'\"`-0-0-'\"`-0-0-' " ; ]

module Slider = struct

  type t = {
    lines : string list ;
    fill_char : char ;
    height : int ;
    last : int ;
    screen_width : int ;
    mutable pref : int ;
    mutable suff : int ;
    mutable from : int ;
    mutable too : int ;
    mutable count: int ;
  }

  let count_default = 10

  let create_slider screen_width = function

    | line :: tail as lines ->
       let width = String.length line in

       assert (List.for_all (fun l -> String.length l == width) tail) ;

       { lines ;
         fill_char = line.[0] ;
         height = List.length lines ;
         last = width - 1 ;
         screen_width ;
         pref = screen_width - 1 ;
         suff = 0 ;
         from = 0 ;
         too = 0 ;
         count = count_default ; }

    | _ -> failwith "Empty header."

  let get_height { height } = height

  let rec fill s n char =
    if n > 0 then
      fill (Printf.sprintf "%s%c" s char) (n-1) char
    else s

  let build_line fill_char pref suff from too line =
    Printf.sprintf
      "%s%s%s"
      (fill "" pref fill_char)
      (String.sub line from (too - from + 1))
      (fill "" suff fill_char)

  let stage_next_frame
        ({ last ; screen_width ; pref ; suff ; from ; too ; count }
         as slider)=

    assert (pref + (too - from) + suff == screen_width - 1) ;

    if count >= 0 then slider.count <- count - 1
    else if suff >= screen_width - 1 then (
      slider.pref <- screen_width - 1 ;
      slider.suff <- 0 ;
      slider.from <- 0 ;
      slider.too <- 0 ;
      slider.count <- count_default
    ) else (
      slider.pref <- max 0 (pref - 1) ;
      slider.from <- if pref > 0 then 0 else min last (from + 1) ;
      slider.suff <- if too < last then 0 else suff + 1 ;
      slider.too <- if suff > 0 then last else min last (too + 1)
    ) ;


  let get_frame
        ({ lines ; fill_char ;
           pref ; suff ; from ; too } as slider) =

    let frame =
      List.map
        ( build_line fill_char pref suff from too )
        lines
    in
    stage_next_frame slider ;
    frame

end


module TableRenderer = struct

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
    mutable log: string list ;
    slider: (int * Slider.t) option ;
  }

  let create_table (col_count, row_count)
		   (col_width, row_height)
		   log_height =
    { col_count = col_count   ;
      row_count = row_count   ;
      col_width = col_width   ;
      row_height = row_height ;
      log_height = log_height ;
      log = []                ;
      slider =
        Some (col_count * row_count,
              Slider.create_slider col_width header_train) }

  let create_default_table () =
    { col_count = 2  ;
      row_count = 3  ;
      col_width = 40 ;
      row_height = 7 ;
      log_height = 7 ;
      log = []       ;
      slider =
        Some (6,
              Slider.create_slider 40 header_train)}

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







  open Cursor

  let print_slider ({ slider } as context) =
    match slider with
    | None -> ()
    | Some (index, slider) ->
       restore () ;

       let to_print = Slider.get_frame slider in
       let cell = index |> index_to_cell context in

       to_print
       |> List.fold_left
            ( fun down line ->
              restore () ;
              north_west_of_cell context cell
              |> go_to_relative ;
              go_down down ;
              printf "%s" line ;
              down + 1
            )
            0
       |> ignore ;
       restore ()

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
    restore () ;

    print_slider table

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

       

end

(* Context type for the renderer. *)
type t = {
  (* Table used by the renderer. *)
  table: TableRenderer.t ;
  (* Associates modules with their cell in the table and their
     title. *)
  map: (Lib.kind_module * (int * string)) list ;
}




(* Returns the index and the title of a module in the renderer table. *)
let rec index_title_of_module map m =
  match map with
  | (m', index_title) :: _ when m == m' -> index_title
  | _ :: tail -> index_title_of_module tail m
  | [] ->
     raise Not_found

(* Turns a formatted string into a string. *)
let format_to_string fmt =
  Format.fprintf (Format.str_formatter) fmt ;
  Format.flush_str_formatter ()


(* Do something if the verbosity level is consistent. *)
let if_level_do level f =
  if output_on_level level then f ()


let update_slider { table } =
  TableRenderer.print_slider table


(* Updates the statistics of the global progress. *)
let update_master_stats { table ; map } trans_sys =

  try

    let index, _ = index_title_of_module map `INVMAN in

    Stat.update_time Stat.total_time ;

    let rec count_status unknowns valids invalids = function
      | (_, TransSys.PropInvariant) :: tail ->
         count_status unknowns (valids + 1) invalids tail
      | (_, TransSys.PropFalse _) :: tail ->
         count_status unknowns valids (invalids + 1) tail
      | _ :: tail ->
         count_status (unknowns + 1) valids invalids tail
      | [] -> (unknowns, valids, invalids)
    in

    let unknowns, valids, invalids =
      TransSys.get_prop_status_all trans_sys
      |> count_status 0 0 0
    in

    let invariants = TransSys.invars_count trans_sys in

    (* Runtime. *)
    TableRenderer.update_line
      table index 1
      (Printf.sprintf "Runtime: %f" (Stat.get_float Stat.total_time)) ;
    (* Unknowns. *)
    TableRenderer.update_line
      table index 2
      (Printf.sprintf "%4i unknown propertie(s)" unknowns) ;
    (* Invalids. *)
    TableRenderer.update_line
      table index 3
      (Printf.sprintf "%4i invalid propertie(s)" invalids) ;
    (* Valids. *)
    TableRenderer.update_line
      table index 4
      (Printf.sprintf "%4i valid   propertie(s)" valids) ;
    (* Invalids. *)
    TableRenderer.update_line
      table index 5
      (Printf.sprintf "%4i invariant(s) discovered" (invariants - valids))

  with
  | Not_found -> failwith "Invariant manager is not in the renderer table."

(* Updates the statistics of the BMC module. *)
let update_bmc_stats table index =

  (* The k at which bmc currently is. *)
  TableRenderer.update_line
    table index 1
    (Printf.sprintf
       "Currently at k = %i" (Stat.get Stat.bmc_k)) ;

  (* How many properties it is analyzing. *)
  TableRenderer.update_line
    table index 2
    (Printf.sprintf
       "%4i unknown" (Stat.get Stat.bmc_unknowns)) ;

  (* How many properties it has disproved. *)
  TableRenderer.update_line
    table index 3
    (Printf.sprintf
       "%4i disproved" (Stat.get Stat.bmc_disproved))

(* Updates the statistics of the IND module. *)
let update_ind_stats table index =

  (* The k at which ind currently is. *)
  TableRenderer.update_line
    table index 1
    (Printf.sprintf
       "Currently at k = %i" (Stat.get Stat.ind_k)) ;

  (* How many properties it is analyzing. *)
  TableRenderer.update_line
    table index 2
    (Printf.sprintf
       "%4i unknown" (Stat.get Stat.ind_unknowns)) ;

  (* How many properties it has proved. *)
  TableRenderer.update_line
    table index 3
    (Printf.sprintf
       "%4i proved" (Stat.get Stat.ind_proved)) ;

  (* How many properties it has found unfalsifiable. *)
  TableRenderer.update_line
    table index 4
    (Printf.sprintf
       "%4i unfalsifiable" (Stat.get Stat.ind_unfalsifiables)) ;

  (* Path compression statistics. *)
  TableRenderer.update_line
    table index 5
    (Printf.sprintf
       "Path compression:") ;
  TableRenderer.update_line
    table index 6
    (Printf.sprintf
       "  %3i eq / %3i succ / %3i pred"
       (Stat.get Stat.ind_compress_equal_mod_input)
       (Stat.get Stat.ind_compress_same_successors)
       (Stat.get Stat.ind_compress_same_predecessors))

(* Updates the statistics of a module. *)
let update_module_stats { table ; map} mdl =
  try
    let index,title = index_title_of_module map mdl in
    match mdl with
    | `BMC -> update_bmc_stats table index
    | `IND -> update_ind_stats table index
    | _ -> ()
  with
  | Not_found -> ()


(* Initializes the renderer. *)
let init modules = 

  (* Creates the map between modules and their index and title. *)
  let rec loop res index = function
    | head :: tail ->
       let res', index' =
         match head with
         (* Handling these separately to make sure they appear first
            if activated. *)
         | `BMC | `IND -> res, index

         | `PDR -> ((head, (index, "PDR")) :: res), index + 1
         | `INVGEN ->
            ((head, (index, "Invariant Generator")) :: res), index + 1
         | _ -> failwith
                  (Printf.sprintf
                     "Renderer does not support module %s."
                     (suffix_of_kind_module head))
       in
       loop
         res'
         index'
         tail
    | [] ->
       (* Adding the master last. *)
       (`INVMAN, (index, "Global Progress")) :: res
  in

  let base i = (`BMC, (i, "Base")) in
  let step i = (`IND, (i, "Step")) in

  (* Building the map from modules to indices / titles. *)
  let map =
    (* Making sure base and step are first and in that order,
       if they are activated. *)
    match List.mem `BMC modules, List.mem `IND modules with
    | true,true ->
       (base 1) :: (step 2) :: (loop [] 3 modules)
    | true,_ ->
       (base 1) :: (loop [] 2 modules)
    | _,true ->
       (step 1) :: (loop [] 2 modules)
    | _ -> loop [] 1 modules
  in

  let module_count = List.length modules + 1 in

  (* Always use two columns. *)
  let columns = 2 in

  (* Row count for the table. *)
  let rows =
    (module_count mod columns) + (module_count / columns)
  in

  (* Creating the table. *)
  let table =
    TableRenderer.create_table
      (columns, rows)
      (* Colums are 40 characters wide, rows are 7 lines high. *)
      (40,7)
      (* Log is 7 lines high. *)
      7
  in

  (* List.iter *)
  (*   (fun (_,(i,t)) -> TableRenderer.log_add_line table (Printf.sprintf "[%i] %s" i t)) *)
  (*   map ; *)

  (* Drawing the table. *)
  Printf.printf "\n\n" ;
  TableRenderer.draw_table table ;
  (* Setting the titles. *)
  List.iter
    ( fun (_, (index, title)) ->
      TableRenderer.set_title table index title )
    map ;

  Pervasives.flush stdout ;

  (* Returning the context of the renderer. *)
  { table ; map }


(* Updates the renderer with a new log message. *)
let printf_rendr ({ table ; map } as context) mdl level fmt =
  let res = Format.fprintf (Format.str_formatter) fmt in
  let string = Format.flush_str_formatter () in
  if string <> "" then (
    if_level_do
      level
      (fun () ->
       TableRenderer.log_add_line
         table
         (Printf.sprintf "%s" string)) ;
    Pervasives.flush stdout) ;
  update_module_stats context mdl ;
  res


(* Updates the renderer with a proved property. *)
let proved_rendr context mdl level trans_sys k prop =
  update_master_stats context trans_sys ;
  update_module_stats context mdl ;

  (* Only ouptut if status was unknown *)
  if not (TransSys.prop_status_known
            (TransSys.get_prop_status trans_sys prop))
  then (
    let line =
      match k with
      | Some k ->
         Printf.sprintf
           "Property proved valid for k=%i: %s." k prop
      | None ->
         Printf.sprintf
           "Property proved valid: %s." prop
    in
    if_level_do
      level
      (fun () -> TableRenderer.log_add_line context.table line)
  )


(* Updates the renderer with a disproved property. *)
let disproved_rendr context mdl level trans_sys prop = function
  | [] -> ()
  | (_,values) :: _ ->
     update_master_stats context trans_sys ;
     update_module_stats context mdl ;

     (* Only ouptut if status was unknown *)
     if not (TransSys.prop_status_known
               (TransSys.get_prop_status trans_sys prop))
     then (
       let k = List.length values in
       let line = Printf.sprintf
                    "Property falsified at %i: %s." k prop
       in
       if_level_do
         level
         (fun () -> TableRenderer.log_add_line context.table line)
     )


(* Updates the statistics of a module. *)
let progress_rendr context mdl level k =
  update_module_stats context mdl

(* Also updates the statistics of a module. *)
let stats_rendr context mdl level =
  update_module_stats context mdl



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

