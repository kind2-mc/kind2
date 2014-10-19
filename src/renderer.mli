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

(** The type of a table. *)
type t

(** Creates a table, the first parameter is the number of columns and
    the number of rows, the second is the columns width and the rows
    height, and the last one is the log height. Cells are ordered left
    to right and top to bottom. So cell with coordinates (2,1) is the
    cell in the second row and the first column. The index of a cell
    corresponds to an array vision of the table following the same
    ordering. So, in a table with 3 columns and 4 rows, the cell of
    index 4 is cell (2,1). *)
val create_table:
  int * int -> int * int -> int -> t

(** Draws a table. *)
val draw_table: t -> unit

(** Creates a table with two columns and three rows with a col width
    of 40 and and a row height of 7. Log height is 7. *)
val create_default_table: unit -> t

(** The number of columns in a table. *)
val get_col_count: t -> int
(** The number of rows in a table. *)
val get_row_count: t -> int

(** The width of columns in a table. *)
val get_col_width: t -> int
(** The height of rows in a table. *)
val get_row_height: t -> int

(** The height of the log in a table. *)
val get_log_height: t -> int

(** The log of a table. *)
val get_log: t -> string list

(** Sets the title of a cell based on its coordinates.  Raises an
    error if the cell coordinates are illegal. *)
val set_title_pair:
      t -> int * int -> string -> unit

(** Sets the title of a cell based on its index.  Raises an
    error if the cell index is illegal. *)
val set_title:
      t -> int -> string -> unit

(** Updates line 'line_index' of a cell based on its coordinates.
    Raises an error if the cell coordinates are illegal. *)
val update_line_pair:
      t -> int * int -> int -> string -> unit

(** Updates line 'line_index' of a cell based on its index.
    Raises an error if the cell index is illegal. *)
val update_line:
      t -> int -> int -> string -> unit

(** Adds a line to the log. *)
val log_add_line:
      t -> string -> unit


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

