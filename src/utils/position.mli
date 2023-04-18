(** A position in the input *)
type position 

(** Dummy position different from any valid position *)
val dummy_pos : position

(** [equal_pos p1 p2] is true if both positions are equal *)
val equal_pos : position -> position -> bool

(** Comparision on positions *)
val compare_pos : position -> position -> int

(** Return [true] if the position is not a valid position in the
    input *)
val is_dummy_pos : position -> bool

(** Pretty-print a position *)
val pp_print_position : Format.formatter -> position -> unit

(** Pretty-print line and column *)
val pp_print_line_and_column : Format.formatter -> position -> unit

val pp_print_lines_and_columns : Format.formatter -> position list -> unit

(** Return the file, line and column of a position; fail with
    [Invalid_argument "file_row_col_of_pos"] if the position is a dummy
    position *)
val file_row_col_of_pos : position -> string * int * int

(** Return the file of a position *)
val file_of_pos : position -> string

(** Return the line and column of a position; fail with
    [Invalid_argument "file_row_col_of_pos"] if the position is a dummy
    position *)
val row_col_of_pos : position -> int * int

(** Inverse of {!file_row_col_of_pos} *)
val pos_of_file_row_col : string * int * int -> position

(** Convert a position of the lexer to a position *)
val position_of_lexing : Lexing.position -> position

val parse_log_xml : Lib.log_level -> position -> string -> unit

val parse_log_json : Lib.log_level -> position -> string -> unit