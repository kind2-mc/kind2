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

module N = LustreNode

type sys = TransSys.t
(*
type svar = StateVar.t
type actlit = UfSymbol.t
type term = Term.t
type model = Model.t
type values = (Term.t * Term.t) list
type k = Numeral.t
*)

type file = Unix.file_descr


(* Stores IO things to log testcases to xml. *)
type 'a t = {
  (* Input system. *)
  input_sys: 'a InputSystem.t ;
  (* System. *)
  sys: sys ;
  (* Counter for test case uid. *)
  mutable uid: int ;
  (* Counter for error uid. *)
  mutable euid: int ;
  (* Name of the testcase class (["unit"] for now). *)
  name: string ;
  (* Directory to log the testcases in. *)
  dir: string ;
  (* XML class file. *)
  class_file: file ;
  (* Graph file. *)
  graph_file: file ;
  (* Error dir. *)
  edir: string ;
  (* Error file. *)
  mutable error_file: file option ;
}

let openfile path = Unix.openfile path [
  Unix.O_TRUNC ; Unix.O_WRONLY ; Unix.O_CREAT
] 0o640

let fmt_of_file file =
  Unix.out_channel_of_descr file |> Format.formatter_of_out_channel

(* Creates a new IO struct. *)
let mk input_sys sys root name title =
  (* |===| Testcases directory. *)
  let dir = Format.sprintf "%s/%s" root name in
  let edir = Format.sprintf "%s/errors" dir in
  mk_dir dir ;
  let class_file =
    if Flags.Testgen.graph_only () |> not then (

      (* |===| XML class file. *)
      let class_file =
        Format.sprintf "%s.xml" dir |> openfile
      in
      let class_fmt = fmt_of_file class_file in
      Format.fprintf class_fmt
        "<?xml version=\"1.0\"?>@.\
         <data system=\"%a\" name=\"%s\">@.@.@?"
        Scope.pp_print_scope (TransSys.scope_of_trans_sys sys)
        title ;
      class_file
    ) else Unix.stderr
  in

  (* |===| Graph file. *)
  let graph_file =
    Format.sprintf "%s.dot" dir |> openfile
  in
  let graph_fmt = fmt_of_file graph_file in
  Format.fprintf graph_fmt "\
    strict digraph mode_graph {@.@[<v 2>\
      graph [bgcolor=black margin=0.0] ;@ \
      node [@ \
        style=filled@ \
        fillcolor=black@ \
        fontcolor=\"#1e90ff\"@ \
        color=\"#666666\"@ \
      ] ;@ \
      edge [color=\"#1e90ff\" fontcolor=\"#222222\"] ;@ \
    @]@.@." ;

  (* Building result. *)
  { input_sys ; sys ; uid = 0 ; euid = 0 ; name ; dir ;
    class_file ; graph_file ; edir ; error_file = None ; }

(* Initialization for error dir and file. *)
let init_error (type s)
: s t -> unit
= fun ({ sys ; dir ; edir } as t) ->
  ( if t.error_file <> None then
      failwith "init_error called with existing error file" ) ;
  mk_dir edir ;
  let error_file = Format.sprintf "%s-errors.xml" dir |> openfile in
  let error_fmt = fmt_of_file error_file in
  Format.fprintf error_fmt
    "<?xml version=\"1.0\"?>@.\
     <data system=\"%a\">@.@.@?"
    Scope.pp_print_scope (TransSys.scope_of_trans_sys sys) ;

  t.error_file <- Some error_file


(* Closes internal file descriptors. *)
let rm (type s) : s t -> unit
= fun { class_file ; graph_file ; error_file } ->
  if Flags.Testgen.graph_only () |> not then (
    (* |===| Finishing class file. *)
    let class_fmt = fmt_of_file class_file in
    Format.fprintf class_fmt "@.</data>@.@?" ;
  ) ;
  (* |===| Finishing error file. *)
  ( match error_file with
    | None -> ()
    | Some error_file ->
      let error_fmt = fmt_of_file error_file in
      Format.fprintf error_fmt "@.</data>@.@?" ;
      Unix.close error_file ) ;
  (* |===| Finishing graph file. *)
  let graph_fmt = fmt_of_file graph_file in
  Format.fprintf graph_fmt "}@.@?" ;
  Unix.close class_file ; Unix.close graph_file ;
  ()

(* The number of testcases generated. *)
let testcase_count (type s) : s t -> int
= fun { uid } -> uid

(* The number of errors logged. *)
let error_count (type s) : s t -> int
= fun  { euid } -> euid

(* Descriptor for a testcase file. *)
let testcase_csv (type s) : s t -> string * string * Unix.file_descr
= fun {uid ; dir} ->
  let name = Format.sprintf "testcase_%d" uid in
  let path = Format.sprintf "%s/%s.csv" dir name in
  name, path, openfile path

(* Descriptor for an error file. *)
let error_csv (type s) : s t -> string * string * Unix.file_descr
= fun ({euid ; edir} as t) ->
  let name = Format.sprintf "error_%d" euid in
  let path = Format.sprintf "%s/%s.csv" edir name in
  t.euid <- euid + 1 ;
  name, path, openfile path

(* Converts a model to the system's input values in csv. *)
let cex_to_inputs_csv fmt in_sys sys cex k =
  Format.fprintf fmt "%a"
    (InputSystem.pp_print_path_in_csv in_sys sys [] true)
    (Model.path_from_model (TransSys.state_vars sys) cex k)

(* Pretty printer for a testcase in xml. *)
let pp_print_tc fmt path name modes =
  let rec loop cpt = function
    | modes :: tail ->
      Format.fprintf fmt
        "    at step %d, activates @[<v>%a@]@." cpt
        (pp_print_list Scope.pp_print_scope " and ")
        modes ;
      loop (cpt + 1) tail
    | [] -> ()
  in
  Format.fprintf fmt
    "  <testcase path=\"%s\" name=\"%s\" format=\"csv\">@." path name ;
  List.rev modes |> loop 0 ;
  Format.fprintf fmt "  </testcase>@.@.@?"

(* Pretty printer for a deadlock in xml. *)
let pp_print_deadlock fmt path name modes =
  let rec loop cpt = function
    | modes :: tail ->
      Format.fprintf fmt
        "    at step %d, activates @[<v>%a@]@." cpt
        (pp_print_list Scope.pp_print_scope " and ")
        modes ;
      loop (cpt + 1) tail
    | [] -> Format.fprintf fmt "    deadlock reached@."
  in
  Format.fprintf fmt
    "  <deadlock path=\"%s\" name=\"%s\" format=\"csv\">@." path name ;
  List.rev modes |> loop 0 ;
  Format.fprintf fmt "  </deadlock>@.@.@?"

(* Pretty printer for a model path in dot. *)
let pp_print_model_path fmt path =
  let rec loop cpt = function
    | modes :: modes' :: tail ->
      Format.fprintf fmt "  \"%a\\n@%d\" -> \"%a\\n@%d\" ;@.@?"
        (pp_print_list Scope.pp_print_scope "\\n") modes cpt
        (pp_print_list Scope.pp_print_scope "\\n") modes' (cpt + 1) ;
      loop (cpt + 1) (modes' :: tail)
    | _ -> Format.fprintf fmt "@.@?"
  in
  List.rev path |> loop 0

(* Logs a test case. *)
let log_testcase (type s)
: s t -> Scope.t list list -> Model.t -> Numeral.t -> unit
= fun t modes model k ->
  Stat.incr Stat.testgen_testcases ;
  (* Format.printf "  log_testcase@." ; *)
  t.uid <- t.uid + 1 ;

  if Flags.Testgen.graph_only () |> not then (
    (* |===| Logging testcase. *)
    (* Format.printf "    logging testcase@." ; *)
    let name, path, tc_file = testcase_csv t in
    let tc_fmt = fmt_of_file tc_file in
    (* Logging test case. *)
    cex_to_inputs_csv tc_fmt t.input_sys t.sys model k ;
    (* Flushing. *)
    Format.fprintf tc_fmt "@?" ;
    (* Close file. *)
    Unix.close tc_file ;

    (* |===| Updating class file. *)
    (* Format.printf "    updating class file@." ; *)
    let class_fmt = fmt_of_file t.class_file in
    pp_print_tc class_fmt (Format.sprintf "%s/%s.csv" t.name name) name modes ;
  ) ;

  (* |===| Updating graph. *)
  (* Format.printf "    updating graph@." ; *)
  let graph_fmt = fmt_of_file t.graph_file in
  pp_print_model_path graph_fmt modes ;

  ()

(* Logs a test case. *)
let log_deadlock (type s)
: s t -> Scope.t list list -> Model.t -> Numeral.t -> unit
= fun t modes model k ->
  Stat.incr Stat.testgen_deadlocks ;

  let error_file = match t.error_file with
    | None -> init_error t ; get t.error_file
    | Some error_file -> error_file
  in
  (* Format.printf "  log_deadlock@." ; *)

  (* |===| Logging error. *)
  (* Format.printf "    logging deadlock@." ; *)
  let name, path, e_file = error_csv t in
  let e_fmt = fmt_of_file e_file in
  (* Logging test case. *)
  cex_to_inputs_csv e_fmt t.input_sys t.sys model k ;
  (* Flushing. *)
  Format.fprintf e_fmt "@?" ;
  (* Close file. *)
  Unix.close e_file ;

  (* |===| Updating class file. *)
  (* Format.printf "    updating error file@." ; *)
  let error_fmt = fmt_of_file error_file in
  pp_print_deadlock error_fmt path name modes ;

  ()


(* Formatter for the cargo command release-compiling a crate. *)
let fmt_cargo_build fmt =
  Format.fprintf fmt "cargo build --release --manifest-path %s/Cargo.toml"


(* Logs a top level XML test file. *)
let log_test_glue_file
  target sys (oracle_path, guarantees, modes) implem_path test_files
=
  let target = Format.sprintf "%s/tests.xml" target |> openfile in
  let fmt = fmt_of_file target in
  Format.fprintf fmt
    "\
      <?xml version=\"1.0\"?>@.\
      <data system=\"%s\">@.\
      @.  @[<v>\
        <oracle@   @[<v>\
          path=\"%s/target/release/%s_oracle\"@ \
          setup=\"%a\"\
        @]@ >@   @[<v>\
          <!-- Guarantees -->@ \
          %a@ \
          <!-- Mode ensures -->@ \
          %a\
        @]@ </oracle>\
      @]@.@.\
      @.  @[<v>%a%t@]@.\
      @.\
      </data>@.@?\
    "
    sys
    oracle_path
    sys
    fmt_cargo_build oracle_path
    (pp_print_list
      (fun fmt (pos, cnt) ->
        let (file, row, col) = file_row_col_of_pos pos in
        Format.fprintf fmt
          "<output \
            count=\"%d\" \
            file=\"%s\" \
            row=\"%d\" \
            col=\"%d\"\
          ></output>"
          cnt file row col
      )
      "@ "
    ) guarantees
    (pp_print_list
      (fun fmt (mode, pos, cnt) ->
        let (file, row, col) = file_row_col_of_pos pos in
        Format.fprintf fmt
          "<output \
            mode=\"%s\" \
            count=\"%d\" \
            file=\"%s\" \
            row=\"%d\" \
            col=\"%d\"\
          ></output>"
          mode cnt file row col
      )
      "@ "
    ) modes
    (pp_print_list
      (fun fmt str -> Format.fprintf fmt "<tests>%s</tests>" str)
      "@ "
    ) test_files
    (fun fmt ->
      (* Binaries, only generate something if compilation to Rust is live. *)
      if Flags.lus_compile () then
        Format.fprintf
          fmt
          "@ @ @[<v>\
            <binary@   @[<v>\
              name=\"Rust implementation generated by Kind 2\"@ \
              setup=\"%a\"\
            @]@ >@   \
              %s/target/release/%s_implem@ \
            </binary>\
          @]"
          fmt_cargo_build implem_path
          implem_path
          sys
    ) ;

  Unix.close target


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
