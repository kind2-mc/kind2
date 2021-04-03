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

(** 
    Error and warning Reporting functions 

 *)

(* Raise parsing exception *)
let fail_at_position_pt pos msg =
  Log.log L_error "Parser error at %a: @[<v>%s@]"
    Lib.pp_print_position pos msg

let fail_at_position pos msg =
  (match Log.get_log_format () with
   | Log.F_pt -> fail_at_position_pt pos msg
   | Log.F_xml -> Log.parse_log_xml L_error pos msg
   | Log.F_json -> Log.parse_log_json L_error pos msg
   | Log.F_relay -> ()
  );
  raise LustreAst.Parser_error


let warn_at_position_pt level pos msg =
  Log.log level "Parser warning at %a: @[<v>%s@]" Lib.pp_print_position pos msg

let warn_at_position pos msg =
  match Log.get_log_format () with
  | Log.F_pt -> warn_at_position_pt L_warn pos msg
  | Log.F_xml -> Log.parse_log_xml L_warn pos msg
  | Log.F_json -> Log.parse_log_json L_warn pos msg
  | Log.F_relay -> ()


let note_at_position pos msg = 
  match Log.get_log_format () with
  | Log.F_pt -> warn_at_position_pt L_note pos msg
  | Log.F_xml -> Log.parse_log_xml L_note pos msg
  | Log.F_json -> Log.parse_log_json L_note pos msg
  | Log.F_relay -> ()


(* Raise parsing exception *)
let fail_no_position msg =
  Log.log L_error "Parser error: @[<v>%s@]" msg;
  raise LustreAst.Parser_error

 
(* Raise parsing exception *)
let warn_no_position msg = Log.log L_warn "Parser warning: @[<v>%s@]" msg
