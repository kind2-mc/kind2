(* This file is part of the Kind 2 model checker.

   Copyright (c) 2025 by the Board of Trustees of the University of Iowa

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
(** Testing the helpers in {!Lib} *)

open OUnit2

let assert_escapes_json input expected =
  assert_equal ~printer:(Printf.sprintf "%S") expected
    (Lib.escape_json_string input)

(* The two characters a JSON string gives a meaning to. A property
   expression that pretty-prints over several lines carried its newlines
   raw into the "expr" field, which made the whole document unparseable. *)
let test_json_structural _ =
  assert_escapes_json "nothing to escape" "nothing to escape";
  assert_escapes_json "a\"b" "a\\\"b";
  assert_escapes_json "a\\b" "a\\\\b";
  (* A Windows path: every separator is a backslash, and leaving them alone
     turns "\n" and "\t" in it into a newline and a tab on the way back *)
  assert_escapes_json "C:\\models\\top.lus" "C:\\\\models\\\\top.lus"

(* Control characters, which a JSON string may not carry raw *)
let test_json_control _ =
  assert_escapes_json "a\nb" "a\\nb";
  assert_escapes_json "a\tb" "a\\tb";
  assert_escapes_json "a\rb" "a\\rb";
  assert_escapes_json "a\bb" "a\\bb";
  assert_escapes_json "a\012b" "a\\fb";
  assert_escapes_json "a\000b" "a\\u0000b";
  assert_escapes_json "a\027b" "a\\u001bb"

(* Bytes above the control range are left alone, so UTF-8 passes through *)
let test_json_utf8 _ =
  assert_escapes_json "\xe2\x88\x80x" "\xe2\x88\x80x"

let assert_escapes_xml input expected =
  assert_equal ~printer:(Printf.sprintf "%S") expected
    (Lib.escape_xml_string input)

(* The characters XML gives a meaning to, in character data and in a
   double-quoted attribute value. A monomorphized node name carries its type
   arguments in angle brackets, and a property may be named anything. *)
let test_xml_markup _ =
  assert_escapes_xml "nothing to escape" "nothing to escape";
  assert_escapes_xml "N<int>" "N&lt;int&gt;";
  assert_escapes_xml "a \"quoted\" name" "a &quot;quoted&quot; name";
  assert_escapes_xml "a & b" "a &amp; b"

(* The ampersands escaping introduces are not escaped again in their turn *)
let test_xml_no_double_escaping _ =
  assert_escapes_xml "&lt;" "&amp;lt;";
  assert_escapes_xml "<&>" "&lt;&amp;&gt;"

let _ = run_test_tt_main ("lib" >::: [
  "escape_json_string: structural characters" >:: test_json_structural;
  "escape_json_string: control characters" >:: test_json_control;
  "escape_json_string: non-ASCII bytes" >:: test_json_utf8;
  "escape_xml_string: markup characters" >:: test_xml_markup;
  "escape_xml_string: no double escaping" >:: test_xml_no_double_escaping;
])
