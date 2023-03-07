(* This file is part of the Kind 2 model checker.

   Copyright (c) 2021 by the Board of Trustees of the University of Iowa

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

type error_kind = 
  | Unknown of string
  | Impossible of string
  (* Add more as needed*)

type error = [
  | `CmcInterpreterError of Lib.position * error_kind
]

let soh = HString.string_of_hstring

let interpreter_error_message kind = match kind with
  | Unknown s -> s
  | Impossible s -> "This should be impossible! " ^ s
  (* | UnboundIdentifier id -> "Unbound identifier: " ^ soh id
  | UnknownFunction id -> "Unknown Function Call: " ^ soh id
  | UnknownAttribute (attr_id, fun_id) -> "Unknown attribute " ^ soh attr_id ^ "used in function call " ^ soh fun_id 
  | UnnamedAttribute fun_id -> "Attribute value passed without name in function call " ^ soh fun_id 
  | InvalidCommandSyntax info -> info *)
  (* Add more as needed*)

let error_message error = match error with
| `CmcInterpreterError (_, kind) -> interpreter_error_message kind

let error_position error = match error with
  | `CmcInterpreterError (pos, _) -> pos

