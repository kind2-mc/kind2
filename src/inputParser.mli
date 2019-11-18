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

(** Represents the lhs of an assignment. For non-array state vars, the index list is empty. 
    For array state vars, the index list indicates which cell of the array must be assigned. *)
type assignment_lhs = StateVar.t * int list

(** Parse a JSON or CSV input file. The format is determined from the extension. *)
val read_file: string list -> string -> (assignment_lhs * (Term.t list)) list

(** Parser for a CSV input file 

    @author Baoluo Meng, Christoph Sticksel *)

(** Parse a CSV input file *)
val read_csv_file: string list -> string -> (StateVar.t * (Term.t list)) list

(** Parse a JSON input file *)
val read_json_file: string list -> string -> (assignment_lhs * (Term.t list)) list

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
