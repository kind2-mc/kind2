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

(* ********************************************************************** *)
(* Types and pretty-printers                                              *)
(* ********************************************************************** *)


module LustreIdent = struct 

  (* An identifier is a string with integer indexes *)
  type t = string * int list 

  (* Use polymorphic hash function *)
  let hash = Hashtbl.hash
             
  (* Use polymorphic equality *)
  let equal = (=)

  (* Use polymorphic copmarison *)
  let compare = Pervasives.compare            

end

include LustreIdent 

(* Hash table over identifiers *)
module Hashtbl = Hashtbl.Make (LustreIdent)

(* Set over identifiers *)
module Set = Set.Make (LustreIdent)

(* Map over identifiers *)
module Map = Map.Make (LustreIdent)


(* Pretty-print a list of indexes *)
let rec pp_print_index safe ppf = function 

  | [] -> ()

  | h :: tl -> 

    (* Pretty-print valid Lustre identifiers? *)
    if safe then 

      (* Use underscore *)
      Format.fprintf ppf "_%d" h

    else
      
      (* Use square brackets around index *)
      Format.fprintf ppf "[%d]" h; 

    (* Pretty-print rest of indexes *)
    pp_print_index safe ppf tl


(* Pretty-print an identifier *)
let pp_print_ident safe ppf (s, i) = 

  Format.fprintf ppf "%s%a" s (pp_print_index safe) i


(* Return a string representation of an identifier *)
let string_of_ident safe = string_of_t (pp_print_ident safe)


let ident_of_state_var sv = (StateVar.string_of_state_var sv, [])

(* ********************************************************************** *)
(* Constructors                                                           *)
(* ********************************************************************** *)


(* Construct an identifier of a string *)
let mk_string_ident string = (string, [])


(* Append an index to the identifier *)
let push_index (base, index) int = (base, int :: index)


(* ********************************************************************** *)
(* Reserved identifiers                                                   *)
(* ********************************************************************** *)


(* Reserved identifiers *)
let abs_ident_string =  "__abs" 
let oracle_ident_string =  "__nondet" 
let instance_ident_string =  "__instance"
let running_ident_string =  "__running"
let first_tick_ident_string =  "__first_tick"
let all_req_ident_string =  "__all_req"
let all_ens_ident_string =  "__all_ens"
let inst_ident_string =  "__inst" 
let init_uf_string = "__node_init"
let trans_uf_string = "__node_trans"
let index_ident_string =  "__index" 

let reserved_strings =
  [ abs_ident_string;
    oracle_ident_string;
    instance_ident_string;
    running_ident_string;
    first_tick_ident_string;
    all_req_ident_string;
    all_ens_ident_string;
    inst_ident_string;
    init_uf_string;
    trans_uf_string;
    index_ident_string ]
  @ StateVar.reserved_strings

(* Identifier for new variables from abstrations *)
let abs_ident = mk_string_ident abs_ident_string

(* Identifier for new oracle input *)
let oracle_ident = mk_string_ident oracle_ident_string

(* Identifier for unique identifier for node instance *)
let instance_ident = mk_string_ident instance_ident_string

(* Identifier for running flag *)
let running_ident = mk_string_ident running_ident_string

(* Identifier for first instant flag *)
let first_tick_ident = mk_string_ident first_tick_ident_string

(* Identifier for observer of contract requirements *)
let all_req_ident = mk_string_ident all_req_ident_string

(* Identifier for observer of contract ensures *)
let all_ens_ident = mk_string_ident all_ens_ident_string

(* Identifier for new variables from node instances *)
let inst_ident = mk_string_ident inst_ident_string

(* Identifier for new clock initialization flag *)
let index_ident = mk_string_ident index_ident_string

(* Return true if the identifier clashes with internal identifier names *)
let ident_is_reserved ident = 

  (* Get string part of identifier *)
  let ident_string, _ = ident in

  reserved_strings
  |> List.exists
       (string_starts_with ident_string)

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
