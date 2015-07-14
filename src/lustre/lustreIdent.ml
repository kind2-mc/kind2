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
  type t = Ident.t * int list 

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


(* ********************************************************************** *)
(* Constructors                                                           *)
(* ********************************************************************** *)


(* Construct an identifier of a string *)
let mk_string_ident string = (string, [])

(* Construct an identifier of a scope *)
let of_scope = function 

  (* Only allow flat scopes for now *)
  | [i] -> Ident.to_string i |> mk_string_ident

  (* Fail on empty scope, or nested scope  *)
  | _ -> raise (Invalid_argument "to_scope")


(* Construct an identifier of a scope *)
let to_scope (base, index) = 
  Scope.mk_scope
    (Ident.of_string base :: 
     (List.map 
        (fun i -> string_of_int i |> Ident.of_string)
        index))


(* Append an index to the identifier *)
let push_index (base, index) int = (base, int :: index)


(* ********************************************************************** *)
(* Reserved identifiers                                                   *)
(* ********************************************************************** *)


(* Reserved identifiers *)
let abs_ident_string =  "abs" 
let oracle_ident_string =  "nondet" 
let instance_ident_string =  "instance"
let init_flag_ident_string =  "init_flag"
let all_req_ident_string =  "all_req"
let all_ens_ident_string =  "all_ens"
let inst_ident_string =  "inst" 
let init_uf_string = "__node_init"
let trans_uf_string = "__node_trans"
let index_ident_string =  "__index" 

let reserved_strings =
  [ abs_ident_string;
    oracle_ident_string;
    instance_ident_string;
    init_flag_ident_string;
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

(* Identifier for first instant flag *)
let init_flag_ident = mk_string_ident init_flag_ident_string

(* Identifier for observer of contract requirements *)
let all_req_ident = mk_string_ident all_req_ident_string

(* Identifier for observer of contract ensures *)
let all_ens_ident = mk_string_ident all_ens_ident_string

(* Identifier for new variables from node instances *)
let inst_ident = mk_string_ident inst_ident_string

(* Identifier for new clock initialization flag *)
let index_ident = mk_string_ident index_ident_string

(* Scope for reserved identifiers *)
let reserved_scope = Scope.mk_scope [ Ident.of_string "res" ]

(* Scope for identifiers in user input *)
let user_scope = Scope.mk_scope [ Ident.of_string "usr" ]


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
