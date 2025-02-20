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


(* TODO: 

   - Hashccons identifiers and use for StateVar, UfSymbol etc. 

   - Hide implementation and provide smart constructors that fail if
     identifier was previously defined

   - Allow several namespaces to avoid spurious name clashes

*)


(* Pretty-print a scope. Only for internal (non-user-facing) use *)
let pp_print_scope_internal ppf s =
  Format.fprintf 
    ppf
    "@{<blue>%a@}"
    (pp_print_list Ident.pp_print_ident ".")
    s

module Scope = struct 

  (* Scope as a sequence of identifiers *)
  type t = Ident.t list
      
  (* Equality on scopes *)
  let equal s1 s2 =
    (* Scopes are equal if all identifiers are equal *)
    try List.for_all2 Ident.equal s1 s2
    (* Scopes of different lengths are not equal *)
    with Invalid_argument _ -> false
      
  (* Total order on scopes *)
  let compare s1 s2 = compare_lists Ident.compare s1 s2

  let hash s = Hashtbl.hash s

end

include Scope

module Set = Set.Make (Scope)

module Map = Map.Make (Scope)

(* Construct a scope from a list of identifiers 

   Simply return the list for now, later do some smarter things. *)
let mk_scope s = s

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
