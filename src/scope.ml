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


module Scope = struct 

  (* Scope as a sequence of identifiers *)
  type t = Ident.t list
      
  (* Equality on scopes *)
  let equal s1 s2 = 
    
    try 
      
      (* Scopes are equal if all identifiers are equal *)
      List.for_all2 Ident.equal s1 s2
        
    (* Scopes of different lengths are not equal *)
    with Invalid_argument _ -> false 
      
  (* Total order on scopes *)
  let compare s1 s2 = compare_lists compare s1 s2

end

include Scope

module Set = Set.Make (Scope)

module Map = Map.Make (Scope)

(* Pretty-print a scope *)
let pp_print_scope ppf s = 

  Format.fprintf 
    ppf
    "%a"
    (pp_print_list Ident.pp_print_ident ".")
    s


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
