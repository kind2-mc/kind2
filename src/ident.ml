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


module Ident = struct

  (* Identifier *)
  type t = string
    
  (* Equality on identifiers *)
  let equal = (=)
              
  (* Total order on identifiers *)
  let compare = Pervasives.compare 

end

include Ident

module IdentSet = Set.Make (Ident)

module IdentMap = Map.Make (Ident)




(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
