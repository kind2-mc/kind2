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

(** Conversion of a Lustre node to a transition system
    
    @author Christoph Sticksel *)

val trans_sys_of_nodes : LustreNode.t list -> (UfSymbol.t * (Var.t list * Term.t)) list * StateVar.t list * Term.t * Term.t

val props_of_nodes : LustreIdent.t -> LustreNode.t list -> (string * Term.t) list

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
