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

(** Simplify a Lustre AST to normalized Lustre nodes 

    

    @author Christoph Sticksel
*)


(** Output a fatal error at position and raise an error *)
val fail_at_position : LustreAst.position -> string -> 'a

(** Output a warning at position *)
val warn_at_position : LustreAst.position -> string -> unit 

(** Return a list of nodes from a parsed input file *)
val declarations_to_nodes : LustreAst.declaration list -> LustreNode.t list


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
