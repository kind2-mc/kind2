(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020 by the Board of Trustees of the University of Iowa

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
(** Functions for type checking surface syntax [LustreAst]
    
    @author Apoorv Ingle *)

module LA = LustreAst
open TypeCheckerContext
         
type 'a tc_result = ('a, Lib.position * string) result
(** The typechecking can either be [Ok] will be an [Error] with some helpful message *)

val type_error: Lib.position -> string -> 'a tc_result 
(** [type_error] returns an [Error] of [tc_result] *)
     
val type_check_infer_globals: tc_context -> LA.t -> tc_context tc_result  
(** Typechecks the toplevel globals i.e. constant decls and type decls. It returns 
    a [Ok (tc_context)] if it succeeds or and [Error of String] if the typechecker fails *)

val type_check_infer_nodes_and_contracts: tc_context -> LA.t -> tc_context tc_result
(** Typechecks and infers type for the nodes and contracts. It returns
    a [Ok (tc_context)] if it succeeds or and [Error of String] if the typechecker fails *)
  
val report_tc_result: unit tc_result list -> unit tc_result
(** Report whether everything is [Ok] or if there are any [Error]s *)

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
                                
