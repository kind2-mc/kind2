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

(** Extract the transition system from the dumpfiles of jKind

    @author Alain Mebsout
*)

val jkind_scope : Scope.t

(** Returns all jKind variables corresponding to a Kind2 variable, given a map
    for lustre streams and callsites information. *)
val jkind_vars_of_kind2_statevar :
  TransSys.t ->
  (StateVar.t * (LustreIdent.t * int * LustreNode.call_cond list) list) list
    StateVar.StateVarMap.t
  -> StateVar.t -> StateVar.t list

(** Return a transition system extracted from a call to jKind. *)
val get_jkind_transsys : string -> TransSys.t
