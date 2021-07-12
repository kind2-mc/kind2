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

(** Conversion of a counterexample to a Lustre model 

    @author Kevin Clancy, Christoph Sticksel *)

(** Output a counterexample as a Lustre execution in XML format *)
val pp_print_path_xml :
  TransSys.t -> TransSys.instance list ->
  LustreGlobals.t -> LustreNode.t SubSystem.t -> bool ->
  Format.formatter -> Model.path -> unit

(** Output a counterexample as a Lustre execution as plain text with
    pre-processing reverted *)
val pp_print_path_pt :
  TransSys.t -> TransSys.instance list ->
  LustreGlobals.t -> LustreNode.t SubSystem.t -> bool ->
  Format.formatter -> Model.path -> unit

(** Output a counterexample as a Lustre execution in JSON format *)
val pp_print_path_json :
  TransSys.t -> TransSys.instance list ->
  LustreGlobals.t -> LustreNode.t SubSystem.t -> bool ->
  Format.formatter -> Model.path -> unit

(** Outputs a model as a sequence of inputs in CSV. *)
val pp_print_path_in_csv :
  TransSys.t -> TransSys.instance list ->
  LustreGlobals.t -> LustreNode.t SubSystem.t -> bool ->
  Format.formatter -> Model.path -> unit

(** Recursively substitute the state variables in a term with their definition
    in [equations]. *)
val substitute_definitions_in_expr :
  LustreNode.equation list -> LustreExpr.t -> LustreExpr.t


(** Reconstruct Lustre streams from state variables *)
val reconstruct_lustre_streams :
  LustreNode.t SubSystem.t list -> 
  (* LustreNode.t list -> *)
  StateVar.t list ->
  (StateVar.t * (LustreIdent.t * int * LustreNode.call_cond list) list) list
    StateVar.StateVarMap.t

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
