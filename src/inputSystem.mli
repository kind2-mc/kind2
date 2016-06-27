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

(** Delegate to concrete functions for input formats.

    All functionality outside this module should be agnostic of the
    input format, with the exception of modules specialized to a
    particular input. Only here we distinguish the actual input
    format and delegate to the respective functions.

    @author Christoph Sticksel *)

type _ t

(** Read input from file *)
val read_input_lustre : string -> LustreNode.t t

(** Translate lustre contracts to properties. *)
val translate_contracts_lustre : string -> string -> unit

(** Read native input from file *)
val read_input_native : string -> TransSys.t t

(** Returns the scopes of all the systems in an input systems, in topological
    order. *)
val ordered_scopes_of : 'a t -> Scope.t list

(** Returns the analysis param for [top] that abstracts all its abstractable
    subsystems if [top] has a contract. *)
val maximal_abstraction_for_testgen :
  'a t -> Scope.t -> (Scope.t * Term.t) list -> Analysis.param option

(** Return the next system to analyze and the systems to abstract *)
val next_analysis_of_strategy :
  'a t -> Analysis.results -> Analysis.param option

(** Return a transition system for an analysis run *)
val trans_sys_of_analysis:
  ?preserve_sig:bool -> 'a t -> Analysis.param -> TransSys.t * 'a t

(** Output a path in the input system *)
val pp_print_path_pt : _ t -> TransSys.t -> TransSys.instance list -> bool -> Format.formatter -> Model.path -> unit

(** Output a path in the input system *)
val pp_print_path_xml : _ t -> TransSys.t -> TransSys.instance list -> bool -> Format.formatter -> Model.path -> unit

(** Output a model as a sequnce of inputs in CSV. *)
val pp_print_path_in_csv : _ t -> TransSys.t -> TransSys.instance list -> bool -> Format.formatter -> Model.path -> unit

val slice_to_abstraction_and_property : 'a t -> Analysis.param -> TransSys.t -> (StateVar.t * Model.term_or_lambda list) list -> Property.t -> TransSys.t * TransSys.instance list * (StateVar.t * Model.term_or_lambda list) list * Term.t * 'a t


val reconstruct_lustre_streams :
  _ t -> 
  StateVar.t list ->
  (StateVar.t * (LustreIdent.t * int * StateVar.t option) list) list
    StateVar.StateVarMap.t


val is_lustre_input : _ t -> bool

(** Compiles a system (scope) to Rust to the folder specified as a crate. *)
val compile_to_rust : _ t -> Scope.t -> string -> unit

(** Compiles a system (scope) to Rust as an oracle to the folder specified as
a crate. *)
val compile_oracle_to_rust : _ t -> Scope.t -> string -> (
  string *
  (Lib.position * int) list *
  (string * Lib.position * int) list
)

(** Parameter for contract generation. *)
val contract_gen_param : _ t -> (Analysis.param * (Scope.t -> LustreNode.t))

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
