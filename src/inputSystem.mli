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

exception UnsupportedFileFormat of string

(** [read_input_lustre only_parse filename] read input from [filename]
    and returns [None] if [only_parse] is true, or an input system
    otherwise.

    See {!LustreInput.of_file} for potential exceptions thrown by this function.
*)
val read_input_lustre : bool -> string -> LustreNode.t t option

(** Translate lustre contracts to properties. *)
val translate_contracts_lustre : string -> string -> unit

(** Read native input from file *)
val read_input_native : string -> TransSys.t t

(** Returns the scopes of all the systems in an input systems, in topological
    order. *)
val ordered_scopes_of : 'a t -> Scope.t list

val analyzable_subsystems : 'a t -> 'a SubSystem.t list

(** Returns the analysis param for [top] that abstracts all its abstractable
    subsystems if [top] has a contract. *)
val maximal_abstraction_for_testgen :
  'a t -> Scope.t -> Analysis.assumptions -> Analysis.param option

(** Return the next system to analyze and the systems to abstract *)
val next_analysis_of_strategy :
  'a t -> Analysis.results -> Analysis.param option

val interpreter_param : 'a t -> Analysis.param

val mcs_params : 'a t -> Analysis.param list

(** Return analysis parameters for all systems without an implementation

    If the system has a contract, the boolean argument is true
*)
val contract_check_params : 'a t -> (Analysis.param * bool) list

(** Return a transition system for an analysis run *)
val trans_sys_of_analysis:
  ?preserve_sig:bool ->
  ?slice_nodes:bool ->
  ?add_functional_constraints: bool ->
  'a t -> Analysis.param -> TransSys.t * 'a t

(** Output a path in the input system *)
val pp_print_path_pt : _ t -> TransSys.t -> bool -> Format.formatter -> Model.path -> unit

(** Output a path in the input system *)
val pp_print_path_xml : _ t -> TransSys.t -> bool -> Format.formatter -> Model.path -> unit

(** Output a path in the input system *)
val pp_print_path_json : _ t -> TransSys.t -> bool -> Format.formatter -> Model.path -> unit

(** Output a model as a sequnce of inputs in CSV. *)
val pp_print_path_in_csv : _ t -> TransSys.t -> bool -> Format.formatter -> Model.path -> unit

(** Output all subsystems of the input system **)
val pp_print_subsystems_debug: Format.formatter -> 'a t -> unit

val pp_print_state_var_instances_debug: Format.formatter -> 'a t -> unit

val pp_print_state_var_defs_debug: Format.formatter -> 'a t -> unit

val lustre_definitions_of_state_var : 'a t -> StateVar.t -> LustreNode.state_var_def list

val lustre_source_ast : 'a t -> LustreAst.t

val pp_print_term_as_expr : _ t -> TransSys.t -> Format.formatter -> Term.t -> unit

val slice_to_abstraction : 'a t -> Analysis.param -> TransSys.t -> 'a t

val slice_to_abstraction_and_property : 'a t -> Analysis.param -> TransSys.t -> (StateVar.t * Model.value list) list -> Property.t -> TransSys.t * TransSys.instance list * (StateVar.t * Model.value list) list * Term.t * 'a t

val retrieve_lustre_nodes : _ t -> LustreNode.t list

val retrieve_lustre_nodes_of_scope : _ t -> Scope.t -> LustreNode.t list

val contain_partially_defined_system : _ t -> Scope.t -> bool

(** Return the lustre node associated to the given scope, or
   [None] if there is no lustre node associated to that scope *)
val get_lustre_node : _ t -> Scope.t -> LustreNode.t option

val reconstruct_lustre_streams :
  _ t -> 
  StateVar.t list ->
  (StateVar.t * (LustreIdent.t * int * LustreNode.call_cond list) list) list
    StateVar.StateVarMap.t

(** Returns a map from state variables to lustre-like names *)
val mk_state_var_to_lustre_name_map :
  _ t -> StateVar.t list -> string StateVar.StateVarMap.t


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
val contract_gen_param : _ t -> Scope.t -> (Analysis.param * (Scope.t -> LustreNode.t))

(** Return the set of dependencies of each state variable for all systems *)
val state_var_dependencies :
  _ t ->
  (StateVar.StateVarSet.t StateVar.StateVarMap.t) Scope.Map.t

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
