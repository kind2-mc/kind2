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


(** Context information used in and obtained from parsing

    @author Christoph Sticksel *)

open Lib

(** Context *)
type t


(** Node or function not found, possible forward reference *)
exception Node_not_found of LustreIdent.t * position

exception Type_not_found of LustreIdent.t * position

exception Contract_not_found of LustreIdent.t * position

(** {1 Scopes and Nodes} *)

(** Create an initial empty context. *)
val mk_empty_context : unit -> t

(** Sets the flag indicating there are unguarded pre's in the lustre code, and
we need to guard them. *)
val set_guard_flag : t -> bool -> t

(** Resets the flag indicating there are unguarded pre's in the lustre code,
and we need to guard them. *)
val reset_guard_flag : t -> t

(** The value of the flag indicating there are unguarded pre's in the lustre
code, and we need to guard them. *)
val guard_flag : t -> bool

(** Add scope to context

    The scopes are added to the name of the node to create scope for
    variables *)
val push_scope : t -> string -> t

(** Remove topmost scope from context *)
val pop_scope : t -> t

(** Add contract scope to context.

    Contract scopes are used for scoping of mode references and ghost
    variables. *)
val push_contract_scope : t -> string -> t

(** Remove topmost contract scope from context *)
val pop_contract_scope : t -> t

(** The contract scope of a context. *)
val contract_scope_of : t -> string list

(** Return a copy of the context with an empty node of the given name
    in the context *)
val create_node : t -> LustreIdent.t -> t 

(** Returns the name of the current node, if any. *)
val current_node_name : t -> LustreIdent.t option

(** Returns the calls made by the current node, if any. *)
val current_node_calls : t -> LustreNode.node_call list

(** Returns the modes of the current node. *)
val current_node_modes : t -> LustreContract.mode list option option

(** Return a copy of the context with an empty function of the given name
    in the context *)
val create_function : t -> LustreIdent.t -> t 

(** Return a context that is identical to the first context with the
    node constructed in the second context added *)
val add_node_to_context : t -> t -> t


(** Resolve a forward reference, fails if a circular dependency is detected. *)
val solve_fref : t -> LustreAst.declaration -> (
  LustreDependencies.decl * LustreIdent.t
) -> LustreAst.declaration list -> LustreAst.declaration list

(** Add a binding of an identifier to an expression to context 

    If the labeled argument [shadow] is true, allow overwriting a
    previous binding to the identifier. Otherwise raise the exception
    [Invalid_argument "add_expr_for_ident"]. *)
val add_expr_for_ident :
  ?shadow:bool -> t -> LustreIdent.t -> LustreExpr.t LustreIndex.t -> t

(** Remove the binding of an identifier from the context 

    If the identifier is not bound to an expression, raise the
    exception [Invalid_argument "remove_expr_for_ident"]. Otherwise,
    remove the most recent binding to the identifier, which may make a
    previous binding visible, which was shadowed by a call to
    [add_expr_for_ident] with the labeled argument [shadow] set to
    true. *)
val remove_expr_for_ident : t -> LustreIdent.t -> t

(** Add a binding of an identifier to a type to context *)
val add_type_for_ident : t -> LustreIdent.t -> Type.t LustreIndex.t -> t

(** Return the nodes in the context *)
val get_nodes : t -> LustreNode.t list

(** Return the current node in context. *)
val get_node : t -> LustreNode.t option

(** The contract nodes in the context. *)
val contract_nodes : t -> LustreAst.contract_node_decl list

(** The svars in the COI of the input expression, in the current node.

Returns [None] if there's no current node.
Raises [Not_found] if some svars in the COI do not have an equation and are
not outputs of node calls.

Used to check that the assumes and requires of a contract do not mention
the outputs in [LustreDeclarations]. *)
val trace_svars_of : t -> LustreExpr.t -> StateVar.StateVarSet.t option

(** Add a contract node to the context for inlining later *)
val add_contract_node_decl_to_context :
  t -> Lib.position * LustreAst.contract_node_decl -> t

(** Return a contract node by its identifier *)
val contract_node_decl_of_ident :
  t -> string -> Lib.position * LustreAst.contract_node_decl

(** Return a context that raises an error when defining an
    expression.

    [fail_on_new_definition ctx pos msg] will evaluate
    {!fail_at_position} with the location [pos] and the message [msg]
    as arguments *)
val fail_on_new_definition : t -> Lib.position -> string -> t

(** Raise exception if no new definitions allowed 

    Raise {!A.ParseError} with the message and position set by
    {!fail_on_new_definition}. Raise an assertion failure if the
    context does allow new definitions.
*)

val raise_no_new_definition_exc : t -> 'a

(** Resolve an indentifier to an expression. *)
val expr_of_ident : t -> LustreIdent.t -> LustreExpr.t LustreIndex.t

(** Return the respective state variable if the expression denotes an
    output or a local variable of the node in the context *)
val assignable_state_var_of_ident :
  t -> LustreIdent.t -> StateVar.t LustreIndex.t

(** Resolve an indentifier to a type. *)
val type_of_ident : t -> LustreIdent.t -> Type.t LustreIndex.t

(** Return [true] if the identifier denotes an expression in the context 

    Raise an [Invalid_argument] exception if the identifier is reserved. *)
val expr_in_context : t -> LustreIdent.t -> bool

(** Return [true] if the identifier denotes a type in the context *)
val type_in_context : t -> LustreIdent.t -> bool

(** Return [true] if the identifier denotes a node in the context *)
val node_in_context : t -> LustreIdent.t -> bool

(** Create a fresh local state variable in the context. *)
val mk_fresh_local : ?is_input:bool -> ?is_const:bool -> ?for_inv_gen:bool -> t -> Type.t -> StateVar.t * t

val set_state_var_source : t -> StateVar.t -> LustreNode.state_var_source -> t

(** Define the expression with a fresh state variable, or the variable
    previously used for the same expression (if the optinal argument [reuse] is
    set to true), record the definition in the context and return the context.

    The [is_input], [is_const] and [for_inv_gen] flags are relevant, and the
    state variable returned has the combination of flags asked for. If a state
    variable was previously created for the same expression but with different
    flags, a new state variable is created. *)
val mk_local_for_expr :
  ?is_input:bool -> ?is_const:bool -> ?for_inv_gen:bool -> ?is_ghost:bool ->
  ?original:LustreAst.expr -> Lib.position ->
  t -> LustreExpr.t -> StateVar.t * t

(** Create a fresh oracle state variable in the context. *)
val mk_fresh_oracle :
  ?is_input:bool -> ?is_const:bool -> ?for_inv_gen:bool ->
  t -> Type.t -> StateVar.t * t

(** Create a fresh oracle state variable for the pre-initial value of
    the given state variable in the context, or return a previously
    created oracle for this state variable. *)
val mk_fresh_oracle_for_state_var : t -> StateVar.t -> StateVar.t * t

(** Return the node of the given name from the context*)
val node_of_name : t -> LustreIdent.t -> LustreNode.t

(** Return variables capturing outputs of node call if a node call
    with the same input parameters and activation condition is in the
    context.

    [call_outputs_of_node_call c n ar i d] compares all node calls in context
    [c] if the identifier of the node matches [n], the activation or restart
    condition matches [ar] all input variables are idential to [a], and all
    default values are identical to [d]. It returns [None] if no such call was
    found, and its output variables otherwise. *)
val call_outputs_of_node_call :
  t -> LustreIdent.t -> LustreNode.call_cond list ->
  StateVar.t LustreIndex.t -> LustreExpr.t LustreIndex.t option ->
  StateVar.t LustreIndex.t option

(** Add node input to context *)
val add_node_input :
  ?is_const:bool -> t -> LustreIdent.t -> Type.t LustreIndex.t -> t

(** Add node output to context *)
val add_node_output :
  ?is_single:bool -> t -> LustreIdent.t -> Type.t LustreIndex.t -> t

(** The output state variables of the current node. *)
val outputs_of_current_node : t -> StateVar.t LustreIndex.t

(** Add node local to context *)
val add_node_local :
  ?ghost:bool -> t -> LustreIdent.t -> Lib.position -> Type.t LustreIndex.t -> t

(** Adds assumptions to a node. *)
val add_node_ass : t -> LustreContract.svar list -> t

(** Adds guarantees to a node. *)
val add_node_gua : t -> LustreContract.svar list -> t

(** Add modes to node *)
val add_node_mode : t -> LustreContract.mode -> t

(** Add assertion to context *)
val add_node_assert : t -> LustreExpr.t -> t

(** Add property to context *)
val add_node_property : t -> Property.prop_source -> string -> LustreExpr.t -> t

(** Add equation to context *)
val add_node_equation :
  t -> Lib.position -> StateVar.t ->
  LustreExpr.expr LustreNode.bound_or_fixed list -> int -> LustreExpr.t -> t

(** Add node call to context *)
val add_node_call : t -> Lib.position -> LustreNode.node_call -> t

(** Mark node as main *)
val set_node_main : t -> t

(** Mark node as function *)
val set_node_function : t -> t

(** Checks if the current node, if any, is a function. *)
val get_node_function_flag : t -> bool

(** Replace unguarded pre operators with oracle constants and return
    expression and modified context. 

    [close_expr pos (expr, ctx)] introduces or uses a previously
    introduced fresh oracle constant for each [pre] operator applied
    to a variable that is not under a [->]. 

    The second argument is a pair so that it can take the output of
    {!LustreSimplify.eval_ast_expr} directly. *)
val close_expr :
  ?original:LustreAst.expr -> Lib.position ->
  (LustreExpr.t * t) -> (LustreExpr.t * t)

(** Check that the node being defined has no undefined local variables *)
val check_local_vars_defined : t -> unit


(** {1 Helpers} *)

(** Output a fatal error at position and raise an error *)
val fail_at_position : Lib.position -> string -> 'a

(** Output a warning at position *)
val warn_at_position : Lib.position -> string -> unit 

(** Output a fatal error without reporting a position and raise an error *)
val fail_no_position : string -> 'a

(** Output a warning without a position *)
val warn_no_position : string -> unit 


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
