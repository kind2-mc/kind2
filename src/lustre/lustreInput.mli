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

(** Parse Lustre input into the intermediate Lustre format 

    An OCamllex lexer in {!LustreLexer} and a Menhir parser in
    {!LustreParser} take the input and produce a sinlge {!LustreAst.t}
    value, which is a minimally processed representation of a Lustre
    AST.

    This AST is then translated into a simplified Lustre, see
    {!LustreNode}, and {!LustreDeclarations} for the translation.

    The main function {!of_file} of this module returns a system for
    the analysis strategies that can be turned into an internal
    transition system {!TransSys} by using functions in
    {!LustreTransSys} with relevant parameters.

    The whole input file is parsed and type checked first, then one
    node is designated as the main node. The returned {!Subsystem.t}
    has this main node at the top, and all called nodes as
    children. Nodes that are in the input file, but not called by the
    main node are discarded. No further cone of influence reduction is
    peformed yet, this happens only in {!LustreTransSys} when the
    parameters of the analysis are known.

    The main node is chosen to be, in order of precedence:

    - the node with the name given by the [--lustre_main] command-line
      option,
    - the node with the annotation [--%MAIN], or
    - the last node in the input.

    An exception [Invalid_argument] is raised if the node given by
    [--lustre_main] is not found, there are two nodes with a [--%MAIN]
    annotation, or the input contains no nodes.

    In particular, the output of the entry point {!LustreParser.main}
    returns a Lustre file as a list of declarations of

    - types [type t = t'],
    - global constants [const c = v], and
    - nodes [node X (...) returns (...); let ... tel].

    A node is viewed as a tuple of an identifier, a list of inputs, a
    list of outputs, declarations of local constants and variables,
    and equations. An equation is either an assignment of an
    expression to a variable, an assertion, a property annotation, or
    flag to mark the node as the top node.

    The function {!LustreSimplify.declarations_to_nodes} is called
    with this list of declarations as input and produces a list of
    {!LustreNode.t} that contains each node with expressions in a
    normalized form, with structured fields unfolded, constants
    propagated and type aliases substituted.

    In detail, the process of normalizing an expression in a node
    abstracts every non-variable expression under a [pre] operator
    into a fresh local variable. All [->] operators are lifted to the
    top of the expression so that an expression can be represented as
    a pair of expressions, one for the first instant and one for the
    following. Each variable at the previous state i the left argument
    to the [->] operator in the resulting expression is replaced with
    a fresh oracle constant per variable that is added to the inputs
    of the node.

    Node calls are factored out into assignments to fresh local
    variables, where input expressions are further abstracted to fresh
    local variables. A node call may be wrapped in a condact with an
    activation condition and default values.

    In detail, {!LustreNode.t} is a record representing a node with 

    - [name] an identifier 
    - [inputs] the list of input variables 

    After finding the designated main node with
    {!LustreNode.find_main}, the definitions in the main node and list
    of nodes is reduced to the nodes in the cone of influence of the
    properties of the main node, see
    {!LustreNode.reduce_to_property_coi}. Last, the equational
    definitions of each node are ordered by their dependencies with
    {!LustreNode.reduce_to_property_coi}.

    The module {!LustreTransSys} turns the list of nodes into a
    transition system {!TransSys.t} by means of the functions
    {!LustreTransSys.trans_sys_of_nodes} and
    {!LustreTransSys.props_of_nodes}.

    @author Christoph Sticksel
*)

exception NoMainNode of string

(** [of_file only_parse f] parse Lustre model from file [f], and
    return [None] if [only_parse] is true, or an input system
    otherwise.

    If a syntax or semantic error is detected, it triggers
    a [Parser_error] exception. If [only_parse] is false, and
    the Lustre model doesn't include a main node, it triggers a
    {!NoMainNode} exception.
*)
val of_file :
  bool -> string ->
  (LustreNode.t SubSystem.t list * LustreGlobals.t * LustreAst.t) option

(** Parse from the file, return the AST. *)
val ast_of_file : string -> LustreAst.t

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
