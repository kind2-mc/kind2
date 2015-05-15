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

(** Parse a Lustre file into a transition system

    An OCamllex lexer in {!LustreLexer} and a Menhir parser in
    {!LustreParser} take the input and produce a {!LustreAst.t} value,
    which is a minimally processed representation of a Lustre AST. 

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

(** Parse from the file, return an input system for further slicing
    and refinement *)
val of_file : string -> LustreNode.t SubSystem.t

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
