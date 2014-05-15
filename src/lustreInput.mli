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

    An OCaml lexer in {!LustreLexer} and a Menhir parser in
    {!LustreParser} take the input and produce a {!LustreAst.t} value,
    which is a minimally processed representation of a Lustre AST. 

    The function {!LustreSimplify.declarations_to_node} is called with
    this representation as input and produces a list of
    {!LustreNode.t} that contains each nodes in a normalized form, see
    {!LustreNode} and {!LustreExpr} for details.

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


(** Parse from the channel *)
val of_channel : in_channel -> TransSys.t

(** Parse from the file *)
val of_file : string -> TransSys.t


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
