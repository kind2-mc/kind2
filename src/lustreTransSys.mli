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

(** Conversion of a Lustre node to a transition system

    {1 Lustre Expressions}

    A Lustre expression {!LustreExpr.t} is rewritten to a normal form
    in the following ways.

    There is exactly one [->] operator at the top of the expression,
    thus an expression can be represented as a pair of expressions
    [(i, t)] without [->] operators. 

    The argument of a [pre] operator is always a variable, therefore
    an expression [pre x] operator can be represented by the variable
    [x] at the previous state. A non-variable expression under a [pre]
    is abstracted to a fresh variable that is defined by this
    expression.

    There are no node calls in a Lustre expression. They are
    abstracted out and the results are captured in fresh variables. If
    an input parameter of a node contains a [pre] operator, the
    expression has to be abstracted to a fresh variable.

    {1 Lustre Nodes} 

    A Lustre node {!LustreNode.t} is simplified and rewritten in the
    following ways.

    Streams are flattened such that each element of a tuple, a record
    or an array becomes a separate stream. Constants are expanded in
    expressions.

    An equational definition of a stream becomes an association of the
    variable of the stream to a Lustre expression as described above,
    where no temporal operators occur, and all node calls are
    abstracted out. Each unguarded pre operators is replaced by a
    fresh constant variable that is an oracle for the initial value.

    Assertions are Lustre expressions of Boolean type, properties are
    abstracted to variables of Boolean type.

    When creating simplified Lustre expressions, all node calls are
    abstracted such that the return values are assigned to fresh
    variables. Further, expressions under a [pre] operator and
    parameters of node calls that contain a [pre] operator are
    abstracted to definitions of fresh variables. 

    The definitions of variables are ordered such that the definition of
    a variable [x] occurs before all definitions that use variable [x].

    {1 Translation}

    Each Lustre node is translated to two definitions of fresh
    uninterpreted predicate symbols over a set of stateful variables
    of the node. The first predicate constrains the initial values of
    the variables, the second predicate constrains the set of primed
    variables as a function of the set of unprimed variables.

    A variable is stateful if it is 

    - an input variable, 
    - an output variable, or
    - a property variable, or further,
    - a variable occurring under a [pre] operator in any expression in
      the node, or
    - a variable capturing the output of a node call.

    The predicates are defined as the conjunction of equational
    definitions of stateful variables, assertions and predicates of
    node calls. Equational definitions of not stateful variable are
    substituted by binding the variable to a [let] definition.


    {1 Condact Encoding}

    If a node call has an activation condition that is not the constant
    true, additional fresh variables are generated. One variable is
    initially false and becomes and remains true on the first time the
    activation condition is true. Further, all input variables are
    duplicated to shadow input variables that freeze the input values
    at the last instant the activation condition has been true.

    The [first_tick] flag is [true] from the first state up to the
    state when the clock first ticks, including that state. After that
    state, the flag is false forever.
    For example:
    {[
state      0     1     2    3     4     5     ...
clock      false false true false true  false ...
first_tick true  true  true false false false ... ]}
    Thus [clock and first_tick] is true when and only when clock ticks
    for the first time. The [first_tick] flag will be passed down to
    the called node as its init flag. It is mandatory for invariant
    lifting: two state invariants are guarded by [init_flag or inv],
    and substitution takes care of rewriting that as
    [clock => first_tick or inv].


    The initial state constraint of the called node is a conjunction of
    formulas representing the following:
    - the [first_tick] flag is true (see paragraph above):
      {[first_tick = true]}
    - the shadow input variables take the values of the actual input
      variables if the activation condition is true:
      {[clock => shadow_input = actual_input]}
    - the initial state predicate of the called node with the
      parameters as above, except for the input variables that are
      replaced by the shadow input variables:
      {[clock => init(first_tick,args)]}
    - if the activation condition is false then the outputs are
      constrained to their default values:
      {[not clock => out = default]}

    The transition relation of the called node is a conjunction of
    formulas representing the following facts:

    - the [first_tick] flag is true in the current state iff it was
      true in the previous instant and the activation condition was
      false in the previous instant:
      {[first_tick' = first_tick and not clock ]}

    - the shadow input variables in the next state take the values of
      the actual input variables if the activation condition is true:
      {[clock' => shadow_input' = actual_input']}
      and their previous values if the activation condition is false.
      More generally, all the arguments of the subnode init/trans stay
      the same:
      {[not clock' => (args' = args)]}

    - the initial state predicate of the called node with the
      parameters as above, except for the input variables that are
      replaced by the shadow input variables, if the activation
      condition is true in the next step and the [first_tick] flag is
      true in the next step:
      {[(clock' and first_tick') => init(first_tick',args')]}

    - the transition relation predicate of the called node with the
      parameters as above, except for the input variables that are
      replaced by the shadow input variables, if the activation
      condition is true and the [first_tick] flag is false in the next
      step.
      {[(clock' and not first_tick') => trans(first_tick',args',first_tick,args)]}

    @author Christoph Sticksel
    @author Adrien Champion *)

(** *)
val trans_sys_of_nodes : LustreNode.t list -> TransSys.t

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
