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

(** Convert a Lustre node to a transition system


    {1 Verification of Contracts}

    From a node's contract annotations, it has requirements that can
    be assumed invariant, and guarantees that have to be shown
    invariant. Each caller of a node must show it keeps the
    requirementes of the callee at call site invariant.

    Besides these proof obligations from contracts, a node may be
    annotated with properties that are to be shown invariant under the
    assumption of the requirements from its contracts.

    Every proof obligation of a called node is instantiated at call
    site as a proof obligation of the calling node. An instantiated
    proof obligation is less general than the one it is generated
    from, because it is embedded in the context of the caller.

    Only proof obligations of the top node are considered, the proof
    obligations of sub-nodes are disregarded in the analysis. All
    proof obligations are considered together, but some verification
    engines may be able to prove invariance of a subset of the proof
    obligations before other proof obligations. 

    To generate proof obligations for a transition system, we exploit
    instantiation of proof obligations, multi-property verification
    and information from previous analysis runs in the following way.

    For every node with a contract but the top node, add a proof
    obligation for its requirements. This proof obligation will be not
    be seen by the analysis, but is instantiated by each caller. The
    requirements of the top node are assumed to be invariant.

    For every node, unless it is abstracted to its contract, add its
    guarantee as a proof obligation. If the guarantee has been
    shown in a previous anaysis run, it becomes an invariant
    instead. If the guarantee remains a proof obligation, it is
    instantied in each calling node, and is proved together with all
    other other proof obligations, thus strengthening the
    analysis. For every node that is abstracted to its contract, add
    the guarantee as an invariant, since it can only be proved by
    providing the implementation.

    This approach works for any combination of modular and
    compositional analysis. 



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

    The [depth_input] and [max_depth_input] control the abstraction of
    the nodes for which a contract is available. Both are constants
    and are inputs of the node. When instantiating a node with a
    contract, the value of the depth input is the caller's depth input
    plus one, meaning that since this node has a contract we are going
    down one abstraction level. The max depth input always has the
    same value and is passed as an input for the sake of uniformity.

    The init / trans predicates are conditional on the depth input.
    If the value of the depth input is greater than the max depth
    input, then the contract definition of the node is used instead of
    the actual init / trans predicate. In this case, lifting the
    properties of the subnode might not make sense since the actual
    init / trans predicate is not used. The abstract predicates
    therefore constrain all the properties to evaluate to true.

    Predicates are thus defined as
    {[     (depth_input < max_depth_input) => contract and (props = true) ]}
    {[ not (depth_input < max_depth_input) => concrete_predicate ]}


    {1 Condact Encoding}

    If a node call has an activation condition that is not the constant
    true, additional fresh variables are generated. One variable is
    initially false and becomes and remains true on the first time the
    activation condition is true. Further, all input variables are
    duplicated to shadow input variables that freeze the input values
    at the last instant the activation condition has been true.

    The [init_flag] flag is [true] from the first state up to the
    state when the clock first ticks, including that state. After that
    state, the flag is false forever.
    For example:
    {[
      state      0     1     2    3     4     5     ...
                                                clock      false false true false true  false ...
                                                                                          init_flag true  true  true false false false ... ]}
    Thus [clock and init_flag] is true when and only when clock ticks
    for the first time. The [init_flag] flag will be passed down to
    the called node as its init flag. It is mandatory for invariant
    lifting: two state invariants are guarded by [init_flag or inv],
    and substitution takes care of rewriting that as
    [clock => init_flag or inv].


    The initial state constraint of the called node is a conjunction of
    formulas representing the following:
    - the [init_flag] flag is true (see paragraph above):
    {[init_flag = true]}
    - the shadow input variables take the values of the actual input
      variables if the activation condition is true:
    {[clock => shadow_input = actual_input]}
    - the initial state predicate of the called node with the
      parameters as above, except for the input variables that are
      replaced by the shadow input variables:
    {[clock => init(init_flag,args)]}
    - if the activation condition is false then the outputs are
      constrained to their default values:
    {[not clock => out = default]}

    The transition relation of the called node is a conjunction of
    formulas representing the following facts:

    - the [init_flag] flag is true in the current state iff it was
      true in the previous instant and the activation condition was
      false in the previous instant:
    {[init_flag' = init_flag and not clock ]}

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
      condition is true in the next step and the [init_flag] flag is
      true in the next step:
    {[(clock' and init_flag') => init(init_flag',args')]}

    - the transition relation predicate of the called node with the
      parameters as above, except for the input variables that are
      replaced by the shadow input variables, if the activation
      condition is true and the [init_flag] flag is false in the next
      step.
    {[(clock' and not init_flag') => trans(init_flag',args',init_flag,args)]}

    @author Christoph Sticksel
    @author Adrien Champion *)


val trans_sys_of_nodes : LustreNode.t SubSystem.t -> Analysis.param -> TransSys.t


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
