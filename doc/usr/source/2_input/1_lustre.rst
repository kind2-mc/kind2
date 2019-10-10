.. _2_input/1_lustre:

Lustre Input
============

Lustre is a functional, synchronous dataflow language. Kind 2 supports most of the Lustre V4 syntax and some elements of Lustre V6. See the file `examples/syntax-test.lus <https://github.com/kind2-mc/kind2/blob/develop/examples/syntax-test.lus>`_ for examples of all supported language constructs.

Properties and top-level node
-----------------------------

To specify a property to verify in a Lustre node, add the following annotation in the body (\ *i.e.* between keywords ``let`` and ``tel``\ ) of the node:

.. code-block:: none

   --%PROPERTY ["<name>"] <bool_expr> ;

or, use a ``check`` statement:

.. code-block:: none

   check ["<name>"] <bool_expr> ;

where ``<name>`` is an identifier for the property and ``<bool_expr>`` is a Boolean Lustre expression.

Without modular reasoning active, Kind 2 only analyzes the properties of what it calls the *top node*. By default, the top node is the last node in the file. To force a node to be the top node, add

.. code-block:: none

   --%MAIN ;

to the body of that node.

You can also specify the top node in the command line arguments, with

.. code-block:: none

   kind2 --lustre_main <node_name> ...

Example
^^^^^^^

The following example declares two nodes ``greycounter`` and ``intcounter``\ , as well as an *observer* node ``top`` that calls these nodes and verifies that their outputs are the same. The node ``top`` is annotated with ``--%MAIN ;`` which makes it the *top node* (redundant here because it is the last node). The line ``--%PROPERTY OK;`` means we want to verify that the Boolean stream ``OK`` is always true.

.. code-block:: none

   node greycounter (reset: bool) returns (out: bool);
   var a, b: bool; 
   let
     a = false -> (not reset and not pre b);
     b = false -> (not reset and pre a);
     out = a and b;

   tel

   node intcounter (reset: bool; const max: int) returns (out: bool);
   var t: int; 
   let
     t = 0 -> if reset or pre t = max then 0 else pre t + 1;
     out = t = 2;

   tel

   node top (reset: bool) returns (OK: bool);
   var b, d: bool;
   let
     b = greycounter(reset);
     d = intcounter(reset, 3);
     OK = b = d;

     --%MAIN ;

     --%PROPERTY OK;

   tel

Kind 2 produces the following on standard output when run with the default options (\ ``kind2 <file_name.lus>``\ ):

.. code-block:: none

   kind2 v0.8.0

   <Success> Property OK is valid by inductive step after 0.182s.

   status of trans sys
   ------------------------------------------------------------------------------
   Summary_of_properties:

   OK: valid

We can see here that the property ``OK`` has been proven valid for the system (by *k*\ -induction).


.. _2_input/1_lustre#contracts:

Contracts
---------

A contract ``(A,G,M)``\ for a node is a set of assumptions ``A``\ , a set of
guarantees ``G``\ , and a set of modes ``M``. The semantics of contracts is given
in the
:ref:`9_other/2_contract_semantics`
section, here we focus on the input format for contracts. Contracts are
specified either locally, using the *inline syntax*\ , or externally in a
*contract node*. Both the local and external syntax have a body
composed of *items*\ , each of which define


* a ghost variable / constant,
* an assumption,
* a guarantee,
* a mode, or
* an import of a contract node.

They are presented in detail below, after the discussion on local and external
syntaxes.

Inline syntax
^^^^^^^^^^^^^

A local contract is a special comment between the signature of the node

.. code-block:: none

   node <id> (...) returns (...) ;

and its body. That is, between the ``;`` of the node signature and the ``let``
opening its body.

A local contract is a special block comment of the form

.. code-block:: none

   (*@contract
     [item]+
   *)

or

.. code-block:: none

   /*@contract
     [item]+
   */

External syntax
^^^^^^^^^^^^^^^

A contract node is very similar to a traditional lustre node. The two
differences are that


* it starts with ``contract`` instead of ``node``\ , and
* its body can only mention *contract items*.

A contract node thus has form

.. code-block:: none

   contract <id> (<in_params>) returns (<out_params>) ;
   let
     [item]+
   tel

To use a contract node one needs to import it through an inline contract. See
the next section for more details.

Contract items and restrictions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Ghost variables and constants
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A ghost variable (constant) is a stream that is local to the contract. That is,
it is not accessible from the body of the node specified. Ghost variables
(constants) are defined with the ``var`` (\ ``const``\ ) keyword. Kind 2 performs type
inference for constants so in most cases type annotations are not necessary.

The general syntax is

.. code-block:: none

   const <id> [: <type>] = <expr> ;
   var   <id>  : <type>  = <expr> ;

For instance:

.. code-block:: none

   const max = 42 ;
   var ghost_stream: real = if input > max then max else input ;

Assumptions
~~~~~~~~~~~

An assumption over a node ``n`` is a constraint one must respect in order to use
``n`` legally. It cannot mention the outputs of ``n`` in the current state, but
referring to outputs under a ``pre`` is fine.

The idea is that it does not make sense to ask the caller to respect some
constraints over the outputs of ``n``\ , as the caller has no control over them
other than the inputs it feeds ``n`` with.
The assumption may however depend on previous values of the outputs produced
by ``n``.

Assumptions are given with the ``assume`` keyword, followed by any legal Boolean
expression:

.. code-block:: none

   assume <expr> ;

Guarantees
~~~~~~~~~~

Unlike assumptions, guarantees do not have any restrictions on the streams
they can mention. They typically mention the outputs in the current state since
they express the behavior of the node they specified under the assumptions of
this node.

Guarantees are given with the ``guarantee`` keyword, followed by any legal
Boolean expression:

.. code-block:: none

   guarantee <expr> ;

Modes
~~~~~

A mode ``(R,E)`` is a set of *requires* ``R`` and a set of *ensures* ``E``. Requires
have the same restrictions as assumptions: they cannot mention outputs of the
node they specify in the current state. Ensures, like guarantees, have no
restriction.

Modes are named to ease traceability and improve feedback. The general syntax
is

.. code-block:: none

   mode <id> (
     [require <expr> ;]*
     [ensure  <expr> ;]*
   ) ;

For instance:

.. code-block:: none

   mode engaging (
     require true -> not pre engage_input ;
     require engage_input ;
     -- No ensure, same as `ensure true ;`.
   ) ;
   mode engaged (
     require engage_input ;
     require false -> pre engage_input ;
     ensure  output <= upper_bound ;
     ensure  lower_bound <= output ;
   ) ;

Imports
~~~~~~~

A contract import *merges* the current contract with the one imported. That
is, if the current contract is ``(A,G,M)`` and we import ``(A',G',M')``\ , the
resulting contract is ``(A U A', G U G', M U M')`` where ``U`` is set union.

When importing a contract, it is necessary to specify how the instantiation of
the contract is performed. This defines a mapping from the input (output)
formal parameters to the actual ones of the import.

When importing contract ``c`` in the contract of node ``n``\ , it is **illegal** to
mention an output of ``n`` in the actual input parameters of the import of ``c``.
The reason is that the distinction between inputs and outputs lets Kind 2 check
that the assumptions and mode requirements make sense, *i.e.* do not mention
outputs of ``n`` in the current state.

The general syntax is

.. code-block:: none

   import <id> ( <expr>,* ) returns ( <expr>,* ) ;

For instance:

.. code-block:: none

   contract spec (engage, disengage: bool) returns (engaged: bool) ;
   let ... tel

   node my_node (
     -- Flags are "signals" here, but `bool`s in the contract.
     engage, disengage: real
   ) returns (
     engaged: real
   ) ;
   (*@contract 
     var bool_eng: bool = engage <> 0.0 ;
     var bool_dis: bool = disengage <> 0.0 ;
     var bool_enged: bool = engaged <> 0.0 ;

     var never_triggered: bool = (
       not bool_eng -> not bool_eng and pre never_triggered
     ) ;

     assume not (bool_eng and bool_dis) ;
     guarantee true -> (
       (not engage and not pre bool_eng) => not engaged
     ) ;

     mode init (
       require never_triggered ;
       ensure not bool_enged ;
     ) ;

     import spec (bool_eng, bool_dis) returns (bool_enged) ;
   *)
   let ... tel

Mode references
~~~~~~~~~~~~~~~

Once a mode has been defined it is possible to *refer* to it with

.. code-block:: none

   ::<scope>::<mode_id>

where ``<mode_id>`` is the name of the mode, and ``<scope>`` is the path to the
mode in terms of contract imports.

In the example from the previous section for instance, say contract ``spec`` has
a mode ``m``. The inline contract of ``my_node`` can refer to it by

.. code-block:: none

   ::spec::m

To refer to the ``init`` mode:

.. code-block:: none

   ::init

A mode reference is syntactic sugar for the ``requires`` of the mode in question.
So if mode ``m`` is

.. code-block:: none

   mode m (
     require <r_1> ;
     require <r_2> ;
     ...
     require <r_n> ; -- Last require.
     ...
   ) ;

then ``::<path>::m`` is exactly the same as

.. code-block:: none

   (<r_1> and <r_1> and ... and <r_n>)

**N.B.**: a mode reference


* is a Lustre expression of type ``bool`` just like any other Boolean expression. 
  It can appear under a ``pre``\ , be used in a node call or a contract import, *etc.*
* is only legal **after** the mode item itself. That is, no
  forward/self-references are allowed.

An interesting use-case for mode references is that of checking properties over
the specification itself. One may want to do so to make sure the specification
behaves as intended. For instance

.. code-block:: none

   mode m1 (...) ;
   mode m2 (...) ;
   mode m3 (...) ;

   guarantee true -> ( -- `m3` cannot succeed to `m1`.
     (pre ::m1) => not ::m3
   ) ;
   guarantee true -> ( -- `m1`, `m2` and `m3` are exclusive.
     not (::m1 and ::m2 and ::m3)
   ) ;

Merge, When, Activate and Restart
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

..

   **Note**\ : the first few examples of this section illustrating (unsafe)
   uses of ``when`` and ``activate`` are **not legal** in Kind 2. They aim at
   introducing the semantics of lustre clocks. As discussed below, they are only
   legal when used inside a ``merge``\ , hence making them safe clock-wise.

   Also, ``activate`` and ``restart`` are actually not a legal Lustre v6
   operator. They are however legal in Scade 6.


A ``merge`` is an operator combining several streams defined on **complementary**
clocks. There is two ways to define a stream on a clock. First, by wrapping its
definition inside a ``when``.

.. code-block:: none

   node example (in: int) returns (out: int) ;
   var in_pos: bool ; x: int ;
   let
     ...
     in_pos = x >= 0 ;
     x = in when in_pos ;
     ...
   tel

Here, ``x`` is only defined when ``in_pos``\ , its clock, is ``true``. 
That is, a trace of execution of ``example`` sliced to ``x`` could be

==== === ====== ==
step in  in_pos x
==== === ====== ==
0    3   true   3
1    -2  false  //
2    -1  false  //
3    7   true   7
4    -42 true   //
==== === ====== ==

where // indicates that ``x`` undefined.

The second way to define a stream on a clock is to wrap a node call with the
``activate`` keyword. The syntax for this is

.. code-block:: none

   (activate <node_name> every <clock>)(<input_1>, <input_2>, ...)

For example, consider the following node:

.. code-block:: none

   node sum_ge_10 (in: int) returns (out: bool) ;
   var sum: int ;
   let
     sum = in + (0 -> pre sum) ;
     out = sum >= 10 ;
   tel

Say now we call this node as follows:

.. code-block:: none

   node example (in: int) returns (...) ;
   var tmp, in_pos: bool ;
   let
     ...
     in_pos = in >= 0 ;
     tmp = (activate sum_ge_10 every in_pos)(in) ;
     ...
   tel

That is, we want ``sum_ge_10(in)`` to tick iff ``in`` is positive. Here is an
example trace of ``example`` sliced to ``tmp``; notice how the internal state of
``sub`` (*i.e.* ``pre sub.sum``) is maintained so that it does refer to the value
of ``sub.sum`` *at the last clock tick of the ``activate``*:

====  ==  ======  ======  ======  ===========  =======
step  in  in_pos  tmp     sub.in  pre sub.sum  sub.sum
====  ==  ======  ======  ======  ===========  =======
0     3   true    false   3       nil          3
1     2   true    false   2       3            5
2     -1  false   nil     nil     5            nil
3     2   true    false   2       5            7
4     -7  false   nil     nil     7            nil
5     35  true    true    35      7            42
6     -2  false   nil     nil     42           nil
====  ==  ======  ======  ======  ===========  =======

Now, as mentioned above the ``merge`` operator combines two streams defined on
**complimentary** clocks. The syntax of ``merge`` is:

.. code-block:: none

   merge( <clock> ; <e_1> ; <e_2> )

where ``e_1`` and ``e_2`` are streams defined on ``<clock>`` and ``not <clock>``
respectively, or on ``not <clock>`` and ``<clock>`` respectively.

Building on the previous example, say add two new streams ``pre_tmp`` and
``safe_tmp``\ :

.. code-block:: none

   node example (in: int) returns (...) ;
   var tmp, in_pos, pre_tmp, safe_tmp: bool ;
   let
     ...
     in_pos = in >= 0 ;
     tmp = (activate sum_ge_10 every in_pos)(in) ;
     pre_tmp = false -> pre safe_tmp  ;
     safe_tmp = merge( in_pos ; tmp ; pre_tmp when not in_pos ) ;
     ...
   tel

That is, ``safe_tmp`` is the value of ``tmp`` whenever it is defined, otherwise it
is the previous value of ``safe_tmp`` if any, and ``false`` otherwise.
The execution trace given above becomes

====  ==  ======  ======  =======  ========
step  in  in_pos  tmp     pre_tmp  safe_tmp
====  ==  ======  ======  =======  ========
0     3   true    false   false    false 
1     2   true    false   false    false
2     -1  false   nil     false    false
3     2   true    false   false    false
4     -7  false   nil     false    false
5     35  true    true    false    true
6     -2  false   nil     true     true
====  ==  ======  ======  =======  ========

Just like with uninitialized ``pre``\ s, if not careful one can easily end up
manipulating undefined streams. Kind 2 forces good practice by allowing
``when`` and ``activate ... every`` expressions only inside a ``merge``. All the
examples of this section above this point are thus invalid from Kind 2's point
of view.

Rewriting them as valid Kind 2 input is not difficult however. Here is a legal
version of the last example:

.. code-block:: none

   node example (in: int) returns (...) ;
   var in_pos, pre_tmp, safe_tmp: bool ;
   let
     ...
     in_pos = in >= 0 ;
     pre_tmp = false -> pre safe_tmp  ;
     safe_tmp = merge(
       in_pos ;
       (activate sum_ge_10 every in_pos)(in) ;
       pre_tmp when not in_pos
     ) ;
     ...
   tel

Kind 2 supports resetting the internal state of a node to its initial state by
using the construct restart/every. Writing

.. code-block:: none

   (restart n every c)(x1, ..., xn)

makes a call to the node ``n`` with arguments ``x1``\ , ..., ``xn`` and every time the
Boolean stream ``c`` is true, the internal state of the node is reset to its
initial value.

In the example below, the node ``top`` makes a call to ``counter`` (which is an
integer counter *modulo* a constant ``max``\ ) which is reset every time the input
stream ``reset`` is true. 

.. code-block:: none

   node counter (const max: int) returns (t: int);
   let
     t = 0 -> if pre t = max then 0 else pre t + 1;
   tel

   node top (reset: bool) returns (c: int);
   let
     c = (restart counter every reset)(3);
   tel

A trace of execution for the node top could be:

====  =====  =
step  reset  c
====  =====  =
0     false  0
1     false  1
2     false  2
3     false  3
4     true   0
5     false  1
6     false  2
7     true   0
8     true   0
9     false  1
====  =====  =

..

   **Note:** This construction can be encoded in traditional Lustre by having a
   Boolean input for the reset stream for each node. However providing a
   built-in  way to do it facilitates the modeling of complex control systems.


Restart and activate can also be combined in the following way:

.. code-block:: none

   (activate (restart n every r) every c)(a1, ..., an)
   (activate n every c restart every r)(a1, ..., an)

These two calls are the same (the second one is just syntactic sugar). The
(instance of the) node ``n`` is restarted whenever ``r`` is true and the *resulting
call* is activated when the clock ``c`` is true. Notice that the restart clock
``r`` is also sampled by ``c`` in this call.

Enumerated data types in Lustre
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: none

   type t = enum { A, B, C };
   node n (x : enum { C1, C2 }, ...) ...

Enumerated datatypes are encoded as subranges so that solvers handle arithmetic
constraints only. This also allows to use the already present quantifier
instantiation techniques in Kind 2.

N-way merge
^^^^^^^^^^^

As in Lustre V6, merges can also be performed on a clock of a user defined
enumerated datatype. 

.. code-block:: none

   merge c
    (A -> x when A(c))
    (B -> w + 1 when B(c));

Arguments of merge have to be sampled with the correct clock. Clock expressions
for merge can be just a clock identifier or its negation or ``A(c)`` which is a
stream that is true whenever ``c = A``.

Merging on a Boolean clock can be done with two equivalent syntaxes:

.. code-block:: none

   merge(c; a when c; b when not c);

   merge c
     (true -> a when c)
     (false -> b when not c);

Partially defined nodes
-----------------------

Kind 2 allows nodes to define their outputs only partially. For instance, the
node

.. code-block:: none

   node count (trigger: bool) returns (count: int ; error: bool) ;
   (*@contract
     var once: bool = trigger or (false -> pre once) ;
     guarantee count >= 0 ;
     mode still_zero (
       require not once ;
       ensure count = 0 ;
     ) ;
     mode gt (
       require not ::still_zero ;
       ensure count > 0 ;
     ) ;
   *)
   let
     count = (if trigger then 1 else 0) + (0 -> pre count) ;
   tel

can be analyzed: first for mode exhaustiveness, and the body is checked against
its contract, although it is only *partially* defined.
Here, both will succeed.

The ``imported`` keyword
----------------------------

Nodes (and functions, see below) can be declared ``imported``. This means that
the node does not have a body (\ ``let ... tel``\ ). In a Lustre compiler, this is
usually used to encode a C function or more generally a call to an external
library.

.. code-block:: none

   node imported no_body (inputs: ...) returns (outputs: ...) ;

In Kind 2, this means that the node is always abstract in the contract sense.
It can never be refined, and is always abstracted by its contract. If none is
given, then the implicit (rather weak) contract

.. code-block:: none

   (*@contract
     assume true ;
     guarantee true ;
   *)

is used.

In a modular analysis, ``imported`` nodes will not be analyzed, although if their
contract has modes they will be checked for exhaustiveness, consistently with
the usual Kind 2 contract workflow.

Partially defined nodes VS ``imported``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Kind 2 allows partially defined nodes, that is nodes in which some streams
do not have a definition. At first glance, it might seem like a node with no
definitions at all (with an empty body) is the same as an ``imported`` node.

It is not the case. A partially defined node *still has a (potentially
empty) body* which can be analyzed. The fact that it is not completely defined
does not change this fact.
If a partially defined node is at the top level, or is in the cone of
influence of the top node in a modular analysis, then it's body **will** be analyzed.

An ``imported`` node on the other hand *explicitly does not have a body*. Its
non-existent body will thus never be analyzed.

Functions
---------

Kind 2 supports the ``function`` keyword which is used just like the ``node`` one
but has slightly different semantics. Like the name suggests, the output(s) of
a ``function`` should be a *non-temporal* combination of its inputs. That is, a
function cannot the ``->``\ , ``pre``\ , ``merge``\ , ``when``\ , ``condact``\ , or ``activate``
operators. A function is also not allowed to call a node, only other functions.
In Lustre terms, functions are stateless.

In Kind 2, these retrictions extend to the contract attached to the function,
if any. Note that besides the ones mentioned here, no additional restrictions
are enforced on functions compared to nodes.

Benefits
^^^^^^^^

Functions are interesting in the model-checking context of Kind 2 mainly as
a mean to make an abstraction more precise. A realistic use-case is when one
wants to abstract non-linear expressions. While the simple expression ``x*y``
seems harmless, at SMT-level it means bringing in the theory of non-linear
arithmetic.

Non-linear arithmetic has a huge impact not only on the performances of the
underlying SMT solvers, but also on the SMT-level features Kind 2 can use (not
to mention undecidability). Typically, non-lineary arithmetic tends to prevent
Kind 2 from performing satisfiability checks with assumptions, a feature it
heavily relies on.

The bottom line is that as soon as some non-linear expression appear, Kind 2
will most likely fail to analyze most non-trivial systems because the
underlying solver will simply give up.

Hence, it is usually `extremely rewarding <https://www.researchgate.net/publication/304360220_CoCoSpec_A_Mode-Aware_Contract_Language_for_Reactive_Systems>`_
to abstract non-linear expressions away in a separate *function* equipped with
a contract. The contract would be a linear abstraction of the non-linear
expression that is precise enough to prove the system using correct. That way,
a compositional analysis would *i)* verify the abstraction is correct and *ii)*
analyze the rest of the system using this abstraction, thus making the analysis
a linear one.

Using a function instead of a node simply results in a better abstraction. Kind
2 will encode, at SMT-level, that the outputs of this component depend on the
*current* version of its inputs only, not on its previous values.

Hierarchical Automata
---------------------

..

   **Experimental feature**


Kind 2 supports both the syntax used in LustreC and a subset of the one used in
Scade 6.

.. code-block:: none

   node n (i1, ..., in : ...) returns (o1, ..., on : ...);
   let

      automaton automaton_name

        initial state S1:
          unless if c restart Si elsif c' resume Sj else restart Sk end;
          var v : ...;
          let
             v = ...;
             o1 = i1 -> last o2 + 1;
             o2 = 99;
          tel
          until c restart S2;

        state S2:
          let
             ...; 
          tel
        ...
      returns o1, o2;

      o3 = something () ...;
   tel

An automaton is declared *inside a node* (there can be several) and can be
anonymous. Automata can be nested, *i.e.* an automaton can contain other
automata in some of its states bodies. This effectively allows to describe
*hierarchical state machines*. An automaton is defined by its list of states
and a ``returns`` statement that specifies which variables (locals or output) are
defined by the automaton.

..

   The set of returned streams can be inferred by writing ``returns ..;``. One can
   also simply omit the ``returns`` statement which will have the same effect.


States (much like regular nodes) do not need to give equations that define
*all* their outputs (but they do for their local variables). If defined streams
are different between the states of the automaton, then the set considered will
be their union and states that do not define all the inferred streams will be
considered underconstrained.

Each state has a name and one of them can be declared ``initial`` (if no initial
state is specified, the first one is considered initial). They can have local
variables (to the state).  The body of the state contains Lustre equations (or
assertions) and can use the operator ``last``. In contrast to ``pre x`` which is
the value of the stream ``x`` the last time the state was in the declared state,
``last x`` (or the Scade 6 syntax ``last 'x``\ ) is the previous value of the stream
``x`` on the base clock. This construct is useful for communicating information
between states.

States can have a *strong* transition (declared with ``unless``\ ) placed before
the body and a *weak* transition placed after the body. The unless transition
is taken when entering the state, whereas the until transition is evaluated
after execution of the body of the state. If none are applicable then the
automaton remains in the same state. These transitions express conditions to
change states following a branching pattern. Following are examples of legal
branching patterns (\ ``c*`` are Lustre Boolean expressions):

.. code-block:: none

   c restart S

.. code-block:: none

   if c1 restart S1
   elsif c2 restart S2
   elsif c3 restart S3
   end;

.. code-block:: none

   if c1
     if c2 restart S2
     else if c3 resume S1
     end
   elsif c3 resume S3
   else restart S0
   end;

Targets are of the form ``restart State_name`` or ``resume State_name``.  When
transiting to a state with ``restart``\ , the internal state of the state is rested
to its initial value. On the contrary when transiting with ``resume``\ , execution
in the state resumes to where it was when the state was last executed.

In counter-examples, we show the value of additional internal state information
for each automaton: ``state`` is a stream that denotes the state in which the
automaton is and ``restart`` indicates if the state in which the automaton is was
restarted in the current instant.

The internal state of an automaton state is also represented in counter-example
traces, separately. States and subsequent streams are sampled with the clock
state, *i.e.* values of streams are shown only when the automaton is in the
corresponding state.
