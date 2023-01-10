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

Without modular reasoning active, Kind 2 only analyzes the properties of what it calls the *top nodes*.
By default, any node that is not depended on by another node (i.e. called by that node) is a top node.
Alternatively, nodes can be marked as *main nodes* by doing the following:

.. code-block:: none

   --%MAIN ;

to the body of that node.

You can also specify the main node in the command line arguments, with

.. code-block:: none

   kind2 --lustre_main <node_name> ...

Main nodes specified by the command line option override main nodes annotated in the source code. If any main nodes exist then only main nodes are analyzed (top nodes are not).

Example
^^^^^^^

The following example declares two nodes ``greycounter`` and ``intcounter``\ , as well as an *observer* node ``top`` that calls these nodes and verifies that their outputs are the same. The node ``top`` is annotated with ``--%MAIN ;`` which makes it a *main node*. The line ``--%PROPERTY OK;`` means we want to verify that the Boolean stream ``OK`` is always true.

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

   kind2 v1.5.1

   ==============================================================
   Analyzing top
     with First top: 'top'
                subsystems
                  | concrete: intcounter, greycounter

   <Success> Property OK is valid by inductive step after 0.065s.

   --------------------------------------------------------------
   Summary of properties:
   --------------------------------------------------------------
   OK: valid (at 5)
   ==============================================================

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
``n`` legally. It cannot depend on outputs of ``n`` in the current state, but
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
they can depend on. They typically mention the outputs in the current state since
they express the behavior of the node they specified under the assumptions of
this node.

Guarantees are given with the ``guarantee`` keyword, followed by any legal
Boolean expression:

.. code-block:: none

   guarantee <expr> ;

Modes
~~~~~
..
   A mode ``(R,E)`` is a set of *requires* ``R`` and a set of *ensures* ``E``. Requires
   have the same restrictions as assumptions: they cannot mention outputs of the
   node they specify in the current state. Ensures, like guarantees, have no
   restriction.

A mode ``(R,E)`` is a set of *requires* ``R`` and a set of *ensures* ``E``.
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
However, each contract import introduces its own namespace to avoid
name collisions.

When importing a contract, it is necessary to specify how the instantiation of
the contract is performed. This defines a mapping from the input (output)
formal parameters to the actual ones of the import.

When importing contract ``c`` in the contract of node ``n``\ ,
the actual input parameters of the import of ``c`` cannot depend on
outputs of ``n`` in the current state.
The reason is that the distinction between inputs and outputs lets Kind 2 check
that the assumptions requirements make sense, *i.e.* do not depend on
outputs of ``n`` in the current state.

The general syntax is

.. code-block:: none

   import <id> ( <expr>,* <expr> ) returns ( <id>,* <id> ) ;

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
* is only legal **outside** the mode item itself. That is, no self-references are allowed.
  Forward references are allowed.

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
     in_pos = in >= 0 ;
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

   type my_enum = enum { A, B, C };
   node n (x : my_enum, ...) ...

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

.. _2_input/1_lustre#imported:

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
function cannot depend on the ``->``\ , ``pre``\ , ``merge``\ , ``when``\ ,
``condact``\ , or ``activate`` operators.
A function is also not allowed to call a node, only other functions.
In Lustre terms, functions are stateless.

In Kind 2, these restrictions extend to the contract attached to the function,
if any. Note that besides the ones mentioned above, no additional restrictions
are enforced on functions compared to nodes.
In particular, functional congruence is not enforced on
partially defined functions, imported functions, and
functions abstracted by their contracts. That is,
Kind 2 might return a counterexample where two calls to an abstract function
with the same input values provide different output values.
To prevent this kind of counterexamples from happening, Kind 2 offers an option
called ``--enforce_func_congruence`` which enforces
abstract functions to behave as mathematical functions.
The downside of using this option is that the IC3 engine is forced to
shut down because its current implementation cannot reason about
the resulting system.

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

If statements and frame conditions
----------------------------------
Within node definitions, Kind 2 has support for two features that allow the programmer 
to use a more imperative style-- (1) ``if`` statements and (2) frame conditions. 

If statements
^^^^^^^^^^^^^
Kind 2 has always supported conditional expressions of the form ``x = if condition then expr1
else expr2``, where the ``if/then/else`` expression either evaluates to ``expression1``
or ``expression2``, depending on the value of ``condition``. However, in some circumstances,
it may be more natural to use ``if`` statements that serve as control flow (rather than
evaluate to a value). For example, Kind 2 now supports statements of the form:

.. code-block:: none

   if condition
   then
      y1 = expr1;
      y2 = expr2;
   else
      y1 = expr3;
      y2 = expr4;
   fi
   
In the above block, if ``condition`` is true, then ``y1`` and ``y2`` will be set to ``expr1`` and ``expr2``, respectively. 
Otherwise, ``y1`` and ``y2`` will be set to ``expr3`` and ``expr4``. The ``if`` statement is closed with
the ``fi`` token. As with other mainstream programming languages, Kind 2 allows for arbitrary nesting of ``if`` statements,
as well as writing ``if`` statements that do not have an ``else`` block. 

Frame conditions
^^^^^^^^^^^^^^^^
Kind 2 also has support for code blocks with frame conditions. At the beginning of the block
(denoted by the ``frame`` keyword), the user specifies a list of variables that they wish to 
define within the frame block. All variables defined within the frame block must be present in
this list. Then, initial values are optionally specified for these variables. 
Variables are defined within the frame block body (denoted by the ``let`` and ``tel`` keywords).
It is possible to leave variables (partially or fully) undefined: On the first timestep, each variable
is set equal to its initialization value, if one exists. On other timesteps, each undefined variable stutters 
(it is set equal to its value on the previous timestep). 

The following example involves three variables ``y1``, ``y2``, and ``y3``. Since ``y1`` is left
undefined within the frame block body, it will always be equal to 0 (its initialization
value). ``y2`` will have value ``100, 0, 1, 2, 3, ...`` because it is set equal to its initialization value (100)
on the first timestep, but on other timesteps it is set equal to ``counter()``. Even though ``y3`` is fully 
defined within the frame block (with no unguarded ``pre``s), its initialization value is still used, so it is equal
to ``5, 1, 2, 3, ...``.

.. code-block:: none

   node example() returns (y1, y2, y3: int);
   let
      frame ( y1, y2, y3 )
      (* Initializations *)
      y1 = 0; y2 = 100; y3 = 5;

      (* Body *)
      let
         y2 = pre counter();
         y3 = counter();
      tel
   tel
   
      
   node counter() returns (y: int);
   let
      y = 0 -> pre y + 1;
   tel


Frame conditions are especially useful when combined with the ``if`` statements described in the previous
subsection, as variables can be left undefined in some branches of the ``if`` statement.

.. code-block:: none

   node example() returns (y1, y2: int);
   let
      frame ( y1, y2 )
      (* Initializations *)
      y1 = 0; 
      y2 = 100;

      (* Body *)
      let
         if (counter() < 10)
         then
            y1 = counter();
         else
            y2 = counter() * 2;
         fi
      tel
   tel
   
      
   node counter() returns (y: int);
   let
      y = 0 -> pre y + 1;
   tel

In the above example, ``y1`` is left undefined in the ``else`` branch of the ``if`` statement,
and ``y2`` is left undefined in the ``then`` branch. ``y1`` is initialized on the first timestep,
set to be equal to ``counter()`` on the second through tenth timesteps, and then stutters (staying at 9) for the 
remaining timesteps. On the other hand, ``y2`` starts at its initialization value (100) and 
stutters there for the first 10 timesteps, and then is set to ``counter() * 2`` for the remaining timesteps.

Note that variables do not have to have initializations. When no initialization is given, 
a variable's initial value is equal to the initial value of the expression defined in the frame block body.
If the corresponding expression is undefined in the first timestep, then the variable is also
undefined in the first timestep. For example, the following code is supported because even though ``y1`` and ``y2`` 
do not have an initializations, they are present in the list of variables ``frame ( y1, y2 )``.
The initial value of ``y1`` is 0 (the initial value assigned by ``counter()``), and the initial value
of ``y2`` is undefined (due to the unguarded ``pre``).

.. code-block:: none

   frame ( y1, y2 )
   let
      y1 = counter();
      y2 = pre counter();
   tel

   node counter() returns (y: int);
   let
      y = 0 -> pre y + 1;
   tel

Also, it is still possible to assign to multiple variables at once
(equations of the form ``y1, y2 = (expr1, expr2);``) in either the initializations or the frame block body. 

Restrictions
^^^^^^^^^^^^
A frame block cannot be nested within an if statement or another frame block, as
demonstrated in the following examples:

.. code-block:: none

   if condition
   then
      frame ( y1, y2 )
      y1 = init1; y2 = init2;
      let
         y1 = 10;
      tel
   fi
   
.. code-block:: none

   frame ( y1, y2 )
   y1 = init1; y2 = init2;
   let
      y1 = expr1;
      frame ( y2 )
      y2 = init3;
      let
         y2 = expr2;
      tel
   tel

Assertions, ``MAIN`` annotations, and ``PROPERTY`` annotations also
cannot be placed within if statements or frame blocks.