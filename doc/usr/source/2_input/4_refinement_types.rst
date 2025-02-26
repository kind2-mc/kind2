.. _2_input/4_refinement_types:


Refinement Types
================

Kind 2 supports refinement types. A refinement type is comprised of two components: 
(i) a **base type**, and
(ii) a predicate that restricts the members of the base type.

Declarations
------------

Refinement types have syntax of the form ``subtype { var: base_type | P(var) }``. 

For example, ``type Nat = subtype { x: int | x >= 0 }``
declares a refinement type ``Nat`` over the base type ``int``, 
where the values of ``Nat`` are all the nonnegative integers.
When assigning a refinement type to a node input, output, or local variable, Kind 2 also 
supports an alternative, more concise syntax of the form ``var: base_type | P(var)``. 

For example,

.. code-block::

   node N(x: int | x >= 0) returns (y: int | y >= 0);

denotes the interface of a node ``N`` which takes a stream of natural numbers ``x`` as input
and returns a stream of natural numbers ``y`` as output. 
The above example can be equivalently expressed using the full syntax:

.. code-block::

   node N(x: subtype { n: int | n >= 0 }) returns (y: subtype { n: int | y >= 0});

The base type being refined can be *any* type, not just a primitive type. 
For example,

.. code-block::

   type Nat = subtype { x: int | x >= 0 };
   type LessThan100 = { x: Nat | x < 100 };

declares a refinement type ``LessThan100`` whose base type ``Nat`` is itself a refinement type.
Note that we can still recursively chase base types until we reach a primitive type.
In this case, ``LessThan100``'s recursively chased primitive base type is ``int``.

Additionally, refinement types can be components of more complicated types:

.. code-block::

   const n: int;
   type Nat = subtype { x: int | x >= 0 };
   type NatArray = Nat^n;

Above, we declare a type ``NatArray``, an array of natural numbers.

Since Lustre is a declarative language, there is no conceptual ordering between variable declarations
(input, output, and local variables). A consequence of this is that refinement type predicates can 
contain variables that are defined before *or after* the current variable in the input file.
For example, the following is legal.

.. code-block::

   node N() returns (x: | x <= y; y | y = x + 10);

Above, the predicate in ``x``'s type references ``y``, which is allowed even though 
``y`` comes after ``x`` in the list of node outputs. 

Semantics
---------

Refinement types on input variables represent assumptions, while refinement types on 
locals and node outputs represent proof obligations. 

Consider the following example:

.. code-block::

   type Even = subtype { n: int | n mod 2 = 0 };
   type Odd = subtype { n: int | n mod 2 = 1 };

   node M(x1: Even; x2: Odd) returns (y: Odd);
   let
      y = x1 + x2;
      --%MAIN;
   tel

Kind2 will attempt to prove that node ``M``'s output ``y`` respects type ``Odd``
while assuming that input ``x1`` has type ``Even`` and input ``x2`` has type ``Odd``.
More intuitively, Kind 2 will prove
that adding an even and an odd integer results in an odd integer. 
Conceptually, the refinement types can be viewed as an augmentation of
``M``'s contract as follows:

.. code-block::

   node M(x1: int; x2: int) returns (y: int);
   (*@contract
      assume x1 mod 2 = 0; 
      assume x2 mod 2 = 1;
      guarantee y mod 2 = 1;
   *)
   let
      y = x1 + x2;
      --%MAIN;
   tel

If an output variable with a refinement type is left undefined, Kind 2 will specify that the value 
ranges over a recursively chased base type.

.. code-block::

   node M() returns (y: Nat | y < 100);
   let
   tel

In the above example, ``M``'s return value ``y`` will range over *all integers*, 
not just natural numbers less than 100. This is because ``y`` is an output variable,
and therefore its refinement type is viewed as a proof obligation. 
In this case, Kind 2 will report that ``y`` violates its refinement type. 

Operations
----------

From the point of view of primitive operations (e.g. ``+``, ``-``, ``pre``) and node 
calls, variables with refinement types can syntactically be used anywhere that variables with the 
corresponding base type can be used, and vice versa. 
For example, if ``x`` has type ``Nat``, ``y`` has type ``Nat``, and ``z`` has type
``int``, then ``x+y``, ``z+x``, and ``y+z`` (among other combinations) are all legal. 
Further, if node ``M`` has a single parameter of type ``Nat``, then 
the node call ``M(z)`` is legal, and if node ``N`` has a single parameter 
of type ``int``, then the node call ``M(x)`` is legal. 

While all of the above are syntactically valid, 
Kind 2 may still fail type-related proof obligations. 
For example, in the node call ``M(z)``
(where ``z`` has type ``int`` and ``M`` takes a single parameter of type ``Nat``),
``M``'s typing assumption on its input will be violated if ``z`` can be negative. 

Realizability
-------------

Because refinement types are essentially contract augmentations, it is possible to specify 
refinement types that are *unrealizable*. In other words, it is possible 
to specify refinement type contraints that are unimplementable (impossible to satisfy with any implementation).

As an example, the following node interface is unrealizable:

.. code-block::

   node M(x: int) returns (y: int | 0 <= y and y <= x);

Output variable ``y``'s refinement type states that ``y`` must be between ``0`` and ``x``.
However, if input ``x`` is negative, then no value for ``y`` will satisfy its type.

One way to make the above interface realizable is to add a refinement type for ``x``:

.. code-block::

   node M(x: int | x >= 0) returns (y: int | 0 <= y and y <= x);

To check the realizability refinement types, one can call ``kind2 <filename> --enable CONTRACTCK``.
Kind 2 performs three types of realizability checks:

1. Node and imported node contracts, including type information
2. Node environments, i.e., checking that the set of assumptions on a node's input is realizable
3. Individual refinement types, i.e., that a global refinement type declaration is realizable

You can specify a particular node or function to analyze using 
``--lus_main <node_name>``, and a specific refinement type using 
``--lus_main_type <type_name>``.

Restrictions
------------

Definitions of global constants with refinement types (as shown in the following example)
are **not** supported:

.. code-block::

   const n: subtype { x : int | x >= 0 } = 3;

However, declarations of free global constants (a.k.a system parameters) are supported:

.. code-block::

   const n: subtype { x : int | x >= 0 };
