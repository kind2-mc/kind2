.. _2_input/3_machine_ints:


Refinement Types
================

Kind 2 supports refinement types. A refinement type is comprised of two components: 
(i) a __base type__, and
(ii) a predicate that restricts the members of the base type.

Declarations
------------

Refinement types can be declared with the syntax ``subtype { var: base_type | P(var) }``. 

For example, the following

.. code-block::

   type Nat = subtype { x: int | x >= 0 };

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

The base type being refined can be __any__ type, not just a primitive type. 
For example,

.. code-block::

   type Nat = subtype { x: int | x >= 0 };
   type LessThan100 = { x: Nat | x < 100 };

declares a refinement type ``LessThan100`` whose base type ``Nat`` is itself a refinement type.

Additionally, refinement types can be components of more complicated types.

.. code-block::

   const n: int;
   type Nat = subtype { x: int | x >= 0 };
   type NatArray = Nat^n;

Above, we declare a type ``NatArray``, an array of natural numbers.

Since Lustre is a declarative language, there is no conceptual ordering between sets of input,
output, and local variables. A consequence of this is that refinement type predicates can 
contain variables that are defined before or after the current variable in the input file.
For example, the following is legal.

.. code-block::

   node N() returns (x: | x <= y; y | y = x + 10);

Above, the predicate in ``x``'s type references ``y``, which is allowed even though 
``y`` comes after ``x`` in the list of node outputs. 
This is analogous to the fact that ordering of node equations and contract elements 
does not matter.

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

When Kind 2 is called on node ``M``, it attempts to prove that ``y`` respects type ``Odd``
while assuming that ``x1`` has type ``Even`` and ``x2`` has type ``Odd``.
Conceptually, the refinement types can be viewed as an augmentation of
``M``'s contract as follows:

.. code-block::
   node M(x1: Even; x2: Odd) returns (y: Odd);
   (*@contract
      assume x1 mod 2 = 0; 
      assume x2 mod 2 = 1;
      guarantee y mod 2 = 1;
   *)
   let
      y = x1 + x2;
      --%MAIN;
   tel

Above, Kind 2 will prove that ``y`` respects its refinement type (intuitively, Kind 2 will prove
that adding an even and an odd integer will result in an odd integer). 

Note that refinement type variables can be arguments to any operation supported 
by their base type. For example, the above expression ``x1 + x2`` is well-typed
because ``x1`` and ``x2`` both have a base type of ``int``, and ``+`` 
is well-defined for integers. 

If the base type of a refinement type is 
nested within other types, then base primitive types are recursively 
computed. For example, if ``x`` has type 
``subtype { n: subtype { m: int | m > 0 } | n < 5 }``,
then ``x + x`` is well-typed because ``x``'s base type is ``int``.

If an output variable with a refinement type is left undefined, Kind 2 will specify that the value 
ranges over its __base__ type.

  .. code-block::
   node M() returns (y: Nat);
   let
   tel

In the above example, ``M``'s return value ``y`` will range over all integers, 
not just natural numbers. This is because ``y`` is an output variable,
and therefore its refinement type is viewed as a proof obligation. 
In this case, Kind 2 will report that ``y`` violates its refinement type predicate. 

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
For example, in node call previously discussed ``M(z)``
(where ``z`` has type ``int`` and ``M`` takes a single parameter of type ``Nat``),
``M``'s typing assumption on its input will be violated if ``z`` is undefined. 

Realizability
----------

Because refinement types are essentially contract augmentations, it is possible to specify 
refinement types that are __unrealizable__. In other words, it is possible 
to specify refinement type contraints that are unimplementable (impossible to satisfy with any implementation).

As an example, the following node interface is unrealizable:
  .. code-block::
   node M(x: int) returns (y: int | 0 <= y and y <= x);

Output variable ``y``'s refinement type states that ``y`` must be between 0 and ``x``.
However, if input ``x`` is negative, then no value for ``y`` will satisfy its type.

One way to make the above interface realizable is to add a refinement type for ``x``:

  .. code-block::
   node M(x: int | x >= 0) returns (y: int | 0 <= y and y <= x);

To check the realizability refinement types, one can call ``kind2 <filename> --enable CONTRACTCK``.
Kind 2 performs four types of realizability checks:

1. Imported node contracts, including type information
2. Implemented (normal) node contracts, including type information
3. Implemented (normal) node environments, i.e., checking that the set of assumptions on a node's input is realizable
4. Individual refinement types, i.e., that a global refinement type declaration is realizable

Restrictions
------

Currently, global constants with refinement types (like the following example) are not supported.

.. code-block::

   const n: int | n >= 0;






