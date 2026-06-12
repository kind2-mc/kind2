Subrange types
==============

Subrange types are types of the form ``subrange [LB, UB] of int`` denoting user-specified integer ranges,
where ``LB`` and ``UB`` are the lower and upper bound (respectively) of the range (inclusive).
In the simplest case, both bounds are concrete integer literals; for example,
``subrange [0, 10] of int`` denotes the type of streams of integers in the range ``0`` through ``10``,
inclusive. Bounds may also be symbolic constant expressions (see `Symbolic bounds`_ below).

Subranges may be unbounded on one side, denoted by using a ``*`` in lieu of a concrete integer for either the upper 
or lower bound (but not both). For example, ``subrange [0, *] of int`` denotes the type of streams of 
nonnegative integers, while ``subrange [*, -1] of int`` denotes the type of streams of negative integers. 

Subrange types can be viewed as particular instances of refinement types: 
a subrange type on an input variable or free constant can be viewed as an assumption, 
while a subrange type on an output variable, local variable, or defined constant can be viewed as a proof obligation.
For example, consider the following Kind 2 input.

.. code-block::

   type Pos = subrange [1, *] of int;
   type Neg = subrange [*, -1] of int;
   const C: Pos;

   node N(arr: int^C; x: Pos) returns (out: Neg)
   let
     out = x - arr[0];
   tel

Above, ``C`` and ``x`` are assumed to be positive integers.
However, Kind 2 will generate a proof obligation that ``out`` is negative,
which fails.

Symbolic bounds
---------------

The bounds ``LB`` and ``UB`` need not be concrete integer literals: each may also
be a *symbolic* constant expression of type ``int``, that is, an expression built
from integer constants. For example, given a constant ``N``, both
``subrange [0, N] of int`` and ``subrange [1, N-1] of int`` are valid subrange
types. This is convenient, for instance, to describe the valid indices of an
array whose length is a symbolic constant.

.. code-block::

   const N: int;
   type Index = subrange [0, N-1] of int;

   node M(a: int^N; i: Index) returns (out: int)
   let
     out = a[i];
   tel

When both bounds are concrete integers, Kind 2 checks at compile time that ``LB``
does not exceed ``UB``, rejecting the type otherwise. When at least one bound is
symbolic, this check cannot be carried out statically. Instead, following the
refinement-type view described above, the range constraint becomes an
*assumption* when the symbolic subrange types an input or free constant, and a
*proof obligation* when it types an output, local variable, or defined constant.
