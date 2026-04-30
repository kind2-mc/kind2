Subrange types
==============

Subrange types are types of the form ``subrange [LB, UB] of int`` denoting user-specified integer ranges, 
where ``LB`` and ``UB``, both integers, are the lower and upper bound (respectively) of the range (inclusive).
For example, ``subrange [0, 10] of int`` denotes the type of streams of integers in the range ``0`` through ``10``, 
inclusive.

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
