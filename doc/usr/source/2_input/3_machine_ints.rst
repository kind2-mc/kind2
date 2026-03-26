.. _2_input/3_machine_ints:


Machine Integers
================

Kind2 supports both signed and unsigned versions of C-style machine integers. 

Declarations
------------

Machine integer variables can be declared as global, local, or as input/ouput of nodes. Signed machine integers are declared as type ``sint<N>`` and unsigned machine integers are declared as type ``uint<N>`` where ``N`` is the width (some concrete positive integer).

The following

.. code-block::

   x : uint<8>;
   y : sint<17>;

declares a variable ``x`` of type unsigned machine integer of width 8, and variable ``y`` of type signed machine integer of width 17.

Values
------

Machine integers values can be constructed using implicit conversion functions applied to integer literals. The implicit conversion functions are of the form ``uint@<N>`` for unsigned machine integers and ``sint@<N>`` for signed machine integers.

The following

.. code-block::

   x = uint@<8> 27;
   y = sint@<17> -5012;

defines ``x`` to have value ``27``, and ``y`` to have value ``-5012``, given that ``x`` is a variable of type ``uint<8>`` and ``y`` is a variable of type ``sint@<17>``.

Semantics
---------

Machine integers of width ``x`` represent binary numbers of size ``x``.
Signed machine integers are represented using 2's complement.

The bounds of selected machine integers are specified here for convenience:

.. code-block::

   uint<8>  : 0 to 255
   uint<16> : 0 to 65535
   uint<32> : 0 to 4294967295
   uint<64> : 0 to 18446744073709551615
   sint<8>   : -128 to 127
   sint<16>  : -32768 to 32767
   sint<32>  : -2147483648 to 2147483647
   sint<64>  : -9223372036854775808 to 9223372036854775807

When the conversion functions are used for literals that are out of this range, they are converted to a machine integer that is in range using the modulo operation, as in C. For instance, in the following

.. code-block::

   x = uint<8> 256;
   y = sint<16> 32768;

``x`` evaluates to ``0`` and ``y`` to ``-3268``, given that ``x`` is a variable of type ``uint<8>`` and ``y`` is a variable of type ``sint<16>``.

Conversions are allowed between machine integers of different widths, as long as both types are either signed or unsigned. Values remain unchanged when converted from a smaller to a larger width; values are adjusted modulo the range of the destination type when converted from larger to smaller width. The following code illustrates this.

.. code-block::

   a : sint<8>;
   b : sint<16>;
   c : uint<16>;
   d : uint<8>;
   a = sint<8> 120;
   b = sint<16> a; -- b == sint<16> 120
   c = uint<16> 300;
   d = uint<8> c; -- c == uint<8> 44

Operations
----------

Kind2 allows the following operations over the machine integer types.

Arithmetic Operations
^^^^^^^^^^^^^^^^^^^^^

Addition (``+``), subtraction (``-``), multiplication (``*``), division (``div``), modulo (``mod``), and
unary negation (``-``) are allowed on either signed or unsigned machine integers, and
return a machine integer with the same sign and same width as the input(s).

.. code-block::

   a, a1, a2 : uint<8>;
   b : uint<16>;
   c : uint<32>;
   d : uint<64>;
   e, f : sint<8>;
   a1 = (uint@<8> 5);
   a2 = (uint@<8> 22);
   a = a1 + a2;
   b = (uint@<16> 20) * (uint@<16> 200);
   c = (uint@<32> 500) div (uint@<32> 5);
   d = (uint@<64> 25) mod (uint@<64> 10);
   e = (sint@<8> -5) + (- (sint@<8> 10));
   f = (sint@<8> 10) - (sint@<8> -5);

Logical Operations
^^^^^^^^^^^^^^^^^^

Conjunction (``&&``), disjunction (``||``), and negation (``!``) are performed in a bitwise fashion over the binary equivalent of their machine integer inputs.  Conjunction and disjunction are binary, while negation is unary. All 3 operations return a machine integer that has the same sign and same width as its input(s).

.. code-block::

   a, b, b1, b2, c : uint<8>;
   a = (uint@<8> 0) && (uint@<8> 45); --a = (uint@<8> 0)
   b1 = (uint@<8> 255);
   b2 = (uint@<8> 45);
   b = b1 && b2; --b = (uint@<8> 45)
   c = !(uint@<8> 0); --c = (uint@<8> 255)

Shift Operations
^^^^^^^^^^^^^^^^

Left shift (``lsh``) and right shift (``rsh``) operations are binary operations: the first input is either signed or unsigned, the second input is unsigned, and the sign of the output matches that of the first input; both inputs and the output have the same width.

Right shifting when the first operand is signed, results in an arithmetic right shift, where the bit shifted in matches the sign bit. 

A left shift is equivalent to multiplication by 2, and a right shift is equivalent to division by 2, as long as the result can fit into the machine integer of the same width. In other words, the left shift operator shifts towards the most-significant bit and the right shift operator shifts towards the least-significant bit.

.. code-block::

   a, b, c : bool;
   a = (uint@<8> 0) lsh (uint@<8> 10) = (uint@<8> 0); --true
   b = (uint@<8> 255) rsh (uint@<8> 12) = (uint@<8> 255); --true
   c = (sint@<8> -1) lsh (uint@<8> 1) = (sint@<8> -2); --true

Comparison Operations
^^^^^^^^^^^^^^^^^^^^^

The following comparison operations are all binary: ``>``, ``<``, ``>=``, ``<=``, ``=``.  They input machine integers of the same size and sign, and output a boolean value.

.. code-block::

   a : bool;
   a = (sint@<8> -12) < (sint@<8> 12); --true

Cast Operations
^^^^^^^^^^^^^^^

In addition to casts to signed and unsigned integers, signed and unsigned integers can also be casted to mathematical integers
with the ``int`` cast operator.

.. code-block::

   a : sint<8>;
   b : uint<8>;
   c : int;
   d : int;
   c = int a;
   d = int b;

Concise Syntax
^^^^^^^^^^^^^^

For signed and unsigned machine integers of widths 8, 16, 32, and 64, we support the concise syntax of ``intN``
for signed integers and ``uintN`` for unsigned integers (where ``N`` is 8, 16, 32, or 64). 
This syntax works for both types and cast operators.

.. code-block::
  
   a : int8;
   b : uint8;
   a = int8 0;
   b = uint8 0;

Limitations
-----------

Currently, only SMT solvers cvc5 and Z3 support logics that allows
the usage of integers and machine integers together. To use any of
the other supported SMT solvers, the Lustre input must contain only
machine integers.

Moreover, the IC3QE engine requires either cvc5 or Z3,
and the IC3IA engine requires MathSAT, cvc5, or Z3,
to run on models with machine integers.
If these requirements are not satisfied,
Kind 2 runs with the corresponding IC3 model checking engine disabled.

