.. _2_input/3_machine_ints:


Machine Integers
================

Kind2 supports both signed and unsigned versions of C-style machine integers of width 8, 16, 32, and 64. 

Declarations
------------

Machine integer variables can be declared as global, local, or as input/ouput of nodes. Signed machine integers are declared as type ``intN`` and unsigned machine integers are declared as type ``uintN`` where N is the width (8, 16, 32, or 64).

The following

.. code-block::

   x : uint8;
   y : int16;

declares a variable ``x`` of type unsigned machine integer of width 8, and variable ``y`` of type signed machine integer of width 16.

Values
------

Machine integers values can be constructed using implicit conversion functions applied to integer literals. The implicit conversion functions are of the form ``uintN`` for unsigned machine integers and ``intN`` for signed machine integers.

The following

.. code-block::

   x = uint8 27;
   y = int16 -5012;

defines ``x`` to have value ``27``, and ``y`` to have value ``-5012``, given that ``x`` is a variable of type ``uint8`` and ``y`` is a variable of type ``int16``.

Semantics
---------

Machine integers of width ``x`` represent binary numbers of size ``x``.
Signed machine integers are represented using 2's complement.

The bounds of machine integers are specified here for convenience:

.. code-block::

   uint8  : 0 to 255
   uint16 : 0 to 65535
   uint32 : 0 to 4294967295
   uint64 : 0 to 18446744073709551615
   int8   : -128 to 127
   int16  : -32768 to 32767
   int32  : -2147483648 to 2147483647
   int64  : -9223372036854775808 to 9223372036854775807

When the conversion functions are used for literals that are out of this range, they are converted to a machine integer that is in range using the modulo operation, as in C. For instance, in the following

.. code-block::

   x = uint8 256;
   y = int16 32768;

``x`` evaluates to ``0`` and ``y`` to ``-3268``, given that ``x`` is a variable of type ``uint8`` and ``y`` is a variable of type ``int16``.

Conversions are allowed between machine integers of different widths, as long as both types are either signed or unsigned. Values remain unchanged when converted from a smaller to a larger width; values are adjusted modulo the range of the destination type when converted from larger to smaller width. The following code illustrates this.

.. code-block::

   a : int8;
   b : int16;
   c : uint16;
   d : uint8;
   a = int8 120;
   b = int16 a; -- b == int16 120
   c = uint16 300;
   d = uint8 c; -- c == uint8 44

Operations
----------

Kind2 allows the following operations over the machine integer types.

Arithmetic Operations
^^^^^^^^^^^^^^^^^^^^^

Addition (``+``), multiplication (``*``), division (``div``), and modulo (``mod``) are binary arithmetic operations, allowed on either signed or unsigned machine integers, and return a machine integer with the same sign and same width as both inputs.

Unary negation (``-``), and binary subtraction (``-``) are allowed only on signed machine integers and return a signed machine integer with the same width as the input(s).

.. code-block::

   a, a1, a2 : uint8;
   b : uint16;
   c : uint32;
   d : uint64;
   e, f : int8;
   a1 = (uint8 5);
   a2 = (uint8 22);
   a = a1 + a2;
   b = (uint16 20) * (uint16 200);
   c = (uint32 500) div (uint32 5);
   d = (uint64 25) mod (uint64 10);
   e = (int8 -5) + (- (int8 10));
   f = (int8 10) - (int8 -5);

Logical Operations
^^^^^^^^^^^^^^^^^^

Conjunction (``&&``), disjunction (``||``), and negation (``!``) are performed in a bitwise fashion over the binary equivalent of their machine integer inputs.  Conjunction and disjunction are binary, while negation is unary. All 3 operations return a machine integer that has the same sign and same width as its input(s).

.. code-block::

   a, b, b1, b2, c : uint8;
   a = (uint8 0) && (uint8 45); --a = (uint8 0)
   b1 = (uint8 255);
   b2 = (uint8 45);
   b = b1 && b2; --b = (uint8 45)
   c = !(uint8 0); --c = (uint8 255)

Shift Operations
^^^^^^^^^^^^^^^^

Left shift (``lsh``) and right shift (``rsh``) operations are binary operations: the first input is either signed or unsigned, the second input is unsigned, and the sign of the output matches that of the first input; both inputs and the output have the same width.

Right shifting when the first operand is signed, results in an arithmetic right shift, where the bit shifted in matches the sign bit. 

A left shift is equivalent to multiplication by 2, and a right shift is equivalent to division by 2, as long as the result can fit into the machine integer of the same width. In other words, the left shift operator shifts towards the most-significant bit and the right shift operator shifts towards the least-significant bit.

.. code-block::

   a, b, c : bool;
   a = (uint8 0) lsh (uint8 10) = (uint8 0); --true
   b = (uint8 255) rsh (uint8 12) = (uint8 255); --true
   c = (int8 -1) lsh (uint8 1) = (int8 -2); --true

Comparison Operations
^^^^^^^^^^^^^^^^^^^^^

The following comparison operations are all binary: ``>``, ``<``, ``>=``, ``<=``, ``=``.  They input machine integers of the same size and sign, and output a boolean value.

.. code-block::

   a : bool;
   a = (int8 -12) < (int8 12); --true

Options
-------

Currently, the Yices2 SMT solver doesn't support logics that will allow for the usage of integers and machine integers together.  When using machine integers in Lustre, Kind2 will throw an error if it is called to use the Yices or Yices2 SMT solvers. To tell Kind2 to explicitly use a particular solver, call it with the option ``--smt_solver solver``, where solver can be 
``CVC4`` or ``Z3``.

IC3 is enabled by default in Kind2, and IC3 methods don't support theories which deal with machine integers, so IC3 must be disabled while using Kind2 with problems containing machine integers. This is done using the option ``--disable IC3``.
