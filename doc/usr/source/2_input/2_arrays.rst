.. _2_input/2_arrays:

Arrays
======

..

   **Experimental feature**


Lustre arrays
-------------

Kind 2 supports the traditional Lustre V5 syntax for arrays.

Declarations
^^^^^^^^^^^^

Array variables can be declared as global, local or as input/output of
nodes. Arrays in Lustre are always indexed by integers (type ``int`` in Lustre),
and the type of an array variable is written with the syntax ``t ^ <size>`` where
``t`` is a Lustre type and ``<size>`` is an integer literal or a constant symbol.

The following

.. code-block:: none

   A : int ^ 3;

declares an array variable ``A`` of type array of size 3 whose elements
are integers. The size of the array can also be given by a defined constant.

.. code-block:: none

   const n = 3;
   ...
   A : int ^ n;

This declaration is equivalent to the previous one for ``A``.

An interesting feature of these arrays is the possibility for users to write
generic nodes and functions that are parametric in the size of the array. For
instance one can write the following node returns the last element of an array.

.. code-block:: none

   node last (const n: int; A: int ^ n) returns (x: int);
   let
     x = A[n-1];
   tel

It takes as input the size of the array and the array itself. Note that the
type of the input ``A`` depends on the value of the first constant input ``n``. In
Lustre, calls to such nodes should of course end up by having concrete values
for ``n``, this is however not the case in Kind 2 (see
:ref:`extension_to_unbounded_arrays`).

Arrays can be multidimensional, so a user can declare *e.g.* matrices with the
following

.. code-block:: none

   const n = 4;
   const m = 5;
   ...

   M1 : bool ^ n ^ m;
   M2 : int ^ 3 ^ 3;

Here ``M1`` is a matrix of size 4x5 whose elements are Boolean, and ``M2`` is a
square matrix of size 3x3 whose elements are integers.

..

   **Remark**

   ``M1`` can also be viewed as an array of arrays of Booleans.


Kind 2 also allows one to nest datatypes, so it is possible to write arrays of
records, records of arrays, arrays of tuples, and so on.

.. code-block:: none

   type rational = { n: int; d: int };

   rats: rational^array_size;
   mm: [int, bool]^array_size;

In this example, ``rats`` is declared as an array of record elements and ``mm`` is
an array of pairs.

Definitions
^^^^^^^^^^^

In the body of nodes or at the top-level, arrays can be defined with literals
of the form

.. code-block:: none

   A = [2, 5, 7];

This defines an array ``A`` of size 3 whose elements are 2, 5 and 7. Another way
to construct Lustre arrays is to have each elements be the same value. This can
be done with expressions of the form ``<value> ^ <size>``. For example the two
following definitions are equivalent.

.. code-block:: none

   A = 2 ^ 3;
   A = [2, 2, 2];

Arrays are indexed starting at 0 and the elements can be accessed using the
selection operator ``[ ]``. For instance the result of the evaluation of the
expression ``A[0]`` for the previously defined array ``A`` is 2.

The selection operators can also be applied to multidimensional arrays.
Given a matrix ``M`` defined by

.. code-block:: none

   M = [[1, 2, 3],
        [4, 5, 6],
        [7, 8, 9]];

then the expression ``M[1][2]`` is valid and evaluates to 6. The result of a
single selection on an *n*\ -dimensional array is an *(n-1)*\ -dimensional
array. The result of ``M[2]`` is the array ``[7, 8, 9]``.

Unsupported features of Lustre V5
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Kind 2 currently **does not support** the following features of `Lustre
V5 <http://www.di.ens.fr/~pouzet/cours/mpri/manual_lustre.ps>`_\ :


* 
  Array concatenation like ``[0, 1] | [2, 3, 4]``

* 
  Array slices like ``A[0..3]``\ , ``A[0..3 step 2]``\ , ``M[0..1][1..2]`` or
  ``M[0..1, 1..2]``

* 
  The operators are not homomorphically extended. For instance ``or`` has type
  ``bool -> bool -> bool``\ , given two arrays of Booleans ``A`` and ``B``\ , the
  expression ``A or B`` will be rejected at typing by Kind 2

* 
  Node calls don't have an homomorphic extension either


.. _extension_to_unbounded_arrays:

Extension to unbounded arrays
-----------------------------

Kind 2 provides an extension of Lustre to express equational constraints
between unbounded arrays. This syntax extension allows users to inductively
define arrays, give whole array definitions and allows to encode most of the
other unsupported array features. This extension was originally suggested by
`Esterel <http://www.esterel-technologies.com>`_.

..

   **Remark**

   Here, by *unbounded* we mean whose size is an unbounded constant.


In addition, we also enriched the specification language of Kind 2 to support
(universal and existential) quantifiers, allowing one to effectively model
*parameterized* system.

Whole array definitions
^^^^^^^^^^^^^^^^^^^^^^^

Equations in the body of nodes can now take the following forms


* 
  ``A = <term> ;`` This equation defines the values of the array ``A`` to be the same
  as the values of the array expression ``<term>``.

* 
  ``A[i] = <term(i)> ;`` This equation defines the values of all elements in the
  array ``A``. The index ``i`` has to be a symbol, it is bound locally to the
  equation and shadows all other mentions of ``i``. Index variables that appear
  on the left hand side of equations are **implicitly universally
  quantified**. The right hand side of the equation, ``<term(i)>`` can depend on
  this index. The meaning of the equation is that, for any integer ``i`` between
  0 and the size of ``A``\ , the value at position ``i`` is defined as the term
  ``<term(i)>``.

Semantically, a whole array equation is equivalent to a quantified
equation. Let ``A`` be an array of size an integer constant ``n``\ , then following 
equation is legal.

.. code-block:: none

   A[i] = if i = 0 then 2 else B[i - 1] ;

It is equivalent to the formula
*∀ i ∈ [0; n]. ( i = 0 ⇒ A[i] = 2 )  ⋀ ( i ≠ 0 ⇒ A[i] = B[i-1] )*.

Multidimensional arrays can also be redefined the same way. For instance the
equation

.. code-block:: none

   M[i][j] = if i = j then 1 else 0 ;

defines ``M`` as the identity matrix

.. code-block:: none

   [[ 1 , 0 , 0 ,..., 0 ],
    [ 0 , 1 , 0 ,..., 0 ],
    [ 0 , 0 , 1 ,..., 0 ],
    .................... ,
    [ 1 , 0 , 0 ,..., 1 ]]

It is possible to write an equation of the form

.. code-block:: none

   M[i][i] = i;

but in this case the second index ``i`` shadows the first one, hence the
definition is equivalent to the following one where the indexes have been
renamed.

.. code-block:: none

   M[j][i] = i;

Inductive definitions
^^^^^^^^^^^^^^^^^^^^^

One interesting feature of these equations is that we allow definitions of
arrays *inductively*. For instance it is possible to write an equation

.. code-block:: none

   A[i] = if i = 0 then 0 else A[i-1] ;

This is however not very exciting because this is the same as saying that ``A``
will contain only zeros, but notice we allow the use of ``A`` in the right hand
side.

Dependency analysis
~~~~~~~~~~~~~~~~~~~

Inductive definitions are allowed under the restriction that they should be
*well founded*. For instance, the equation

.. code-block:: none

   A[i] = A[i];

is not and will be rejected by Kind 2 the same way the equation ``x = x;`` is
rejected. Of course this restriction does not apply for array variables under a
``pre``\ , so the equation ``A[i] = pre A[i];`` is allowed.

In practice, Kind 2 will try to prove statically that the definitions are
well-founded to ensure the absence of dependency cycles. We only attempt to
prove that definitions for an array ``A`` at a given index ``i`` depends on on
values of ``A`` at indexes strictly smaller than ``i``.

For instance the following set of definitions is rejected because *e.g.* ``A[k]``
depends on ``A[k]``.

.. code-block:: none

   A[k] = B[k+1] + y;
   B[k] = C[k-1] - 2;
   C[k] = A[k] + k;

On the other hand this one will be accepted.

.. code-block:: none

   A[k] = B[k+1] + y;
   B[k] = C[k-1] - 2;
   C[k] = ( A[k-1] + B[k] ) * k ;

Because the order is fixed and that the checks are simple, it is possible that
Kind 2 rejects programs that are well defined (with respect to our semantic for
whole array updates). It will not, however, accept programs that are
ill-defined.

For instance each of the following equations will be rejected.

.. code-block:: none

   A[i] = if i = 0 then 0 else if i = 1 then A[0] else A[i-1];

.. code-block:: none

   A[i] = if i = n then 0 else A[i+1];

.. code-block:: none

   A[i] = if i = 0 then 0 else A[0];

Examples
~~~~~~~~

This section gives some examples of usage for inductive definitions and whole
array updates as a way to encode unsupported features and as way to encode
complicated functions succinctly.

Sum of the elements in an array
"""""""""""""""""""""""""""""""

The following node returns the sum of all elements in an array.

.. code-block:: none

   node sum (const n: int; A: int ^ n) returns (s: int);
   var cumul: int ^ n;
   let
     cumul[i] = if i = 0 then A[0] else A[i] + cumul[i-1];
     s = cumul[n-1];
   tel

We declare a local array ``cumul`` to store the cumulative sum (\ *i.e.* ``cumul[i]``
contains the sum of elements in ``A`` up to index ``i``\ ) and the returned value of
the node is the element stored in the last position of ``cumul``.

Note that this node is parametric in the size of the array.

Array slices
""""""""""""

Array slices can be trivially implemented with the features presented above.

.. code-block:: none

   node slice (const n: int; A: int ^ n; const low: int; const up: int)
   returns (B : int ^ (up-low));
   let
     B[i] = A[low + i];
   tel

Homomorphic extensions
""""""""""""""""""""""

Encoding an homomorphic ``or`` on Boolean arrays is even simpler.

.. code-block:: none

   node or_array (const n: int; A, B : bool^n) returns (C: bool^n);
   let
     C[i] = A[i] or B[i];
   tel

Defining a generic homomorphic extension of node calls is not possible because
nodes are not first order objects in Lustre.

Parameterized systems
"""""""""""""""""""""

It is possible to describe and check properties of parameterized
systems. Contrary to the Lustre compilers, Kind 2 does not require the
constants used as array sizes to be instantiated with actual values. In this
case the properties are checked *for any* array sizes.

.. code-block:: none

   node slide (const n:int; s: int) returns(A: int^n);
   let
     A[i] = if i = 0 then s else (-1 -> pre A[i-1]);

     --%PROPERTY n > 1 => (true -> A[1] = pre s);
   tel

This node stores in an array ``A`` a *sliding window* over an integer stream
``s``. It saves the values taken by ``s`` up to ``n`` steps in the past, where ``n`` is
the size of the array.

Here the property says, that if the array ``A`` has at least two cells then its
second value is the previous value of ``s``.

Quantifiers in specifications
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

To better support parameterized systems or systems with large arrays, we expose
quantifiers for use in the language of the specifications. Quantifiers can
thus appear in **properties**\ , **contracts** and **assertions**.

Universal quantification is written with:

.. code-block:: none

   forall ( <x : type>;+ ) P(<x>+)

where ``x`` are the quantified variables and ``type`` is their type. ``P`` is a
formula or a predicate in which the variable ``x`` can appear.

For example, the following

.. code-block:: none

   forall (i, j: int) 0 <= i and i < n and 0 <= j and j < n => M[i][j] = M[j][i]

is a formula that specifies that the matrix ``M`` is symmetric.

..

   **Remark**

   Existential quantification takes the same form except we use
   ``exists`` instead of ``forall``.


Quantifiers can be arbitrarily nested and alternated at the propositional level.

Example
~~~~~~~

The same parameterized system of a sliding window, slightly modified to express
the property that ``A`` contains in each of its cells, an uninitialized value
(\ *i.e.* value ``-1``\ ), or one of the previous values of the stream ``s``.

.. code-block:: none

   node slide (const n:int; s: int) returns(ok: bool^n);
   var A: int^n;
   let
     A[i] = if i = 0 then s else (-1 -> pre A[i-1]);
     ok[i] = A[i] = -1 or A[i] = s or (false -> pre ok[i]);

     --%PROPERTY forall (i: int) 0 <= i and i < n => ok[i];
   tel

Limitations
^^^^^^^^^^^

One major limitation that is present in the arrays of Kind 2 is that one cannot
have node calls in inductive array definitions whose parameters contain unbounded
array indices.

For instance, it is currently not possible to write the following in Kind 2
where ``A`` and ``B`` are arrays, ``n`` is a symbolic constant,
and ``some_node`` takes values as inputs.

.. code-block:: none

   node some_node (x: int) returns (y: int);
   ...

   A, B: int^n;
   ...

   A[i] = some_node(B[i]);

Another limitation is that quantified variables cannot appear in the parameters
of a node call.
These limitations do not apply if the call is to an *inlinable* function, which
is currently defined as a function that meets all the following criteria:

- It has a single output, and the output is defined by an equation.
- Either there is no proof obligation on its output (via a contract or a refinement type),
  or the function is annotated as transparent.
- It does not include ``assert`` statements or array definitions.


Command line options
^^^^^^^^^^^^^^^^^^^^

We provide different encodings of inductive array definitions in our internal
representation of the transition system. The command line interface exposes
different options to control which encoding is used. This is particularly
relevant for SMT solvers that have built-in features, whether it is support for
the theory of arrays, or special options or annotations for quantifier
instantiation.

These options are summed up in the following table and described in more detail
in the rest of this section.

===============    ===========
Option             Description
===============    ===========
--smt_arrays       Use the builtin theory of arrays in solvers
--inline_arrays    Instantiate quantifiers over array bounds in case they are statically known
--arrays_rec       Define recursive functions for arrays (for cvc5)
===============    ===========

The default encoding will use quantified formulas for inductive definitions and
whole array updates.

For example if we have

.. code-block:: none

   A : int^6;
   ...
   A[k] = x;

we will generate internally the constraint

   *∀ k: int. 0 <= k < 6 => (select A k) = x*

These form of constraint are handled in an efficient way by cvc5 (thanks to
finite model finding).

``--smt_arrays``
~~~~~~~~~~~~~~~~~~~~

By default arrays are converted using ah-hoc selection functions to avoid
stressing the theory of arrays in the SMT solvers. This option tells Kind 2 to
use the builtin theory of arrays of the solvers instead. If you want to try it,
it’s probably a good idea to use it in combination of ``--smtlogic detect`` for
better performances.

``--inline_arrays``
~~~~~~~~~~~~~~~~~~~~

By default, Kind 2 will generate problems with quantifiers for arrays which
should be useful for problems with large arrays. This option tells Kind 2 to
instantiate these quantifiers when it can reasonably do so. Only cvc5 has a
good support for this kind of quantification so you may want to use this option
with the other solvers.

The previous example

.. code-block:: none

   A : int^6;
   ...
   A[k] = x;

will now be encoded by the constraint

   *(select A 0) = x ⋀ (select A 1) = x ⋀ (select A 2) = x ⋀ (select A 3) = x ⋀ (select A 4) = x ⋀ (select A 5) = x*

``--arrays_rec``
~~~~~~~~~~~~~~~~~~~~

This uses a special kind of encoding to tell cvc5 to treat quantified
definitions of some uninterpreted functions as recursive definitions.
