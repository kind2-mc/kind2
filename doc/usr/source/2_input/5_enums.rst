Enumeration types
==================

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
