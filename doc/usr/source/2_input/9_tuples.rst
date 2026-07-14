Tuples
======

Tuples are constructed with the syntax ``'(x1, ..., xn)`` and destructed with the syntax ``t[idx]``, 
where ``idx`` is some concrete natural number that is in range (with ``0``-based indexing).

.. code-block:: none

   type my_tuple = [int, bool, real];
   node n (x : my_tuple) returns (y : my_tuple)
   let
     y = '(0, false, x[2]);
   tel

.. note::

   This syntax changed after Kind 2 v2.3.0. In v2.3.0 and earlier, tuples were
   constructed with curly braces, ``{x1, ..., xn}``, and a component was accessed
   with the ``.%`` operator, as in ``t.%idx`` (with ``0``-based indexing); nested
   accesses were chained, as in ``t.%1.%0``. For example, the definition
   ``y = '(0, false, x[2]);`` above would previously have been written
   ``y = {0, false, x.%2};``.

   The change was motivated by the introduction of :doc:`set data types <10_sets>`:
   the ``{...}`` notation is now used for set constructors.

Element update
--------------

A new tuple that is identical to an existing one except at selected positions
can be constructed with the *element update* syntax ``t[idx := v]``. It denotes
a copy of the tuple ``t`` in which the component at position ``idx`` is replaced
by ``v``; the original tuple ``t`` is not modified. As with destruction, ``idx``
must be a concrete natural number that is in range (with ``0``-based indexing).

.. code-block:: none

   type MyPair = [int, bool];
   node n (p1 : MyPair) returns (p2 : MyPair)
   let
     p2 = p1[1 := true];
   tel

Here ``p2`` is equal to ``p1`` except that its second component (index ``1``) is
``true``. Several components can be updated at once by separating the individual
updates with semicolons, as in ``p1[0 := 0; 1 := false]``.

