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

