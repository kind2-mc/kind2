Enumeration types
==================

Tuples are constructed with the syntax ``'(x1, ..., xn)`` and destructed with the syntax ``t[idx]``, 
where ``idx`` is some concrete natural number that is in range (with ``0``-based indexing).

.. code-block:: none

   type my_tuple = [int, bool, real];
   node n (x : my_tuple) returns (y1 : my_tuple) 
   let
     y1 = '(0, false, x[2]);
   tel

