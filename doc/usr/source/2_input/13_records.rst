.. _2_input/13_records:

Records
=======

A record type groups a fixed set of named *fields*, each with its own type.
Record types are introduced as type aliases, listing the fields between curly
braces and separating them with semicolons:

.. code-block:: none

   type rat = { n: real; d: real };

A record value is constructed by giving a value to each field, using the type
name followed by the field assignments (note that fields are assigned with
``=``):

.. code-block:: none

   r = rat { n = 1.0; d = 2.0 };

The field ``f`` of a record ``r`` is accessed with the dot syntax ``r.f``. For
instance, ``r.n`` evaluates to ``1.0`` for the record ``r`` above.

Element update
--------------

A new record that is identical to an existing one except at selected fields can
be constructed with the *element update* syntax ``r[f := v]``. It denotes a copy
of the record ``r`` in which field ``f`` is replaced by ``v``; the original
record ``r`` is not modified. For example,

.. code-block:: none

   type rat = { n: real; d: real };
   node x (r: rat) returns (y: rat)
   let
     y = r[n := r.n * 2.0];
   tel

defines ``y`` to be equal to ``r`` except that its ``n`` field is doubled.
Several fields can be updated at once by separating the individual updates with
semicolons, as in ``r[n := 1.0; d := 2.0]``.
