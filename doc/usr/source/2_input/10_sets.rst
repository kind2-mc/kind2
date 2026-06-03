Sets
==================

Set types have the syntax ``set<T>``, where ``T`` is any type that does not contain 
sets, maps, or arrays. For example ``set<int>`` denotes (streams of) sets of integers, and 
``set<[bool, int]>`` denotes (streams of) sets of Boolean and integer pairs.

**Set literals** can be constructed with curly braces with comma-separated elements, 
e.g. ``{ 1 }``, ``{ 1, 2, 3 }``, and ``{ x, 4 }`` (assuming ``x`` has type ``int``).
Type annotations are *required* for empty sets (e.g. ``{}@<int>``)
and optional for non-empty set literals (e.g. ``{ 1 }@<int>``).

The built-in set operators are **set union** (denoted by ``+``), 
**set intersection** (denoted by ``*``), and 
**set difference** (denoted by ``-``), and 
**set membership** (denoted by ``in``). 
All are infix and take the expected semantics; 
see below for an example.

.. code-block:: none

   node N (s1, s2: set<int>) returns (out: set<int>) 
   let
     out = s1 * { 1, 2, 3 } + {}@<int>;

     check forall (i: int) not (i in s1 + s2) = (not (i in s1) and not (i in s2));
     check forall (i: int) i in s1 - s2 = (i in s1 and not (i in s2));
     check forall (i: int) i in out => (i = 1 or i = 2 or i = 3);
   tel
