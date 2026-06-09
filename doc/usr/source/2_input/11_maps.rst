Maps
==================

Map types have the syntax ``map<K, V>`` (or ``map<K; V>``), where ``V`` is any type, and 
``K`` is any type that does not contain sets, maps, or arrays. 
For example ``map<int, int>`` denotes (streams of) maps of integers to integers, and 
``map<set<[bool, int]>, real>`` denotes (streams of) maps of Boolean and integer pairs to reals.

**Map literals** can be built with the constructor ``map[k1 := v1; ...; kn := v2]`` 
which creates a map with keys ``k1`` through ``kn``, each mapping to its corresponding value.
For example, ``map[0 := 0; 1 := 1]``, ``map[{ '(false, 0) } := 0.0]``, and ``map[x := y]`` 
are all valid map literals.
Type annotations are *required* for empty maps (e.g. ``map[]@<int, int>``).

The built-in map operators are **map insertion/update**
(denoted by ``m[k1 := v1; ...; kn := vn]`` for map expression ``m``),
**map index access** (denoted by ``m[k]``),
**map subtraction** (denoted by ``m - s`` for map expression ``m`` and set
expression ``s`` whose elements have the same type as the keys of ``m``, which
removes from ``m`` all keys contained in ``s``), and
**map (key) membership** (denoted by ``in``).
Indexing a map with ``m[k]`` returns the associated value for ``k`` in map ``m``. 
If ``m`` does not have a binding for ``k``, 
then the output of the operation is unconstrained.
However, the operation is still *functional* in the sense that 
indexing a map will always yield the same value for a fixed key and timestep
(i.e., for all maps ``m`` and keys ``k`` of the proper type, 
``m[k] = m[k]`` is valid, even if key ``k`` is not in the map ``m``).
Otherwise, the operators all take the expected semantics.

Maps also support **structural equality** (denoted by ``=``) and
**structural disequality** (denoted by ``<>``). Two maps are structurally
equal when they bind exactly the same keys to the same values, regardless of
how they were constructed (e.g., ``map[0 := 0; 1 := 1] = map[1 := 1; 0 := 0]``
is valid).

See below for an example.

.. code-block:: none

   node N (inp: map<int, int>) returns (out, out2, out3: map<int, int>)
   let
     out = inp[0 := 0; 1 := 1; 2 := 2];
     out2 = map[0 := 0; 1 := 1];
     out3 = out - { 0, 1 };

     check 0 in out;
     check out[0] = 0;
     check forall (i: int) not (i in { 0, 1, 2 }) => out[i] = inp[i];
     check forall (i: int) not (i = 0 or i = 1) => not (i in out2);
     check forall (i: int) (i in out3) = (i in out and not (i in { 0, 1 }));
   tel

