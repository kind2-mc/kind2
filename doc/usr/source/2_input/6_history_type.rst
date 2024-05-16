
History Types
=============

In order to improve the expressivity of Kind 2's specification language,
the tool provides a built-in type constructor that allows users to
refer to an `unbounded` number of previous values of a stream.
Specifically, the unary type constructor ``history(x)``, that 
takes a stream ``x`` of arbitrary type ``T`` as its single argument,
represents the set of all streams ``z`` of values of type ``T`` such that 
at any time ``t >= 0``, there exists a ``k`` in the interval ``[0, t]`` such that
``z(t) = x(k)``.

For instance, given a node with an input stream ``x`` and an output
stream ``y``, both with the same type, the property `the current value of stream y
equals the current value or a previous value of a stream x plus one`
can't be expressed in Lustre. However, using the type constructor 
``history``, one can easily express the property as 
``exists (z: history(x)) y=z+1``.

Notice that ``history(x)`` denotes a refinement type, 
suggesting its applicability wherever a type is expected in the model. 
However, at present, the implementation restricts the use of the 
type constructor ``history`` to the type of a quantified variable. 
We plan to lift this restriction in future versions of Kind 2.
