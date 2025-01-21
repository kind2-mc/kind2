Polymorphic User Types
======================

Kind 2 supports **polymorphic user types**, 
which are user-defined types that contain type parameters. 
An example is a polymorphic user-defined ``Pair`` type, 
shown below, declared as ``type Pair<<T; U>> = [T, U];``.

A polymorphic user-defined type ``T`` is instantiated with ``T<<...>>``
syntax (analogous to polymorphic nodes and node calls) 
as in the following examples.

.. code-block:: none
    type Pair<<T; U>> = [T, U];

    node SwapIntBool(x: Pair<<int; bool>>) returns (y: Pair <<bool; int>>)
    let
        y = {x.%1, x.%0};
    tel

    node SwapGeneric<<T; U>>(x: Pair<<T; U>>) returns (y: Pair <<U; T>>)
    let
        y = {x.%1, x.%0};
    tel

In other words, ``Pair`` (or any other user-defined polymorphic type) can 
be viewed as as a ``type constructor`` which takes types as inputs 
and returns a type.