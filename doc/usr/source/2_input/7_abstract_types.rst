Abstract Types
==============

Kind 2 supports Lustre's **abstract types**, 
which are user-declared types without definitions.
Abstract types are declared with the syntax ``type <name>``.
Below is a simple Lustre file that declares an identity 
node that takes an input of (abstract) type ``T`` 
and returns an output of type ``T`` equal to the input.

.. code-block::

    type T;
    function id_T (x: T) returns (y: T);
    let
        y = x;
    tel
