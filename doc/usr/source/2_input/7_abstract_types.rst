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

Domain and quantification
-------------------------

Because an abstract type has no definition, Kind 2 treats it as an
*uninterpreted* domain: the only operations available on its values are equality
``=`` and disequality ``<>``. Quantifiers may range over an abstract type, so
both ``forall (x: T) ...`` and ``exists (x: T) ...`` are allowed. For example:

.. code-block::

    type T;
    node N() returns ()
    let
      check forall (t: T) t = t;
    tel

Kind 2 does not assume that the domain of an abstract type is infinite; it may
contain any number of values, whether finite or infinite. As a consequence, an
assumption that constrains an abstract type to finitely many values is now
consistent. For instance, the assumption below restricts ``T`` to a single
value:

.. code-block::

    type T;
    function id_T (x: T) returns (y: T);
    con
        assume forall (v1: T) (forall (v2: T) v1 = v2);
    noc
    let
        y = x;
        check "P1" exists (v: T) y = v;
        check "P2" exists (v1: T) exists (v2: T) v1 <> v2;
    tel

Under this assumption ``P1`` holds, because ``y`` is itself a value of ``T``,
while ``P2``, which asserts that ``T`` contains two distinct values, is falsified.

.. note::

   This behavior changed after Kind 2 v2.3.0. In v2.3.0 and earlier, abstract
   types were assumed to have infinite domains, and quantifying over a variable
   of an abstract type was rejected during type checking. Consequently, an
   assumption constraining an abstract type to a finite domain (such as the one
   above) was inconsistent.
