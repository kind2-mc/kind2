.. _9_other/9_maximal_unsafe_abstraction:

Maximal Unsafe Abstraction
==========================

The maximal unsafe abstraction generation is a post-analysis treatement that computes a maximal subset
of weak assumptions to add to the system such that the system is still unsafe.

To enable maximal unsafe abstraction generation, run

.. code-block:: none

  kind2 <lustre_file> --mua true

Options
-------

* ``--mua_category {weak_assumptions|node_calls|contracts|equations|assertions}`` (default: weak_assumptions) -- Consider only a specific category of elements, repeat option to consider multiple categories
* ``--mua_enter_nodes <bool>`` (default ``false``\ ) -- Consider elements of all the nodes (not only elements of the top-level node)
* ``--print_mua <bool>`` (default ``true``\ ) -- Print the maximal unsafe abstraction computed
* ``--print_mua_complement <bool>`` (default ``false``\ ) -- Print the complement of the maximal unsafe abstraction computed (this is equivalent to computing a minimal correction set)
* ``--mua_all <bool>`` (default ``false``\ ) -- Specify whether all the Maximal Unsafe Abstractions must be computed or just one

Example
-------

Let's consider the following Lustre code:

.. code-block:: none

  contract spec(x,y: real) returns(z: real);
  let
      weakly assume x = -y;
      weakly assume x >= 0.0;
  tel;

  node main(x, y : real) returns (a : real);
  (*@contract import spec(x,y) returns (z) ; *)
  var P : bool;
  let
      a = x + y;
      P = a = 0.0;
      --%MAIN;
      --%PROPERTY P;
  tel;

If we are interesting in determining which of the weak assumptions of the contract ``fSpec`` can be satisfied by still remaining unsafe,
we should run this command:

.. code-block:: none

  kind2 <lustre_file> --mua true --mua_category weak_assumptions

Note that ``--mua_category weak_assumptions`` is not required since it is the default value.

We obtain the following maximal unsafe abstraction:

.. code-block:: none

  ----- main -----
  Weak assumption (abs_2 and (abs_2 = (x >= 0))) at position [l5c4]
