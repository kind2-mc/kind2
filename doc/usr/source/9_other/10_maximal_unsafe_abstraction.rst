.. _9_other/9_maximal_unsafe_abstraction:

Maximal Unsafe Abstraction
==========================

The maximal unsafe abstraction generation is a post-analysis treatement that computes a maximal subset
of the weak assumptions such that the system is still unsafe even if these weak assumptions are satisifed.

To enable maximal unsafe abstraction generation, run

.. code-block:: none

  kind2 <lustre_file> --mua true

Options
-------

* ``--mua_category {weak_assumptions|node_calls|contracts|equations|assertions}`` (default: weak_assumptions) -- Consider only a specific category of elements, repeat option to consider multiple categories
* ``--mua_enter_nodes <bool>`` (default ``false``\ ) -- Consider elements of all the nodes (not only elements of the top-level node)
* ``--mua_all <bool>`` (default ``false``\ ) -- Specify whether all the Maximal Unsafe Abstractions must be computed or just one
* ``--mua_per_property <bool>`` (default ``true``\ ) -- If true, MUAs will be computed for each property separately
* ``--print_mua <bool>`` (default ``true``\ ) -- Print the maximal unsafe abstraction computed
* ``--print_mua_complement <bool>`` (default ``false``\ ) -- Print the complement of the maximal unsafe abstraction computed (this is equivalent to computing a minimal correction set)
* ``--print_mua_legacy <bool>`` (default ``false``\ ) -- Print the maximal unsafe abstraction using the legacy format (only available if ``--mua_per_property`` is true)
* ``--print_mua_counterexample <bool>`` (default ``false``\ ) -- Print a counterexample for each MUA found (ignored if ``--print_mua_legacy`` is true)

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

If you are interesting in determining which of the weak assumptions of the contract ``fSpec`` can be satisfied by still remaining unsafe,
you can run this command:

.. code-block:: none

  kind2 <lustre_file> --mua true --mua_category weak_assumptions

Note that ``--mua_category weak_assumptions`` is not required since it is the default value.

The following maximal unsafe abstraction is printed:

.. code-block:: none

  ----- main -----
  Weak assumption (abs_2 and (abs_2 = (x >= 0))) at position [l5c4]
