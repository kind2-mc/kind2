.. _9_other/11_minimal_correction_set:

Minimal Correction Set
======================

The minimal correction set generation is a post-analysis treatement that computes a minimal subset of
the model elements (contract items, equations or node calls) such that the system become unsafe if we remove these assumptions.

To enable minimal correction set generation, run

.. code-block:: none

  kind2 <lustre_file> --mcs true

Options
-------

* ``--mcs_category {annotations|node_calls|contracts|equations|assertions}`` (default: annotations) -- Consider only a specific category of elements, repeat option to consider multiple categories
* ``--mcs_only_main_node <bool>`` (default ``false``\ ) -- Compute a MCS over the elements of the main node only
* ``--mcs_all <bool>`` (default ``false``\ ) -- Specify whether all the Minimal Correction Sets must be computed or just one
* ``--mcs_max_cardinality <int>`` (default ``-1``\ ) -- Only search for MCS of cardinality lower or equal to this parameter. If ``-1``, all cardinalities will be considered
* ``--mcs_per_property <bool>`` (default ``true``\ ) -- If true, MCS will be computed for each property separately
* ``--print_mcs <bool>`` (default ``true``\ ) -- Print the minimal correction set computed
* ``--print_mcs_complement <bool>`` (default ``false``\ ) -- Print the complement of the minimal correction set computed (this is equivalent to computing a Maximal Unsafe Abstraction)
* ``--print_mcs_legacy <bool>`` (default ``false``\ ) -- Print the minimal correction set using the legacy format
* ``--print_mcs_counterexample <bool>`` (default ``false``\ ) -- Print a counterexample for each MCS found (ignored if ``--print_mcs_legacy`` is true)

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

  kind2 <lustre_file> --mcs true --mcs_category annotations

Note that ``--mcs_category annotations`` is not required since it is the default value.

The following minimal correction set is printed:

.. code-block:: none

  ----- main -----
  Weak assumption (x = -y) at position [l4c4]
