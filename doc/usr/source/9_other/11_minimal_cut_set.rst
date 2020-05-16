.. _9_other/11_minimal_correction_set:

Minimal Cut Set
================

The minimal cut set generation is a special mode where Kind 2 computes a minimal subset of
the model elements (assumptions, guarantees, equations or node calls) whose no satisfaction leads to the violation of a property.

To enable minimal cut set generation, run

.. code-block:: none

  kind2 <lustre_file> --enable MCS

Options
-------

* ``--mcs_category {annotations|node_calls|contracts|equations|assertions}`` (default: annotations) -- Consider only a specific category of elements, repeat option to consider multiple categories
* ``--mcs_only_main_node <bool>`` (default ``false``\ ) -- Only elements of the main node are considered in the computation
* ``--mcs_all <bool>`` (default ``false``\ ) -- Specify whether all the Minimal Cut Sets must be computed or just one
* ``--mcs_max_cardinality <int>`` (default ``-1``\ ) -- Only search for MCSs of cardinality lower or equal to this parameter. If ``-1``, all MCSs will be considered
* ``--mcs_per_property <bool>`` (default ``true``\ ) -- If true, MCSs will be computed for each property separately
* ``--print_mcs <bool>`` (default ``true``\ ) -- Print the minimal cut set computed
* ``--print_mcs_complement <bool>`` (default ``false``\ ) -- Print the complement of the minimal cut set computed (this is equivalent to computing a Maximal Unsafe Abstraction)
* ``--print_mcs_legacy <bool>`` (default ``false``\ ) -- Print the minimal cut set using the legacy format
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

If you are interesting in determining a minimal set of the weak assumptions of the contract ``fSpec`` whose no satisfaction leads to the violation of P,
you can run this command:

.. code-block:: none

  kind2 <lustre_file> --enable MCS --mcs_category annotations

Note that ``--mcs_category annotations`` is not required since it is the default value.

The following minimal cut set is printed:

.. code-block:: none

  ----- main -----
  Weak assumption (x = -y) at position [l4c4]
