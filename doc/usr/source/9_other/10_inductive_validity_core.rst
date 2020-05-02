.. _9_other/10_inductive_validity_core:

Inductive Validity Core
=======================

The inductive validity core generation is a post-analysis treatement that computes a minimal subset of
equations, nodes or contract items such that the system is still safe.

To enable inductive validity core generation, run

.. code-block:: none

  kind2 <lustre_file> --ivc true

Options
-------

* ``--ivc_category {node_calls|contracts|equations|assertions}`` (default: all categories) -- Minimize only a specific category of elements, repeat option to minimize multiple categories
* ``--ivc_only_main_node <bool>`` (default ``false``\ ) -- Compute an IVC over the elements of the main node only
* ``--ivc_all <bool>`` (default ``false``\ ) -- Compute all the Inductive Validity Cores
* ``--ivc_approximate <bool>`` (default ``false``\ ) -- Compute an approximation (superset) of an IVC
* ``--ivc_smallest_first <bool>`` (default ``false``\ ) -- Compute the smallest IVC first. Ignored if ``--ivc_all`` is ``true``
* ``--ivc_must_set <bool>`` (default ``false``\ ) -- Compute the MUST set first and then compute the IVCs starting from it
* ``--print_ivc <bool>`` (default ``true``\ ) -- Print the inductive validity core computed
* ``--print_ivc_complement <bool>`` (default ``false``\ ) -- Print the complement of the inductive validity core computed (= the elements that are not necessary to prove the system safe)
* ``--minimize_program {no|valid_lustre|concise}`` (default ``no``\ ) -- Minimize the source Lustre program according to the inductive validity core(s) computed
* ``--ivc_output_dir <string>`` (default ``<INPUT_FILENAME>``\ ) -- Output directory for the minimized programs
* ``--ivc_uc_timeout <int>`` (default ``10``\ ) -- Set a timeout for each unsat core check sent to the solver
* ``--ivc_precomputed_mcs <int>`` (default ``0``\ ) -- When computing all IVCs, determine the cardinality up to which MCS will be computed before starting to compute the IVCs

Example
-------

Let's consider the following Lustre code:

.. code-block:: none

  contract fSpec(u,v: real) returns(r: real);
  let
      guarantee r >= 0.0;
      guarantee true -> r >= pre(r);
      guarantee r >= u;
      guarantee r >= v;
  tel;

  node f(u, v : real) returns (r : real);
  (*@contract import fSpec(u,v) returns (r) ; *)
  var m1,m2: real;
  let
      m1 = if v > u then v else u;
      m2 = if m1 > 0.0 then m1 else 0.0;
      r = m2 -> if pre(r) > m1 then pre(r) else m1;
  tel;

  node main(x, y : real) returns (P : bool);
  var a,b : real;
  let
      a = f(x,y);
      b = f(y,x);
      P = a >= x and a >= y and b >= x and b >= y;
      --%PROPERTY P;
  tel;

If we are interesting in determining which guarantees of the contract ``fSpec`` of ``f`` are needed to prove ``P``,
we should run this command:

.. code-block:: none

  kind2 <lustre_file> --ivc true --ivc_category contracts --ivc_only_main_node false --compositional true

* ``--ivc_category contracts``: because we are only interested in minimizing the contract ``fSpec``
* ``--ivc_only_main_node false``: because ``fSpec`` is not the contract of the main node, so we need to consider all nodes
* ``--compositional true``: as we want to minimize the contract of ``f`` and not its implementation, we must enable the compositionnal reasonning

We obtain the following inductive validity core:

.. code-block:: none

  ----- f -----
  Contract item (r >= u) at position [l6c4]
  Contract item (r >= v) at position [l7c4]

  ----- main -----

Computing all Inductive Validity Cores
--------------------------------------

If we want to compute ALL the minimal inductive validity cores, we can use the following flags:

.. code-block:: none

  kind2 <lustre_file> --ivc true --ivc_all true --ivc_must_set true

* ``--ivc_all true``: specify that we want to compute all the IVCs
* ``--ivc_must_set true``: indicate that the MUST set should be computed first. In general, when ``--ivc_all`` is ``true``, it is more efficient to enable this option
