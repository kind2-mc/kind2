.. _9_other/10_inductive_validity_core:

Inductive Validity Core
=======================

The inductive validity core generation is a post-analysis treatement that computes a minimal subset of
the model elements (assumptions, guarantees, stateful equations, or node calls) that are sufficient to prove all properties.

To enable inductive validity core generation, run

.. code-block:: none

  kind2 <lustre_file> --ivc true

Options
-------

* ``--ivc_category {node_calls|contracts|equations|assertions|annotations}`` (default: all categories) -- Minimize only a specific category of elements, repeat option to minimize multiple categories
* ``--ivc_only_main_node <bool>`` (default ``false``\ ) -- Only elements of the main node are considered in the computation
* ``--ivc_all <bool>`` (default ``false``\ ) -- Compute all the Minimal Inductive Validity Cores
* ``--ivc_approximate <bool>`` (default ``true``\ ) -- Compute an approximation (superset) of a MIVC. Ignored if ``--ivc_all`` is ``true``
* ``--ivc_smallest_first <bool>`` (default ``false``\ ) -- Compute a smallest IVC first. If ``--ivc_all`` is ``false``, the computed IVC will be a smallest one
* ``--ivc_must_set <bool>`` (default ``false``\ ) -- Compute the MUST set in addition to the IVCs
* ``--print_ivc <bool>`` (default ``true``\ ) -- Print the inductive validity core computed
* ``--print_ivc_complement <bool>`` (default ``false``\ ) -- Print the complement of the inductive validity core computed (= the elements that were not necessary to prove the properties)
* ``--minimize_program {no|valid_lustre|concise}`` (default ``no``\ ) -- Minimize the source Lustre program according to the inductive validity core(s) computed
* ``--ivc_output_dir <string>`` (default ``<INPUT_FILENAME>``\ ) -- Output directory for the minimized programs
* ``--ivc_uc_timeout <int>`` (default ``0``\ ) -- Set a timeout for each unsat core check sent to the solver
* ``--ivc_precomputed_mcs <int>`` (default ``0``\ ) -- When computing all MIVCs, set a cardinality upper bound for the precomputed MCSs (helps prune space of candidates)

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
* ``--compositional true``: as we want to minimize the contract of ``f`` and not its implementation, we need to enable compositional analysis

We obtain the following inductive validity core:

.. code-block:: none

  IVC (2 elements):
    Node f
      Guarantee fSpec[l11c12].guarantee[l6c4][3] at position [l6c4]
      Guarantee fSpec[l11c12].guarantee[l7c4][4] at position [l7c4]

Minimizing over a subset of the assumptions/guarantees
------------------------------------------------------

If you are interested in computing an IVC among a subset of the assumptions or guarantees, you can use the category ``annotations``.
The assumptions and guarantees that should be considered must be preceded by the keyword ``weakly``.
All the other assumptions and guarantees will be considered as always present when computing the IVCs.

For instance, we can modify the previous example as follows:

.. code-block:: none

  contract fSpec(u,v: real) returns(r: real);
  let
      weakly guarantee r >= 0.0;
      guarantee true -> r >= pre(r);
      weakly guarantee r >= u;
      guarantee r >= v;
  tel;

.. code-block:: none

  kind2 <lustre_file> --ivc true --ivc_category annotations --ivc_only_main_node false --compositional true

We obtain the following inductive validity core:

.. code-block:: none

  IVC (1 elements):
    Node f
      Guarantee fSpec[l11c12].weakly_guarantee[l6c4][3] at position [l6c4]

Computing all Inductive Validity Cores
--------------------------------------

If we want to compute ALL the minimal inductive validity cores, we can use the following flags:

.. code-block:: none

  kind2 <lustre_file> --ivc true --ivc_all true

* ``--ivc_all true``: specify that we want to compute all the IVCs
