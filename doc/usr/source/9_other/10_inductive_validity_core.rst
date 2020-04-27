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
* ``--ivc_enter_nodes <bool>`` (default ``false``\ ) -- Minimize elements of all the nodes (not only elements of the top-level node)
* ``--print_ivc <bool>`` (default ``true``\ ) -- Print the inductive validity core computed
* ``--print_ivc_complement <bool>`` (default ``false``\ ) -- Print the complement of the inductive validity core computed (= the elements that are not necessary to prove the system safe)
* ``--minimize_program {no|valid_lustre|concise}`` (default ``no``\ ) -- Minimize the source Lustre program according to the inductive validity core(s) computed
* ``--ivc_output_dir <string>`` (default ``<INPUT_FILENAME>``\ ) -- Output directory for the minimized programs
* ``--ivc_impl {AUC|UC|BF|UCBF|UMIVC}`` (default ``UC``\ ) -- Select the implementation for the IVC computation
* ``--ivc_umivc_k <int>`` (default ``0``\ ) -- Set the parameter 'k' for the implementation UMIVC
* ``--ivc_uc_timeout <int>`` (default ``10``\ ) -- Set a timeout for each unsat core check sent to the solver

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

  kind2 <lustre_file> --ivc true --ivc_category contracts --ivc_enter_nodes true --compositional true

* ``--ivc_category contracts``: because we are only interested in minimizing the contract ``fSpec``
* ``--ivc_enter_nodes true``: because ``fSpec`` is not the contract of the top-level node, so we need to minimize inside node calls
* ``--compositional true``: as we want to minimize the contract of ``f`` and not its implementation, we must enable the compositionnal reasonning

We obtain the following inductive validity core:

.. code-block:: none

  ----- f -----
  Contract item (r >= u) at position [l6c4]
  Contract item (r >= v) at position [l7c4]

  ----- main -----

Computing all Inductive Validity Cores
--------------------------------------

If we want to compute ALL the minimal inductive validity cores, we must select the implementation ``UMIVC``:

.. code-block:: none

  kind2 <lustre_file> --ivc true --ivc_impl UMIVC

The ``UMIVC`` implementation does not terminate until all minimal inductive validity cores have been found,
but when an inductive validity core is found, it is directly printed (no need to wait for the algorithm to terminate).

``UMIVC`` is composed of two phases: the first one reduces the search space by computing some Maximal Unsafe Abstractions,
and the second one search for Minimal Inductive Validity Cores.
A parameter ``k`` between 0 and infinity determines how long the first phase will be.
More precisely, the first phase computes all the Maximal Unsafe Abstractions of cardinality up to ``k``.
``k`` can be set using the option ``--ivc_umivc_k``, with the value -1 for infinity.
