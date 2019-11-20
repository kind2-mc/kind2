.. _9_other/9_inductive_validity_core:

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
* ``--minimize_program {no|valid_lustre|concise}`` (default ``no``\ ) -- Minimize the source Lustre program according to the inductive validity core computed
* ``--minimized_program_filename <string>`` (default ``<INPUT_FILENAME>_min.<EXT>``\ ) -- Filename for the minimized Lustre program
* ``--ivc_impl {AUC|UC|BF|UCBF}`` (default ``UC``\ ) -- Select the implementation for the IVC computation
