.. _9_other/11_contract_checks:

Contract Check
==============

Kind 2 provides an option to check the realizability of contracts and refinement types.
When an input model includes :ref:`imported nodes <2_input/1_lustre#imported>` or
:ref:`refinement types <2_input/4_refinement_types>`,
it is particularly important to verify that
their associated contracts are realizable, i.e.,
a component can be constructed such that, for any input satisfying
the contract assumptions, there exists some output value that
the component can produce to meet the contract guarantees.

To check the contracts of nodes and functions, run:

.. code-block:: none

  kind2 --enable CONTRACTCK <lustre_file>

You can specify a particular node or function to analyze using 
``--lus_main <node_name>``, and a specific refinement type using 
``--lus_main_type <type_name>``.

If Kind 2 is able to prove some contract *unrealizable*
and the ``--print_deadlock`` flag is true,
Kind 2 will show a deadlocking trace such that
all states except the last one satisfy the contract constraints.
If the trace only has one state, the state shows input values
such that no initial state values satisfy the contract constraints
(including the state values chosen as sample).
For traces with more than one state, the trace is such that
no next state values satisfy the contract constraints
from the second-to-last state giving the input values of
the last state.
Kind 2 will also show a set of conflicting constraints for the
last state in the trace.

When the ``--check_contract_is_sat`` flag is true, Kind 2 will also check
whether the unrealizable contract is at least satisfiable, i.e.,
it is possible to construct a component such that for
*at least* one input sequence allowed by the contract assumptions,
there is some output value that the component can produce that satisfies
the contract guarantees.

In addition, Kind 2 will check the realizability of
the component's environment. This check is also important 
for the top-level contract, as an unrealizable environment
specification can lead to the same flawed compositional proof arguments as 
an unrealizable leaf-level component contract.
You can disable this check by passing ``--check_environment false``.