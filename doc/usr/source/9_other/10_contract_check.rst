.. _9_other/11_contract_checks:

Contract Check
==============

When an input model includes :ref:`imported nodes <2_input/1_lustre#imported>`,
it is important to check that
the contracts associated with them can be realized, i.e.,
it is possible to construct a component such that for any input allowed 
by the contract assumptions, there is some output value that the component
can produce that satisfies the contract guarantees.

To check the contracts of imported nodes, run

.. code-block:: none

  kind2 --enable CONTRACTCK <lustre_file>

If Kind 2 is able to prove some contract *unrealizable*,
it will show a deadlocking trace such that
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

In addition, Kind 2 will check
whether the unrealizable contract is at least satisfiable, i.e.,
it is possible to construct a component such that for
*at least* one input sequence allowed by the contract assumptions,
there is some output value that the component can produce that satisfies
the contract guarantees.
