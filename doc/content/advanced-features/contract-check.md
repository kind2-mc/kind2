---
title: "Contract Check"
weight: 11
---

Kind 2 provides an option to check the realizability of contracts and refinement types.
When an input model includes [imported nodes]({{< relref "/inputs-and-outputs/lustre#the-imported-keyword" >}}) or
[refinement types]({{< relref "/inputs-and-outputs/refinement-types" >}}),
it is particularly important to verify that
their associated contracts are realizable, i.e.,
a component can be constructed such that, for any input satisfying
the contract assumptions, there exists some output value that
the component can produce to meet the contract guarantees.

To check the contracts of nodes and functions, run:

```text
kind2 --enable CONTRACTCK <lustre_file>
```

You can specify a particular node or function to analyze using
`--lus_main <node_name>`, a specific refinement type using
`--lus_main_type <type_name>`, or a specific constant using
`--lus_main_const <const_name>`.

If Kind 2 is able to prove some contract *unrealizable*
and the `--print_deadlock` flag is true,
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

### Contracts of functions

A function is applied pointwise: its outputs at each step only depend on
its inputs at that step. When the contract of a function has temporal
operators, a component that realizes it may still need to remember its past
inputs, which no function can do. For example, the contract

```lustre
function imported F(x: int) returns (y: int);
(*@contract
  guarantee y = (0 -> pre x);
*)
```

is realized by a node that outputs its previous input, but not by a function:
on input `0` at the first step, the output must be `0`, and on input `0`
after input `1`, it must be `1`.

For such a contract, once it is known to be realizable by a node, Kind 2
checks whether a function realizes it. It looks for a function in a loop
guided by counterexamples:

1. It collects input traces from the counterexamples to the guarantees,
   with the outputs left free.
2. It checks whether some function satisfies the contract on all of the
   traces at once. If none does, the contract is unrealizable, and the
   traces show why.
3. Otherwise, it generalizes the values of such a function at the inputs of
   the traces into a candidate function defined over all inputs, an
   `if ... then ... else` over the conditions of the contract.
4. It checks the contract with the outputs defined by the candidate. If the
   guarantees hold, the candidate realizes the contract. Otherwise, the
   inputs of the counterexamples are added to the traces, and the loop
   repeats from step 2.

When the contract is realizable, Kind 2 shows the function it found. When it
is unrealizable and `--print_deadlock` is true, Kind 2 shows the conflicting
input traces instead of a deadlocking trace. The loop tries at most
`--function_realizability_iter` candidates (20 by default). The check may be
unable to decide: a candidate may never be found, and a contract whose
outputs range over infinitely many values may be unrealizable by a function
while every finite set of traces is satisfiable. The contract is then left
undetermined.

When the `--check_contract_is_sat` flag is true, Kind 2 will also check
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
You can disable this check by passing `--check_environment false`.
