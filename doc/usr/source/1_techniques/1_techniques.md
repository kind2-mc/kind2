# Techniques

This section presents the techniques available in Kind 2: how they work,
and how they can be tweaked through various options:

* [k-induction](./2_kinduction.md#k-induction)
* [invariant generation](./3_invgen.md#invariant-generation)
* [IC3](./4_ic3.md#ic3)



## Compositional reasoning

When verifying a node `n`, *compositional reasoning* consists in abstracting
the complexity of the subnodes of `n` by their
[contracts](./../9_other/2_contract_semantics.md#contract-semantics). The idea
is that the contract has typically a lot less state than the node it specifies,
which in addition to its own state contains that of its subnodes recursively.

Compositional reasoning thus improves the scalability of Kind 2 by taking
advantage of information provided by the user to abstract the complexity away.
When in compositional mode (`--composition true`), Kind 2 will abstract all
calls (to subnodes that have a contract) in the top node and verify the
resulting, abstract system.


A successful compositional proof of a node does not guarantee the correctness
of the concrete (un-abstracted) node though, since the subnodes have not been
verified. For this reason compositional reasoning is usually applied in
conjunction with *modular reasoning*, discussed in the next section.



## Modular reasoning

*Modular reasoning* is activated with the option `--modular true`. In this
mode, Kind 2 will perform whatever type of analysis is specified by the other
flags on **every node** of the hierarchy, bottom-up. The analysis is
completed on every node even if some node is proved unsafe because of
the falsification of one of its properties.

A timeout for *each analysis* can be specified using the `--timeout_analysis`
flag. It can be used in conjunction with the *global timeout* given with the
`--timeout` or `--timeout_wall` time.

Internally Kind 2 builds on previous analyses when starting a new one. For
instance, by using the invariants previously discovered in subnodes of the node
under analysis.


## Refinement in compositional and modular analyses

An interesting configuration is
```
kind2 --modular true --compositional true ...
```

If `top` calls `sub` and we analyze `top`, it means we have previously analyzed
`sub`. We are running in compositional mode so the call to `sub` is originally
abstracted by its contract.
Say the analysis fails with a counterexample. The counterexample might be
spurious for the concrete version of `sub`: the failure would not happen if we
used the concrete call to `sub` instead of the abstract one.

Say now that when we analyzed `sub`, we proved that it is correct. In this case
Kind 2 will attempt to *refine* the call to `sub` in top. That is, undo the
abstraction and use the implementation of `sub` in a new analysis.

Note that since `sub` is known to be correct, it is stronger than its contract.
More precisely, it accepts fewer execution traces than its contract does. Hence
anything proved with the abstraction of `sub` is still valid after refinement,
and Kind 2 will use these results right away.
