# Contract Generation

> This feature is very experimental. In particular, the modes (if any) of the
> contracts generated might not be exhaustive. In this case Kind 2 will reject
> the contract during the mode exhaustiveness check.

Contract generation is intended, at least for now, as a helper for users to
getting started with Kind 2's contract language. Contract generation is
activated by the flag `--contract_gen`.

Internally, this feature is implemented by running invariant generation on the
input system up to some depth, specified by flag `--contract_gen_depth`. Doing
so will discover equivalence and implication invariants over the system. The
ones that talk only about the input / outputs of the systems are used to create
the contract dumped in a lustre file in the output directory.