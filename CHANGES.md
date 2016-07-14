# Kind 2 v1.0.0

This new version brings many new features and improvements over v0.8 (more
than 800 commits).

NB:

- Kind 2 now requires OCaml 4.03 or higher

New features:

- 2-induction: makes Kind 2 react quicker to *good strengthening invariants*
  discovered by invariant generation
- Assume/guarantee-based contract language with modes as Lustre annotations (see [documentation](https://github.com/kind2-mc/kind2/blob/develop/doc/usr/content/2_input/1_lustre.md#contracts))
    - specification-checking: before checking a node with a contract, check
      that the modes from the contract cover all situations allowed by the
      assumptions (implementation-agnostic mode exhaustiveness)
- Compositional reasoning: `--compositional` (see [contract semantics](https://github.com/kind2-mc/kind2/blob/develop/doc/usr/content/9_other/2_contract_semantics.md))
    - abstraction of subnodes by their contract
- Modular analyses: `--modular`
    - Kind 2 traverses the node hierarchy bottom-up
    - applying the analysis specified by the other flags to each node
    - reusing results (invariants) from previous analyses when relevant
    - allows refinement when used with compositional reasoning
- Compilation from Lustre to [Rust](https://www.rust-lang.org/): `--compile`
- Mode-based test generation: `--testgen`
    - explores the DAG of activeable modes from the initial state up to a depth
    - generates witnesses as traces of inputs logged as XML files
    - compiles the contract as an executable oracle in
      [Rust](https://www.rust-lang.org/): reads a sequence of inputs/outputs
      values for the original node on `stdin` and prints on `stdout` the
      boolean values the different parts of the contract evaluate to
- Generation of certificates and proofs: `--proof` and `--certif`
    - produces either SMTLIB-2 certificates or LFSC proofs
    - distributed with LFSC proof rules for k-induction
    - requires CVC4, JKind and the LFSC checker for proofs
    - generate proofs skeletons for potential holes
- Support for forward references on nodes, types, constants and contracts
- Output and parser for native (internal) transition system format
 

Improvements:

- Flags are now organized into modules, see `--help` and `--help_of <module>`
- Mode information (when available) to counterexample output
- Optimized invariant generation
- Named properties and guarantees
- Colored output
- No more dependencies on Camlp4
- Strict mode to disallow unguarded pre and undefined local variables
- Many bug fixes and performance improvements


Refer to the [user documentation online](https://github.com/kind2-mc/kind2/tree/develop/doc/usr/content) for more details.

# Kind 2 v0.8.0

- Optimize IC3/PDR engine, add experimental IC3 with implicit abstraction 
- Add two modular versions of the [graph-based invariant generation from PKind](http://link.springer.com/chapter/10.1007%2F978-3-642-20398-5_15).
- Add path compression in k-induction
- Support Yices 1 and 2 as SMT solvers 
- Optimize Lustre translation and internal term data structures
- Optimize queries to SMT solvers with check-sat with assumption instead of push/pop
- Return Lustre counterexamples faithful to input by undoing optimizations in translation
- Improve output and logging
- Many bug and performance fixes
- Web service to accept jobs from remote clients

Refer to the [user documentation](https://github.com/kind2-mc/kind2/blob/develop/doc/usr/content/Home.md#kind-2) for more details.
