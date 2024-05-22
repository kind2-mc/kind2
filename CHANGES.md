# Unreleased

New features:
- Support for [refinement types](https://kind.cs.uiowa.edu/kind2_user_doc/2_input/4_refinement_types.html)
- A new built-in operator, [any](https://kind.cs.uiowa.edu/kind2_user_doc/2_input/1_lustre.html#nondeterministic-choice-operator), to denote an arbitrary stream of values
- Realizability checks for contracts of non-imported nodes and refinement types
  - It also checks the realizability of a node's assumption. The check can be disabled by passing `--check_environment false`
- A new type constructor, [history](https://kind.cs.uiowa.edu/kind2_user_doc/2_input/6_history_type.html), to refer to an unbounded number of previous values of a stream

Improvements:
- Optimized encoding of counters in reachability queries
- Fixed issue where checks on assumptions of called nodes were not instantiated if an intermediate node has no properties
- The new version applies slicing per IC3IA engine instance

Changes:
- For imported nodes and functions, Kind 2 now assumes conservatively that each output stream depends on the current values of all inputs. The user must refine the model to avoid false positives of circular dependencies
- A call to a node without a contract but with at least one output that has a subrange type is now abstracted. Subrange types are now treated as a special case of refinement types, handled as an extension of the contract's node, or as the sole specification if none is provided
- Undefined initial values and values of undefined output streams with a subrange type range over the base integer type
- The type of constants must be provided in their declaration
- Invariant generation engines now always start generating invariants from the top

# Kind 2 v2.1.1

This release includes some minor improvements and various fixes. Notably:

- Fix soundness bug in IC3IA engine
- Allow variables with subrange types in the interface of a contract node
- Accept new versions of cvc5 for proof production (up to 1.1.0)


# Kind 2 v2.1.0

This release includes multiple improvements and bug fixes. Notably:

- Add new option for printing the set of viable states of a realizable contract (`--print_viable_states`).
- Allow the second argument of a shift operator to be non-constant.
- Add support for the latest versions of SMT solver Bitwuzla (v0.1.1 and above).
- Fix compatibility issue with OCaml 5.0.0+
- Fix printing of values of stateless variables in counterexamples (bug introduced in v2.0.0).
- Fix several bugs related to the definition and use of arrays in Lustre models.
- Add static checks on the definition of global subrange constants.
- Accept `param` keyword for the declaration of system parameters (global constants without a definition).
- Add subrange and enum constraints on system parameters.
- Fix type checking and handling of constant node arguments.
- Other improvements and bug fixes in the Lustre front end.


# Kind 2 v2.0.0

New features:

- Support for SMTInterpol as a backend solver.
- New IC3 engine based on Implicit (Predicate) Abstraction:
  - Supported interpolating SMT solvers: MathSAT, SMTInterpol, and OpenSMT.
  - Generation of interpolants with Z3 and cvc5 supported through built-in method based on QE.
  - See [documentation](https://kind.cs.uiowa.edu/kind2_user_doc/1_techniques/4_ic3.html) for more details.
- Support for subrange types with an open end:
  - `type T = subrange [*,N] of int`
  - `type T = subrange [N,*] of int`

Improvements:

- Add additional non-vacuity check for contract modes.
  - The new check considers only the info of the contract.
- Optimize performance of counterexample reconstruction.
- Fix handling of reachability properties in compositional-modular analysis.
- Fix simulation of systems with imported subnodes.
- Fix logic setting for Yices 2.
- Fix logic setting and constant declaration in certificates.

Changes:

- Add `--exit_code_mode` option to control exit code convention.


# Kind 2 v1.9.0

New features:

- Add support for `elsif` clauses in If-Then-Else constraints.
- Add dedicated syntax for reachability properties of the form:
  - `check reachable P [from <int>] [within <int>]`
  - `check reachable P at <int>`
  The modifiers `from`, `within` and `at` allow users to specify a lower and upper bound on the number of execution steps in the witness trace.
- Add dedicated syntax for conditional properties of the form:
  - `check A provided B`
- Add non-vacuity checks for conditional properties and contract mode implications.
- Add command-line options `--check_reach` and `--check_nonvacuity` that allow users to enable/disable reachability and non-vacuity checks.
- Add command-line options `--print_cex` and `--print_witness` that allow users to enable/disable printing of counterexamples and reachability witnesses.
- Add command-line options `--dump_witness` and `--dump_deadlock` that allow users to dump witnesses and deadlocks to files. Note: Kind 2 already supported the command-line option `--dump_cex`.

Improvements:

- Fix underreporting issue in the computation of conflicting constraints (bug introduced in v1.6.0).
- Fix reporting of contract mode elements in IVCs and conflicting constraints (bug introduced in v1.8.0).
- Fix setting of SMT-LIB logic for the non-linear combination of integers and reals.
- Fix computation of dependencies for clock operators in new the Lustre front-end.
- Other fixes and improvements in the new front-end.

Changes:

- New backward-incompatible convention for exit codes.
  - Now Kind 2 follows the POSIX convention of returning `0` for successful checks.
  - See [documentation](https://kind.cs.uiowa.edu/kind2_user_doc/3_output/3_exit_codes.html) for more details.
- Add `--fake_filepath` option for LSP server.


# Kind 2 v1.8.0

New features:

- Add syntax for If-Then-Else constraints and Frame Condition constraints (see [documentation](https://kind.cs.uiowa.edu/kind2_user_doc/2_input/1_lustre.html#if-statements-and-frame-conditions)).
- Add support for SMT solver Bitwuzla.
  - Its predecessor, Boolector, is no longer supported.
- Add option `--flatten_proof` to break down LFSC proofs into a sequence of lemmas.
  - This option helps reduce the memory footprint of the LFSC checker and improve its performance as the proof for each lemma is verified by the LFSC checker independently.

Improvements:

- Fixes and improvements solving machine integer problems:
  - Support for non-standard bit-vector constants and symbols returned by MathSAT and Z3
  - Fix path compression bit-vector encoding in minimization of set of invariants.
- Fixes and improvements in the new Lustre front-end.


# Kind 2 v1.7.0

New features:

- Support for new SMT solver cvc5.
  - Its predecessor, CVC4, is no longer supported.
- A revamp of Kind 2's proof production facility:
  - The new version replaces CVC4 with cvc5 as the main back-end proof-producing SMT solver.
  - It produces more detailed proofs and covers a wider range of input models.
  - The new proofs are still processable by the external proof checker LFSC.

Improvements:

- Support for unary negation and subtraction of unsigned machine integers.
- Fix invariant pruner: some non-trivial one-state invariants were not included in certificates.
- Fix problem with reported locations in IVC output.
- Fix selection of logic in computation of MCS.
- Fix version detection of SMT solvers.
- Multiple fixes and improvements in the new Lustre front-end.


# Kind 2 v1.6.0

New features:

- A new implementation of Kind 2's language front-end with:
  - Support for forward references to nodes and modes in contracts.
  - Individual namespaces for imported contracts.
  - Enhanced type checking of composite data types.

  Internally, the new implementation follows a multi-pass approach more strictly.
  This should facilitate the extensibility and maintenance of the new front-end.
  Although we strongly encourage users to use the new front-end,
  the old front-end can still be enabled for now by passing
  `--old_frontend true` to Kind 2.

Improvements:

- Fix issue where the inductive step check could incorrectly declare a property
  k-inductive after a contract has been refined in compositional verification.
- Fix bug in minimization of set of invariants.
- Fix XML and JSON output produced by the certificate generation post-analysis.
- Include various updates and fixes to the realizability and
  satisfiability checks of contracts. Now there is a flag to (de)activate
  the computation of a deadlocking trace, `--print_deadlock`, and a flag to
  (de)activate the satisfiability check of an unrealizable contract,
  `--check_contract_is_sat`.

Changes:

- New default behavior: if no node is marked as a main node,
  Kind 2 considers _all_ the top nodes for analysis.
- Functional congruence is only enforced on abstract functions when
  the flag `--enforce_func_congruence` is true (default: false).
- Make Kind 2 compatible with recent versions of Menhir (20211230 and later).
- Remove two experimental post-analyses: invariant logging and silent contract loading.
- Remove support for automata.


# Kind 2 v1.5.1

This release includes performance improvements and various fixes. Notably:

- Improve performance of realizability checks with Z3.
- Fix realizability check of imported functions.
- Fix realizability check when `--ae_val_use_ctx` is false (bug introduced in v1.5.0).
- Fix generation of tracing information when a contract is proven unrealizable.
- Fix shape of generated invariant candidates when `--invgen_all_out` is true.
- Fix generation of SMT-LIB 2 certificates.
- Make Kind 2 compatible with the latest version (5.1.4) of the OCaml bindings for ZMQ.

In addition, this version adds support for a new Visual Studio Code
[extension](https://github.com/kind2-mc/vscode-kind2) for Kind 2.

Thanks to Andreas Katis for his feedback and bug reports.


# Kind 2 v1.5.0

New features:

- Print a deadlocking trace and a set of conflicting constraints when a contract is proven unrealizable.
- Multiple nodes can be annotated as main nodes so that analysis results for common subnodes are shared in modular analysis.
- New option to dump each counterexample to a file (`--dump_cex`).

Improvements:

- Require and ensure clauses of contract modes are eligible elements for IVCs and MCSs when the contracts category is selected.
- Print values of (free) constants in counterexamples.
- Print summary before terminating when CTRL-C is pressed.
- Prevent invariant generation engine from crashing when processing global constants.
- Fix handling of XOR operator in IC3.
- Fix minor issues in IVC/MCS module.
- Other bug fixes and enhancements.

Changes:

- Kind 2 now requires:
  - OCaml 4.09 or later
  - Dune 2.7 or later

Thanks to M. Anthony Aiello, Andreas Katis, and
Amos Robinson for their feedback and suggestions.


# Kind 2 v1.4.0

New features:

- New option for checking contracts of imported nodes (see [documentation](https://kind.cs.uiowa.edu/kind2_user_doc/9_other/12_contract_check.html)).
  - Current checks: realizability and satisfiability checking.

Improvements:

- Improve compositional reasoning about assumptions of called nodes.
  - See issue [#736](https://github.com/kind2-mc/kind2/issues/736) for more details (thanks to Amos Robinson).
- Print values of ghost variables in counterexamples.
- Fix and update bounds checking feature for subrange streams.
  - Thanks to Aaron Carroll, Amos Robinson, and Vivian Ye-Ting Dang for their bug reports.
- Fix issue in MUST set generation when a single MIVC is computed.
- Accept fractions in JSON input for interpreter.
- Other bug fixes.

Changes:

- Always check node calls are safe, not only in compositional mode.
- Set `check_subproperties` flag to true by default.
  - Ignored if modular analysis is true.
- Abstract call only if contract has at least one guarantee or one mode.


# Kind 2 v1.3.1

This release includes performance improvements and various fixes. Notably:

- Fix soundness issue in path compression when there are temporal dependencies
  between input values.
  - Thank you to M. Anthony Aiello for finding this bug.
- Fix bug in extraction of an active path during IC3 generalization.
- Improve IC3 performance over large models that contain reals or machine integers.
- Fix issue reading models from the latest version of Z3 (4.8.10).
  It caused a runtime error during IVC generation.


# Kind 2 v1.3.0

New features:

- Computation of [Inductive Validity Cores](https://kind.cs.uiowa.edu/kind2_user_doc/9_other/10_inductive_validity_core.html) and [Minimal Cut Sets](https://kind.cs.uiowa.edu/kind2_user_doc/9_other/11_minimal_cut_set.html).
- Invariant generation for machine integers.
  - Engine names: INVGENMACH and INVGENMACHOS.
- IC3 model checking engine for machine integers.
  - The pre-image computation is based on quantifier elimination over bit-vectors.
  - It requires SMT solver Z3 at this time.
- Support for abstract types ([#594](https://github.com/kind2-mc/kind2/pull/594), thanks to Amos Robinson).
- Support for SMT solvers Boolector and MathSAT.
  - It requires the develop version of Boolector at this time (commit 5d18baa and later).
- New command-line option to only parse Lustre inputs (`--only_parse true`).

Improvements:

- Support for version 1.8 of SMT solver CVC4.
- Improved support for [machine integers](https://kind.cs.uiowa.edu/kind2_user_doc/2_input/3_machine_ints.html).
- Reduced number of activation literals used in BMC encoding.
- Fixed returned exit code for modular analysis ([#684](https://github.com/kind2-mc/kind2/pull/684)).
- Other bug fixes.

Changes:

- Removed CZMQ sources and OCaml bindings for CZMQ from the Kind 2 repository.
  - Kind 2 now requires [ZMQ](https://zeromq.org/) 4.x or later to be installed on your system.
- Replaced old build system with new one based on [dune](https://dune.build/) and [OPAM](https://opam.ocaml.org/).
  - See [README](README.rst) file for new requirements and installation instructions.


# Kind 2 v1.2.0

New features:

- Support for [machine integers](https://kind.cs.uiowa.edu/kind2_user_doc/2_input/3_machine_ints.html).
- Option to output results in [JSON format](https://kind.cs.uiowa.edu/kind2_user_doc/3_output/2_machine_readable.html).
- [Interpreter](https://kind.cs.uiowa.edu/kind2_user_doc/9_other/8_interpreter.html) accepts input values in JSON format.

Many bug fixes!


# Kind 2 v1.1.0

This new version features many internal improvements as well as several new
features over v1.0.1 (more than 300 commits):

- Support for Scade 6 automata (see [documentation](https://kind.cs.uiowa.edu/kind2_user_doc/2_input/1_lustre.html#hierarchical-automata))
- Support for Scade 6 arrays
- Arithmetic invariant generation: up to v1.0.1, the main invariant generation
  technique besides the IC3 engine was boolean template-based invariant
  generation. This technique can discover equalities and implications between
  predicates over the state variables of the system.

  The technique has been extended to arithmetic terms (`int` and `real`): Kind
  2 can discover equalities and orderings (`<=`) between arithmetic terms mined
  from the input system.

  The boolean, integer and real template-based invariant generation techniques
  all come in two flavors: one-state which can only relate terms over the
  current state, and two-state which can relate terms mentioning the current
  and the previous state.

  Each of them runs as a different process at runtime. By default, only the
  following are active:

  - INVGENOS (one-state boolean)
  - INVGEN (two-state boolean)
  - INVGENINTOS (one-state integer)
  - INVGENREALOS (one-state real)
- Several features distinct from the actual verification process were
  introduced in Kind 2 v1.0.0: certification, contract generation, compilation
  to Rust, and test generation.

  These features are now aggregated under the term [*post-analyses*](https://kind.cs.uiowa.edu/kind2_user_doc/9_other/1_post_analyses.html).
  Most of them have been improved and v1.1.0 introduces a post-analysis:
  [invariant logging](https://kind.cs.uiowa.edu/kind2_user_doc/9_other/7_invariant_logging.html). This feature attempts to log
  strengthening invariants discovered by Kind 2 as a contract.
- *Silent contract loading* attempts to load contracts generated by Kind 2
  during previous runs as candidate properties for the current run (see
  [documentation](https://kind.cs.uiowa.edu/kind2_user_doc/9_other/1_post_analyses.html#silent-contract-loading))


# Kind 2 v1.0.1

- Read files on standard input in Lustre format


# Kind 2 v1.0.0

This new version brings many new features and improvements over v0.8 (more
than 800 commits).

NB:

- Kind 2 now requires OCaml 4.03 or higher

New features:

- 2-induction: makes Kind 2 react quicker to *good strengthening invariants*
  discovered by invariant generation
- Assume/guarantee-based contract language with modes as Lustre annotations (see [documentation](https://kind.cs.uiowa.edu/kind2_user_doc/2_input/1_lustre.html#contracts))
    - specification-checking: before checking a node with a contract, check
      that the modes from the contract cover all situations allowed by the
      assumptions (implementation-agnostic mode exhaustiveness)
- Compositional reasoning: `--compositional` (see [contract semantics](https://kind.cs.uiowa.edu/kind2_user_doc/9_other/2_contract_semantics.html))
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
- Contract generation: `--contract_gen`
  - Very experimental: the modes generated might not be exhaustive and the
    check exhaustiveness check might fail
  - This feature's main goal, for now, is to help users get started with
    contracts by generating a contract stub partially filled with invariants
    discovered by invariant generation

Improvements:

- Flags are now organized into modules, see `--help` and `--help_of <module>`
- Mode information (when available) to counterexample output
- Optimized invariant generation
- Named properties and guarantees
- Colored output
- No more dependencies on Camlp4
- Strict mode to disallow unguarded pre and undefined local variables
- Many bug fixes and performance improvements
- Added mode information (when available) to counterexample output
- Rewrote invariant generation from scratch: much faster now
- czmq fixes: there should be no process still running after Kind 2 exits

Refer to the [user documentation online](https://kind.cs.uiowa.edu/kind2_user_doc/) for more details.


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

Refer to the [user documentation](https://kind.cs.uiowa.edu/kind2_user_doc/home.html#kind-2) for more details.
