## Post Analyses Treatments

Post-analysis treatments are flag-activated Kind 2 features that are not
directly related to verification. The current post-analysis treatments available are

- certification,
- compilation to Rust,
- test generation,
- contract generation, and
- invariant logging.

All of them are deactivated by default. Post-analysis treatments run on the
*last analysis* of a system. It is defined as the last analysis performed by
Kind 2 on a given system. With the default settings, Kind 2 performs a single,
monolithic analysis of the top node. In this case, the *last analysis* is this
unique analysis.

This behavior is changed by the `compositional` flag. For example, say Kind 2
is asked to analyze node `top` calling two subnodes `sub_1` and `sub_2`, in
compositional mode. Say also `sub_1` and `sub_2` have contracts, and that
refinement is possible.
In this situation, Kind 2 will analyze `top` by abstracting its two subnodes.
Assume for now that this analysis concludes the system is safe. Kind 2 has
nothing left to do on `top`, so this compositional analysis is the *last
analysis* of `top`, Kind 2 will run the post-analysis treatments.
Assume now that this purely compositional analysis discovers a counterexample.
Since refinement is possible, Kind 2 will refine `sub_1` (and/or `sub_2`) and
start a new analysis. Hence, the first, purely compositional analysis is not
the *last analysis* of `top`.
The analysis where `sub_1` and `sub_2` are refined is the *last analysis* of
`top` regardless of its outcome (assuming no other refinement is possible).

Long story short, the *last analysis* of a system is either the first analysis
allowing to prove the system safe, or the analysis where all refineable systems
have been refined.

The `modular` flag forces Kind 2 to apply whatever analysis / treatment the
rest of the flags specify to all the nodes of the system, bottom-up.
Post-analysis treatments respect this behavior and will run on the last
analysis of each node.


### Prerequisites

Some treatments can fail (which results in a warning) because some conditions
were not met by the system and/or the last analysis. The prerequisites for each
treatment are:

| Treatment | Condition | Notes |
|:---:|:---|:---|
| certification | last analysis proved the system safe | |
| compilation to Rust | none | will fail if node is partially defined |
| test generation | system has a contract with more than one mode | |
|                 | last analysis proved the system safe          | |
| contract generation | none | experimental |
| invariant logging | last analysis proved the system safe | |


### Silent Contract Loading

Two of the treatments mentioned above end up, if successful, generating a
contract for the current node: invariant logging and contract generation. The
natural way to benefit from these contracts is to import them explicitly in the original system.

If you do not import these contracts however, *silent contract loading* will
still try to take advantage of them. That is, contracts logged by Kind 2 in
previous runs will be loaded as *candidate properties*. A candidate property
is similar to a normal property except that it is allowed to be falsifiable.
That is, falsification of a candidate property does not impact the safety of
the system under analysis.

Note that if you change the signature of the system, silent contract loading
may fail. This failure is silent, and simply results in Kind 2 analyzing the
system without any candidates.

> **NB**: for silent contract loading to work, it needs to be able to find
> the contracts. In practice, Kind 2 will look in the *output directory*
> specified by `--output_dir`, the default being `<input_file>.out/`.
>
> Kind 2 writes the contracts resulting from invariant logging and contract
> generation in the output directory, in a sub-directory named after the
> system the contract is for.
>
> As a result, running `kind2 --log_invs on --lus_main top example.lus` will
> log invariants in `example.lus.out/top/kind2_strengthening.lus`.
> Running the same command again will cause Kind 2 to silently load this
> contract as candidates.
>
> If one changes the output directory though, for instance by running
> `kind2 --output_dir out --log_invs on --lus_main top example.lus`, then
> silent contract loading will not find the contracts written to
> `example.lus.out/top` because it will look in `out/top`.
>
> Running `kind2 --output_dir out --log_invs on --lus_main top example.lus`
> two times however results in Kind 2 silently loading the contract generated
> during the first analysis in `out/top` on the second run.
