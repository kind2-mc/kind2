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
