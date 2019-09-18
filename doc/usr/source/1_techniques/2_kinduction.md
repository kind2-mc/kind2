## k-Induction

**k-Induction** is a well-known technique for the verification of transition systems. A k-induction engine is composed of two parts: *base* and *step*. Base performs bounded model checking on the properties, *i.e.* checks the **base case**. Step checks whether it is possible to reach a violation of one of the properties from a trace of states satisfying them: the **inductive step**.

In Kind 2 base and step run in parallel, and can be enabled separately. Running
step alone with

```
kind2 --enable IND <file>
```

will not yield anything interesting, as step cannot falsify properties nor prove anything without base. To run the actual k-induction engine, you must enable base (`BMC`) and step (`IND`):

```
kind2 --enable BMC --enable IND <file>
```

### Options

k-Induction can be tweaked with the following options.

`--bmc_max <int>` (default `0`) -- sets an upper bound on the number of unrolling base and step will perform. `0` is for unlimited.

`--ind_compress <bool>` (default `false`) -- activates path compression in step, **i.e.** counterexamples with a loop will be dismissed. You can activate several path compression strategies:

* `--ind_compress_equal <bool>` (default `true`) -- compresses states if they are equal modulo inputs
* `--ind_compress_same_succ <bool>` (default `false`) -- compresses states if they have the same successors (experimental)
* `--ind_compress_same_pred <bool>` (default `false`) -- compresses states if they have the same predecessors (experimental)

`--ind_lazy_invariants <bool>` (default `false`) -- deactivates eager use of invariants in step. Instead, when a step counterexample is found each invariant is evaluated on the model until one blocks it. The invariant is then asserted to block the counterexample, and step starts a new check-sat.

