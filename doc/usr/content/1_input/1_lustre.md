# Lustre

Lustre is a functional, synchronous dataflow language. Kind2 supports most of the Lustre V4 syntax and some elements of Lustre V6. See the file [examples/syntax-test.lus](../examples/syntax-test.lus) for examples of all supported language constructs.


## Lustre contract extension

The Kind 2 contract formalism build on the traditional assume/guarantee framework and offers a finer granularity on the encoding of a specification. A contract in Kind 2 is typically composed of several *modes*.

A specification for a component usually comes as a list of items describing the
expected behavior of said component in different cases. Consider a component with signature

```
node component (on, off: bool) returns (active: bool) ;
```

Here is a semi-formal specification for this component :

name | require  |   | ensure
:---:|:--------:|:-:|:------:
*nop* | `(not on) and (not off)` | `=>` | `active = (pre active)`
*on* | `on` | `=>` | `active`
*inhibited* | `active` raised less than `n` cycles ago | `=>` | `active`
*off* | `(not on) and off` and `active` raised more than `n` cycles ago | `=>` | `not active`


Writing contracts in Kind 2 amounts to writing these items, or *modes*, and let the engine construct the actual assume/guarantee contract. A mode is a *require* and an *ensure*, and a *mode implication* is `require => ensure`.

The assume/guarantee contract corresponding to a set of modes `{m_i}` is **the assume**: the disjunction of the `require_i`, and **the guarantee**: the conjunction of the mode implications. The semantics of the modes is thus

> assuming we always are in the context (require) of at least one mode, then all the mode implications are true, *i.e.* the component should behave consistently with the specification.

In addition one can use a *global mode* to further restrict the context in which a component may be used, *i.e.* strengthen the assumption part of the contract. A global mode also has a require and an ensure, the difference being that its require is always assumed to be true. The assumption becomes

```
require and (or (require_i))
```

and the guarantee is now

```
(require => ensure) and (and (require_i => ensure_i))
```

which is the same as

```
ensure and (and (require_i => ensure_i))
```

since `require` has to be true anyways.

The following sections present the
[syntax for inlined contracts](#lustre-inlined-contracts)
to specify modes directly in the lustre node, and the
[CoCoSpec syntax](#lustre-cocospec-contracts)
allowing to declare modes outside of the node and attach them as needed.


## Lustre inlined contracts


## Lustre CoCoSpec contracts




