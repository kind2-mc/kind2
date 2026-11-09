---
title: "Sets"
weight: 11
---

Set types have the syntax `set<T>`, where `T` is any type that does not contain
sets, maps, or arrays. For example `set<int>` denotes (streams of) sets of integers, and
`set<[bool, int]>` denotes (streams of) sets of Boolean and integer pairs.

Sets are **finite**: a set of type `set<int>` has finitely many elements,
and Kind 2 reports no counterexample that relies on an infinite set (see
[Finiteness](#finiteness) below). Sets that may be infinite have the type
`iset<T>` (see [Possibly infinite sets](#possibly-infinite-sets)).

**Set literals** can be constructed with curly braces with comma-separated elements,
e.g. `{ 1 }`, `{ 1, 2, 3 }`, and `{ x, 4 }` (assuming `x` has type `int`).
Type annotations are *required* for empty sets (e.g. `{}@<int>`).

The built-in set operators are **set union** (denoted by `+`),
**set intersection** (denoted by `*`), and
**set difference** (denoted by `-`), and
**set membership** (denoted by `in`).
All are infix and take the expected semantics;
see below for an example.

Sets also support **structural equality** (denoted by `=`) and
**structural disequality** (denoted by `<>`). Two sets are structurally
equal when they contain exactly the same elements, regardless of how they
were constructed (e.g., `{ 1, 2 } = { 2, 1, 1 }` is valid).

Two sets of the same type can also be compared with the **subset**
(denoted by `<=`), **proper subset** (denoted by `<`), **superset**
(denoted by `>=`), and **proper superset** (denoted by `>`) operators.
`s1 <= s2` holds when every element of `s1` is also an element of `s2`, and
`s1 < s2` holds when, in addition, the two sets are not equal
(e.g., `{ 1, 2 } < { 1, 2, 3 }` and `{ 1, 2 } <= { 2, 1, 1 }` are valid, but
`{ 1, 2 } < { 2, 1, 1 }` is not). `s1 >= s2` and `s1 > s2` are `s2 <= s1` and
`s2 < s1`, respectively.

```lustre
node N (s1, s2: set<int>) returns (out: set<int>) 
let
  out = s1 * { 1, 2, 3 } + {}@<int>;

  check forall (i: int) not (i in s1 + s2) = (not (i in s1) and not (i in s2));
  check forall (i: int) (i in s1 - s2) = (i in s1 and not (i in s2));
  check forall (i: int) i in out => (i = 1 or i = 2 or i = 3);

  check out <= { 1, 2, 3 };
  check s1 * s2 <= s1 and s1 <= s1 + s2;
  check {}@<int> <= s1;
tel
```

## Finiteness

Sets are finite. Kind 2 encodes them as arrays, which may be infinite, and
only constrains them to be finite where it makes a difference: a
counterexample can only rely on an infinite set when a quantifier observes
its elements, as in `exists (i: int) not (i in s)`, which every finite set
of integers satisfies. Without quantifiers, a counterexample tests the
membership of finitely many elements and holds of finite sets too; sets over
a finite type (`bool`, enumerations, subranges, machine integers, and tuples
and records of those) are always finite.

Nor can a quantifier that a counterexample satisfies with a witness: a
counterexample to an invariant property `forall (i: int) (i in s) => i >= 0`
is a set with a negative element, and a trace to a reachable property
`exists (i: int) i in s` is one where the set has an element, which a
finite set can be in either case. Only a quantifier that the counterexample
must satisfy for every element can observe that a set is infinite: an
`exists` in an invariant property, a `forall` in a reachable property, and
any quantifier elsewhere in the model (an assumption, an equation, a type).

For the sets whose elements such a quantifier, or a function called within
one, can observe, Kind 2 first analyzes the model without the finiteness
constraints, which slow the solvers down and which a proof does not need.
When it finds a counterexample to a property that depends on such a set, it
does not report it right away. It looks for a counterexample with the same
inputs and finite sets, with a short time limit, and reports that one if it
finds it. Otherwise it runs the analysis again with the sets constrained to
be finite (the log says so), and reports a counterexample only if it is
found again. The constraints apply to the sets that the model does not
build from other sets (inputs, sets given by `any`, outputs of imported
nodes, free constants), which are finite when those are: each is included in
a finite universe of its element type.

A property that holds only because a set is finite, such as
`exists (i: int) not (i in s)`, is therefore not reported falsifiable, but
it is typically not proved either, and is left unknown.

## Possibly infinite sets

The type `iset<T>` is the type of sets of elements of type `T` that may be
infinite. It has the same operators as `set<T>`, and Kind 2 never constrains
its sets to be finite: a counterexample that relies on an infinite set is a
genuine one, and it is reported right away. A model whose sets may be
infinite, or that does not need them to be finite, avoids the cost of the
[finiteness](#finiteness) check this way.

A finite set is a possibly infinite one: a set (or a set literal) can be
used where an `iset` is expected, as the value of a variable, an argument of
a node or the operand of an operator, and an operation on sets one of which
is possibly infinite gives a possibly infinite set. A possibly infinite set
cannot be used where a finite one is expected.

```lustre
node Extend (s: iset<int>; x: int) returns (t: iset<int>)
let
  t = s + { x };

  check x in t;
  -- Falsifiable, by a set s of every integer. With s of type set<int>,
  -- the property holds but is left unknown (see Finiteness)
  check exists (i: int) not (i in t);
tel
```
