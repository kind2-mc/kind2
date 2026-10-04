---
title: "Enumeration types"
weight: 6
---

```lustre
type my_enum = enum { A, B, C };
node n (x : my_enum, ...) ...
```

Enumerated datatypes are encoded as subranges so that solvers handle arithmetic
constraints only. This also allows to use the already present quantifier
instantiation techniques in Kind 2.

## Selecting on an enumerated value

A `when` expression evaluates only its selected branch, so a stream can be
defined by cases on the value of an enumerated stream, as a Lustre V6 `merge`
on an enumerated clock does:

```lustre
o = when c = A then x else w + 1;
```

A temporal operator or a node call in a branch only advances at the steps at
which the branch is selected (see [Restart]({{< relref "/inputs-and-outputs/lustre#restart" >}})
for the correspondence with the clock operators of Lustre).
