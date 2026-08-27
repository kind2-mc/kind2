---
title: "Algebraic Datatypes"
weight: 14
---

Kind 2 supports **algebraic datatypes** (ADTs).
An ADT packages together a fixed set of *constructors*, each of which may
carry zero or more named *fields*.

## Declarations

An ADT is introduced with the `datatype` keyword:

```text
datatype Shape =
  | Circle (radius: real)
  | Rectangle (width: real, height: real)
  | Point;
```

Each constructor is separated by `|`. A constructor with no fields (e.g.
`Point`) is called *nullary*. Fields are listed inside parentheses and
separated by commas.

Multiple ADTs can be declared in a single file, and they may be **recursive**:

```text
datatype List = Cons (head: int, tail: List) | Nil;

datatype Nat = Succ (pred: Nat) | Zero;
```

## ADT Terms

A value of an ADT is built by applying a constructor to its field values:

```text
datatype Shape = Circle (radius: real) | Rectangle (width: real, height: real);

node main(r: real) returns (s: Shape);
let
  s = Circle(r);
tel
```

A nullary constructor is written without parentheses:

```text
datatype Color = Red | Green | Blue;
const c: Color = Red;
```

ADT equality (`=` and
`<>`) is structurally defined: two values are equal if and only if they were built with
the same constructor and all their fields are pairwise equal (within this given constructor).

## Pattern Matching

The primary way to inspect an ADT value is with match expressions of the form `match ... with ... end`:

```text
datatype Color = Red | Green | Blue;

node main(c: Color) returns (ok: bool);
let
  ok = match c with
    | Red   : true
    | Green : false
    | Blue  : true
  end;
tel
```

Each arm `| C (x1, ..., xn) : e` introduces fresh pattern variables
`x1, ..., xn` that are bound to the fields of constructor `C` and are in
scope only within `e`. Nullary constructors are matched without parentheses.
The `match` expression is well-typed only when every constructor of the ADT
is covered (exhaustiveness is checked statically).

Nested patterns are supported---a field position can itself be a constructor
pattern:

```text
datatype List = Cons (head: int, tail: List) | Nil;

-- Match the first two elements
out = match inp with
  | Cons (i, Cons (j, _)) : i + j
  | Cons (i, Nil)         : i
  | Nil                   : 0
end;
```

A wildcard `_` matches any value and binds no name.

## Testers

A **tester** `C?(e)` is a Boolean expression that is `true` if and only if `e` was
built with constructor `C`:

```text
datatype Shape = Circle (radius: real) | Rectangle (width: real, height: real);

node main(s: Shape) returns (is_circle: bool);
let
  is_circle = Circle?(s);
tel
```

Testers are convenient in conditions where matching on field values is not
required:

```text
datatype Option<T> = None | Some (val: T);

node main(x: Option<int>) returns (ok: bool);
let
  ok = Some?(x) and then x.val > 0;
tel
```

## Selectors

A **selector** `e.f` extracts field `f` from an ADT value `e`. The field
`f` must belong to exactly one constructor of `e`'s type. The selector is
*partial*: its result is well-defined only when `e` was built with the
constructor that has field `f`. Kind 2 generates a **proof obligation** for
each selector use, requiring that the correct constructor is active at the point
of use. For example, `s.radius` generates an obligation that `Circle?(s)`
holds. The obligation is reported as a property named
`Selector[L<line>C<column>]`, positioned at the `.` of the selector.
When the obligation does not hold, the value of the selector is arbitrary but
fixed for a given ADT value: two reads of the same value agree, and equal
values give equal results.

### Discharging the obligation

To discharge the proof obligations, one must only use selectors in contexts where
the constructor of the term is known. For example, the usage of a tester `C?(t)`
in an assumption, the antecedent of a lazy implication `==>`, or
the guard of a `when` block is sufficient to prove the well-foundedness
of the corresponding selector in the node/function body,
lazy implication antecedent, or `then` branch expression, respectively.
Only the *lazy* forms guard a selector. The branches of `if ... then ... else
...`, the operands of `and`, `or` and `=>`, the operands of an `arrow`, and the
arms of a `merge` are all evaluated unconditionally, so a tester there does not
discharge an obligation.

```text
datatype Shape = Circle (radius: real) | Rectangle (width: real, height: real);

node is_large_circle(s: Shape) returns (ok: bool);
let
  ok = Circle?(s) ==> s.radius > 10.0;
tel
```

## Polymorphic ADTs

ADT declarations may have **type parameters**, making them polymorphic:

```text
datatype Option<T> = None | Some (val: T);
datatype Either<A; B> = Left (left: A) | Right (right: B);
```

A polymorphic ADT is instantiated by supplying type arguments:

```text
datatype Option<T> = None | Some (val: T);

node main(i: int; r: real) returns (ok: bool);
var xi: Option<int>;
    xr: Option<real>;
let
  xi = Some(i);
  xr = Some(r);
  ok = Some?(xi) and Some?(xr);
tel
```
