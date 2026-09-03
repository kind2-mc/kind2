---
title: "A Lustre Primer"
weight: 1
---
This page is a self-contained introduction to Lustre,
the input language of Kind 2, intended for new users.

## Basic Concepts

### Lustre Nodes

Lustre is a language for modeling and implementing
reactive systems in the synchronous model.
It can be seen indifferently as either a declarative parallel programming language
or as an executable specification language.
The most basic unit of computation in a Lustre program, or model, is a **node**,
which can be viewed as a stream transformer:
it takes streams of input and produces streams of output.
Operationally, a node reads its input and generates its output incrementally
in discrete *timesteps*, or cycles, determined by an abstract global clock.
At each cycle, all output values are assumed to be computed instantaneously
from the current input and state values.
By default, all nodes in a model compute synchronously and in parallel according
to the global clock.

A **stream** is an infinite sequence of values, all of the same (given) type.
Hence, a Lustre node can be viewed as modeling an infinite sequence of discrete
timesteps, where at each timestep, each node variable takes its next value.

Below, the node `Combine` takes as input two integer streams \(x\) and \(y\), and
produces integer stream \(z\) as output. If we consider \(x = (x_0, x_1, \dots)\)
and \(y = (y_0, y_1, \dots)\), then `Combine` produces output
\(z = (x_0 + 2 \cdot y_0,\ x_1 + 2 \cdot y_1,\ \dots)\) (or more concisely,
\(z_n = x_n + 2 \cdot y_n\) at each timestep \(n\)).

{{< callout type="info" >}}
It is not possible to specify a stream pointwise in Lustre, so when we write
\(x = (1, 2, 3, \dots)\), say, we are writing a mathematical statement about
stream \(x\), not an equation in Lustre.
{{< /callout >}}

Notice that `z = x + 2*y` is an equation between streams of integers.
The operators `=`, `+` and `*` are stream operators
obtained by lifting to streams the corresponding operators over integers.
The same is true of concrete constants in Lustre, such as `2` below,
which are streams with the same value at each time step.
Lustre respects typical rules of operator precedence, so `x + 2*y` will be
parsed as `x + (2*y)` rather than `(x + 2)*y`.

```text
node Combine(x: int; y: int) returns (z: int);
let
  z = x + 2*y;
tel
```

The first line of `Combine` is referred to as the **node interface**, where the
node's inputs and outputs, and their types, are declared.

The code block surrounded by `let` and `tel` denotes
the **node implementation** (or **node body**),
where the node's outputs are defined in terms of the node's inputs.
A node implementation is composed of a set of equations of the form
`<var> = <expr>`, where `<var>` is an output variable or a local variable (see
below) and `<expr>` is an expression in terms of any of the variables that are
in scope.

Nodes can have more than one output stream as exemplified by the node `TwoOuts`
below.

```text
node TwoOuts(x: int) returns (double: int; square: int);
let
  double = x + x;
  square = x * x;
tel
```

Another optional component that can be added to a Lustre node is a set of
**local declarations**. The local variables and constants declared in this
section can be used in the node implementation, but they are not exposed in the
node interface.

Finally, **global constants** can be declared outside of the node body, and are
visible within every node.

Below is another version of `Combine`, where the value `2` is stored in a global
constant `C` and the local variable `l` is used to store an intermediate
computation.

```text
const C: int = 2;
node Combine(x: int; y: int) returns (z: int);
var l: int;
let
  l = C*y;
  z = x + l;
tel
```

The order of the equations in the body of a node is immaterial.
However, the definition of a variable provided by the equations
cannot be *circular*, as explained in
[Declarative Semantics](#declarative-semantics).

In Lustre, identifiers (for constants, variables, types, and keywords)
are delimited by whitespace characters, separators
such as parentheses and semicolons, and other symbols such as `+`, `*` and so on,
as in most programming languages.
Whitespace is, however, not semantically meaningful.
For instance, indentation does not change the parsing of an expression.

### Node Analyses

Lustre was designed to be a programming language.
Well-formed Lustre nodes are executable in the sense that they can be compiled
to executable programs computing their output values incrementally
from their input values and internal state.

Here, we are mostly interested in *analyzing* Lustre programs and their possible
behavior with a tool like Kind 2.

A basic form of analysis that can be applied to a Lustre program is **node
simulation**. During simulation, the user specifies a number \(n\) of timesteps
to simulate, as well as the first \(n\) values of each input variable. Given this
information, the first \(n\) values of each output variable are computed. For the
`Combine` node above, if the user performed simulation with \(n = 3\) and with
given input stream prefixes \(x = (1, 2, 3)\) and \(y = (4, 5, 6)\), the output
value \(z = (9, 12, 15)\) would be computed.

Another form of analysis is **property checking**, where the user specifies a
property in the node body (in the form of a Boolean expression) to be proven or
disproven **invariant**, that is, true at every time step.
For example, the conditional property `y > 0 => l > y` in the node below would be
proven invariant.
In contrast, the property `z > 0` would be disproven in the `Combine` node,
as `z` is negative in timesteps where both `x` and `y` are negative.

```text
const C: int = 2;
(* Example with 
   two properties
*)
node Combine(x: int; y: int) returns (z: int);
var l: int;
let
  l = C*y;
  z = x + l;

  check y > 0 => l > y; -- invariant
  check z > 0;          -- not invariant
tel
```

We discuss properties in greater detail in 
[Specifying and Checking Properties](#specifying-and-checking-properties)
below. 

## Comments

The example above shows the two ways to add comments in Lustre programs.
Single line comments are introduced by the character sequence `--`.
Multiline comments are delimited by the sequences `(*` and `*)`.
Nested multiline comments are not allowed.

## Primitive Types

Lustre's primitive types are `bool`, `int`, and `real`.
Informally, we say that `bool` is the type of Boolean values (`true`, `false`).
Strictly speaking, `bool` is the type of *streams* of Boolean values.
We identify the two for brevity since there is no possibility of confusion
as all values in Lustre are streams.
The same is true for the other types.

{{< callout type="info" >}}
It is not possible to refer directly to the scalar values in a stream in Lustre.
Even constants, such as `true`, `2`, `3.6` denote streams of values, not
individual values.
{{< /callout >}}

In the **idealized** semantics of Lustre, `int` is the type of mathematical
(infinite precision) integers, and `real` is the type of real numbers.
Lustre compilers approximate that semantics by using machine integers
for `int` and floating point numbers for `real`.
In contrast, Kind 2 is faithful to the idealized semantics.

Lustre supports the Boolean operators `not`, `and`, `or`, `xor`, and `=>`
(implies), as well as the arithmetic operators `+`, `-` (both unary and binary),
`*`, `/`, `mod`, and `div` (integer division), all with the expected arity and
(pointwise) semantics.
The arithmetic operators (`+` and so on) are overloaded as they apply
both to `int` and `real` terms.
The binary operators, however, are applicable only to arguments of the same type
(both `int` or both `real`).
Numerals (`0`, `1`, ...) have type `int`
while decimals (e.g., `0.0`, `31.97`) have type `real`.

Alongside the mathematical `int` and `real`, Lustre offers fixed-width
**machine integers**, signed as `sint<N>` and unsigned as `uint<N>` for a
width `N` in bits, with the concise names `int8`, `uint8`, `int16`, and so on
for the widths 8, 16, 32, and 64. Unlike `int`, these types are finite: their
values are built by applying a conversion operator to a literal, as in
`uint8 27`, and their arithmetic wraps around modulo the width of the type, as
in C, with signed values represented in two's complement. They also support the
bitwise operators `&&`, `||`, and `!`, and the shifts `lsh` and `rsh`. See
[Machine Integers]({{< relref "/docs/inputs-and-outputs/machine-ints" >}}) for
the conversion rules between widths and the solver restrictions these types
imply.

## Conditionals

Equations can be grouped under a condition with an `if` *statement*, closed
with `fi`:

```text
node Sign(x: int) returns (neg, pos: bool);
let
  if x < 0 then
    neg = true; pos = false;
  elsif x > 0 then
    neg = false; pos = true;
  else
    neg = false; pos = false;
  fi
tel
```

Each condition is evaluated once per timestep, and every variable assigned by
the block takes the same branch. 

Conditions can also be encoded as 
`if` *expressions*:

```text
if <expr_0> then <expr_1> else <expr_2>
```

where `<expr_0>` has type `bool`, and `<expr_1>` and `<expr_2>` must have the
same type. 

```text
node Max(x, y: int) returns (m: int);
let
  m = if x > y then x else y;
tel
```

## Temporal Operators

Lustre contains two temporal operators:
the binary operator `->`
(pronounced "arrow" and not to be confused with `=>`) and
the unary operator `pre`.

The arrow operator is an *initialization* operator, where the expression `a -> b`
denotes the stream whose first value is equal to the first value of stream `a`,
and whose \(n\)th value is equal to the \(n\)th value of stream `b` for every
\(n > 0\).
For example, if \(\texttt{a} = (-1, -1, -1, \dots)\) and
\(\texttt{b} = (1, 2, 3, \dots)\), then \(\texttt{a -> b} = (-1, 2, 3, \dots)\).

The `pre` operator can be viewed as referencing the previous value at every
timestep—the expression `pre a` denotes the stream whose value at step \(n\) is
equal to the value of stream `a` at step \(n-1\). For example, if
\(\texttt{b} = (1, 2, 3, \dots)\), then \(\texttt{pre b} = (?, 1, 2, \dots)\).
Notice that with these semantics, `pre b` is undefined in the initial timestep
(denoted by the question mark here).

Kind 2 treats undefined expressions as **underspecified**.
That is, when simulating the stream `pre b`, it could take values
\((-23, 1, 2, \dots)\), \((79, 1, 2, \dots)\), etc.
In other words, Kind 2 assigns the first element of `pre b` an arbitrary integer.
Consistently with that,
a property of a node containing `pre`s is considered invariant only
if it holds at every step, regardless of the value assigned
to the first element of any stream resulting from a `pre` application.

Because `pre` creates underspecified streams, we can combine it with `->` to
obtain fully specified streams. For example, if \(\texttt{b} = (1, 2, 3, \dots)\),
then \(\texttt{0 -> pre b} = (0, 1, 2, 3, \dots)\),
where the arrow operator supplies the initial value \(0\) for the resulting stream.
If an application of `pre` occurs without a corresponding application of `->`,
the `pre` is **unguarded**.
While unguarded `pre`s are allowed in Lustre, Kind 2 will produce warnings
for nodes that contain them as this is usually an oversight by the user and
may lead to unexpected results.

The `pre` operator has the same precedence as other unary operators
such as `not`.
For example, `pre x + y` is read as `(pre x) + y`,
not as `pre (x + y)`.
Note that `pre` distributes over all non-temporal operators.
For instance,
the expression `pre (x + y)` is equivalent to `pre x + pre y`.

To further reinforce how operators work over streams,
the computation of the expression `1 -> (1 + pre x)` is
illustrated in the table below.

| Expression           | \(0\)     | \(1\)       | \(2\)       | ... | \(n\)           |
| -------------------- | --------- | ----------- | ----------- | --- | --------------- |
| `1`                | \(1\)     | \(1\)       | \(1\)       | ... | \(1\)           |
| `x`                | \(x_0\)   | \(x_1\)     | \(x_2\)     | ... | \(x_n\)         |
| `pre x`            | \(?\)     | \(x_0\)     | \(x_1\)     | ... | \(x_{n-1}\)     |
| `1 + pre x`        | \(1 + ?\) | \(1 + x_0\) | \(1 + x_1\) | ... | \(1 + x_{n-1}\) |
| `1 -> (1 + pre x)` | \(1\)     | \(1 + x_0\) | \(1 + x_1\) | ... | \(1 + x_{n-1}\) |

Using temporal operators, we can define a `Counter` node as follows.

```text
node Counter(init: int) returns (out: int);
let
  out = init -> pre out + 1;
tel
```

In `Counter`, the output stream `out` is initialized to the input initialization
value `init`, and it is incremented at every timestep. Notice that `out` is
recursively defined—the \(n+1\)st value of `out` is equal to the \(n\)th value
of `out` plus 1, except in the *base case* of initialization.

The `pre` and `->` operators provide
a declarative and mathematically elegant way to define **stateful** computations.
An alternative, operational way to understand the functionality
of node `Counter` is that `init` is an input variable and
`out` is a *state* variable.
Initially, the value of `out` is that of `init`.
At each successive iteration, the new value of `out` is its old value
(denoted as `pre out`) plus one.

A deceptively difficult example is defining in Lustre a stream with value
\((1, 2, 3, 3, 3, \dots)\), with infinite repetitions of \(3\) from the third
step on.
A first guess might be the term `1 -> (2 -> 3)` or perhaps the term
`(1 -> 2) -> 3`. However, both of these streams will omit the value \(2\), as
they take the initial value from the first argument of the outer arrow (which is
`1` in both cases) and the non-initial values from the second argument of the
outer arrow (which is a stream of `3`s in both cases). A key insight is that the
`pre` operator can also be viewed as a *right-shift operator* on streams. From
this, the correct answer is `1 -> pre (2 -> 3)`, which takes the initial value 1
and the remaining values from the stream \((?, 2, 3, 3, 3, \dots)\).

The table below helps illustrate the difference between the various expressions
above.

| Expression            | \(0\) | \(1\) | \(2\) | \(3\) | ... |
| --------------------- | ----- | ----- | ----- | ----- | --- |
| `1`                 | \(1\) | \(1\) | \(1\) | \(1\) | ... |
| `2`                 | \(2\) | \(2\) | \(2\) | \(2\) | ... |
| `3`                 | \(3\) | \(3\) | \(3\) | \(3\) | ... |
| `1 -> 2`            | \(1\) | \(2\) | \(2\) | \(2\) | ... |
| `2 -> 3`            | \(2\) | \(3\) | \(3\) | \(3\) | ... |
| `pre (2 -> 3)`      | \(?\) | \(2\) | \(3\) | \(3\) | ... |
| `1 -> (2 -> 3)`     | \(1\) | \(3\) | \(3\) | \(3\) | ... |
| `(1 -> 2) -> 3`     | \(1\) | \(3\) | \(3\) | \(3\) | ... |
| `1 -> pre (2 -> 3)` | \(1\) | \(2\) | \(3\) | \(3\) | ... |

A node that generates the stream \((1, 2, 3, 3, 3, \dots)\) from no inputs
can then be defined as follows.

```text
node N() returns(y: int);
let
   -- defining output stream (1, 2, 3, 3, 3, ...)
   y = 1 -> pre (2 -> 3);
tel
```

Another deceptively difficult example is the following Lustre node which outputs
the stream of all Fibonacci numbers in increasing order.
Because `Fib` is defined in terms of the two previous Fibonacci values, the first
*two* steps need to be initialized. The example is tricky and may require some
thought for those new to Lustre.

```text
node Fibonacci() returns(Fib: int);
let
  Fib = 1 -> pre (1 -> Fib + pre Fib);
tel
```

The example can perhaps be easier to see by introducing local names
for the subexpressions on the equation's right-hand side.

```text
node Fibonacci() returns(Fib: int);
  var preFib: int;
  var prepreFib: int;
let
  preFib = 0 -> pre Fib;
  prepreFib = 1 -> pre preFib;
  Fib = preFib + prepreFib;
tel
```

## Frame Blocks

A `frame` block names a set of variables, gives them optional initial values,
and defines them in a body between `let` and `tel`. Any variable the body
leaves undefined at a step *stutters*: it keeps the value it had at the previous step, starting
from its initialization.

```text
node Hold(latch: bool; v: int) returns (out: int);
let
  frame ( out )
  out = 0;
  let
    if latch then
      out = v;
    fi
  tel
tel
```

Here `out` starts at `0`, takes the value of `v` whenever `latch` is true, and
otherwise holds its previous value.

## Declarative Semantics

Lustre has a **declarative** semantics, meaning that the order of equations in
node bodies does not matter. Because of this, node equations should not be viewed
imperatively as assignments; instead, a node body is a set of stream constraints
of the form `<var> = <expr>`.

To illustrate this concept, consider the following `Factorial` node which outputs
a stream of factorial numbers (the \(n\)th value of the stream is \(n!\)). When
defining output stream `F`, we can reference the helper stream `N` before it is
defined.

```text
node Factorial() returns (F: int);
var N: int;
let
  -- all the factorial numbers
  F = 1 ->  N * (pre F);
  -- all the natural numbers
  N = 0 -> (pre N) + 1;
tel
```

Even though Lustre has a declarative semantics and allows recursive definitions,
circular definitions are rejected. For example, the following node is invalid
Lustre because the \(n\)th value of `out1` is defined in terms of the \(n\)th
value of `out2`, and the \(n\)th value of `out2` is defined in terms of the
\(n\)th value of `out1`.

```text
node Circular() returns (out1, out2: int);
let
  out1 = out2 + 1;
  out2 = out1 - 1; 
tel
```

In fact, there are no values for the streams `out1` and `out2` that satisfy both
equations. However, even if it is possible to satisfy all equations,
as in the following example,
any node with a circular dependence is conservatively rejected.

```text
node Circular() returns (out1, out2: int);
let
  out1 = out2;
  out2 = out1; 
tel
```

Note that there is no circularity in the definition of local variable `N`
of node `Factorial` since `N` is defined in terms of `pre N`, and
not in terms of `N` itself.

## Composite Types

In addition to the primitive types, Lustre provides records, arrays, tuples,
sets, maps, and algebraic datatypes.

### Records

Record types have the syntax

```text
struct { <field_1>: <type_1>; ...; <field_n>: <type_n> }
```

They must be named and declared with a global **type declaration** of the form

```text
type <ty_name> = <type>;
```

Record values can be constructed with the syntax

```text
<ty_name> { <field_1> = <expr_1>; ...; <field_n> = <expr_n> }
```

and destructed with the syntax

```text
<record_term>.<field>
```

as seen in the next example.

```text
type sensorData = struct { speed: real; height: real; direction: int };

node AdjustSensorData(in: sensorData) returns (out: sensorData);
  var h: real;
let
  h = if in.height < 0.0 then 0.0 else in.height;
  out = sensorData { speed = in.speed; 
                     height = h; 
                     direction = in.direction };
tel
```

See [Records]({{< relref "/docs/inputs-and-outputs/records" >}}) for the
remaining record operations, such as element updates.

### Arrays

Array types have the syntax

```text
<element_type>^<numeral>
```

Values of an array type can be constructed in two different ways.
Lustre supports the **array literal** syntax of the form

```text
[<element_1>, ..., <element_n>]
```

as well as the (constant) **array constructor** syntax of the form

```text
<element>^<length>
```

Array elements can be accessed with the standard **array access** syntax
`<array_var>[<index>]`, with zero-based indexing.

```text
node TwoArrays() returns (out1: bool^5; out2: int^4);
let
  out1 = [true, true, false, true, false];
  out2 = 1^4;   -- equivalent to out2 = [1, 1, 1, 1]
tel
```

```text
node Nth(in: int^10; k: int) returns (out: int);
let
  out = if 0 <= k and k < 10 then in[k] else in[0];
tel
```

See [Arrays]({{< relref "/docs/inputs-and-outputs/arrays" >}}) for element
update, structural equality, and inductively defined arrays.

### Tuples

A tuple type is written `[<type_1>, ..., <type_n>]`. Tuples are constructed
with the syntax `'(<expr_1>, ..., <expr_n>)`, and their components are read
back by position with `<tuple>[<index>]`, using zero-based indexing. The index
must be a concrete numeral, since it selects a component rather than computing
one.

```text
type Pair = [int, bool];

node Swap(p: Pair) returns (q: [bool, int]);
let
  q = '(p[1], p[0]);
tel
```

### Sets and Maps

The type `set<T>` denotes streams of finite sets of elements of type `T`, and
the type `map<K, V>` denotes streams of finite maps from keys of type `K` to
values of type `V`. Set literals are written with braces, and map literals with
the `map[...]` constructor:

```text
node N(s: set<int>; m: map<int, int>) returns (u: set<int>; v: int);
let
  u = s + { 1, 2, 3 };
  v = m[0];
tel
```

The set operators are union `+`, intersection `*`, difference `-`, and
membership `in`. A map is updated (functionally, producing a copy) with
`m[k := v]`, read with `m[k]`, and restricted with `m - s`, which removes every
key in the set `s`. Membership `k in m` tests for a key.

Empty map and set literals carry no element type of their own, so the user must annotate types:
`{}@<int>` and `map[]@<int, int>`.

Reading a key that a map does not bind, as in `m[k]` where `k` is absent,
yields an unconstrained value rather than an error. The read is still
*functional*, though: the same key always yields the same value at the same
timestep.

See [Sets]({{< relref "/docs/inputs-and-outputs/sets" >}}) and
[Maps]({{< relref "/docs/inputs-and-outputs/maps" >}}) for the full operator
set and the restrictions on element and key types.

### Algebraic Datatypes

An algebraic datatype packages a fixed set of *constructors*, each carrying
zero or more named fields. They are introduced with the `datatype` keyword,
with constructors separated by `|`:

```text
datatype Shape =
  | Circle (radius: real)
  | Rectangle (width: real, height: real)
  | Point;
```

A value is built by applying a constructor to its field values, with nullary
constructors such as `Point` written without parentheses. Values are taken
apart with a `match` expression, whose arms must cover every constructor. Each
arm names fresh variables for the fields of its constructor, in scope only
within that arm:

```text
datatype Shape = Circle (radius: real) | Rectangle (width: real, height: real);

node Area(s: Shape) returns (a: real);
let
  a = match s with
    | Circle (r)       : 3.14 * r * r
    | Rectangle (w, h) : w * h
  end;
tel
```

Datatypes may be recursive, which makes it possible to describe unbounded
structures such as lists:

```text
datatype IntList = Cons (head: int, tail: IntList) | Nil;
```

See [Algebraic Datatypes]({{< relref "/docs/inputs-and-outputs/algebraic-datatypes" >}})
for testers, selectors, and polymorphic datatypes.

## Enumerations and Subranges

Two named types describe restricted sets of scalar values.

An **enumeration** is a finite set of named constants:

```text
type Color = enum { Red, Green, Blue };
```

A **subrange** describes the integers within given inclusive bounds, with the
syntax `subrange [LB, UB] of int`. Either bound may be `*`, leaving that side
unbounded, and either may be a symbolic constant expression rather than a
literal:

```text
type Percent = subrange [0, 100] of int;
type Pos = subrange [1, *] of int;
```

Subranges are not merely documentation. A subrange on an input or a free
constant is an *assumption* Kind 2 may rely on; a subrange on an output, a
local variable, or a defined constant is a *proof obligation* Kind 2 must
discharge. The node below type-checks, but Kind 2 falsifies the obligation on
its output, since nothing prevents `x + y` from exceeding `100`:

```text
type Percent = subrange [0, 100] of int;

node Add(x, y: Percent) returns (z: Percent);
let
  z = x + y;
tel
```

Kind 2 reports this as a failed property named for the position of the
offending declaration, alongside a counterexample — here, any two inputs
summing above `100`.

This assumption/obligation split is the same one that governs refinement
types, described next; a subrange is really a special case of one.

## Refinement Types

A **refinement type** restricts a base type with a predicate. It is written
`subtype { <var>: <base_type> | <predicate> }`:

```text
type Nat = subtype { x: int | x >= 0 };
```

The base type can be any type, including another refinement type, and
refinement types may appear inside composite types (as the element type of an
array or set, for instance).

Where a variable is declared, a more concise form is available: writing
`<var>: <base_type> | <predicate>` in a node's interface or local declarations
means the same thing.

```text
node Sqrt(x: real | x >= 0.0) returns (y: real | y >= 0.0);
```

Refinement types follow exactly the rule given for subranges above:
a refinement type on an input or a free constant is an **assumption**, while
one on an output, a local variable, or a defined constant is a **proof
obligation**. So in `Sqrt`, Kind 2 may assume `x >= 0.0` and must prove
`y >= 0.0`.

See [Refinement Types]({{< relref "/docs/inputs-and-outputs/refinement-types" >}})
for the treatment of defined versus free constants, and for refinement types
nested inside structured types.

## Abstract Types

An **abstract type** is a type declared without a definition:

```text
type T;
```

Kind 2 treats it as an uninterpreted domain: the only operations on its values
are equality `=` and disequality `<>`, and nothing is assumed about how many
values it holds. This is useful to model data whose representation is
irrelevant to the properties being checked.

```text
type T;

function IdT(x: T) returns (y: T);
let
  y = x;
tel
```

## Composition

A Lustre model can be hierarchically defined
by defining nodes in terms of other nodes through the use of **node applications**.
Revisiting the `Counter` node, we can use node applications to instantiate two
distinct counter streams.
In the following example, the output streams `ctr1` and `ctr2`
of node `Top` are defined using expressions that contain node applications.
More specifically, output variable `ctr1` is defined as the stream output by node
`Counter` when applied to input `0`, incremented by `3`, and the output variable
`ctr2` is defined as the stream output by node `Counter` when applied to input `5`.
Output `P1` is a Boolean stream representing the property that `ctr2` is greater
than `ctr1`.

Note that nodes can have no inputs (as node `Top` below)
or no outputs.

```text
node Top() returns (ctr1, ctr2: int; P1: bool);
let
  ctr1 = Counter(0) + 3;
  ctr2 = Counter(5);
  P1 = (ctr2 > ctr1);
tel

node Counter(init: int) returns (out: int);
let
  out = init -> pre out + 1;
tel
```

Node applications must respect the expected type checking rules:
each argument of the application of a node \(N\),
which can be any stream-denoting expression,
must have a type that matches the type of the corresponding input parameter
in \(N\)'s interface.
Similarly, the return type of \(N\) must be
a valid type for the expression that contains the node application.
For example, the return type of `Counter` matches the expected type
for the first argument of the `+` operator in the expression
`Counter(0) + 3`.

Note that the definition of node `Top` includes an application
of node `Counter`,
even though `Top` is defined before `Counter`.
Similarly to equations in a node body, the order of node definitions
in a Lustre model is immaterial.
However, the application graph cannot contain cycles.
In other words, a node cannot be defined, directly or indirectly (through
subnodes), in terms of itself.

In general, an application of a node with a single output stream of some type
\(T\) can occur anywhere an expression of type \(T\) can occur on the right-hand
side of an equation in a node's body.
In contrast, an application of a node with multiple outputs can occur only in
an equation of the form

```text
(<var_1>, ..., <var_n>) = <node_name>(<arg_1>, ..., <arg_m>);
```

or

```text
<var_1>, ..., <var_n> = <node_name>(<arg_1>, ..., <arg_m>);
```

where `<var_1>`, ..., `<var_n>`
are local or output variables of the node containing the application,
with types matching the types of the outputs of the applied node `<node_name>`,
in the same order as in that node's interface.

```text
node Top(x: int) returns (P1: bool);
  var positive: bool;
  var nonnegative: bool;
let
  (positive, nonnegative) = N(x);
  P1 = positive => nonnegative;
tel

node N(x: int) returns (positive, nonnegative: bool);
let
  positive = (x > 0);
  nonnegative = (x >= 0);
tel
```

### Functions

Besides `node`, the language provides the keyword `function`, used in exactly
the same way but with stricter semantics: a function's outputs must be a
*non-temporal* combination of its inputs
(i.e., *combinational*). 
A function may not use `->`, `pre`,
`merge`, `when`, `condact`, or `activate`, and it may only call other
functions, never nodes. Functions are, in other words, stateless.

```text
function Abs(x: real) returns (y: real);
let
  y = if x < 0.0 then -x else x;
tel
```

A function behaves as a mathematical function: the same inputs always yield the
same outputs, whatever the timestep. This also narrows the scope of its
contract assumptions: a function's guarantees rest on its assumptions holding
at the current step alone, whereas a node's rest on them having held at every
step so far.

### Imported Nodes

A node or function declared `imported` has an interface but no body:

```text
node imported Sensor(t: int) returns (reading: real);
```

For example, this is useful to model an
external routines where the specification is known, but not the implementation. 
For Kind 2 it means the component is *always* abstract: it is
represented solely by its contract (see [Contracts](#contracts) below), and
Kind 2 never looks inside it, because there is nothing to look at. With no contract, the implicit one is
`assume true; guarantee true;`, which says nothing at all — so an imported node
without a contract may produce any 
(well-typed) output whatsoever. 

### Polymorphic Nodes

Nodes and functions may take type parameters, declared in angle brackets after
the name:

```text
node SafePre<T>(x: T) returns (y: T);
let
  y = x -> pre x;
tel

node Top() returns (y1: int; y2: bool);
let
  y1 = SafePre@<int>(0);
  y2 = SafePre@<bool>(false);
tel
```

The `@<...>` instantiation at the call site is usually optional: Kind 2 infers
the type arguments *bottom-up*, by matching the declared parameter types
against the types of the actual arguments, so `SafePre(x1)` (without the annotation) 
would also work here.

However, in some cases, Kind 2 cannot 
infer the type bottom-up.

```text
node Default<T>() returns (y: T);
let
  y = any@<T>;
tel

node Top() returns (b: bool);
let
  b = Default();
tel
```

Kind 2 rejects this during type checking, with

```text
Call requires explicit annotation; type variable T cannot be inferred bottom-up
```

The fix is to supply the type argument explicitly (here, writing `Default@<bool>()`). In short: leave the annotation out, and
add one at the call site if Kind 2 
asks for it.

Type declarations take parameters in the same way, so a user-defined type can
be polymorphic as well. Such a type acts as a *type constructor*: applying it
to types yields a type, which is then written `<name><...>` wherever a type is
expected.

```text
type Pair<T; U> = [T, U];

node Swap<T; U>(x: Pair<T; U>) returns (y: Pair<U; T>);
let
  y = '(x[1], x[0]);
tel
```

## Lazy Operators

Most operators are **eager**: they evaluate every operand, whichever one the
result turns out to depend on. Both branches of `if <cond> then <e1> else <e2>`
are evaluated at each step, and so are both operands of `and`, `or`, and `=>`.

Each has a **lazy** counterpart that evaluates an operand only when the result
depends on it:

| Eager                    | Lazy                       | Right operand evaluated |
| ------------------------ | -------------------------- | ----------------------- |
| `if c then e1 else e2`   | `when c then e1 else e2`   | only the selected branch |
| `e1 and e2`              | `e1 and then e2`           | only when `e1` is true  |
| `e1 or e2`               | `e1 or else e2`            | only when `e1` is false |
| `e1 => e2`               | `e1 ==> e2`                | only when `e1` is true  |

Whenever the right operand *is* evaluated, each lazy operator agrees with its
eager counterpart; the two differ only in what happens to the operand that is
skipped.

That difference is not merely a matter of efficiency. 
Consider reading a field of an algebraic datatype: the selector `x.val` carries a proof obligation that `x`
was built with the constructor that has a `val` field. 

```text
datatype Option = None | Some (val: int);

node Unwrap(x: Option) returns (y: int);
let
  y = when Some?(x) then x.val else 0;
tel
```

Written with `if ... then ... else ...` instead, the same node is falsified:
both branches are evaluated at every step, so `x.val` is read even when `x` is
`None`, and the selector's obligation fails. Under `when`, the `then` branch is
evaluated only where `Some?(x)` holds, and the obligation is discharged. 

The lazy Boolean operators 
can be used to guard selectors in the same way, as in `Some?(x) ==> x.val > 0`,
and well as the division in `x <> 0 and then y / x > 1`.

The same laziness is available at statement level, in the `when` and `cond`
blocks described next.

### Lazy Blocks

The lazy counterpart of the `if` statement is the `when` block, closed with
`end`:

```text
when <cond> then
   <equations>
else
   <equations>
end
```

Further branches are written by nesting another `when` block inside the `else`
branch. A `cond` block gives the same thing a flatter, pattern-matching shape,
with any number of guarded branches and an `otherwise` clause:

```text
cond
  | <cond_1>:
     <equations>
  | <cond_2>:
     <equations>
  otherwise:
     <equations>
end
```

In both, only the selected branch is evaluated, with the consequences
described above. The same restrictions apply: a branch may not contain temporal
operators or calls to nodes, and `if` blocks and lazy blocks may not be nested
inside one another.

Laziness also changes what "the previous value" means. Inside a lazy branch,
`pre x` refers to the value of `x` the last time *that branch was selected*,
which may be several steps earlier. When a lazy block sits inside a
[frame block](#frame-blocks), `last x` is the dependable way to say *the value
at the immediately preceding timestep*.

## Nondeterministic Choice

The operator
`any { <var>: <type> | <predicate> }` denotes an arbitrary stream of values of
the given type satisfying the predicate:

```text
node N(y: int) returns (z: int);
var l: int;
let
  l = any { x: int | x mod 2 = 1 };
  z = y + l;
tel
```

Here `l` is some odd stream, with no further commitment as to which — it may
take a different odd value at every step.

The variant `choose { ... }` is similar to `any { ... }`, but functional 
(that is, given the same type as input, it 
always produces the same output).

Both operators can be written with an explicit type instantiation instead of a
predicate, as in `any@<bool>`, which denotes an arbitrary Boolean stream.

## Type Ascription

The ascription operator `(<expr>: <type>)` checks that an expression satisfies
a type. It generates a proof obligation; it does *not* introduce an assumption.
So given the type `Nat` above, if `x` is an input of type `int`, then
`(x: Nat)` obliges Kind 2 to prove `x >= 0`.

Ascription applies to ordinary types as well, where it acts as a static check
rather than a proof obligation: `(1 + 2: bool)` is rejected during type
checking.

## Common Auxiliary Nodes

While the temporal operators `->` and `pre` may not seem very powerful, they can
be used to define auxiliary temporal operators, presented below.

```text
-- Y is true iff X has been true so far
node Sofar ( X : bool ) returns ( Y : bool ) ;
let
 Y = X -> (X and (pre Y)) ;
tel

-- Z is true iff X has been true at some point in the past, 
-- and Y has been true since then.
node Since ( X, Y : bool ) returns ( Z : bool ) ;
let
  Z =  X or (Y and (false -> pre Z)) ;
tel

-- Y is true iff X was true in the initial timestep
node Initially(X: bool) returns (Y: bool);
let
  Y = X -> pre Y;
tel

-- Y is true iff X has been true at least once
node Once(X : bool) returns (Y : bool);
let
  Y = (false -> pre Y) or X;
tel
```

## Specifying and Checking Properties

Property checking was introduced informally at the start of this page. This
section covers the constructs the language provides for it.

### Properties

A property to be proven invariant is written with a `check` statement in the
body of a node. Properties may be named, which makes Kind 2's output easier to
read when there are several:

```text
node Count(trigger: bool) returns (n: int);
let
  n = (if trigger then 1 else 0) + (0 -> pre n);

  check "nonneg" n >= 0;
  check "small" n <= 10;
tel
```

Kind 2 reports each property as valid or falsified independently. For `Count`
above, `"nonneg"` is proven invariant, while `"small"` is falsified, and Kind 2
prints a counterexample: an input sequence, with the resulting values of every
stream, that drives the model to a state violating the property.

An older annotation syntax, `--%PROPERTY <expr>;`, is equivalent to a `check`
statement and still accepted.

### Choosing What to Analyze

By default, Kind 2 analyzes the *top nodes* of a model: those no other node
calls. A node can be designated explicitly by adding the annotation
`--%MAIN;` to its body, or by passing `--lus_main <node_name>` on the command
line. If any main node is designated, only main nodes are analyzed.

### Reachability Properties

Invariants say that something never happens. The dual — that something *can*
happen — is written with `check reachable`, which asks Kind 2 to find a witness
trace rather than to rule one out:

```text
check reachable "can reach ten" n = 10;
```

The search can be bounded: `from <int>` requires the witness to take at least
that many steps, `within <int>` at most that many, and `at <int>` exactly that
many.

Reachability checks are worth writing even in a model whose invariants all
hold, because they catch a model that is accidentally over-constrained — one
where the interesting states are simply unreachable.

### Conditional Properties

Properties are often of the form "in this situation, this behavior". Written
naively as `check B => A;`, such a property is trivially true whenever the
situation `B` never arises, which can hide a modeling error. The language
provides a dedicated syntax for this case:

```text
check A provided B;
```

This checks that `B => A` is invariant *and*, separately, that `B` is
reachable, so a vacuously true property is reported as such.

### Quantifiers

Properties and contracts may use the quantifiers `forall` and
`exists`. They may appear only in specifications, not in the equations that
define a node's outputs, and they are indispensable for models parameterized by
a size:

```text
check forall (i: int) 0 <= i and i < n => a[i] >= 0;
```

A quantified variable may be given a refinement type with the concise syntax
`x: <type> | <predicate>`, so the property above can also be written
`forall (i: int | 0 <= i and i < n) a[i] >= 0`.

## Contracts

Properties state facts about one node. A **contract** describes a node's
obligations to, and expectations of, its callers, which is what lets Kind 2
analyze a large model *compositionally*: each node is verified once against its
own contract, and callers reason about it through that contract instead of
re-examining its body.

A contract is a set of **assumptions**, which the caller must establish, and
**guarantees**, which the node must then deliver. It is written inline between
a node's interface and its body, delimited by `con` and `noc`:

```text
node Divide(x, y: real) returns (z: real);
con
  assume "nonzero divisor" y <> 0.0;
  guarantee "exact" z * y = x;
noc
let
  z = x / y;
tel
```

The meaning is: *if the assumptions always hold, the guarantees always hold.*
The obligation is shared. Kind 2 checks that `Divide` delivers `"exact"` given
`y <> 0.0`, and separately checks, at every call site, that the caller really
does supply a nonzero `y`. An assumption may not refer to the node's outputs
at the current step — the caller has no control over those — though it may
refer to them under a `pre`.

A contract may also declare **ghost variables** and constants with `var` and
`const`. These are visible to the contract but not to the node body, which
makes them useful for expressing specifications that need state the
implementation does not have:

```text
con
  var once: bool = trigger or (false -> pre once);
  guarantee once => count > 0;
noc
```

### Modes

Requirements in a specification document are usually of the form "in this
situation, behave this way". A **mode** captures that shape directly: it pairs
a set of `require` clauses (the situation) with a set of `ensure` clauses (the
required reaction).

```text
node Times(lhs, rhs: real) returns (res: real);
con
  mode absorbing (
    require lhs = 0.0 or rhs = 0.0;
    ensure res = 0.0;
  );
  mode positive (
    require lhs > 0.0 and rhs > 0.0;
    ensure res > 0.0;
  );
noc
let
  res = lhs * rhs;
tel
```

A mode is equivalent to the guarantee `requires => ensures`, but naming it buys
more than readability: Kind 2 uses modes to report *which* mode was active in a
counterexample, and it checks the set of modes for **exhaustiveness**, warning
when the modes leave some situation unspecified. A mode can be referred to
elsewhere in the contract by name, as in `require not ::absorbing;`.

### Contract Nodes

A contract can also be written separately and reused, as a **contract node** —
like an ordinary node, but introduced with `contract` and containing only
contract items. It is brought into a node's contract with `import`, which
merges the imported assumptions, guarantees, and modes into the importing
contract:

```text
contract Spec(x: real) returns (y: real);
let
  assume x >= 0.0;
  guarantee y >= 0.0;
tel

node Sqrt(x: real) returns (y: real);
con
  import Spec(x) returns (y);
noc
let
  y = if x <= 0.0 then 0.0 else x;
tel
```

See [Contract Semantics]({{< relref "/docs/advanced-features/contract-semantics" >}})
for the formal reading of assumptions, guarantees, and modes.

## Compositional and Modular Analysis

Contracts pay off in how a model is analyzed. By default Kind 2 analyzes a node
against the full implementations of everything it calls, however deep the
hierarchy runs. Two flags change that.

**Compositional** analysis, `--compositional true`, abstracts each call away by
the callee's contract, so the analysis sees only what the contract promises
instead of the callee's state. This is where the effort of writing contracts is
repaid: a contract normally carries far less state than the node it specifies,
which also drags in the state of everything *it* calls. Only calls to nodes
whose contract has at least one guarantee or mode are abstracted.

On its own this leaves a gap. Proving `top` correct with its callees abstracted
says nothing about whether those callees honor their contracts. That is what
**modular** analysis, `--modular true`, supplies: it analyzes every node in the
hierarchy, bottom-up, and keeps going even when some node's properties are
falsified.

The two are meant to be used together:

```text
kind2 --modular true --compositional true <file>.lus
```

Analyzed this way, each node is verified once against its own contract, and
every caller uses that contract in place of the body. If a compositional
analysis of `top` fails, the counterexample may be spurious — an artifact of
the abstraction rather than a real defect — and when the callee has already been
proved correct, Kind 2 *refines* the call, replacing the contract with the real
implementation and analyzing again. A per-analysis limit is available as
`--timeout_analysis`, alongside the global `--timeout`.

Two modifiers override these choices for an individual component. Writing
`transparent` before `node` or `function` keeps it from being abstracted by its
contract; writing `opaque` keeps it from being refined:

```text
transparent function F(x: int) returns (y: int);
let
  y = x;
tel
```

See [Techniques]({{< relref "/docs/techniques" >}}) for how the two modes
interact with each verification engine.

## Realizability Checking

A contract can be wrong in a way no amount of implementation effort will fix:
it can demand something impossible. The contract below cannot be satisfied by
any implementation, because a negative `x` leaves no legal value for `y`:

```text
node imported M(x: int) returns (y: int);
con
  guarantee 0 <= y and y <= x;
noc
```

Such a contract is **unrealizable**. Realizability is a stronger question than
consistency: it asks whether a component can be built that, *for every* input
sequence permitted by the assumptions, produces *some* output satisfying the
guarantees — and must do so step by step, without seeing the future.

This matters most for the specifications Kind 2 takes on trust. An imported
node is replaced by its contract everywhere it is called, so an unrealizable
contract is a false assumption that can prove anything downstream. The same
holds for refinement types and for the predicates of `any` and `choose`
expressions.

Kind 2 performs the check when the `CONTRACTCK` engine is enabled:

```text
kind2 --enable CONTRACTCK <file>.lus
```

It covers node and imported-node contracts, refinement types, free constants,
and the predicates of `any` and `choose` expressions. As with property
checking, `--lus_main <node_name>` restricts the analysis to one component,
and `--lus_main_type` and `--lus_main_const` select an individual type or
constant.

Kind 2 also checks the realizability of a node's *environment* — that the
assumptions themselves can be met. This is easy to overlook: assumptions that
no input sequence can satisfy make a node's guarantees vacuous, and the
resulting compositional argument is just as flawed as one built on an
unrealizable guarantee. Pass `--check_environment false` to disable it.

When a contract is found unrealizable, `--print_deadlock` shows a trace ending
in a state from which the contract cannot be satisfied, together with the
conflicting constraints.

See [Contract Check]({{< relref "/docs/advanced-features/contract-check" >}})
for the remaining options.

## More Examples

For more examples, see the Kind 2 web application at
[https://kind.cs.uiowa.edu/app/](https://kind.cs.uiowa.edu/app/).

This page has left out a good deal: the details of clock calculus, proof
certificates, test generation, contract generation, and the many options that
control each verification engine. For the full language reference, see
[Kind 2 Input]({{< relref "/docs/inputs-and-outputs/lustre" >}}); the pages
alongside it cover each type in depth, and
[Advanced Features]({{< relref "/docs/advanced-features" >}}) covers what Kind 2
can do beyond proving properties invariant.
