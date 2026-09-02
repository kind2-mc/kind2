---
title: "A Lucent Primer"
weight: 1
---

This page is a self-contained introduction to Lucent, 
the input language of Kind 2, intended for new users.

## Basic Concepts

### Lucent Nodes

Lucent is a language for modeling and implementing
reactive systems in the synchronous model.
It can be seen indifferently as either a declarative parallel programming language
or as an executable specification language.
The most basic unit of computation in a Lucent program, or model, is a **node**,
which can be viewed as a stream transformer:
it takes streams of input and produces streams of output.
Operationally, a node reads its input and generates its output incrementally
in discrete *timesteps*, or cycles, determined by an abstract global clock.
At each cycle, all output values are assumed to be computed instantaneously
from the current input and state values.
By default, all nodes in a model compute synchronously and in parallel according
to the global clock.

A **stream** is an infinite sequence of values, all of the same (given) type.
Hence, a Lucent node can be viewed as modeling an infinite sequence of discrete
timesteps, where at each timestep, each node variable takes its next value.

Below, the node `Combine` takes as input two integer streams \(x\) and \(y\), and
produces integer stream \(z\) as output. If we consider \(x = (x_0, x_1, \dots)\)
and \(y = (y_0, y_1, \dots)\), then `Combine` produces output
\(z = (x_0 + 2 \cdot y_0,\ x_1 + 2 \cdot y_1,\ \dots)\) (or more concisely,
\(z_n = x_n + 2 \cdot y_n\) at each timestep \(n\)).

{{< callout type="info" >}}
It is not possible to specify a stream pointwise in Lucent, so when we write
\(x = (1, 2, 3, \dots)\), say, we are writing a mathematical statement about
stream \(x\), not an equation in Lucent.
{{< /callout >}}

Notice that `z = x + 2*y` is an equation between streams of integers.
The operators `=`, `+` and `*` are stream operators
obtained by lifting to streams the corresponding operators over integers.
The same is true of concrete constants in Lucent, such as `2` below,
which are streams with the same value at each time step.
Lucent respects typical rules of operator precedence, so `x + 2*y` will be
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

Another optional component that can be added to a Lucent node is a set of
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

In Lucent, identifiers (for constants, variables, types, and keywords)
are delimited by whitespace characters, separators
such as parentheses and semicolons, and other symbols such as `+`, `*` and so on,
as in most programming languages.
Whitespace is, however, not semantically meaningful.
For instance, indentation does not change the parsing of an expression.

### Node Analyses

Lucent was designed to be a programming language.
Well-formed Lucent nodes are executable in the sense that they can be compiled
to executable programs computing their output values incrementally
from their input values and internal state.

Here, we are mostly interested in *analyzing* Lucent programs and their possible
behavior with a tool like Kind 2.

A basic form of analysis that can be applied to a Lucent program is **node
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

Property checking is performed by model checkers such as Kind 2,
so further details are outside the scope of this page.

## Comments

The example above shows the two ways to add comments in Lucent programs.
Single line comments are introduced by the character sequence `--`.
Multiline comments are delimited by the sequences `(*` and `*)`.
Nested multiline comments are not allowed.

## Primitive Types

Lucent's primitive types are `bool`, `int`, and `real`.
Informally, we say that `bool` is the type of Boolean values (`true`, `false`).
Strictly speaking, `bool` is the type of *streams* of Boolean values.
We identify the two for brevity since there is no possibility of confusion
as all values in Lucent are streams.
The same is true for the other types.

{{< callout type="info" >}}
It is not possible to refer directly to the scalar values in a stream in Lucent.
Even constants, such as `true`, `2`, `3.6` denote streams of values, not
individual values.
{{< /callout >}}

In the **idealized** semantics of Lucent, `int` is the type of mathematical
(infinite precision) integers, and `real` is the type of real numbers.
Lucent compilers approximate that semantics by using machine integers
for `int` and floating point numbers for `real`.
In contrast, Kind 2 is faithful to the idealized semantics.

Lucent supports the Boolean operators `not`, `and`, `or`, `xor`, and `=>`
(implies), as well as the arithmetic operators `+`, `-` (both unary and binary),
`*`, `/`, `mod`, and `div` (integer division), all with the expected arity and
(pointwise) semantics.
The arithmetic operators (`+` and so on) are overloaded as they apply
both to `int` and `real` terms.
The binary operators, however, are applicable only to arguments of the same type
(both `int` or both `real`).
Numerals (`0`, `1`, ...) have type `int`
while decimals (e.g., `0.0`, `31.97`) have type `real`.

Additionally, Lucent supports if-then-else expressions with the syntax

```text
if <expr_0> then <expr_1> else <expr_2>
```

where `<expr_0>` has type `bool` and
`<expr_1>` and `<expr_2>` must have the same type.

## Temporal Operators

Lucent contains two temporal operators:
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
While unguarded `pre`s are allowed in Lucent, Kind 2 will produce warnings
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

| Expression | \(0\) | \(1\) | \(2\) | ... | \(n\) |
|---|---|---|---|---|---|
| `1` | \(1\) | \(1\) | \(1\) | ... | \(1\) |
| `x` | \(x_0\) | \(x_1\) | \(x_2\) | ... | \(x_n\) |
| `pre x` | \(?\) | \(x_0\) | \(x_1\) | ... | \(x_{n-1}\) |
| `1 + pre x` | \(1 + ?\) | \(1 + x_0\) | \(1 + x_1\) | ... | \(1 + x_{n-1}\) |
| `1 -> (1 + pre x)` | \(1\) | \(1 + x_0\) | \(1 + x_1\) | ... | \(1 + x_{n-1}\) |

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

A deceptively difficult example is defining in Lucent a stream with value
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

| Expression | \(0\) | \(1\) | \(2\) | \(3\) | ... |
|---|---|---|---|---|---|
| `1` | \(1\) | \(1\) | \(1\) | \(1\) | ... |
| `2` | \(2\) | \(2\) | \(2\) | \(2\) | ... |
| `3` | \(3\) | \(3\) | \(3\) | \(3\) | ... |
| `1 -> 2` | \(1\) | \(2\) | \(2\) | \(2\) | ... |
| `2 -> 3` | \(2\) | \(3\) | \(3\) | \(3\) | ... |
| `pre (2 -> 3)` | \(?\) | \(2\) | \(3\) | \(3\) | ... |
| `1 -> (2 -> 3)` | \(1\) | \(3\) | \(3\) | \(3\) | ... |
| `(1 -> 2) -> 3` | \(1\) | \(3\) | \(3\) | \(3\) | ... |
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

Another deceptively difficult example is the following Lucent node which outputs
the stream of all Fibonacci numbers in increasing order.
Because `Fib` is defined in terms of the two previous Fibonacci values, the first
*two* steps need to be initialized. The example is tricky and may require some
thought for those new to Lucent.

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

## Declarative Semantics

Lucent has a **declarative** semantics, meaning that the order of equations in
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

Even though Lucent has a declarative semantics and allows recursive definitions,
circular definitions are rejected. For example, the following node is invalid
Lucent because the \(n\)th value of `out1` is defined in terms of the \(n\)th
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

In addition to the primitive types, Lucent supports records and arrays.
Kind 2 also supports a number of composite types that are not part of standard
Lucent, such as [tuples]({{< relref "/docs/inputs-and-outputs/tuples" >}}),
[sets]({{< relref "/docs/inputs-and-outputs/sets" >}}),
[maps]({{< relref "/docs/inputs-and-outputs/maps" >}}), and
[algebraic datatypes]({{< relref "/docs/inputs-and-outputs/algebraic-datatypes" >}}).

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
additional record features supported by Kind 2.

### Arrays

Array types have the syntax

```text
<element_type>^<numeral>
```

Values of an array type can be constructed in two different ways.
Lucent supports the **array literal** syntax of the form

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

See [Arrays]({{< relref "/docs/inputs-and-outputs/arrays" >}}) for the
additional array features supported by Kind 2.

## Composition

A Lucent model can be hierarchically defined
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
in a Lucent model is immaterial.
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

## More Examples

For more examples, see the Kind 2 web application at
<https://kind.cs.uiowa.edu/app/>. Note that these examples contain some language
features that are extensions to Lucent (for example, contracts) that are not
covered in this page. For more information on Kind 2 and its extensions to
Lucent, see [Kind 2 Input]({{< relref "/docs/inputs-and-outputs/lustre" >}}) and
the rest of this documentation.
