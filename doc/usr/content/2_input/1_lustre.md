# Kind2 Input

The input language for Kind2 is an extended version of the Lustre language. Lustre is a functional, synchronous dataflow language. Kind 2 supports most of the Lustre V4 syntax and some elements of Lustre V6. See the file [`./examples/syntax-test.lus`](https://github.com/kind2-mc/kind2/blob/develop/examples/syntax-test.lus) for examples of all supported language constructs.

## Properties and top-level node

To specify a property to verify in a Lustre node, add the following annotation in the body (*i.e.* between keywords ```let``` and ```tel```) of the node:

```
--%PROPERTY ["<name>"] <bool_expr> ;
```

or, use a `check` statement:

```
check ["<name>"] <bool_expr> ;
```

where `<name>` is an identifier for the property and `<bool_expr>` is a Boolean Lustre expression.

Without modular reasoning active, Kind 2 only analyzes the properties of what it calls the *top node*. By default, the top node is the last node in the file. To force a node to be the top node, add

```
--%MAIN ;
```

to the body of that node.

You can also specify the top node in the command line arguments, with

```
kind2 --lustre_main <node_name> ...
```

### Example

The following example declares two nodes ```greycounter``` and ```intcounter```, as well as an *observer* node ```top``` that calls these nodes and verifies that their outputs are the same. The node ```top``` is annotated with ```--%MAIN ;``` which makes it the *top node* (redundant here because it is the last node). The line ```--%PROPERTY OK;``` means we want to verify that the Boolean stream ```OK``` is always true.

```
node greycounter (reset: bool) returns (out: bool);
var a, b: bool; 
let
  a = false -> (not reset and not pre b);
  b = false -> (not reset and pre a);
  out = a and b;

tel

node intcounter (reset: bool; const max: int) returns (out: bool);
var t: int; 
let
  t = 0 -> if reset or pre t = max then 0 else pre t + 1;
  out = t = 2;

tel

node top (reset: bool) returns (OK: bool);
var b, d: bool;
let
  b = greycounter(reset);
  d = intcounter(reset, 3);
  OK = b = d;

  --%MAIN ;

  --%PROPERTY OK;

tel
```

Kind 2 produces the following on standard output when run with the default options (```kind2 <file_name.lus>```):

```
kind2 v0.8.0

<Success> Property OK is valid by inductive step after 0.182s.

status of trans sys
------------------------------------------------------------------------------
Summary_of_properties:

OK: valid
```

We can see here that the property ```OK``` has been proven valid for the system (by *k*-induction).


## Contracts

A contract `(A,G,M)`for a node is a set of assumptions `A`, a set of
guarantees `G`, and a set of modes `M`. The semantics of contracts is given
in the
[Contract semantics](./../9_other/2_contract_semantics.md#contract-semantics)
section, here we focus on the input format for contracts. Contracts are
specified either locally, using the *inline syntax*, or externally in a
*contract node*. Both the local and external syntax have a body
composed of *items*, each of which define

* a ghost variable / constant,
* an assumption,
* a guarantee,
* a mode, or
* an import of a contract node.

They are presented in detail below, after the discussion on local and external
syntaxes.


### Inline syntax

A local contract is a special comment between the signature of the node
```
node <id> (...) returns (...) ;
```
and its body. That is, between the `;` of the node signature and the `let`
opening its body.

A local contract is a special block comment of the form

```
(*@contract
  [item]+
*)
```

or

```
/*@contract
  [item]+
*/
```


### External syntax

A contract node is very similar to a traditional lustre node. The two
differences are that

* it starts with `contract` instead of `node`, and
* its body can only mention *contract items*.

A contract node thus has form

```
contract <id> (<in_params>) returns (<out_params>) ;
let
  [item]+
tel
```

To use a contract node one needs to import it through an inline contract. See
the next section for more details.





### Contract items and restrictions


#### Ghost variables and constants

A ghost variable (constant) is a stream that is local to the contract. That is,
it is not accessible from the body of the node specified. Ghost variables
(constants) are defined with the `var` (`const`) keyword. Kind 2 performs type
inference for constants so in most cases type annotations are not necessary.

The general syntax is
```
const <id> [: <type>] = <expr> ;
var   <id>  : <type>  = <expr> ;
```

For instance:
```
const max = 42 ;
var ghost_stream: real = if input > max then max else input ;
```


#### Assumptions

An assumption over a node `n` is a constraint one must respect in order to use
`n` legally. It cannot mention the outputs of `n` in the current state, but
referring to outputs under a `pre` is fine.

The idea is that it does not make sense to ask the caller to respect some
constraints over the outputs of `n`, as the caller has no control over them
other than the inputs it feeds `n` with.
The assumption may however depend on previous values of the outputs produced
by `n`.

Assumptions are given with the `assume` keyword, followed by any legal Boolean
expression:
```
assume <expr> ;
```



#### Guarantees

Unlike assumptions, guarantees do not have any restrictions on the streams
they can mention. They typically mention the outputs in the current state since
they express the behavior of the node they specified under the assumptions of
this node.

Guarantees are given with the `guarantee` keyword, followed by any legal
Boolean expression:
```
guarantee <expr> ;
```



#### Modes

A mode `(R,E)` is a set of *requires* `R` and a set of *ensures* `E`. Requires
have the same restrictions as assumptions: they cannot mention outputs of the
node they specify in the current state. Ensures, like guarantees, have no
restriction.

Modes are named to ease traceability and improve feedback. The general syntax
is
```
mode <id> (
  [require <expr> ;]*
  [ensure  <expr> ;]*
) ;
```

For instance:
```
mode engaging (
  require true -> not pre engage_input ;
  require engage_input ;
  -- No ensure, same as `ensure true ;`.
) ;
mode engaged (
  require engage_input ;
  require false -> pre engage_input ;
  ensure  output <= upper_bound ;
  ensure  lower_bound <= output ;
) ;
```



#### Imports

A contract import *merges* the current contract with the one imported. That
is, if the current contract is `(A,G,M)` and we import `(A',G',M')`, the
resulting contract is `(A U A', G U G', M U M')` where `U` is set union.

When importing a contract, it is necessary to specify how the instantiation of
the contract is performed. This defines a mapping from the input (output)
formal parameters to the actual ones of the import.

When importing contract `c` in the contract of node `n`, it is **illegal** to
mention an output of `n` in the actual input parameters of the import of `c`.
The reason is that the distinction between inputs and outputs lets Kind 2 check
that the assumptions and mode requirements make sense, *i.e.* do not mention
outputs of `n` in the current state.

The general syntax is
```
import <id> ( <expr>,* ) returns ( <expr>,* ) ;
```

For instance:
```
contract spec (engage, disengage: bool) returns (engaged: bool) ;
let ... tel

node my_node (
  -- Flags are "signals" here, but `bool`s in the contract.
  engage, disengage: real
) returns (
  engaged: real
) ;
(*@contract 
  var bool_eng: bool = engage <> 0.0 ;
  var bool_dis: bool = disengage <> 0.0 ;
  var bool_enged: bool = engaged <> 0.0 ;

  var never_triggered: bool = (
    not bool_eng -> not bool_eng and pre never_triggered
  ) ;

  assume not (bool_eng and bool_dis) ;
  guarantee true -> (
    (not engage and not pre bool_eng) => not engaged
  ) ;

  mode init (
    require never_triggered ;
    ensure not bool_enged ;
  ) ;

  import spec (bool_eng, bool_dis) returns (bool_enged) ;
*)
let ... tel
```



#### Mode references

Once a mode has been defined it is possible to *refer* to it with
```
::<scope>::<mode_id>
```
where `<mode_id>` is the name of the mode, and `<scope>` is the path to the
mode in terms of contract imports.

In the example from the previous section for instance, say contract `spec` has
a mode `m`. The inline contract of `my_node` can refer to it by
```
::spec::m
```
To refer to the `init` mode:
```
::init
```

A mode reference is syntactic sugar for the `requires` of the mode in question.
So if mode `m` is
```
mode m (
  require <r_1> ;
  require <r_2> ;
  ...
  require <r_n> ; -- Last require.
  ...
) ;
```
then `::<path>::m` is exactly the same as
```
(<r_1> and <r_1> and ... and <r_n>)
```

**N.B.**: a mode reference
* is a Lustre expression of type `bool` just like any other Boolean expression. 
  It can appear under a `pre`, be used in a node call or a contract import, *etc.*
* is only legal **after** the mode item itself. That is, no
  forward/self-references are allowed.


An interesting use-case for mode references is that of checking properties over
the specification itself. One may want to do so to make sure the specification
behaves as intended. For instance
```
mode m1 (...) ;
mode m2 (...) ;
mode m3 (...) ;

guarantee true -> ( -- `m3` cannot succeed to `m1`.
  (pre ::m1) => not ::m3
) ;
guarantee true -> ( -- `m1`, `m2` and `m3` are exclusive.
  not (::m1 and ::m2 and ::m3)
) ;
```



### Merge, When, Activate and Restart

> **Note**: the first few examples of this section illustrating (unsafe)
> uses of `when` and `activate` are **not legal** in Kind 2. They aim at
> introducing the semantics of lustre clocks. As discussed below, they are only
> legal when used inside a `merge`, hence making them safe clock-wise.
>
> Also, `activate` and `restart` are actually not a legal Lustre v6
> operator. They are however legal in Scade 6.

A `merge` is an operator combining several streams defined on **complementary**
clocks. There is two ways to define a stream on a clock. First, by wrapping its
definition inside a `when`.

```
node example (in: int) returns (out: int) ;
var in_pos: bool ; x: int ;
let
  ...
  in_pos = x >= 0 ;
  x = in when in_pos ;
  ...
tel
```

Here, `x` is only defined when `in_pos`, its clock, is `true`. 
That is, a trace of execution of `example` sliced to `x` could be

| step |   | `in` | `in_pos` | `x` |
|:----:|---|:----:|:--------:|:---:|
| `0` | | `3` | `true` | `3` |
| `1` | | `-2` | `false` | // |
| `2` | | `-1` | `false` | // |
| `3` | | `7` | `true` | `7` |
| `4` | | `-42` | `true` | // |

where // indicates that `x` undefined.

The second way to define a stream on a clock is to wrap a node call with the
`activate` keyword. The syntax for this is

```
(activate <node_name> every <clock>)(<input_1>, <input_2>, ...)
```

For example, consider the following node:

```
node sum_ge_10 (in: int) returns (out: bool) ;
var sum: int ;
let
  sum = in + (0 -> pre sum) ;
  out = sum >= 10 ;
tel
```

Say now we call this node as follows:

```
node example (in: int) returns (...) ;
var tmp, in_pos: bool ;
let
  ...
  in_pos = in >= 0 ;
  tmp = (activate sum_ge_10 every in_pos)(in) ;
  ...
tel
```

That is, we want `sum_ge_10(in)` to tick iff `in` is positive. Here is an
example trace of `example` sliced to `tmp`; notice how the internal state of
`sub` (*i.e.* `pre sub.sum`) is maintained so that it does refer to the value
of `sub.sum` *at the last clock tick of the `activate`*:

| step |   | `in` | `in_pos` |  `tmp`  |   | `sub.in` | `pre sub.sum` | `sub.sum` |
|:----:|---|:----:|:--------:|:-------:|---|:--------:|:-------------:|:---------:|
| 0    |   |  `3` |   `true` | `false` |   |      `3` |         `nil` |       `3` |
| 1    |   |  `2` |   `true` | `false` |   |      `2` |           `3` |       `5` |
| 2    |   | `-1` |  `false` |   `nil` |   |    `nil` |           `5` |     `nil` |
| 3    |   |  `2` |   `true` | `false` |   |      `2` |           `5` |       `7` |
| 4    |   | `-7` |  `false` |   `nil` |   |    `nil` |           `7` |     `nil` |
| 5    |   | `35` |   `true` |  `true` |   |     `35` |           `7` |      `42` |
| 6    |   | `-2` |  `false` |   `nil` |   |    `nil` |          `42` |     `nil` |


Now, as mentioned above the `merge` operator combines two streams defined on
**complimentary** clocks. The syntax of `merge` is:

```
merge( <clock> ; <e_1> ; <e_2> )
```

where `e_1` and `e_2` are streams defined on `<clock>` and `not <clock>`
respectively, or on `not <clock>` and `<clock>` respectively.


Building on the previous example, say add two new streams `pre_tmp` and
`safe_tmp`:

```
node example (in: int) returns (...) ;
var tmp, in_pos, pre_tmp, safe_tmp: bool ;
let
  ...
  in_pos = in >= 0 ;
  tmp = (activate sum_ge_10 every in_pos)(in) ;
  pre_tmp = false -> pre safe_tmp  ;
  safe_tmp = merge( in_pos ; tmp ; pre_tmp when not in_pos ) ;
  ...
tel
```
That is, `safe_tmp` is the value of `tmp` whenever it is defined, otherwise it
is the previous value of `safe_tmp` if any, and `false` otherwise.
The execution trace given above becomes


| step |   | `in` | `in_pos` |   `tmp` | `pre_tmp` | `safe_tmp` | 
|:----:|---|:----:|:--------:|:-------:|:---------:|:----------:|
| 0    |   |  `3` |   `true` | `false` |   `false` |    `false` |
| 1    |   |  `2` |   `true` | `false` |   `false` |    `false` |
| 2    |   | `-1` |  `false` |   `nil` |   `false` |    `false` |
| 3    |   |  `2` |   `true` | `false` |   `false` |    `false` |
| 4    |   | `-7` |  `false` |   `nil` |   `false` |    `false` |
| 5    |   | `35` |   `true` |  `true` |   `false` |     `true` |
| 6    |   | `-2` |  `false` |   `nil` |    `true` |     `true` |


Just like with uninitialized `pre`s, if not careful one can easily end up
manipulating undefined streams. Kind 2 forces good practice by allowing
`when` and `activate ... every` expressions only inside a `merge`. All the
examples of this section above this point are thus invalid from Kind 2's point
of view.

Rewriting them as valid Kind 2 input is not difficult however. Here is a legal
version of the last example:

```
node example (in: int) returns (...) ;
var in_pos, pre_tmp, safe_tmp: bool ;
let
  ...
  in_pos = in >= 0 ;
  pre_tmp = false -> pre safe_tmp  ;
  safe_tmp = merge(
    in_pos ;
    (activate sum_ge_10 every in_pos)(in) ;
    pre_tmp when not in_pos
  ) ;
  ...
tel
```

Kind 2 supports resetting the internal state of a node to its initial state by
using the construct restart/every. Writing

```
(restart n every c)(x1, ..., xn)
```

makes a call to the node `n` with arguments `x1`, ..., `xn` and every time the
Boolean stream `c` is true, the internal state of the node is reset to its
initial value.

In the example below, the node `top` makes a call to `counter` (which is an
integer counter _modulo_ a constant `max`) which is reset every time the input
stream `reset` is true. 

```
node counter (const max: int) returns (t: int);
let
  t = 0 -> if pre t = max then 0 else pre t + 1;
tel

node top (reset: bool) returns (c: int);
let
  c = (restart counter every reset)(3);
tel
```

A trace of execution for the node top could be:

| step |   | `reset` | `c` |
|:----:|---|:-------:|:---:|
| 0    |   | `false` |   0 |
| 1    |   | `false` |   1 |
| 2    |   | `false` |   2 |
| 3    |   | `false` |   3 |
| 4    |   |  `true` |   0 |
| 5    |   | `false` |   1 |
| 6    |   | `false` |   2 |
| 7    |   |  `true` |   0 |
| 8    |   |  `true` |   0 |
| 9    |   | `false` |   1 |

> **Note:** This construction can be encoded in traditional Lustre by having a
> Boolean input for the reset stream for each node. However providing a
> built-in  way to do it facilitates the modeling of complex control systems.


Restart and activate can also be combined in the following way:

```
(activate (restart n every r) every c)(a1, ..., an)
(activate n every c restart every r)(a1, ..., an)
```

These two calls are the same (the second one is just syntactic sugar). The
(instance of the) node `n` is restarted whenever `r` is true and the _resulting
call_ is activated when the clock `c` is true. Notice that the restart clock
`r` is also sampled by `c` in this call.

### Enumerated data types in Lustre

```
type t = enum { A, B, C };
node n (x : enum { C1, C2 }, ...) ...
```

Enumerated datatypes are encoded as subranges so that solvers handle arithmetic
constraints only. This also allows to use the already present quantifier
instantiation techniques in Kind 2.

### N-way merge

As in Lustre V6, merges can also be performed on a clock of a user defined
enumerated datatype. 

```
merge c
 (A -> x when A(c))
 (B -> w + 1 when B(c));
```

Arguments of merge have to be sampled with the correct clock. Clock expressions
for merge can be just a clock identifier or its negation or `A(c)` which is a
stream that is true whenever `c = A`.

Merging on a Boolean clock can be done with two equivalent syntaxes:

```
merge(c; a when c; b when not c);

merge c
  (true -> a when c)
  (false -> b when not c); 
```



## Partially defined nodes

Kind 2 allows nodes to define their outputs only partially. For instance, the
node

```
node count (trigger: bool) returns (count: int ; error: bool) ;
(*@contract
  var once: bool = trigger or (false -> pre once) ;
  guarantee count >= 0 ;
  mode still_zero (
    require not once ;
    ensure count = 0 ;
  ) ;
  mode gt (
    require not ::still_zero ;
    ensure count > 0 ;
  ) ;
*)
let
  count = (if trigger then 1 else 0) + (0 -> pre count) ;
tel
```
can be analyzed: first for mode exhaustiveness, and the body is checked against
its contract, although it is only *partially* defined.
Here, both will succeed.


## The `imported` keyword

Nodes (and functions, see below) can be declared `imported`. This means that
the node does not have a body (`let ... tel`). In a Lustre compiler, this is
usually used to encode a C function or more generally a call to an external
library.

```
node imported no_body (inputs: ...) returns (outputs: ...) ;
```

In Kind 2, this means that the node is always abstract in the contract sense.
It can never be refined, and is always abstracted by its contract. If none is
given, then the implicit (rather weak) contract

```
(*@contract
  assume true ;
  guarantee true ;
*)
```
is used.

In a modular analysis, `imported` nodes will not be analyzed, although if their
contract has modes they will be checked for exhaustiveness, consistently with
the usual Kind 2 contract workflow.


### Partially defined nodes VS `imported`

Kind 2 allows partially defined nodes, that is nodes in which some streams
do not have a definition. At first glance, it might seem like a node with no
definitions at all (with an empty body) is the same as an `imported` node.

It is not the case. A partially defined node *still has a (potentially
empty) body* which can be analyzed. The fact that it is not completely defined
does not change this fact.
If a partially defined node is at the top level, or is in the cone of
influence of the top node in a modular analysis, then it's body **will** be analyzed.

An `imported` node on the other hand *explicitly does not have a body*. Its
non-existent body will thus never be analyzed.


## Functions

Kind 2 supports the `function` keyword which is used just like the `node` one
but has slightly different semantics. Like the name suggests, the output(s) of
a `function` should be a *non-temporal* combination of its inputs. That is, a
function cannot the `->`, `pre`, `merge`, `when`, `condact`, or `activate`
operators. A function is also not allowed to call a node, only other functions.
In Lustre terms, functions are stateless.

In Kind 2, these retrictions extend to the contract attached to the function,
if any. Note that besides the ones mentioned here, no additional restrictions
are enforced on functions compared to nodes.

### Benefits

Functions are interesting in the model-checking context of Kind 2 mainly as
a mean to make an abstraction more precise. A realistic use-case is when one
wants to abstract non-linear expressions. While the simple expression `x*y`
seems harmless, at SMT-level it means bringing in the theory of non-linear
arithmetic.

Non-linear arithmetic has a huge impact not only on the performances of the
underlying SMT solvers, but also on the SMT-level features Kind 2 can use (not
to mention undecidability). Typically, non-lineary arithmetic tends to prevent
Kind 2 from performing satisfiability checks with assumptions, a feature it
heavily relies on.

The bottom line is that as soon as some non-linear expression appear, Kind 2
will most likely fail to analyze most non-trivial systems because the
underlying solver will simply give up.

Hence, it is usually [extremely rewarding](https://www.researchgate.net/publication/304360220_CoCoSpec_A_Mode-Aware_Contract_Language_for_Reactive_Systems)
to abstract non-linear expressions away in a separate *function* equipped with
a contract. The contract would be a linear abstraction of the non-linear
expression that is precise enough to prove the system using correct. That way,
a compositional analysis would *i)* verify the abstraction is correct and *ii)*
analyze the rest of the system using this abstraction, thus making the analysis
a linear one.

Using a function instead of a node simply results in a better abstraction. Kind
2 will encode, at SMT-level, that the outputs of this component depend on the
*current* version of its inputs only, not on its previous values.



## Hierarchical Automata

> **Experimental feature**

Kind 2 supports both the syntax used in LustreC and a subset of the one used in
Scade 6.


```
node n (i1, ..., in : ...) returns (o1, ..., on : ...);
let

   automaton automaton_name

     initial state S1:
       unless if c restart Si elsif c' resume Sj else restart Sk end;
       var v : ...;
       let
          v = ...;
          o1 = i1 -> last o2 + 1;
          o2 = 99;
       tel
       until c restart S2;

     state S2:
       let
          ...; 
       tel
     ...
   returns o1, o2;

   o3 = something () ...;
tel
```

An automaton is declared _inside a node_ (there can be several) and can be
anonymous. Automata can be nested, _i.e._ an automaton can contain other
automata in some of its states bodies. This effectively allows to describe
_hierarchical state machines_. An automaton is defined by its list of states
and a `returns` statement that specifies which variables (locals or output) are
defined by the automaton.

> The set of returned streams can be inferred by writing `returns ..;`. One can
> also simply omit the `returns` statement which will have the same effect.

States (much like regular nodes) do not need to give equations that define
_all_ their outputs (but they do for their local variables). If defined streams
are different between the states of the automaton, then the set considered will
be their union and states that do not define all the inferred streams will be
considered underconstrained.

Each state has a name and one of them can be declared `initial` (if no initial
state is specified, the first one is considered initial). They can have local
variables (to the state).  The body of the state contains Lustre equations (or
assertions) and can use the operator `last`. In contrast to `pre x` which is
the value of the stream `x` the last time the state was in the declared state,
`last x` (or the Scade 6 syntax `last 'x`) is the previous value of the stream
`x` on the base clock. This construct is useful for communicating information
between states.

States can have a _strong_ transition (declared with `unless`) placed before
the body and a _weak_ transition placed after the body. The unless transition
is taken when entering the state, whereas the until transition is evaluated
after execution of the body of the state. If none are applicable then the
automaton remains in the same state. These transitions express conditions to
change states following a branching pattern. Following are examples of legal
branching patterns (`c*` are Lustre Boolean expressions):

```
c restart S
```
```
if c1 restart S1
elsif c2 restart S2
elsif c3 restart S3
end;
```
```
if c1
  if c2 restart S2
  else if c3 resume S1
  end
elsif c3 resume S3
else restart S0
end;
```

Targets are of the form `restart State_name` or `resume State_name`.  When
transiting to a state with `restart`, the internal state of the state is rested
to its initial value. On the contrary when transiting with `resume`, execution
in the state resumes to where it was when the state was last executed.

In counter-examples, we show the value of additional internal state information
for each automaton: `state` is a stream that denotes the state in which the
automaton is and `restart` indicates if the state in which the automaton is was
restarted in the current instant.

The internal state of an automaton state is also represented in counter-example
traces, separately. States and subsequent streams are sampled with the clock
state, _i.e._ values of streams are shown only when the automaton is in the
corresponding state.



## Arrays

> **Experimental feature**

### Lustre arrays

Kind 2 supports the traditional Lustre V5 syntax for arrays.

#### Declarations

Array variables can be declared as global, local or as input/output of
nodes. Arrays in Lustre are always indexed by integers (type `int` in Lustre),
and the type of an array variable is written with the syntax `t ^ <size>` where
`t` is a Lustre type and `<size>` is an integer literal or a constant symbol.

The following

```
A : int ^ 3;
```

declares an array variable `A` of type array of size 3 whose elements
are integers. The size of the array can also be given by a defined constant.

```
const n = 3;
...
A : int ^ n;
```

This declaration is equivalent to the previous one for `A`.


An interesting feature of these arrays is the possibility for users to write
generic nodes and functions that are parametric in the size of the array. For
instance one can write the following node returns the last element of an array.

```
node last (const n: int; A: int ^ n) returns (x: int);
let
  x = A[n-1];
tel
```

It takes as input the size of the array and the array itself. Note that the
type of the input `A` depends on the value of the first constant input `n`. In
Lustre, calls to such nodes should of course end up by having concrete values
for `n`, this is however not the case in Kind 2 (see
[here](#extension-to-unbounded-arrays)).


Arrays can be multidimensional, so a user can declare *e.g.* matrices with the
following

```
const n = 4;
const m = 5;
...

M1 : bool ^ n ^ m;
M2 : int ^ 3 ^ 3;
```

Here `M1` is a matrix of size 4x5 whose elements are Boolean, and `M2` is a
square matrix of size 3x3 whose elements are integers.

> **Remark**
>
> `M1` can also be viewed as an array of arrays of Booleans.

Kind 2 also allows one to nest datatypes, so it is possible to write arrays of
records, records of arrays, arrays of tuples, and so on.

```
type rational = { n: int; d: int };

rats: rational^array_size;
mm: [int, bool]^array_size;
```

In this example, `rats` is declared as an array of record elements and `mm` is
an array of pairs.


#### Definitions

In the body of nodes or at the top-level, arrays can be defined with literals
of the form

```
A = [2, 5, 7];
```

This defines an array `A` of size 3 whose elements are 2, 5 and 7. Another way
to construct Lustre arrays is to have each elements be the same value. This can
be done with expressions of the form `<value> ^ <size>`. For example the two
following definitions are equivalent.

```
A = 2 ^ 3;
A = [2, 2, 2];
```

Arrays are indexed starting at 0 and the elements can be accessed using the
selection operator `[ ]`. For instance the result of the evaluation of the
expression `A[0]` for the previously defined array `A` is 2.

The selection operators can also be applied to multidimensional arrays.
Given a matrix `M` defined by

```
M = [[1, 2, 3],
     [4, 5, 6],
     [7, 8, 9]];
```

then the expression `M[1][2]` is valid and evaluates to 6. The result of a
single selection on an *n*-dimensional array is an *(n-1)*-dimensional
array. The result of `M[2]` is the array `[7, 8, 9]`.


#### Unsupported features of Lustre V5

Kind 2 currently **does not support** the following features of [Lustre
V5](http://www.di.ens.fr/~pouzet/cours/mpri/manual_lustre.ps):

- Array concatenation like `[0, 1] | [2, 3, 4]`

- Array slices like `A[0..3]`, `A[0..3 step 2]`, `M[0..1][1..2]` or
`M[0..1, 1..2]`

- The operators are not homomorphically extended. For instance `or` has type
  `bool -> bool -> bool`, given two arrays of Booleans `A` and `B`, the
  expression `A or B` will be rejected at typing by Kind 2
  
- Node calls don't have an homomorphic extension either



### Extension to unbounded arrays

Kind 2 provides an extension of Lustre to express equational constraints
between unbounded arrays. This syntax extension allows users to inductively
define arrays, give whole array definitions and allows to encode most of the
other unsupported array features. This extension was originally suggested by
[Esterel](http://www.esterel-technologies.com).


> **Remark**
>
> Here, by *unbounded* we mean whose size is an unbounded constant.


In addition, we also enriched the specification language of Kind 2 to support
(universal and existential) quantifiers, allowing one to effectively model
*parameterized* system.


#### Whole array definitions

Equations in the body of nodes can now take the following forms

- `A = <term> ;` This equation defines the values of the array `A` to be the same
  as the values of the array expression `<term>`.

- `A[i] = <term(i)> ;` This equation defines the values of all elements in the
  array `A`. The index `i` has to be a symbol, it is bound locally to the
  equation and shadows all other mentions of `i`. Index variables that appear
  on the left hand side of equations are **implicitly universally
  quantified**. The right hand side of the equation, `<term(i)>` can depend on
  this index. The meaning of the equation is that, for any integer `i` between
  0 and the size of `A`, the value at position `i` is defined as the term
  `<term(i)>`.

Semantically, a whole array equation is equivalent to a quantified
equation. Let `A` be an array of size an integer constant `n`, then following 
equation is legal.

```
A[i] = if i = 0 then 2 else B[i - 1] ;
```

It is equivalent to the formula
_∀ i ∈ [0; n]. ( i = 0 ⇒ A[i] = 2 )  ⋀ ( i ≠ 0 ⇒ A[i] = B[i-1] )_.

Multidimensional arrays can also be redefined the same way. For instance the
equation

```
M[i][j] = if i = j then 1 else 0 ;
```

defines `M` as the identity matrix

```
[[ 1 , 0 , 0 ,..., 0 ],
 [ 0 , 1 , 0 ,..., 0 ],
 [ 0 , 0 , 1 ,..., 0 ],
 .................... ,
 [ 1 , 0 , 0 ,..., 1 ]]
```

It is possible to write an equation of the form

```
M[i][i] = i;
```

but in this case the second index `i` shadows the first one, hence the
definition is equivalent to the following one where the indexes have been
renamed.

```
M[j][i] = i;
```


#### Inductive definitions


One interesting feature of these equations is that we allow definitions of
arrays *inductively*. For instance it is possible to write an equation

```
A[i] = if i = 0 then 0 else A[i-1] ;
```

This is however not very exciting because this is the same as saying that `A`
will contain only zeros, but notice we allow the use of `A` in the right hand
side.


##### Dependency analysis

Inductive definitions are allowed under the restriction that they should be
*well founded*. For instance, the equation

```
A[i] = A[i];
```

is not and will be rejected by Kind 2 the same way the equation `x = x;` is
rejected. Of course this restriction does not apply for array variables under a
`pre`, so the equation `A[i] = pre A[i];` is allowed.

In practice, Kind 2 will try to prove statically that the definitions are
well-founded to ensure the absence of dependency cycles. We only attempt to
prove that definitions for an array `A` at a given index `i` depends on on
values of `A` at indexes strictly smaller than `i`.

For instance the following set of definitions is rejected because *e.g.* `A[k]`
depends on `A[k]`.

```
A[k] = B[k+1] + y;
B[k] = C[k-1] - 2;
C[k] = A[k] + k;
```

On the other hand this one will be accepted.

```
A[k] = B[k+1] + y;
B[k] = C[k-1] - 2;
C[k] = ( A[k-1] + B[k] ) * k ;
```

Because the order is fixed and that the checks are simple, it is possible that
Kind 2 rejects programs that are well defined (with respect to our semantic for
whole array updates). It will not, however, accept programs that are
ill-defined.

For instance each of the following equations will be rejected.

```
A[i] = if i = 0 then 0 else if i = 1 then A[0] else A[i-1];
```

```
A[i] = if i = n then 0 else A[i+1];
```

```
A[i] = if i = 0 then 0 else A[0];
```

##### Examples

This section gives some examples of usage for inductive definitions and whole
array updates as a way to encode unsupported features and as way to encode
complicated functions succinctly.

###### Sum of the elements in an array

The following node returns the sum of all elements in an array.

```
node sum (const n: int; A: int ^ n) returns (s: int);
var cumul: int ^ n;
let
  cumul[i] = if i = 0 then A[0] else A[i] + cumul[i-1];
  s = cumul[n-1];
tel
```

We declare a local array `cumul` to store the cumulative sum (*i.e.* `cumul[i]`
contains the sum of elements in `A` up to index `i`) and the returned value of
the node is the element stored in the last position of `cumul`.

Note that this node is parametric in the size of the array.


###### Array slices

Array slices can be trivially implemented with the features presented above.

```
node slice (const n: int; A: int ^ n; const low: int; const up: int)
returns (B : int ^ (up-low));
let
  B[i] = A[low + i];
tel
```


###### Homomorphic extensions

Encoding an homomorphic `or` on Boolean arrays is even simpler.

```
node or_array (const n: int; A, B : bool^n) returns (C: bool^n);
let
  C[i] = A[i] or B[i];
tel
```

Defining a generic homomorphic extension of node calls is not possible because
nodes are not first order objects in Lustre.



###### Parameterized systems

It is possible to describe and check properties of parameterized
systems. Contrary to the Lustre compilers, Kind 2 does not require the
constants used as array sizes to be instantiated with actual values. In this
case the properties are checked *for any* array sizes.

```
node slide (const n:int; s: int) returns(A: int^n);
let
  A[i] = if i = 0 then s else (-1 -> pre A[i-1]);

  --%PROPERTY n > 1 => (true -> A[1] = pre s);
tel
```

This node stores in an array `A` a *sliding window* over an integer stream
`s`. It saves the values taken by `s` up to `n` steps in the past, where `n` is
the size of the array.

Here the property says, that if the array `A` has at least two cells then its
second value is the previous value of `s`.


#### Quantifiers in specifications

To better support parameterized systems or systems with large arrays, we expose
quantifiers for use in the language of the specifications. Quantifiers can
thus appear in **properties**, **contracts** and **assertions**.

Universal quantification is written with:

```
forall ( <x : type>;+ ) P(<x>+)
```

where `x` are the quantified variables and `type` is their type. `P` is a
formula or a predicate in which the variable `x` can appear.

For example, the following
```
forall (i, j: int) 0 <= i and i < n and 0 <= j and j < n => M[i][j] = M[j][i]
```
is a formula that specifies that the matrix `M` is symmetric.

> **Remark**
>
> Existential quantification takes the same form except we use
> `exists` instead of `forall`.

Quantifiers can be arbitrarily nested and alternated at the propositional level.


##### Example

The same parameterized system of a sliding window, slightly modified to express
the property that `A` contains in each of its cells, an uninitialized value
(*i.e.* value `-1`), or one of the previous values of the stream `s`.

```
node slide (const n:int; s: int) returns(ok: bool^n);
var A: int^n;
let
  A[i] = if i = 0 then s else (-1 -> pre A[i-1]);
  ok[i] = A[i] = -1 or A[i] = s or (false -> pre ok[i]);

  --%PROPERTY forall (i: int) 0 <= i and i < n => ok[i];
tel
```


#### Limitations

One major limitation that is present in the arrays of Kind 2 is that one cannot
have node calls in inductive array definitions whose parameters are array
selections.

For instance, it is currently not possible to write the following in Kind 2
where `A` and `B` are array and `some_node` takes values as inputs.

```
node some_node (x: int) returns (y: int);
...

A, B: int^4;
...

A[i] = some_node(B[i]);
```

This limitation exists only for technical implementation reasons.
A workaround for the moment is to redefine an homorphic extension of the node
and use that instead.

```
node some_node (const n: int; x: int^n) returns (y: int^n);
...

A, B: int^4;
...

A = some_node(4, B);
```


#### Command line options

We provide different encodings of inductive array definitions in our internal
representation of the transition system. The command line interface exposes
different options to control which encoding is used. This is particularly
relevant for SMT solvers that have built-in features, whether it is support for
the theory of arrays, or special options or annotations for quantifier
instantiation.

These options are summed up in the following table and described in more detail
in the rest of this section.

Option           | Description
----------------|---------------------------------------------------
`--smt_arrays`   | Use the builtin theory of arrays in solvers
`--inline_arrays` | Instantiate quantifiers over array bounds in case they are statically known
`--arrays_rec` |  Define recurvsive functions for arrays (for CVC4)


The default encoding will use quantified formulas for inductive definitions and
whole array updates.


For example if we have

```
A : int^6;
...
A[k] = x;
```
  
we will generate internally the constraint

   *∀ k: int. 0 <= k < 6 => (select A k) = x*

These form of constraint are handled in an efficient way by CVC4 (thanks to
finite model finding).


###### `--smt_arrays`

By default arrays are converted using ah-hoc selection functions to avoid
stressing the theory of arrays in the SMT solvers. This option tells Kind 2 to
use the builtin theory of arrays of the solvers instead. If you want to try it,
it’s probably a good idea to use it in combination of `--smtlogic detect` for
better performances.


###### `--inline_arrays`

By default, Kind 2 will generate problems with quantifiers for arrays which
should be useful for problems with large arrays. This option tells Kind 2 to
instantiate these quantifiers when it can reasonably do so. Only CVC4 has a
good support for this kind of quantification so you may want to use this option
with the other solvers.

The previous example

```
A : int^6;
...
A[k] = x;
```

will now be encoded by the constraint

   *(select A 0) = x ⋀ (select A 1) = x ⋀ (select A 2) = x ⋀ (select A 3) = x ⋀
    (select A 4) = x ⋀ (select A 5) = x*


###### `--arrays_rec`

This uses a special kind of encoding to tell CVC4 to treat quantified
definitions of some uninterpreted functions as recursive definitions.



## Machine Integers
Kind2 supports both signed and unsigned versions of C-style machine integers of width 
8, 16, 32, and 64. 

### Declarations
Machine integer variables can be declared as global, local, or as input/ouput
of nodes. Signed machine integers are declared as type `intN` and unsigned machine 
integers are declared as type `uintN` where N is the width (8, 16, 32, or 64).

The following
```
x : uint8;
y : int16;
```
declares a variable `x` of type unsigned machine integer of width 8, and variable 
`y` of type signed machine integer of width 16.


### Values
Machine integers values can be constructed using implicit conversion functions
applied to integer literals. The
implicit conversion functions are of the form `uintN` for unsigned machine 
integers and `intN` for signed machine integers.

The following
```
x = uint8 27;
y = int16 -5012;
```
defines `x` to have value `27`, and `y` to have value `-5012`, given that `x` 
is a variable of type `uint8` and `y` is a variable of type `int16`.


### Semantics
Machine integers of width `x` represent binary numbers of size `x`.
Signed machine integers are represented using 2's complement.

The bounds of machine integers are specified here for convenience:
```
uint8  : 0 to 255
uint16 : 0 to 65535
uint32 : 0 to 4294967295
uint64 : 0 to 18446744073709551615
int8   : -128 to 127
int16  : -32768 to 32767
int32  : -2147483648 to 2147483647
int64  : -9223372036854775808 to 9223372036854775807
```

When the conversion functions are used for literals that are out of this range, 
they are converted to a machine integer that is in range using the modulo operation,
as in C. For instance, in the following
```
x = uint8 256;
y = int16 32768;
```
`x` evaluates to `0` and `y` to `-3268`, given that `x` 
is a variable of type `uint8` and `y` is a variable of type `int16`.

Conversions are allowed between machine integers of different widths, as long as 
both types are either signed or unsigned. Values remain unchanged when 
converted from a smaller to a larger width; values are adjusted modulo 
the range of the destination type when converted from larger to smaller 
width. The following code illustrates this.
```
a : int8;
b : int16;
c : uint16;
d : uint8;
a = int8 120;
b = int16 a; -- b == int16 120
c = uint16 300;
d = uint8 c; -- c == uint8 44

```


### Operations

Kind2 allows the following operations over the machine integer types.

#### Arithmetic Operations
Addition (`+`), multiplication (`*`), division (`div`), and modulo (`mod`) are 
binary arithmetic operations, allowed on either signed or unsigned 
machine integers, and return a 
machine integer with the same sign and same width as both inputs.

Unary negation (`-`), and binary subtraction (`-`) are allowed only on signed 
machine integers and return a signed machine integer with the same 
width as the input(s).
```
a, a1, a2 : uint8;
b : uint16;
c : uint32;
d : uint64;
e, f : int8;
a1 = (uint8 5);
a2 = (uint8 22);
a = a1 + a2;
b = (uint16 20) * (uint16 200);
c = (uint32 500) div (uint32 5);
d = (uint64 25) mod (uint64 10);
e = (int8 -5) + (- (int8 10));
f = (int8 10) - (int8 -5);
```

#### Logical Operations
Conjunction (`&&`), disjunction (`||`), and negation (`!`) are performed in a 
bitwise fashion over the binary equivalent of their machine integer inputs.
Conjunction and disjunction are binary, while negation is unary. All 3 
operations return a machine integer that has the same sign and same
width as its input(s).
```
a, b, b1, b2, c : uint8;
a = (uint8 0) && (uint8 45); --a = (uint8 0)
b1 = (uint8 255);
b2 = (uint8 45);
b = b1 && b2; --b = (uint8 45)
c = !(uint8 0); --c = (uint8 255)
```

#### Shift Operations
Left shift (`lsh`) and right shift (`rsh`) operations are binary operations: 
the first input is either signed or unsigned, the second input is unsigned, 
and the sign of the output matches that of the first input; both inputs and 
the output have the same width.

Right shifting when the first operand is signed, results in an arithmetic
right shift, where the bit shifted in matches the sign bit. 

A left shift is equivalent to multiplication by 2, and a right shift is 
equivalent to division by 2, as long as the result can fit into the 
machine integer of the same width. In other words, the left shift 
operator shifts towards the most-significant bit and the right shift 
operator shifts towards the least-significant bit.
```
a, b, c : bool;
a = (uint8 0) << (uint8 10) = (uint8 0); --true
b = (uint8 255) >> (uint8 12) = (uint8 255); --true
c = (int8 -1) << (uint8 1) = (int8 -2); --true
```

#### Comparison Operations
The following comparison operations are all binary: `>`, `<`, `>=`, `<=`, `=`. 
They input machine integers of the same size and sign, and output a boolean value.
```
a : bool;
a = (int8 -12) < (int8 12); --true
```


### Options
Currently, the Yices2 SMT solver doesn't support logics that will allow 
for the usage of integers and machine integers together. 
When using combinations of integers and machine integers, currently Kind2 
must be told to use CVC4 or Z3. This can be done with the option 
"--smt_solver CVC4", or "--smt_solver Z3", respectively.

IC3 is enabled by default in Kind2, and IC3 methods don't support theories
which deal with machine integers, so IC3 must be disabled while using Kind2
with problems containing machine integers. This is done using the option
"--disable IC3".

To reason about machine integers, Kind2 uses the SMT theory of bitvectors.
Since we still haven't implemented logic detection, whenever you use
machine integers, you need to tell Kind2 to consider all logics. This 
is done using the option "--smt_logic none".
