# Lustre Input

Lustre is a functional, synchronous dataflow language. Kind 2 supports most of the Lustre V4 syntax and some elements of Lustre V6. See the file [`./examples/syntax-test.lus`](https://github.com/kind2-mc/kind2/blob/develop/examples/syntax-test.lus) for examples of all supported language constructs.

## Syntax extensions

To specify a property to verify in a Lustre node, add the following in the body (*i.e.* between keywords ```let``` and ```tel```) of the node:

```
--%PROPERTY <bool_expr> ;
```

where `<bool_expr>` is a boolean Lustre expression.

Kind 2 only analyzes what it calls the *top node*. By default, the top node is the last node in the file. To force a node to be the top node, add

```
--%MAIN ;
```

to the body of that node.

You can also specify the top node in the command line arguments, with

```
kind2 --lustre_main <node_name> ...
```

## Example

The following example declares two nodes ```greycounter``` and ```intcounter```, as well as an *observer* node ```top``` that calls these nodes and verifies that their outputs are the same. The node ```top``` is annotated with ```--%MAIN ;``` which makes it the *top node* (redundant here because it is the last node). The line ```--PROPERTY OK;``` means we want to verify that the boolean stream ```OK``` is always true.

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
