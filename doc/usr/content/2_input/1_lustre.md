# Lustre Input

Lustre is a functional, synchronous dataflow language. Kind 2 supports most of the Lustre V4 syntax and some elements of Lustre V6. See the file [`./examples/syntax-test.lus`](https://github.com/kind2-mc/kind2/blob/develop/examples/syntax-test.lus) for examples of all supported language constructs.

## Syntax extensions

To specify a property to verify in a Lustre node, add the following in the body of the node:

```
--%PROPERTY <bool_expr> ;
```

where `<bool_expr>` is a boolean Lustre expression.

Kind 2 only analyzes what it calls the *top node*. By default, the top node is the last node in the file. To force a node to be the top node, add

```--%MAIN ;```

to the body of that node.

You can also specify the top node in the command line arguments, with

```
kind2 --lustre_main <node_name> ...
```
