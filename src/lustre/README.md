Note on error message generation
--------------------------------

Menhir's incremental API generates a template file for mapping error messages for the grammar.

The following steps are used to update the `LustreParserErrors.message` function

1. Edit the error message in `src/lustre/lustreParser.message` file
2. Generate the function using the following command from (project root directory)
```
$ menhir --compile-errors src/lustre/lustreParser.messages src/lustre/lustreParser.mly > src/lustre/lustreParserErrors.ml
```
3. Compile against the new `LustreParserErrors.ml` file
```
$ make kind2
```
4. Test if the error message is displayed. There is some over-approximation/under-approximation caveats for
producing proper error messages.

A detailed guide to Menhir's incremental parser is [here](http://gallium.inria.fr/~fpottier/menhir/manual.html#sec57)
and how to manage error messages is given [here](http://gallium.inria.fr/~fpottier/menhir/manual.html#sec67). 

