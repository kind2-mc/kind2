# Compilation to Rust

> While this feature has been tested on rather large systems, is still
> considered experimental. The Kind 2 team is eagerly awaiting feedback and bug
> reports to improve/fix it.

[Rust](https://www.rust-lang.org/) is a very efficient language with a focus on
safety. Kind 2 can compile Lustre to Rust, as long as the input system does not
have **any unguarded pre's**, regardless of whether the initial undefined value
is actually used. Arrays and records are **not** supported.

Compilation is activated by the `--compile true` flag.

The result is a Rust project in the `implem` subdirectory of the Kind 2 output
directory. The project is extensively documented, you can read the
documentation by running `cargo doc` in the project directory and opening
`target/doc/<system>/index.html`.


## Technical details

The project produces a binary that reads inputs as comma-separated values from
its standard input and prints back outputs as comma-separated values on its
standard output. Lustre's `real`s are compiled as 64-bits floats while
`int`egers become `usize`: 32-bits (64-bits) signed integers on 32-bits
(64-bits) platforms.


## Assertions, properties and contracts

Compilation in Kind 2 works under the assumption that the model *has been
proved correct*. Therefore properties, guarantees, and modes are not compiled
as they have already been proved at model-level.

**N.B.** To be precise, Kind 2 works with mathematical integers and reals, not
machine integers and float. Thus, it could be the case that the binary actually
falsifies the specification. We are considering offering to compile properties
/ guarantees / modes optionally through a flag.

Assertions and assumptions from the original models are compiled as internal
checks and, when falsified, will cause the binary to stop after outputting an
error message pointing to the assertion / assumption falsified in the original
Lustre model.