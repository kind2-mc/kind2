(lang dune 2.2)

(name kind2)

(package
 (name kind2)
 (synopsis
   "Multi-engine, parallel, SMT-based automatic model checker for safety properties of Lustre programs")
 (description
   "Kind 2 is a multi-engine, parallel, SMT-based automatic model checker for safety properties of Lustre programs.\n\nKind 2 takes as input a Lustre file annotated with properties to be proven invariant, and outputs which of the properties are true for all inputs, as well as an input sequence for those properties that are falsified. To ease processing by external tools, Kind 2 can output its results in JSON and XML formats.\n\nBy default Kind 2 runs a process for bounded model checking (BMC), a process for k-induction, two processes for invariant generation, and a process for IC3 in parallel on all properties simultaneously. It incrementally outputs counterexamples to properties as well as properties proved invariant.")
 (license Apache-2.0)
 (authors "Kind2 developers")
 (maintainers "Kind2 developers")
 (source
  (github kind2-mc/kind2))
 (homepage "https://kind2-mc.github.io/kind2")
 (documentation "https://kind.cs.uiowa.edu/kind2_user_doc")
 (depends
  (ocaml
   (>= 4.07))
  dune
  menhir
  num
  yojson
  zmq))

(using menhir 2.1)

(generate_opam_files true)
