(lang dune 2.7)

(name kind2)
(version v1.5.0)

(package
 (name kind2)
 (synopsis
   "Multi-engine, parallel, SMT-based automatic model checker for safety properties of Lustre programs")
 (description "Kind 2 is an open-source, multi-engine, SMT-based automatic model checker for safety properties of finite-state
or infinite-state synchronous reactive systems expressed as in an extension of the Lustre language.
In its basic configuration it takes as input a Lustre file annotated with properties to be proven invariant,
and outputs for each property either a confirmation or a counterexample, i.e., a sequence inputs that falsifies the property.
More advanced features include contract-based compositional verification, proof generation for proven properties, and contract-based test generation.")
 (license Apache-2.0)
 (authors "The Kind 2 development team")
 (maintainers "Daniel Larraz <daniel-larraz@uiowa.edu>")
 (source
  (github kind2-mc/kind2))
 (homepage "https://kind2-mc.github.io/kind2")
 (documentation "https://kind.cs.uiowa.edu/kind2_user_doc")
 (depends
  (ocaml
   (>= 4.09))
  dune
  dune-build-info
  menhir
  num
  (odoc :with-doc)
  (ounit2 :with-test)
  yojson
  (zmq
   (>= 5.0.0))
 )
)

(using menhir 2.0)

(generate_opam_files true)
