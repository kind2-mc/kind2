## Compositional analysis

Option `--compositional true` takes advantage of the contracts of the nodes of the system to *abstract* subcomponents. In Kind 2, contracts are specified in Lustre systems using the
[inline syntax](./../1_input/1_lustre.md#lustre-inlined-contracts) or the
[CoCoSpec syntax](./../1_input/1_lustre.md#lustre-cocospec-contracts).

As explained in the
[Lustre contract extension](./../1_input/1_lustre.md#lustre-contract-extension)
section these contracts correspond to traditional assume/guarantee contracts encoding modes of the specification. In the following we say

* *assumption* for the assume part of the contract, and
* *mode* for a conjunct of the "guarantee" part.



