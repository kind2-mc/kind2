# Analysis

By default a Kind 2 analysis only considers the cone of influence of the top node, its properties, and its contracts. More precisely, the techniques running will attempt to prove

* the properties of the top node,
* the properties of its subnodes at call site,
* the contract of the top node (if any), and
* the requirements of its subnodes (if any).

If the top node has a contract, then the analysis will be conducted assuming the assumption of the contract.

