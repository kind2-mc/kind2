Description of tests
=====================

NB: `State: Fails at TC` implies an error originates in `LustreTypeChecker.ml` 

Success
--------

| File name                           | Comment                               | Status |
| -----------------------------       | ----------                            | ------ |
| `abstract_type.lus`                 |                                       |        |
| `array-const.lus`                   |                                       |        |
| `array.lus`                         |                                       |        |
| `autoN.lus`                         |                                       |        |
| `automata_counter.lus`              |                                       |        |
| `block_annot_syntax.lus`            |                                       |        |
| `bv-logical.lus`                    |                                       |        |
| `const_to_non_const.lus`            |                                       |        |
| `contract_ordering.lus`             |                                       |        |
| `enum.lus`                          |                                       |        |
| `forward_refs.lus`                  |                                       |        |
| `function.lus`                      |                                       |        |
| `function_same_arg.lus`             |                                       |        |
| `imported.lus`                      |                                       |        |
| `merge_enum.lus`                    |                                       |        |
| `merge_enum1.lus`                   |                                       |        |
| `mode_reqs_by_idents.lus`           |                                       |        |
| `mode_reqs_by_idents_shadowing.lus` | type checker does not implement paths | Fail   |
| `pingpong.lus`                      |                                       |        |
| `pre_const.lus`                     |                                       |        |
| `record.lus`                        |                                       |        |
| `record2.lus`                       |                                       |        |
| `reset_counters.lus`                |                                       |        |
| `test-alias.lus`                    |                                       |        |
| `test-condact.lus`                  |                                       |        |
| `test-hex.lus`                      |                                       |        |
| `test-init-per-node.lus`            |                                       |        |
| `test-issue-317.lus`                |                                       |        |
| `test-merge.lus`                    |                                       |        |
| `test-oracles.lus`                  |                                       |        |

Error
------

| File name                                 | Comment                                                                | Status      |
| -----------------------------             | ----------                                                             | ------      |
| `abstract_type.lus`                       | Free type COUNTER used as numeric type                                 | Fails at TC |
| `array_node.lus`                          | Array assignment with implicit parameter & node call `(y[i] = n(a[i])` |             |
| `automaton_ab.lus`                        | Automation is not supported                                            |             |
| `bv-sh-exception.lus`                     | Expect a constant argument to rsh  operator                            | Fails at TC |
| `check_type.lus`                          | Basic syntactic type check                                             | Fails at TC |
| `circular_contracts.lus `                 | Contract declaration has circularity                                   | Fails at TC |
| `circular_nodes.lus`                      | Node declaration has circularity                                       | Fails at TC |
| `circular_types.lus`                      | Type declaration has circularity                                       | Fails at TC |
| `cocospec_out_param.lus`                  |                                                                        |             |
| `const_not_const.lus`                     |                                                                        |             |
| `empty_range.lus`                         |                                                                        |             |
| `function_no_arrow_in_body.lus`           |                                                                        |             |
| `function_no_node_call.lus`               |                                                                        |             |
| `function_no_pre_in_body.lus`             |                                                                        |             |
| `function_no_stateful_contract.lus`       |                                                                        |             |
| `function_stateful_contract_import.lus`   |                                                                        |             |
| `imported_fun_no_body.lus`                |                                                                        |             |
| `imported_node_no_body.lus`               |                                                                        |             |
| `merge_enum.lus`                          |                                                                        |             |
| `merge_enum1.lus`                         |                                                                        |             |
| `merge_enum2.lus`                         |                                                                        |             |
| `mode_reqs_by_idents_no_forward_ref.lus`  |                                                                        |             |
| `mode_reqs_by_idents_no_self_ref.lus`     |                                                                        |             |
| `no_contracts_in_contract.lus`            |                                                                        |             |
| `test-func-sliced.lus`                    |                                                                        |             |
| `test-nodes.lus`                          |                                                                        |             |
| `test-type.lus`                           |                                                                        |             |
| `undefined_local.lus`                     |                                                                        |             |
| `unguarded_pre_in_contract.lus`           |                                                                        |             |
| `unguarded_pre_in_contract_call.lus`      |                                                                        |             |
| `unguarded_pre_node_call_in_contract.lus` |                                                                        |             |

Falsifiable
-----------
