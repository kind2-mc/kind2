# Kind 2 v0.7.1

## New features 
- Support XOR operator in PDR
- Cover more cases in type inference to widen integer interval types 
- Instantiate properties in sub-nodes in calling nodes 
- Implement path compression in k-induction
- Allow calling interpreter without input to get empty output containing all variables 
- Undo intermediate optimizations and abstractions to output counterexamples exactly in terms of input problem
- Output trace file for interaction with SMT solvers
- Native input format as alternative to Lustre

## Bug fixes 
- Interpolate input variables for nodes in condact between clock ticks 
- Fix assertion failure in PDR on zero or one step counterexamples when BMC and PDR run in parallel
- Automatically switch quantifer elimination in PDR when not in LIA logic
- Start child processes in separate process groups for clean termination
- Various fixes in plain text and XML output
- Type check and arity check for defaults in condact calls
