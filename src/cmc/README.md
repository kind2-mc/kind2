# CMC Build Instructions
### Build Dolmen
```
cd dolmen
make
dune build # Not necessary?
opam pin add -n dolmen .
opam install
```
### Build kind2
```
cd ../kind2
opam install ../dolmen # Not necessary?
make
dune build # Not necessary?
./_build/default/bin/kind2 examples/example.cmc --condensed_cmc_output true
```

### Flags
`--condensed_cmc_output <true|false>` When true only changes to the state are showed in each step of the reachability trace.

### Examples
Examples are stored in `kind2/examples/CMCExamples`. The most complete examples are `TrafficLight` files. 


`TrafficLight1.cmc` Models a traffic light with a few issues, several queries are issued on the system and some fail due to a under specified system.


`TrafficLight3.cmc` Is a corrected version of the previous example. This example passes all queries as expected. 


`TrafficLightEnum.cmc` Is another completely correct model of a traffic light. This example makes use of subsystems and enumerations to model the system. 

