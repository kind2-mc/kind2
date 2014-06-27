# Draft of the Concrete Syntax for Kind 2's Native Format #

The concrete syntax is closely related to the [SMTLIB Format](http://smt-lib.org). The input consists of S-expressions, comments are delimited with `;;`.

    {transition_system} := {pred_def}+ (check-prop ({property}+))

A transition system consists of one or more definitions of initial state and transition relation predicates, and one or more properties to check.

	{pred_def} := ( define-pred ( {identifier} {state_var_def}* ) 
	                (init ( {state_var}* ) {term} ) 
	                (trans ( {state_var}* ) {term} )

The definition of a predicate starts with a unique identifier for the predicate, followed by the declaration of the state variables and the initial state constraint, usually over some unprimed state variables and the transition relation, usually over primed and unprimed state variables.

Predicate definitions may reference predicates defined earlier, the transition relation may in addition reference the initial state constraint of the predicate. 

	{state_var_def} := {identifier} {type} {state_var_flag}*

The declaration of a state variable consists of an identifier unique within the predicate definition, a type and some optional flags.

    {state_var_flag} := :const

A state variable can be marked as a constant with this flag.

	{state_var} := {identifier}.0 | {identifier}.1 | identifier

A state variable, which is not declared as constant, is either unprimed by appending `.0`, or primed by appending `.1` to its identifier. State variables that are declared as constant must not be primed or unprimed.

    {property} := {string} {term}

A property is a pair of a string name and a term over the unprimed state variables of the last predicate definition.

    {var_binding} := ({identifier} {type})
    {term} := {value_literal} | 
              {identifier} | 
              {identifier}.0 | 
              {identifier}.1 | 
              ( {identifier} {term*} ) | 
              ( {identifier}.init {term*} ) | 
              ( {identifier}.trans {term*} ) | 
              (let ({var*binding}+) {term})

A term is either a value literal (such as a numeric, decimal or Boolean value), an identifier (standing for a defined constant), an identifier standing for a constant state variable, a primed or unprimed identifier standing for a non-constant state variable, a function application or a let binding.

A function application may be a built-in function such as `and`, `or`, `+` or `-`. It may also be the application of a previously defined initial state or transition relation predicate, selected by appending `.init` or `.trans`. These predicates are of type `Bool`.

    {type} := Int | Real | Bool

The supported types are integer numbers, real numbers (both with arbitrary precision) and Booleans.

For an example see [two_counters.kind2](../examples/two_counters.kind2), which is a translation of [two_counters.lus](../examples/two_counters.lus)

## More features for the future ##

Global constants with define-const, global function definitions, global assertions

More data types, in particular scalars or arrays.
