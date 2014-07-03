# Concrete Syntax of Kind 2's Native Format #

The input format for Kind 2 is closely related to the [SMTLIB Format](http://smt-lib.org). The input consists of S-expressions, comments are delimited with `;;`. 

For an example see [two_counters.kind2](../examples/two_counters.kind2), which is a translation of [two_counters.lus](../examples/two_counters.lus)

The following are EBNF-style grammar rules.

    {transition_system} := {pred_def}+ (check-prop ({property}+))

A transition system consists of one or more definitions of pairs of initial state and transition relation predicates, and one or more properties about the last defined predicate to check.

	{pred_def} := (define-pred {identifier} {state_var_def}* 
                   (init {term} ) 
	               (trans {term_primed} ))

The definition of a predicate starts with a unique identifier for the predicate, followed by the declaration of the state variables and the initial state constraint over unprimed state variables, and the transition relation over primed and unprimed state variables.

Predicate definitions may reference predicates defined earlier, but not themselves. The transition relation may reference the initial state constraint of the predicate it is defined in. 

	{state_var_def} := {identifier} {type} {state_var_flag}*

The declaration of a state variable consists of an identifier unique within the body of the predicate definition, a type and some optional flags.

    {type} := Int | Real | Bool

The supported types are integer numbers, real numbers (both with arbitrary precision) and Booleans.

    {state_var_flag} := :const

A state variable can be marked as a constant with this flag.

	{state_var} := {identifier}

A state variable is referenced by its identifier.

    {state_var_primed} := {identifier} | (prime {identifier} )

A state variable, if it is not declared as constant, may be primed by  applying the function `prime` to it. State variables that are declared as constant cannot be primed. A primed state variable refers to its value in the next state, while an unprimed state variable refers to its value in the current state.

    {property} := ({string} {term})

A property is a pair of a string name (in double quotes) and a term over  unprimed state variables of the predicate named in the second argument of `check-prop` it occurs in.

    {var_binding} := ({identifier} {type})
    
    {term} := {value_literal}  
            | {state_var}  
            | ( {identifier} {term*} ) 
            | (let ({var_binding}+) {term}) 
            | ( {identifier}.init {term*} )  
    
An (unprimed) term is either a value literal (such as a numeric, decimal or Boolean value), an identifier standing of a state variable, a function application or a let binding. 

A function application may be a built-in function such as `and`, `or`, `+` or `-`. It may also be the application of a previously defined initial state predicate, selected by appending `.init` to its identifier. Such predicates are of type `Bool`, their arguments are the state variables in the order of their declaration in the respective `define-pred`. 


    {term_primed} := {value_literal}  
                   | {state_var_primed} 
                   | ( {identifier} {term_primed}+ ) 
                   | (let ({var_binding}+) {term_primed})
                   | ( {identifier}.init {term_primed}+ ) 
                   | ( {identifier}.trans {term_primed}+ ) 

A primed term is an unprimed term, where in addition identifiers of non-constant state variables may be primed to stand for the next state value. One may also use a transition relation predicate by appending `.trans` to the identifier of its definition. The arguments of a transition relation predicate are terms for the unprimed state variables in the order defined, followed by the primed state variables in the order defined, but with the constant state variables omitted.
    
## Possible features for the future ##

- Global constants with `define-const`
- Global function definitions with `define-fun`
- global assertions with `assert`
- More data types, in particular scalars or arrays
