.. _9_other/13_assumption_generation:

Assumption Generation
=====================

In the early stages of model development and analysis, 
properties of system components often fail to hold
because the assumptions made about a component's environment 
are insufficient to guarantee these properties,
even when component's behavior is correctly specified.
When this happens, the system designer must study the counterexample provided 
by Kind 2,
pinpoint the cause, and identify possible restrictions 
on the environment that the properties need in order to hold ---
which were perhaps assumed by the designer but were not made explicit.

For instance, consider the following Lustre program:

.. code-block:: none

   node Arbiter (s1,s2: bool; e1,e2:int) returns(o: int);
   (*@contract
     guarantee "G1" s1 => o=e1;
     guarantee "G2" s2 => o=e2;
   *)
   let
     if s1 and s2 then
       o = any { o:int | o = e1 or o = e2 };
     elsif s1 then
       o = e1;
     else
       o = e2;
     fi
   tel

If we run Kind 2 to check guarantees ``G1`` and ``G2``, Kind 2 determines
the properties are invalid, providing a counterexample for each of them.
In the first counterexample, ``s1`` and ``s2`` are true initially, and
the output is equal to the value of ``e2``, which falsifies ``G1``.
In the second counterexample, ``s1`` and ``s2`` are true initially, and
the output is equal to the value of ``e1``, which falsifies ``G2``.

From the description of the counterexamples,
it is evident that one potential missing assumption is that
``s1`` and ``s2`` are never simultaneously true. 
If that is indeed the case, explicitly stating this assumption 
in the contract of the node,
allows Kind 2 to prove both properties valid.

Generating the missing assumptions for straightforward examples like the one
above is not very difficult. However, in more realistic scenarios,
this task can become quite challenging.
To help system designers in those situations,
Kind 2 offers a post-analysis that can be enabled by
passing the command-line option ``--assumption_gen true``.
When this option is enabled, Kind 2 will automatically generate assumptions
that are strong enough to prove the set of falsified properties
in the verification analysis while not being overly restrictive.
Note that just finding sufficient assumptions is not challenging.
The challenge is to find `minimally restrictive` assumptions
which can then be recognized as realistic by the designer.

For the example above, Kind 2 generates the assumption:
``(not s2) or (not s1) or (e1 = e2)``.
Notice that this assumption is a weaker version of the one mentioned above, 
as it considers a third case where the inputs ``e1`` and
``e2`` equal.

The functionality generates one-state constraints on a node's environment,
but it currently lacks the capability to generate two-state properties,
which presents a significantly more complex challenge.
