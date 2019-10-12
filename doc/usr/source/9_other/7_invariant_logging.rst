.. _9_other/7_invariant_logging:

Invariant Logging
-----------------

This treatment can only run after Kind 2 concluded the system ``s`` is safe. If
this condition is met, then invariant logging will minimize the invariants used
in the proof and log them as a contract for ``s`` in the output directory.

..

   **NB**\ : *minimization* is understood here in terms of inclusion, not
   cardinality. That is, a set of invariants is *minimal* if
   removing an invariant either increases the ``k`` of the k-induction proof
   or causes the set of invariants to not strengthen the properties of the
   system any more (the properties and the remaining invariants are not
   k-inductive).

   It can be that a smaller set of strengthening invariants exists though.


The point of this feature is that it is often the case that while finding
strengthening invariants takes a long time, proving the properties with these
invariants is actually rather simple.
Logging a minimized set of invariants allows to replay the analysis without
re-discovering them.

The Kind 2 team also thinks that these invariant can turn out to be useful
even after the system was modified, assuming the changes are not too important.
Different invariants usually characterize different parts of the system, and
some of the invariants previously logged may still apply.

Last, this feature also lets users inspect the (useful) invariants discovered
by Kind 2 to make sure they conform to their understanding of the system.

The Kind 2 team is looking forward to receiving feedback on this feature, which
we think can greatly improve user experience if used properly.

Failures
^^^^^^^^

Logging invariants is actually rather challenging. During an analysis, the
state of the whole system is made explicit. That is, Kind 2 sees the state
variables of the component under analysis as well as that of all its
sub-components.

Hence Kind 2 can discover invariants that relate state variables that, at
Lustre level, belong to different sub-nodes burried deep in the node
hierarchy. Expressing such invariants purely in terms of the top node can
be challenging, especially if some node calls use ``condact``\ s or ``merge`` /
``activate``\ s.

As a consequence, the current invariant logging strategy can fail with a
warning saying that it is not able to express some of the invariants at top
level. If you are interested in the invariant logging feature, but run into
this kind of problem, please contact us. It may be that in your case, we can
solve the problem relatively easily.
