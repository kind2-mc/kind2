.. _9_other/2_contract_semantics:

Contract Semantics
==================

Assume-guarantee contracts
--------------------------

This section discusses the semantics of contracts, and in particular modes, in
Kind 2. For details regarding the syntax, please see the
:ref:`2_input/1_lustre#contracts` section.

An *assume-guarantee contract* ``(A,G)`` for a node ``n`` is a set of *assumptions*
``A`` and a set of *guarantees* ``G``. Assumptions describe how ``n`` **must** be
used, while guarantees specify how ``n`` behaves.

More formally, ``n`` respects its contract ``(A,G)`` if all of its executions 
satisfy the temporal LTL formula

.. math::

  \square A \Rightarrow \square G

That is, if the assumptions always hold then the guarantees hold. Contracts are
interesting when a node ``top`` calls a node ``sub``\ , where ``sub`` has a contract
``(A,G)``.

From the point of view of ``sub``\ , a contract
``({a_1, ..., a_n}, {g_1, ..., g_m})`` represents the same verification
challenge as if ``sub`` had been written

.. code-block:: none

   node sub (...) returns (...) ;
   let
     ...
     assert a_1 ;
     ...
     assert a_n ;
     --%PROPERTY g_1 ;
     ...
     --%PROPERTY g_m ;
   tel

The guarantees must be invariant of ``sub`` when the assumptions are forced.

For the caller however, the call ``sub(<params>)`` is legal **if and only if**
the assumptions of ``sub`` are invariants of ``top`` at call-site. The verification
challenge for ``top`` is therefore the same as

.. code-block:: none

   node top (...) returns (...) ;
   let
     ... sub(<params>) ...
     --%PROPERTY a_1(<call_site>) ;
     ...
     --%PROPERTY a_n(<call_site>) ;
   tel

Modes
-----

Kind 2 augments traditional assume-guarantee contracts with the notion of
*mode*. A mode ``(R,E)`` is a set ``R`` or *requires* and a set ``E`` of *ensures*.
A Kind 2 contract is therefore a triplet ``(A,G,M)`` where ``M`` is a set of modes.
If ``M`` is empty then the semantics of the contract is exactly that of an
assume-guarantee contract.

Semantics
^^^^^^^^^

A mode represents a *situation* / *reaction* implication. A contract ``(A,G,M)``
can be re-written as an assume-guarantee contract ``(A,G')`` where

.. math::

   G' = G\ \cup\ \{\ \bigwedge_i r_i \Rightarrow \bigwedge_i e_i \mid (\{r_i\}, \{e_i\}) \in M \}

For instance, a (linear) contract for non-linear multiplication could be

.. code-block:: none

   node abs (in: real) returns (res: real) ;
   let res = if in < 0.0 then - in else in ; tel

   node times (lhs, rhs: real) returns (res: real) ;
   (*@contract

     mode absorbing (
       require lhs = 0.0 or rhs = 0.0 ;
       ensure res = 0.0 ;
     ) ;
     mode lhs_neutral (
       require not absorbing ;
       require abs(lhs) = 1.0 ;
       ensure abs(res) = abs(rhs) ;
     ) ;
     mode rhs_neutral (
       require not absorbing ;
       require abs(rhs) = 1.0 ;
       ensure abs(res) = abs(lhs) ;
     ) ;
     mode positive (
       require (
         rhs > 0.0 and lhs > 0.0
       ) or (
         rhs < 0.0 and lhs < 0.0
       ) ;
       ensure res > 0.0 ;
     ) ;
     mode pos_neg (
       require (
         rhs > 0.0 and lhs < 0.0
       ) or (
         rhs < 0.0 and lhs > 0.0
       ) ;
       ensure res < 0.0 ;
     ) ;
   *)
   let
     res = lhs * rhs ;
   tel

**Motivation:** modes were introduced in the contract language of Kind 2 to
account for the fact that most requirements found in specification documents
are actually implications between a situation and a behavior.
In a traditional assume-guarantee contract, such requirements have to be
written as ``situation => behavior`` guarantees. We find this cumbersome,
error-prone, but most importantly we think some information is lost in this
encoding.
Modes make writing specification more straightforward and user-friendly, and
allow Kind 2 to keep the mode information around to


* improve feedback for counterexamples,
* generate mode-based test-cases, and
* adopt a defensive approach to guard against typos and specification
  oversights to a certain extent.
  This defensive approach is discussed in the next section.

Defensive check
^^^^^^^^^^^^^^^

Conceptually modes correspond to different situations triggering different
behaviors for a node. Kind 2 is *defensive* in the sense that when a contract
has at least one mode, it will check that the modes account for **all
situations** the assumptions allow before trying to prove the node respects
its contract.

More formally, consider a node ``n`` with contract

.. math::

   (A, G, \{(R_i, E_i)\})

The defensive check consists in checking that the disjunction of the requires
of each mode

.. math::

   \mathsf{one\_mode\_active} = \bigvee_i (\bigwedge_j r_{ij})

is an invariant for the system

.. math::

   A \wedge G \wedge (\bigwedge r_i \Rightarrow \bigwedge e_i)

If ``one_mode_active`` is indeed invariant, it means that as long as


* the assumptions are respected, and
* the node is correct *w.r.t.* its contract
  then at least one mode is active at all time.

Kind 2 follows this defensive approach.
If a mode is missing, or a requirement is more restrictive than it should be
then Kind 2 will detect the modes that are not exhaustive and provide a counterexample.

This defensive approach is not as constraining as it first appears.
If one wants to leave some situation unspecified on purpose,
it is enough to add to the current set of (non-exhaustive) modes a mode like

.. code-block:: none

   mode base_case (
     require true ;
   ) ;

which explicitly accounts for, and hence documents, the missing cases.
