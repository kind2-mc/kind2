.. _3_output/3_exit_codes:

Exit codes
==========

Since version 1.9.0, Kind 2 returns the standard exit code ``0`` for success,
and a non-zero exit code to indicate an error, or an unsuccessful
analysis result. The precise meaning of the exit codes are described
in section :ref:`Code Convention<Current Exit Codes>`.
For information on the old convention, see section
:ref:`Former Convention<Former Exit Codes>`.

.. _Current Exit Codes:

Code Convention
^^^^^^^^^^^^^^^

With the default settings, Kind 2 performs a single, monolithic analysis of the main node.
If Kind 2 proves all invariant properties valid and all reachability properties reachable,
then it returns (exit code) ``0``.
If no properties are disproven, but some properties could not be proven (e.g. due to a timeout),
Kind 2 returns ``30``.
When Kind 2 disproves one or more properties, it returns ``40``.

In modular mode, the properties of all nodes are checked bottom-up.
Moreover, when compositional analysis is enabled too, the same node may be analyzed several
times with different levels of abstraction (see section
:ref:`1_techniques/1_techniques:Refinement in compositional and modular analyses`
for details).
In this case, Kind 2 returns ``40`` if one or more properties were disproven in *any* analysis.
It returns ``30`` if no properties were disproven, but some nodes were not analyzed (e.g. due to a timeout)
or some properties could not be proven.
It returns ``0`` if all properties were proven for all nodes in every analysis.

When contracts of imported nodes are checked for :ref:`realizability<9_other/11_contract_checks>`,
Kind 2 also reports an exit status following a similar convention.
If all the contracts are proven realizable, it returns ``0``.
If some contract is proven unrealizable, it returns ``40``.
When no contract is proven unrealizable, but some contract could not be proven realizable,
it returns ``30``.

If Kind 2 detects a general error, it returns ``1``. When the error is related to an incorrect
command-line argument, it returns ``2``.  If Kind 2 detects a parse error, it returns ``3``. 
If Kind 2 cannot find an SMT solver on the PATH, it returns ``4``.
When an unknown or unsupported version of an SMT solver is detected, it returns ``5``.

.. _Former Exit Codes:

Former Convention
^^^^^^^^^^^^^^^^^

Version 1.8.0 and earlier were not following the POSIX convention of returning ``0`` for success.
When all properties were proven, Kind 2 returned ``20``. If some property was disproven, it returned ``10``.
If no properties were disproven, but some result was unknown, it returned ``0``.
Moreover, Kind 2 returned ``2`` for any error.
