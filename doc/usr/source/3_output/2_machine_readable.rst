.. _3_output/2_machine_readable:

JSON / XML Output
=================

Kind 2 can output its results in two structured formats:
:ref:`JSON<JSON format>` and :ref:`XML<XML format>`.
They facilite the processing of Kind 2's results by external tools.
The next sections describe each of these output formats in detail.

.. _JSON format:

JSON format
-----------

.. _schemas/kind2-output.json: https://github.com/kind2-mc/kind2/blob/develop/schemas/kind2-output.json

The JSON output is activated by running Kind 2 with the ``-json`` option.
Its syntax is fully specified by the JSON schema available in the
`schemas/kind2-output.json`_ file.

The root element of a JSON output document is either a :ref:`Log Object` if Kind 2
terminates early with an error, or an array of :ref:`Results Objects`
if Kind 2 succeeds generating some result.
Every :ref:`Results Object<Results Objects>` (including :ref:`Log Object`)
is identified and distinguished from other :ref:`Results<Results Objects>`
objects by a property of type string called ``objectType``.

In a successful execution, a :ref:`Kind2 Options Object` specifies the options
used by the tool, and any :ref:`Log<Log Object>` message is added to the array
as it is written. When Kind 2 is run as an
:ref:`interpreter<9_other/8_interpreter>`, the array includes one
:ref:`Execution Object` that contains a description of the computed values
for the output and state variables.
Otherwise, Kind 2 works as a model checker and performs
a series of analyses. The beginning of a main analysis is indicated by an
:ref:`AnalysisStart Object`, and its end by an :ref:`AnalysisStop Object`.
Within these delimiters, a :ref:`Property Object` describes the result
for a particular property of the input model under the parameters of the analysis.
When the verbose mode is enabled,
statistics and progress info of the analysis is also recorded along
through :ref:`Stat<Stat Object>` and :ref:`Progress<Progress Object>` objects.

Similarly to main analyses, when a post-analysis is enabled, the beginning of the post-analysis
is indicated by an :ref:`PostAnalysisStart Object`, and its end by an :ref:`PostAnalysisEnd Object`.

.. _Log Object:

Log Object
^^^^^^^^^^

A ``Log`` object records an informative message from the tool.
The value of its ``objectType`` property is ``log``.
The list of properties of a ``Log`` object are:

.. csv-table::
   :header: "Key", "Type", "Description"
   :widths: 5,5,30

   ``level``, ``string``, "A level that gives a rough guide of the importance of the message. Can be ``fatal``, ``error``, ``warn``, ``note``, ``info``, ``debug``, or ``trace``."
   ``source``, ``string``, "The name of the Kind 2 module which wrote the log."
   ``file``, ``string``, "Associated input file, if any."
   ``line``, ``integer``, "Associated line in the input file, if any."
   ``column``, ``integer``, "Associated column in the input file, if any."
   ``value``, ``string``, "The log message."

.. _Results Objects:

Results Objects
^^^^^^^^^^^^^^^

A ``Result object`` can be one of the following objects: a :ref:`Log Object`,
a :ref:`Kind2 Options Object`, an :ref:`AnalysisStart Object`, an :ref:`AnalysisStop Object`,
a :ref:`Property Object`, a :ref:`Stat Object`, a :ref:`Progress Object`,
a :ref:`PostAnalysisStart Object`, or a :ref:`PostAnalysisEnd Object`.

.. _Kind2 Options Object:

Kind2 Options Object
^^^^^^^^^^^^^^^^^^^^

A ``Kind2 options`` object describes the options used by the tool in the current execution.
The value of its ``objectType`` property is ``kind2Options``.
The list of properties of a ``Kind2 options`` object are:

.. csv-table::
   :header: "Key", "Type", "Description"
   :widths: auto

   ``enabled``, ``array``, "List of Kind 2 module names that are enabled."
   ``timeout``, ``number``, "The wallclock timeout used for all the analyses."
   ``bmcMax``, ``integer``, "Maximal number of iterations for BMC and K-induction."
   ``compositional``, ``boolean``, "Whether compositional analysis is enabled or not."
   ``modular``, ``boolean``, "Whether modular analysis is enabled or not."

.. _AnalysisStart Object:

AnalysisStart Object
^^^^^^^^^^^^^^^^^^^^

An ``AnalysisStart`` object indicates the beginning of a main analysis.
The value of its ``objectType`` property is ``analysisStart``.
The list of properties of an ``AnalysisStart`` object are:

.. csv-table::
   :header: "Key", "Type", "Description"
   :widths: auto

   ``top``, ``string``, "Name of the current top-level component."
   ``concrete``, ``array``, "Names of the subcomponents whose implementation is used in the analysis."
   ``abstract``, ``array``, "Names of the subcomponents whose contract is used in the analysis."
   ``assumptions``, ``array``, "Array of pairs (name of subcomponent, number of considered invariants)."

.. _AnalysisStop Object:

AnalysisStop Object
^^^^^^^^^^^^^^^^^^^

An ``AnalysisStop`` object indicates the end of a main analysis.
The value of its ``objectType`` property is ``analysisStop``. No properties are associated.

.. _Property Object:

Property Object
^^^^^^^^^^^^^^^

A ``Property`` object describes the result for a particular property of the input model.
The result should be considered in the context of the analysis in which the property object
is contained. The value of its ``objectType`` property is ``property``.
The list of properties of an ``AnalysisStart`` object are:

.. csv-table::
   :header: "Key", "Type", "Description"
   :widths: 10,5,30

   ``name``, ``string``, "Property identifier or description."
   ``scope``, ``string``, "Name of the component where the property was analyzed."
   ``line``, ``integer``, "Associated line in the input file, if any."
   ``column``, ``integer``, "Associated column in the input file, if any."
   ``source``, ``string``, "Origin of the property. Can be ``Assumption`` if it comes from an assumption check, ``Guarantee`` if it comes from the check of a guarantee, ``Ensure`` if it comes from a check of an ensure clause in a contract mode, ``OneModeActive`` if it comes from an exhaustiveness check of the state space covered by the modes of a contract, and ``PropAnnot`` if it comes from the check of a property annotation."
   ``runtime``, ``object``, "The runtime of the analysis (in seconds), and whether the timeout expired"
   ``k``, ``integer``, "The value of ``k`` in a k-inductive proof, if any."
   ``trueFor``, ``integer``, "The largest value of ``k`` for which the property was proved to be true, if any."
   ``answer``, ``object``, "The ``source`` of the answer, and the result ``value`` of the check. The result can be ``valid``, ``falsifiable``, or ``unknown``."
   ``counterExample``, ``object``, "Counterexample to the property satisfaction (only available when ``answer`` is ``falsifiable``). It describes a sequence of values for each stream, and automaton, that leads the system to the violation of the property. It also gives the list of contract modes that are active at each step, if any."

.. _Stat Object:

Stat Object
^^^^^^^^^^^

An ``Stat`` object provides statistics info about the current analysis.
The value of its ``objectType`` property is ``stat``.
The list of properties of a ``Stat`` object are:

.. csv-table::
   :header: "Key", "Type", "Description"
   :widths: 5,5,30

   ``source``, ``string``, "Name of the Kind 2 module which reported the info."
   ``sections``, ``array``, "List of ``statSection`` objects, each of them with a section ``name`` and a list of ``statItem`` objects. Each ``statItem`` has a ``name``, a ``type``, and a ``value``. See `schemas/kind2-output.json`_ for further details."

.. _Progress Object:

Progress Object
^^^^^^^^^^^^^^^

An ``Progress`` object reports the current value of ``k`` for k-inductive-based analyses.
The value of its ``objectType`` property is ``progress``.
The list of properties of a ``Progress`` object are:

.. csv-table::
   :header: "Key", "Type", "Description"
   :widths: auto

   ``source``, ``string``, "Name of the k-inductive-based analysis."
   ``k``, ``integer``, "Value for ``k``."

.. _PostAnalysisStart Object:

PostAnalysisStart Object
^^^^^^^^^^^^^^^^^^^^^^^^

An ``PostAnalysisStart`` object indicates the beginning of a post-analysis.
The value of its ``objectType`` property is ``postAnalysisStart``.
The list of properties of an ``PostAnalysisStart`` object are:

.. csv-table::
   :header: "Key", "Type", "Description"
   :widths: auto

   ``name``, ``string``, "Name of the post-analysis"

.. _PostAnalysisEnd Object:

PostAnalysisEnd Object
^^^^^^^^^^^^^^^^^^^^^^

An ``PostAnalysisEnd`` object indicates the end of a post-analysis.
The value of its ``objectType`` property is ``postAnalysisEnd``. No properties are associated.

.. _Execution Object:

Execution Object
^^^^^^^^^^^^^^^^

An ``Execution`` object describes the sequences of values for the output and state variables
of an input model computed from its simulation (see the :ref:`interpreter<9_other/8_interpreter>` mode).
The value of its ``objectType`` property is ``execution``. It only has one object property called
``trace`` which follows the same format than property ``counterExample`` in :ref:`Property Object`.

.. _XML format:

XML format
----------

.. _schemas/kind2-output.xsd: https://github.com/kind2-mc/kind2/blob/develop/schemas/kind2-output.xsd

The XML output is activated by running Kind 2 with the ``-xml`` option.
Its syntax is fully specified by the XML schema available in the
`schemas/kind2-output.xsd`_ file.

The root element of a XML output document is either a :ref:`Log Element` if Kind 2
terminates early with an error, or a :ref:`Results Element`
if Kind 2 succeeds generating some result.

.. _Log Element:

Log Element
^^^^^^^^^^^

A ``Log`` element is a simple element that records an informative message from the tool.
The list of attributes of a ``Log`` element are:

.. csv-table::
   :header: "Attribute", "Base Type", "Description"
   :widths: 5,8,30

   ``class``, ``xs:string``, "A level that gives a rough guide of the importance of the message. Can be ``fatal``, ``error``, ``warn``, ``note``, ``info``, ``debug``, or ``trace``."
   ``source``, ``xs:string``, "The name of the Kind 2 module which wrote the log."
   ``line``, ``xs:integer``, "Associated line in the input file, if any."
   ``column``, ``xs:integer``, "Associated column in the input file, if any."

.. _Results Element:

Results Element
^^^^^^^^^^^^^^^

A ``Results`` element is a sequence of zero or more of the following elements: a :ref:`Log Element`,
an :ref:`AnalysisStart Element`, an :ref:`AnalysisStop Element`,
a :ref:`Property Element`, a :ref:`Stat Element`, a :ref:`Progress Element`,
a :ref:`PostAnalysisStart Element`, a :ref:`PostAnalysisEnd Element`, or
an :ref:`Execution Element`.

The list of attributes of a ``Results`` element are:

.. csv-table::
   :header: "Attribute", "Base Type", "Description"
   :widths: auto

   ``enabled``, ``xs:string``, "List of comma-separated Kind 2 enabled module names."
   ``timeout``, ``xs:decimal``, "The wallclock timeout used for all the analyses."
   ``bmc_max``, ``xs:integer``, "Maximal number of iterations for BMC and K-induction."
   ``compositional``, ``xs:boolean``, "Whether compositional analysis is enabled or not."
   ``modular``, ``xs:boolean``, "Whether modular analysis is enabled or not."

.. _AnalysisStart Element:

AnalysisStart Element
^^^^^^^^^^^^^^^^^^^^^

An ``AnalysisStart`` element is an empty element that indicates the beginning of a main analysis.
The list of attributes of an ``AnalysisStart`` element are:

.. csv-table::
   :header: "Attribute", "Base Type", "Description"
   :widths: 8,8,30

   ``top``, ``xs:string``, "Name of the current top-level component."
   ``concrete``, ``xs:string``, "Names of the subcomponents whose implementation is used in the analysis (comma-separated list)."
   ``abstract``, ``xs:string``, "Names of the subcomponents whose contract is used in the analysis (comma-separated list)."
   ``assumptions``, ``xs:string``, "Comma-separated list of pairs (subcomponent name, number of considered invariants)."

.. _AnalysisStop Element:

AnalysisStop Element
^^^^^^^^^^^^^^^^^^^^

An ``AnalysisStop`` element is an empty element that indicates the end of a main analysis. No attributes.

.. _Property Element:

Property Element
^^^^^^^^^^^^^^^^

A ``Property`` element describes the result for a particular property of the input model.
The result should be considered in the context of the analysis in which the property element
is contained. The list of attributes of a ``Property`` element are:

.. csv-table::
   :header: "Attribute", "Base Type", "Description"
   :widths: 5,7,30

   ``name``, ``xs:string``, "Property identifier or description."
   ``scope``, ``xs:string``, "Name of the component where the property was analyzed."
   ``file``, ``xs:string``, "Associated input file, if any."
   ``line``, ``xs:integer``, "Associated line in the input file, if any."
   ``column``, ``xs:integer``, "Associated column in the input file, if any."
   ``source``, ``xs:string``, "Origin of the property. Can be ``Assumption`` if it comes from an assumption check, ``Guarantee`` if it comes from the check of a guarantee, ``Ensure`` if it comes from a check of an ensure clause in a contract mode, ``OneModeActive`` if it comes from an exhaustiveness check of the state space covered by the modes of a contract, and ``PropAnnot`` if it comes from the check of a property annotation."

A ``Property`` element contains one ``Answer`` element, which includes the result for the property check
(``valid``, ``falsifiable``, or ``unknown``), and identifies the Kind 2 module responsible for the answer.
If the result is ``valid``, or ``falsifiable``, it also contains a ``Runtime`` element, which reports
the runtime of the analysis (in seconds), and whether the timeout expired or not.
If the result is ``valid``, a ``K`` element gives the value of ``k`` for which the property was proved valid.
If the result is ``falsifiable``, a ``Counterexample`` element describes a sequence of values for each stream,
and automaton, that leads the system to the violation of the property.
It also gives the list of contract modes that are active at each step, if any.
If the result is ``unknown``, the ``Property`` element may contain a ``TrueFor`` element
specifying the largest value of ``k`` for which the property was proved to be true.

.. _Stat Element:

Stat Element
^^^^^^^^^^^^

An ``Stat`` element provides statistics info about the current analysis.
It has only one attribute of type ``xs:string``, ``source``,
which is the name of the Kind 2 module which reported the piece of information.
Its content consists in one or more ``Section`` elements. Each section has
one ``name`` element, and one or more ``item`` elements. Each ``item`` element
has one ``name`` element, and either a ``value`` element or a ``valuelist`` element.
A ``valuelist`` has one or more ``value`` elements, and each ``value`` element
has a ``type`` attribute (currently ``int`` or ``float``), and
its content is the actual value.

.. _Progress Element:

Progress Element
^^^^^^^^^^^^^^^^

A ``Progress`` element is a simple element that reports the
current value of ``k`` for a k-inductive-based analysis.
It has only one attribute of type ``xs:string``, ``source``,
which is the name of the k-inductive-based analysis.

.. _PostAnalysisStart Element:

PostAnalysisStart Element
^^^^^^^^^^^^^^^^^^^^^^^^^

An ``PostAnalysisStart`` element is an empty element that indicates
the beginning of a post-analysis. It has only one attribute of type ``xs:string``,
the ``name`` of the post-analysis.

.. _PostAnalysisEnd Element:

PostAnalysisEnd Element
^^^^^^^^^^^^^^^^^^^^^^^

An ``PostAnalysisEnd`` element is an empty element that indicates
the end of a post-analysis. No attributes.

.. _Execution Element:

Execution Element
^^^^^^^^^^^^^^^^^

An ``Execution`` element describes the sequences of values for the output and
state variables of an input model computed from the simulation of its execustion
(see the :ref:`interpreter<9_other/8_interpreter>` mode).
