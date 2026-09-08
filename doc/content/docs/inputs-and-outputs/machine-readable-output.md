---
title: "JSON / XML Output"
weight: 16
---

Kind 2 can output its results in two structured formats:
[JSON]({{< relref "/docs/inputs-and-outputs/machine-readable-output#json-format" >}}) and [XML]({{< relref "/docs/inputs-and-outputs/machine-readable-output#xml-format" >}}).
They facilite the processing of Kind 2's results by external tools.
The next sections describe each of these output formats in detail.

## JSON format

The JSON output is activated by running Kind 2 with the `-json` option.
Its syntax is fully specified by the JSON schema available in the
[schemas/kind2-output.json](https://github.com/kind2-mc/kind2/blob/main/schemas/kind2-output.json) file.

The root element of a JSON output document is either a [Log Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#log-object" >}}) if Kind 2
terminates early with an error, or an array of [Results Objects]({{< relref "/docs/inputs-and-outputs/machine-readable-output#results-objects" >}})
if Kind 2 succeeds generating some result.
Every [Results Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#results-objects" >}}) (including [Log Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#log-object" >}}))
is identified and distinguished from other [Results]({{< relref "/docs/inputs-and-outputs/machine-readable-output#results-objects" >}})
objects by a property of type string called `objectType`.

In a successful execution, a [Kind2 Options Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#kind2-options-object" >}}) specifies the options
used by the tool, and any [Log]({{< relref "/docs/inputs-and-outputs/machine-readable-output#log-object" >}}) message is added to the array
as it is written. When Kind 2 is run as an
[interpreter]({{< relref "/docs/advanced-features/interpreter" >}}), the array includes one
[Execution Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#execution-object" >}}) that contains a description of the computed values
for the output and state variables.
Otherwise, Kind 2 works as a model checker and performs
a series of analyses. The beginning of a main analysis is indicated by an
[AnalysisStart Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#analysisstart-object" >}}), and its end by an [AnalysisStop Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#analysisstop-object" >}}).
Within these delimiters, a [Property Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#property-object" >}}) describes the result
for a particular property of the input model under the parameters of the analysis.
When the verbose mode is enabled,
statistics and progress info of the analysis is also recorded along
through [Stat]({{< relref "/docs/inputs-and-outputs/machine-readable-output#stat-object" >}}) and [Progress]({{< relref "/docs/inputs-and-outputs/machine-readable-output#progress-object" >}}) objects.

Similarly to main analyses, when a post-analysis is enabled, the beginning of the post-analysis
is indicated by an [PostAnalysisStart Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#postanalysisstart-object" >}}), and its end by an [PostAnalysisEnd Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#postanalysisend-object" >}}).

### Incremental JSON format

The incremental JSON output is activated by running Kind 2 with the `-ijson`
option. It contains the same [Results Objects]({{< relref "/docs/inputs-and-outputs/machine-readable-output#results-objects" >}}) as the regular JSON
output, but prints them as a sequence of independent JSON objects rather than as
elements of a single enclosing array.

With the `-json` option, the output is not a complete, parsable JSON document
until Kind 2 terminates and closes the root array. The `-ijson` option emits
each object as a complete JSON value as soon as it becomes available. This allows
external tools to process Kind 2's output incrementally without waiting for the
entire analysis to finish.

### Log Object

A `Log` object records an informative message from the tool.
The value of its `objectType` property is `log`.
The list of properties of a `Log` object are:

| Key      | Type      | Description                                                                                                                              |
|----------|-----------|------------------------------------------------------------------------------------------------------------------------------------------|
| `level`  | `string`  | A level that gives a rough guide of the importance of the message. Can be `fatal`, `error`, `warn`, `note`, `info`, `debug`, or `trace`. |
| `source` | `string`  | The name of the Kind 2 module which wrote the log.                                                                                       |
| `file`   | `string`  | Associated input file, if any.                                                                                                           |
| `line`   | `integer` | Associated line in the input file, if any.                                                                                               |
| `column` | `integer` | Associated column in the input file, if any.                                                                                             |
| `value`  | `string`  | The log message.                                                                                                                         |

### Results Objects

A `Result object` can be one of the following objects: a [Log Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#log-object" >}}),
a [Kind2 Options Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#kind2-options-object" >}}), an [AnalysisStart Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#analysisstart-object" >}}), an [AnalysisStop Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#analysisstop-object" >}}),
a [Property Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#property-object" >}}), a [Stat Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#stat-object" >}}), a [Progress Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#progress-object" >}}),
a [PostAnalysisStart Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#postanalysisstart-object" >}}), or a [PostAnalysisEnd Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#postanalysisend-object" >}}).

### Kind2 Options Object

A `Kind2 options` object describes the options used by the tool in the current execution.
The value of its `objectType` property is `kind2Options`.
The list of properties of a `Kind2 options` object are:

| Key             | Type      | Description                                           |
|-----------------|-----------|-------------------------------------------------------|
| `enabled`       | `array`   | List of Kind 2 module names that are enabled.         |
| `timeout`       | `number`  | The wallclock timeout used for all the analyses.      |
| `bmcMax`        | `integer` | Maximal number of iterations for BMC and K-induction. |
| `compositional` | `boolean` | Whether compositional analysis is enabled or not.     |
| `modular`       | `boolean` | Whether modular analysis is enabled or not.           |

### AnalysisStart Object

An `AnalysisStart` object indicates the beginning of a main analysis.
The value of its `objectType` property is `analysisStart`.
The list of properties of an `AnalysisStart` object are:

| Key           | Type     | Description                                                              |
|---------------|----------|--------------------------------------------------------------------------|
| `top`         | `string` | Name of the current top-level component.                                 |
| `concrete`    | `array`  | Names of the subcomponents whose implementation is used in the analysis. |
| `abstract`    | `array`  | Names of the subcomponents whose contract is used in the analysis.       |
| `assumptions` | `array`  | Array of pairs (name of subcomponent, number of considered invariants).  |

### AnalysisStop Object

An `AnalysisStop` object indicates the end of a main analysis.
The value of its `objectType` property is `analysisStop`. No properties are associated.

### Property Object

A `Property` object describes the result for a particular property of the input model.
The result should be considered in the context of the analysis in which the property object
is contained. The value of its `objectType` property is `property`.
The list of properties of an `AnalysisStart` object are:

| Key              | Type      | Description                                                                                                                                                                                                                                                                                                                                                                                                    |
|------------------|-----------|----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `name`           | `string`  | Property identifier or description.                                                                                                                                                                                                                                                                                                                                                                            |
| `scope`          | `string`  | Name of the component where the property was analyzed.                                                                                                                                                                                                                                                                                                                                                         |
| `line`           | `integer` | Associated line in the input file, if any.                                                                                                                                                                                                                                                                                                                                                                     |
| `column`         | `integer` | Associated column in the input file, if any.                                                                                                                                                                                                                                                                                                                                                                   |
| `source`         | `string`  | Origin of the property. Can be `Assumption` if it comes from an assumption check, `Guarantee` if it comes from the check of a guarantee, `Ensure` if it comes from a check of a require-ensure clause in a contract mode, `OneModeActive` if it comes from an exhaustiveness check of the state space covered by the modes of a contract, and `PropAnnot` if it comes from the check of a property annotation. |
| `runtime`        | `object`  | The runtime of the analysis (in seconds), and whether the timeout expired                                                                                                                                                                                                                                                                                                                                      |
| `k`              | `integer` | The value of `k` in a k-inductive proof, if any.                                                                                                                                                                                                                                                                                                                                                               |
| `trueFor`        | `integer` | The largest value of `k` for which the property was proved to be true, if any.                                                                                                                                                                                                                                                                                                                                 |
| `answer`         | `object`  | The `source` of the answer, and the result `value` of the check. The result can be `valid`, `falsifiable`, or `unknown`.                                                                                                                                                                                                                                                                                       |
| `counterExample` | `object`  | Counterexample to the property satisfaction (only available when `answer` is `falsifiable`). It describes a sequence of values for each stream that leads the system to the violation of the property. It also gives the list of contract modes that are active at each step, if any.                                                                                                                          |

### Stat Object

An `Stat` object provides statistics info about the current analysis.
The value of its `objectType` property is `stat`.
The list of properties of a `Stat` object are:

| Key        | Type     | Description                                                                                                                                                                                                                                                                            |
|------------|----------|----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `source`   | `string` | Name of the Kind 2 module which reported the info.                                                                                                                                                                                                                                     |
| `sections` | `array`  | List of `statSection` objects, each of them with a section `name` and a list of `statItem` objects. Each `statItem` has a `name`, a `type`, and a `value`. See [schemas/kind2-output.json](https://github.com/kind2-mc/kind2/blob/main/schemas/kind2-output.json) for further details. |

### Progress Object

An `Progress` object reports the current value of `k` for k-inductive-based analyses.
The value of its `objectType` property is `progress`.
The list of properties of a `Progress` object are:

| Key      | Type      | Description                             |
|----------|-----------|-----------------------------------------|
| `source` | `string`  | Name of the k-inductive-based analysis. |
| `k`      | `integer` | Value for `k`.                          |

### PostAnalysisStart Object

An `PostAnalysisStart` object indicates the beginning of a post-analysis.
The value of its `objectType` property is `postAnalysisStart`.
The list of properties of an `PostAnalysisStart` object are:

| Key    | Type     | Description               |
|--------|----------|---------------------------|
| `name` | `string` | Name of the post-analysis |

The post-analyses currently available are [Test Generation]({{< relref "/docs/advanced-features/test-generation" >}}) (`testgen`),
[Proof Certificates]({{< relref "/docs/advanced-features/proofs" >}}) (`certification`),
[Contract Generation]({{< relref "/docs/advanced-features/contract-generation" >}}) (`contractgen`),
[Invariant Printing]({{< relref "/docs/advanced-features/invariant-printing" >}}) (`invprint`), and
[Inductive Validity Core]({{< relref "/docs/advanced-features/inductive-validity-core" >}}) (`ivc`).

### PostAnalysisEnd Object

An `PostAnalysisEnd` object indicates the end of a post-analysis.
The value of its `objectType` property is `postAnalysisEnd`. No properties are associated.

### Execution Object

An `Execution` object describes the sequences of values for the output and state variables
of an input model computed from its simulation (see the [interpreter]({{< relref "/docs/advanced-features/interpreter" >}}) mode).
The value of its `objectType` property is `execution`. It only has one object property called
`trace` which follows the same format than property `counterExample` in [Property Object]({{< relref "/docs/inputs-and-outputs/machine-readable-output#property-object" >}}).

### ModelElementSet Object

A `ModelElementSet` object describes a set of model elements (a model element can be an equation, a node call, an assumption, a guarantee, etc).
It is used to describe a core that we can get from an [Inductive Validity Core]({{< relref "/docs/advanced-features/inductive-validity-core" >}}) (`ivc`)
or [Minimal Cut Set]({{< relref "/docs/advanced-features/minimal-cut-set#minimal-cut-set" >}}) (`mcs`) analysis.
The result should be considered in the context of the analysis or post-analysis in which the ModelElementSet object
is contained. The value of its `objectType` property is `modelElementSet`.

| Key              | Type      | Description                                                                                                                                                  |
|------------------|-----------|--------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `class`          | `string`  | Class of the core. Can be `must`, `must complement`, `ivc`, `ivc complement`, `mcs` or `mcs complement`.                                                     |
| `size`           | `integer` | Number of model elements in the core.                                                                                                                        |
| `property`       | `string`  | The property associated with the core. If all properties are considered, this field is missing.                                                              |
| `runtime`        | `object`  | The runtime for computing the core (in seconds).                                                                                                             |
| `nodes`          | `array`   | For each node, contains an object that enumerates the model elements of the node that are part of the core.                                                  |
| `counterExample` | `object`  | Counterexample to the property satisfaction (only when relevant, that is, when class is `mcs` or `mcs complement`). See the `property` object for more info. |

## XML format

The XML output is activated by running Kind 2 with the `-xml` option.
Its syntax is fully specified by the XML schema available in the
[schemas/kind2-output.xsd](https://github.com/kind2-mc/kind2/blob/main/schemas/kind2-output.xsd) file.

The root element of a XML output document is either a [Log Element]({{< relref "/docs/inputs-and-outputs/machine-readable-output#log-element" >}}) if Kind 2
terminates early with an error, or a [Results Element]({{< relref "/docs/inputs-and-outputs/machine-readable-output#results-element" >}})
if Kind 2 succeeds generating some result.

### Log Element

A `Log` element is a simple element that records an informative message from the tool.
The list of attributes of a `Log` element are:

| Attribute | Base Type    | Description                                                                                                                              |
|-----------|--------------|------------------------------------------------------------------------------------------------------------------------------------------|
| `class`   | `xs:string`  | A level that gives a rough guide of the importance of the message. Can be `fatal`, `error`, `warn`, `note`, `info`, `debug`, or `trace`. |
| `source`  | `xs:string`  | The name of the Kind 2 module which wrote the log.                                                                                       |
| `line`    | `xs:integer` | Associated line in the input file, if any.                                                                                               |
| `column`  | `xs:integer` | Associated column in the input file, if any.                                                                                             |

### Results Element

A `Results` element is a sequence of zero or more of the following elements: a [Log Element]({{< relref "/docs/inputs-and-outputs/machine-readable-output#log-element" >}}),
an [AnalysisStart Element]({{< relref "/docs/inputs-and-outputs/machine-readable-output#analysisstart-element" >}}), an [AnalysisStop Element]({{< relref "/docs/inputs-and-outputs/machine-readable-output#analysisstop-element" >}}),
a [Property Element]({{< relref "/docs/inputs-and-outputs/machine-readable-output#property-element" >}}), a [Stat Element]({{< relref "/docs/inputs-and-outputs/machine-readable-output#stat-element" >}}), a [Progress Element]({{< relref "/docs/inputs-and-outputs/machine-readable-output#progress-element" >}}),
a [PostAnalysisStart Element]({{< relref "/docs/inputs-and-outputs/machine-readable-output#postanalysisstart-element" >}}), a [PostAnalysisEnd Element]({{< relref "/docs/inputs-and-outputs/machine-readable-output#postanalysisend-element" >}}), or
an [Execution Element]({{< relref "/docs/inputs-and-outputs/machine-readable-output#execution-element" >}}).

The list of attributes of a `Results` element are:

| Attribute       | Base Type    | Description                                           |
|-----------------|--------------|-------------------------------------------------------|
| `enabled`       | `xs:string`  | List of comma-separated Kind 2 enabled module names.  |
| `timeout`       | `xs:decimal` | The wallclock timeout used for all the analyses.      |
| `bmc_max`       | `xs:integer` | Maximal number of iterations for BMC and K-induction. |
| `compositional` | `xs:boolean` | Whether compositional analysis is enabled or not.     |
| `modular`       | `xs:boolean` | Whether modular analysis is enabled or not.           |

### AnalysisStart Element

An `AnalysisStart` element is an empty element that indicates the beginning of a main analysis.
The list of attributes of an `AnalysisStart` element are:

| Attribute     | Base Type   | Description                                                                                     |
|---------------|-------------|-------------------------------------------------------------------------------------------------|
| `top`         | `xs:string` | Name of the current top-level component.                                                        |
| `concrete`    | `xs:string` | Names of the subcomponents whose implementation is used in the analysis (comma-separated list). |
| `abstract`    | `xs:string` | Names of the subcomponents whose contract is used in the analysis (comma-separated list).       |
| `assumptions` | `xs:string` | Comma-separated list of pairs (subcomponent name, number of considered invariants).             |

### AnalysisStop Element

An `AnalysisStop` element is an empty element that indicates the end of a main analysis. No attributes.

### Property Element

A `Property` element describes the result for a particular property of the input model.
The result should be considered in the context of the analysis in which the property element
is contained. The list of attributes of a `Property` element are:

| Attribute | Base Type    | Description                                                                                                                                                                                                                                                                                                                                                                                             |
|-----------|--------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `name`    | `xs:string`  | Property identifier or description.                                                                                                                                                                                                                                                                                                                                                                     |
| `scope`   | `xs:string`  | Name of the component where the property was analyzed.                                                                                                                                                                                                                                                                                                                                                  |
| `file`    | `xs:string`  | Associated input file, if any.                                                                                                                                                                                                                                                                                                                                                                          |
| `line`    | `xs:integer` | Associated line in the input file, if any.                                                                                                                                                                                                                                                                                                                                                              |
| `column`  | `xs:integer` | Associated column in the input file, if any.                                                                                                                                                                                                                                                                                                                                                            |
| `source`  | `xs:string`  | Origin of the property. Can be `Assumption` if it comes from an assumption check, `Guarantee` if it comes from the check of a guarantee, `Ensure` if it comes from a check of an ensure clause in a contract mode, `OneModeActive` if it comes from an exhaustiveness check of the state space covered by the modes of a contract, and `PropAnnot` if it comes from the check of a property annotation. |

A `Property` element contains one `Answer` element, which includes the result for the property check
(`valid`, `falsifiable`, or `unknown`), and identifies the Kind 2 module responsible for the answer.
If the result is `valid`, or `falsifiable`, it also contains a `Runtime` element, which reports
the runtime of the analysis (in seconds), and whether the timeout expired or not.
If the result is `valid`, a `K` element gives the value of `k` for which the property was proved valid.
If the result is `falsifiable`, a `Counterexample` element describes a sequence of values for each stream
that leads the system to the violation of the property.
It also gives the list of contract modes that are active at each step, if any.
If the result is `unknown`, the `Property` element may contain a `TrueFor` element
specifying the largest value of `k` for which the property was proved to be true.

### Stat Element

An `Stat` element provides statistics info about the current analysis.
It has only one attribute of type `xs:string`, `source`,
which is the name of the Kind 2 module which reported the piece of information.
Its content consists in one or more `Section` elements. Each section has
one `name` element, and one or more `item` elements. Each `item` element
has one `name` element, and either a `value` element or a `valuelist` element.
A `valuelist` has one or more `value` elements, and each `value` element
has a `type` attribute (currently `int` or `float`), and
its content is the actual value.

### Progress Element

A `Progress` element is a simple element that reports the
current value of `k` for a k-inductive-based analysis.
It has only one attribute of type `xs:string`, `source`,
which is the name of the k-inductive-based analysis.

### PostAnalysisStart Element

An `PostAnalysisStart` element is an empty element that indicates
the beginning of a post-analysis. It has only one attribute of type `xs:string`,
the `name` of the post-analysis.
The post-analyses currently available are [Test Generation]({{< relref "/docs/advanced-features/test-generation" >}}) (`testgen`),
[Proof Certificates]({{< relref "/docs/advanced-features/proofs" >}}) (`certification`),
[Contract Generation]({{< relref "/docs/advanced-features/contract-generation" >}}) (`contractgen`),
[Invariant Printing]({{< relref "/docs/advanced-features/invariant-printing" >}}) (`invprint`), and
[Inductive Validity Core]({{< relref "/docs/advanced-features/inductive-validity-core" >}}) (`ivc`).

### PostAnalysisEnd Element

An `PostAnalysisEnd` element is an empty element that indicates
the end of a post-analysis. No attributes.

### Execution Element

An `Execution` element describes the sequences of values for the output and
state variables of an input model computed from the simulation of its execustion
(see the [interpreter]({{< relref "/docs/advanced-features/interpreter" >}}) mode).

### ModelElementSet Element

A `ModelElementSet` element describes a set of model elements (a model element can be an equation, a node call, an assumption, a guarantee, etc).
It is used to describe a core that we can get from an [Inductive Validity Core]({{< relref "/docs/advanced-features/inductive-validity-core" >}}) (`ivc`)
or [Minimal Cut Set]({{< relref "/docs/advanced-features/minimal-cut-set#minimal-cut-set" >}}) (`mcs`) analysis.
The result should be considered in the context of the analysis or post-analysis in which the ModelElementSet element
is contained. The list of attributes of a `ModelElementSet` element are:

| Attribute  | Base Type | Description                                                                                              |
|------------|-----------|----------------------------------------------------------------------------------------------------------|
| `class`    | `string`  | Class of the core. Can be `must`, `must complement`, `ivc`, `ivc complement`, `mcs` or `mcs complement`. |
| `size`     | `integer` | Number of model elements in the core.                                                                    |
| `property` | `string`  | The property associated with the core. If all properties are considered, this attribute is missing.      |

A `ModelElementSet` element contains one `Runtime` element, which indicates the runtime for computing the core.
It also contains a sequence of `Node` elements, each one enumerating the model elements in that node that are part of the core.
When relevant, it can also contain a `Counterexample` element (see the `Property` element for more info).
