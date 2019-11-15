.. _9_other/8_interpreter:

Interpreter
===========

The interpreter is a special mode where Kind 2 reads inputs from a
file and prints the outputs of the system at each step.

To use the interpreter, run

.. code-block:: none

  kind2 --enable interpreter <lustre_file> --interpreter_input_file <input_file>

You can specify the number of steps to run with the option ``--interpreter_steps <int>``.
By default, the number of steps is determined by the input file.

Structure of the input file
---------------------------

The inputs must be specified in a JSON file.

The overall structure is as follows:

.. code-block:: json

  [
    {
      "var1": "42",
      "var2": true,
      "var3": "0.5"
    },
    {
      "var1": "24",
      "var2": false,
      "var3": "0.5"
    }
  ]

The top-level JSON array corresponds to the successive time steps.
Each time step is described by a JSON object associating to each input variable its value for this time step.

*NOTE: Kind2 also accepts the CSV format for backward compatibility reasons. However,
it does not support records, arrays and tuples. Please give your input file the adequate extension (\*.json or \*.csv) in order to indicate to Kind2 which format you are using.*

Integers and reals
------------------

As in the above example, integers and reals should be written as strings in order to avoid a potential loss of precision or an integer overflow while parsing the file.
Nevertheless, small integers can be written as native JSON integers without problem.

Records
-------

Record values can be expressed using a JSON object.

For instance, a variable ``c`` of type ``{ re: real; im: real }``
can be assigned as follows:

.. code-block:: json

  [
    {
      "c": { "re": "-1.0", "im": "0.25" }
    }
  ]

Arrays
------

Array values can be expressed using a JSON array.

For instance, a variable ``a`` of type ``bool^3^2``
can be assigned as follows:

.. code-block:: json

  [
    {
      "a": [[true, true, false], [false, true, true]]
    }
  ]

Tuples
------

The JSON format does not support tuples by default.
However, Kind2 extends the JSON syntax so that tuples can be easily expressed.

For instance, a variable ``t`` of type ``[int, bool, real]``
can be assigned as follows:

.. code-block:: none

  [
    {
      "t": ("36", false, "5.0")
    }
  ]

An alternative syntax using a JSON object is allowed in case you want to produce a valid JSON file:

.. code-block:: json

  [
    {
      "t": { "0":"36", "1": false, "2":"5.0" }
    }
  ]
