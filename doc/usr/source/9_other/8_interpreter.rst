.. _9_other/8_interpreter:

Interpreter
===========

The interpreter is a special mode where Kind 2 reads input values from
a file and prints the computed values for the output and local variables
of a node at each step. If the Lustre file contains two or more top nodes,
a single node must be selected with either the command-line option :code:`--lus_main <node_name>` or
a single :code:`--%MAIN` annotation in the Lustre file.

To use the interpreter, run:

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
      "var3": "1.0/2.0"
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

.. _contract-monitor:

Contract Monitor
----------------

The contract monitor is a special mode of the interpreter where Kind 2 reads input and output values from a file and prints a full contract trace of the execution of the top-level node and the subnodes that appear in the contract. The trace includes truth values for assumptions, guarantees, mode requires, and mode ensures.


To use the contract monitor, run:

.. code-block:: none

  kind2 --enable contract_monitor <lustre_file> --monitor_trace_file <input_file>



You can specify the number of steps to run with the option ``--monitor_steps <int>``.
By default, the number of steps is determined by the input file.


For example, consider the following ``stopwatch`` system:

.. code-block:: none

   contract stopwatchSpec ( tgl, rst : bool ) returns ( c : int ) ;
   let
     var on: bool = tgl -> (pre on and not tgl) or (not pre on and tgl) ;
     assume not (rst and tgl) ;
     guarantee c >= 0 ;
     mode resetting ( require rst ; ensure c = 0 ; ) ;
     mode running (
       require not rst ; require on ; ensure c = (1 -> pre c + 1) ;
     ) ;
     mode stopped (
       require not rst ; require not on ; ensure c = (0 -> pre c) ;
     ) ;
   tel

   node previous ( x : int ) returns ( y : int ) ;
   let
     y = 0 -> pre x ;
   tel

   node stopwatch ( toggle, reset : bool ) returns ( count : int ) ;
   con
     import stopwatchSpec ( toggle, reset ) returns ( count ) ;
   noc
   var running : bool ;
   let
     running = (false -> pre running) <> toggle ;
     count = if reset then 0 else
       if running then previous(count) + 1 else previous(count) ;
   tel

Using a JSON file contianing a full execution trace:

.. code-block:: none

  [
    {
    "toggle": true,
    "reset": false,
    "count": 1
    },
    {
      "toggle": true,
      "reset": false,
      "count": 1
    },
    {
      "toggle": false,
      "reset": false,
      "count": 1
    },
    {
      "toggle": false,
      "reset": false,
      "count": 1
    },
    {
      "toggle": true,
      "reset": false,
      "count": 2
    },
    {
      "toggle": false,
      "reset": false,
      "count": 3
    }
  ]

.. code-block:: none

  kind2 --enable contract_monitor stopwatch.lus 
  --monitor_trace_file stopwatch_trace.json --monitor_steps 6

This produces the following output:

.. code-block:: none

  Execution:
  Node stopwatch ()
    == Assumptions ==
    assume[l4c3]          tt    tt    tt    tt    tt    tt
    == Guarantees ==
    guarantee[l5c3]       tt    tt    tt    tt    tt    tt
    == Modes ==
    stopped.requires      ff    tt    tt    tt    ff    ff
    stopped.ensures       ff    tt    tt    tt    ff    ff
    running.requires      tt    ff    ff    ff    tt    tt
    running.ensures       tt    ff    ff    ff    tt    tt
    resetting.requires    ff    ff    ff    ff    ff    ff
    resetting.ensures     ff    ff    ff    ff    ff    ff
    == Inputs ==
    toggle                tt    tt    ff    ff    tt    ff
    reset                 ff    ff    ff    ff    ff    ff
    == Outputs ==
    count                  1     1     1     1     2     3
    == Ghosts ==
    on                    tt    ff    ff    ff    tt    tt


