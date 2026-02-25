.. _contract_monitor:

Contract Monitor
================

The contract monitor is a special mode where Kind 2 reads input and output values from
a file and prints a full contract trace of the execution of the top-level node and
the subnodes that appear in the contract. The trace includes truth values for assumptions,
guarantees, mode requires, and mode ensures.


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

