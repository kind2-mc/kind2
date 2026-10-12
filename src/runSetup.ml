(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)

(* Process setup common to the executables that run an analysis (kind2,
   kmoxi), done once the command line is parsed and before any input is
   read: descriptors kept from the children, signal handlers, the wall
   clock timeout and the global timer.

   Without it a SIGTERM keeps its default action and ends the process on
   the spot, without the teardown that kills the solvers. The solvers are
   started from engine domains, which block SIGTERM, SIGINT, SIGQUIT,
   SIGALRM and SIGPIPE, and they keep that signal mask across exec: left
   behind, they ignore everything but SIGKILL. *)

open Lib

module Signals = TermLib.Signals

let setup () =
  (* Keep the descriptors of Kind 2 to itself.

     On Windows a child inherits every handle marked inheritable, not
     only the three it is given, so a solver ends up holding the
     standard input, output and error of Kind 2 as well as its own
     pipes. A solver that outlives Kind 2 then keeps them open, and
     whoever is reading that output waits for an end that never comes,
     long after Kind 2 is gone. Its standard input goes the same way:
     a harness writing to Kind 2 would not see its reader go away.
     Clearing the flag leaves the solvers with the pipes they are
     given, which [Unix.create_process] duplicates as inheritable
     itself.

     Only on Windows. Elsewhere a child of [Unix.create_process] gets
     the three descriptors it is given duplicated over its own, and
     never sees these.

     [Sys.command] does expect to inherit them, and the certificate
     paths, which use it, are not guarded against running here: the
     output of what they start goes nowhere from now on. What those
     paths produce is unusable on Windows in any case, being [#!/bin/sh]
     scripts and command lines that redirect to [/dev/null], so what is
     lost is the console output of something that cannot work there
     anyway. Making them work is a matter of handing them the
     descriptors, not of leaving these inheritable for every child. *)
  if Sys.win32 then (
    let keep fd name =
      try Unix.set_close_on_exec fd with Unix.Unix_error (e, _, _) ->
        (* Loud rather than logged: failing here quietly puts the
           output of Kind 2 back within reach of its solvers, on the one
           platform where that leaves whoever reads it waiting. It
           should never happen, and there is no sign of it if it does. *)
        KEvent.log L_warn
          "Could not keep %s from the children of Kind 2 (%s).@ A solver \
           outliving Kind 2 may hold it open."
          name (Unix.error_message e)
    in
    keep Unix.stdin "stdin" ;
    keep Unix.stdout "stdout" ;
    keep Unix.stderr "stderr"
  ) ;

  (* Raise exception on CTRL+C. *)
  Sys.catch_break true ;

  (* Set sigalrm handler. *)
  Signals.set_sigalrm_timeout_from_flag () ;

  (* On Windows there is no SIGALRM, and the wall clock is looked at
     only in the polling loop of the supervisor. That is enough while
     the supervisor runs. It has stopped running: runs given 84s have
     been killed by the test harness still going at 204s, having
     written nothing since the analysis header -- no engine output and
     no timeout banner, which is what a process makes when nothing in
     it is executing rather than when it is slow.

     One cause of that is known and fixed: ocaml/ocaml#15028, where a
     thread that never yields kept its domain's runtime lock and the
     other threads of that domain never ran, released in OCaml 5.5.1.
     A reproducer of one domain and two threads is clean from 5.5.1 on.
     Kind 2 is not. It overran the same way on 5.5.1, on a build that
     had this backstop removed, which says either that something else
     starves the supervisor or that the fix does not cover what Kind 2
     does -- about ten domains with threads of their own each, which
     is not what the reproducer tested. See #1477 and #1485.

     So the last word on the wall clock here belongs to a thread the
     operating system schedules, which the runtime cannot stop, until
     that is understood.

     It is a backstop and not the timeout. Windows has the ordinary path
     too -- the polling loop notices the clock and raises [TimeoutWall],
     which unwinds through the exit path and reports what was proved,
     the same as SIGALRM does elsewhere -- and that path works on every
     run whose supervisor is running, which is every healthy one. The
     grace is how long to wait for it before concluding it will not
     come.

     Sixty, from what CI measures rather than from a multiple. The
     ordinary path is not quick and steady: it waits out the same
     stalls the backstop exists because of, so how late it is has no
     bound to take a multiple of. One test on the Windows runner came
     in 4.2s past its timeout on one commit, 11.5s on another and 29.0s
     on a third, all healthy runs reporting what they had proved. A
     grace of thirty would have killed the third one had it been a
     second slower, taking its verdict with it -- and the run that most
     needs the grace is exactly the stalled one, which is the run most
     likely to exhaust it.

     Not less, and never zero. This ends the process rather than
     unwinding it, so it forfeits the results and forces its own status
     -- fire it while an orderly teardown is still running and a run
     that had disproved a property would report an incomplete analysis
     instead. The grace is the width of that window, and it is worth
     being generous with. *)
  ( if Sys.win32 then
      match Flags.timeout_wall () with
      | timeout when timeout > 0. ->
        (* A count of seconds the other side can hold. It reaches a
           thirty-two bit count of milliseconds, and it comes from a
           float the user chose: [--timeout inf] converts to zero, which
           would arm the backstop at the grace alone and kill a run that
           asked for no limit, and a large enough value wraps the
           multiplication instead. Anything past the ceiling is a run
           that means to go on indefinitely, and the backstop simply
           does not arm for it. *)
        let ceiling = 1_000_000. in
        if Float.is_nan timeout || timeout > ceiling then ()
        else
          NativeTimeout.arm
            (int_of_float timeout + 60) ExitCodes.incomplete_analysis
      | _ -> () ) ;

  (* Install generic signal handlers for other signals. *)
  Signals.set_sigint () ;
  (* SIGPIPE is ignored, not turned into an exception: signal handlers
     are global to the process and may run in any domain, so a broken
     pipe of one engine would crash an arbitrary other engine or the
     supervisor. With the signal ignored, a write to a broken pipe
     fails in place with EPIPE in the domain that wrote. *)
  Signals.ignore_sigpipe () ;
  Signals.set_sigterm () ;
  Signals.set_sigquit () ;

  (* Starting global timer. *)
  Stat.start_timer Stat.total_time
