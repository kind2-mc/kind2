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

(* Registry and lifecycle of engine domains.

   Every analysis engine runs in its own domain, spawned by the
   supervisor. This module keeps track of the running domains, replacing
   the list of child process PIDs of the process-based implementation:
   the supervisor polls {!take_finished} where it used to poll
   [Unix.waitpid].

   A domain cannot be killed. Termination is cooperative: the
   supervisor broadcasts a termination message which engines check on
   every iteration of their event loop, and an engine that does not
   react because it is stuck in a solver call is unblocked by killing
   the solver processes of its domain ({!kill_solvers}). *)

(* Outcome of an engine. [Done None] is normal termination, [Done
   (Some e)] termination on an unexpected exception. *)
type outcome = Running | Done of exn option

type t = {
  id : int ;                    (* Identifier of the engine among the
                                   children of the supervisor,
                                   replacing the PID *)
  mdl : Lib.kind_module ;
  domain : unit Domain.t ;
  outcome : outcome Atomic.t ;
  disconnect : unit -> unit ;   (* Detaches the engine from the
                                   messaging system *)
}

let id { id } = id

let mdl { mdl } = mdl

let outcome { outcome } = Atomic.get outcome

(* Fresh identifiers for engines *)
let next_id =
  let c = Atomic.make 1 in
  fun () -> Atomic.fetch_and_add c 1

(* Running engine domains. Guarded by [lock]; only the supervisor
   spawns and reaps, but engines are spawned from callbacks whose
   context is easier to audit with a lock than without. *)
let running : t list ref = ref []
let lock = Mutex.create ()

(* Set when the supervisor starts terminating the engines of an
   analysis. Engines failing after this point fail because their
   solvers were killed under them, which is not a crash. Solver
   instances are killed outright instead of shut down gracefully while
   the flag is set. *)
let terminating = Atomic.make false

let set_terminating b =
  Atomic.set terminating b ;
  SMTSolver.set_shutting_down b

let is_terminating () = Atomic.get terminating

(* Signals are handled by the supervisor domain: engine domains keep
   them blocked.

   SIGPIPE must be blocked as well: a write to the pipe of a killed
   solver would otherwise generate a signal whose OCaml handler (which
   raises [Signal]) may run in any domain, crashing an unrelated engine
   or the supervisor. With the signal blocked, the write of the engine
   fails in place with [EPIPE] instead. *)
let signals_to_block =
  [ Sys.sigalrm; Sys.sigint; Sys.sigterm; Sys.sigquit; Sys.sigpipe ]

(* Size of the minor heap of an engine domain, in words.

   A minor collection stops every domain of the process: the collecting
   domain waits for all the others to reach a safe point. An engine
   allocates heavily, and with the default minor heap of 256k words the
   engines of an analysis collect often enough that, when there are more
   engines than cores, they spend most of their time waiting for the
   domains the scheduler has descheduled. The engines then progress
   noticeably slower than the separate processes they replaced, which
   had a collector each.

   Four times less often closes that gap on Linux and macOS. On
   Windows the wait at that safe point costs seconds, so it does not.
   Measured there on four cores, `test-issue-127.lus [slice_on]` at
   `--timeout 84`, two runs per size:

     1M words   70s, 73s, killed at 204s twice    ~50 freezes
     4M words   14s, 15s                          1
     16M words  20s, 24s                          0 to 1
     64M words  25s, 9s                           0 to 1

   Four million is where it flattens, and the collection count stops
   falling past it. The step from one to four is what turns a run
   sometimes killed at the harness budget into one that is reliably
   fifteen seconds.

   Windows alone, because Linux and macOS do not move across that whole
   range and the memory is not free: 32MB per engine against 8, and
   162MB to 432MB of peak resident memory on that model. The setting is
   not inherited from the supervisor, so each domain applies it to
   itself.

   A mitigation, not a diagnosis: why the wait costs seconds on Windows
   is not established. See #1477. *)
let engine_minor_heap_size = if Sys.win32 then 1 lsl 22 else 1 lsl 20

(* Give the minor heap of the supervisor the size the engines use.

   Growing a minor heap past the largest one the runtime has reserved
   so far stops every domain and reallocates the minor heap of each,
   promoting everything they hold. An engine sizing its own minor heap
   would pay that price, once per engine and per analysis, while the
   engines of the analysis are running: the collections it saves cost
   less than the ones it forces. Enlarging the minor heap of the
   supervisor first, while it is the only domain, raises that maximum
   once and for the whole run, and leaves the engines nothing to
   reserve.

   Call before spawning any engine. *)
let reserve_minor_heaps () =
  Gc.set { (Gc.get ()) with Gc.minor_heap_size = engine_minor_heap_size }

(* Spawn [f] in a new domain as the engine [mdl] with identifier [id].
   [f] handles its own cleanup and returns the unexpected exception it
   terminated on, if any. *)
let spawn mdl id ~disconnect f =
  let outcome = Atomic.make Running in
  let domain =
    Domain.spawn (fun () ->
      Gc.set { (Gc.get ()) with Gc.minor_heap_size = engine_minor_heap_size } ;
      (* Number the names this engine invents apart from the names of
         the others, and independently of them. Before anything it
         builds. *)
      Lib.set_naming_range id ;
      (* No signal masks on Windows; the signals of the list do not
         exist there anyway *)
      if not Sys.win32 then
        ignore (Thread.sigmask Unix.SIG_BLOCK signals_to_block) ;
      let r = try f () with e -> Some e in
      Atomic.set outcome (Done r))
  in
  let child = { id ; mdl ; domain ; outcome ; disconnect } in
  Mutex.protect lock (fun () -> running := child :: !running) ;
  child

(* Return the engines that have terminated since the last call, joined
   and removed from the registry *)
let take_finished () =
  let finished =
    Mutex.protect lock (fun () ->
      let f, s =
        List.partition (fun c -> Atomic.get c.outcome <> Running) !running
      in
      running := s ;
      f)
  in
  (* The domains have finished their computation: joining only reaps
     them. *)
  List.iter (fun c -> Domain.join c.domain) finished ;
  finished

(* Return the engines that are still running *)
let live () = Mutex.protect lock (fun () -> !running)

(* Return the running engine with the given identifier, if any *)
let find id_ =
  Mutex.protect lock (fun () ->
    List.find_opt (fun c -> c.id = id_) !running)

(* Kill the solver processes of the domain of an engine, without
   interacting with them, to unblock an engine stuck in a solver
   call *)
let kill_solvers { domain } =
  SMTSolver.kill_solvers_of_domain ((Domain.get_id domain :> int))

(* Give up on the engines that are still running: a domain cannot be
   killed, and an engine busy in a long computation would delay the end
   of the analysis arbitrarily. They are detached from the messaging
   system, so that they cannot disturb the next analysis, and their
   solvers are killed, so that they unwind as soon as they leave the
   computation they are in. They are removed from the registry and
   their outcome is never observed; they die with the process.

   Returns the engines that were abandoned. *)
let abandon_live () =
  let abandoned = Mutex.protect lock (fun () -> let l = !running in running := [] ; l) in
  abandoned |> List.iter (fun c -> c.disconnect () ; kill_solvers c) ;
  abandoned


(*
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End:
*)
