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

(* Spawn [f] in a new domain as the engine [mdl] with identifier [id].
   [f] handles its own cleanup and returns the unexpected exception it
   terminated on, if any. *)
let spawn mdl id ~disconnect f =
  let outcome = Atomic.make Running in
  let domain =
    Domain.spawn (fun () ->
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
