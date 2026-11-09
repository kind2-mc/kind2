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

(* Systems are built by the supervisor and, for IC3IA, by engines in
   domains of their own: the tables are shared under a lock *)
let lock = Mutex.create ()

let enabled_tops : Scope.t list ref = ref []

(* Whether the systems built in the domain have the constraints whatever
   their top system (see [with_enabled]) *)
let forced = Domain.DLS.new_key (fun () -> false)

let enabled top =
  Domain.DLS.get forced
  || Mutex.protect lock (fun () -> List.exists (Scope.equal top) !enabled_tops)

let with_enabled f =
  let saved = Domain.DLS.get forced in
  Domain.DLS.set forced true ;
  Fun.protect ~finally:(fun () -> Domain.DLS.set forced saved) f

let enable top =
  Mutex.protect lock (fun () ->
    if not (List.exists (Scope.equal top) !enabled_tops) then
      enabled_tops := top :: !enabled_tops)

(* The systems built without some finiteness constraints, compared
   physically. Only the latest are of use (the system the engines run on,
   and one sliced to a property, looked at as soon as it is built), so the
   list is kept short. *)
let omitted_systems : TransSys.t list ref = ref []

let max_omitted = 64

let note_omitted sys =
  Mutex.protect lock (fun () ->
    omitted_systems :=
      sys :: List.filteri (fun i _ -> i < max_omitted - 1) !omitted_systems)

let omitted sys =
  Mutex.protect lock (fun () -> List.exists (fun s -> s == sys) !omitted_systems)

let requested_flag = ref false

(* The time spent checking counterexamples on the systems with the
   constraints in the round, and the most it may be: past it, the engines
   running again on such a system costs less *)
let checked_time = ref 0.

let check_budget = 10.

let check_timeout = 5

let within_check_budget () = !checked_time < check_budget

let spent_checking t = checked_time := !checked_time +. t

let start_round () =
  requested_flag := false ;
  checked_time := 0.

let request () = requested_flag := true

let requested () = !requested_flag
