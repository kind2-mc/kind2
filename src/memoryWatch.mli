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

(** Stopping the engine whose solvers take the memory of the analysis.

    Under a memory limit on Kind 2 and its solvers, as a cgroup sets it,
    the first process to exceed the limit ends the analysis. When they
    use more than 80% of the limit, [check] stops the engine whose
    solvers use the most memory, by killing its solvers, so that the
    other engines go on: only if the solvers of the engines use more
    than the excess in all, and a second after the last engine stopped
    at the earliest. The limit is
    that of [--memory_limit], and the memory used that of Kind 2 and its
    solvers, or else the limit is that of the cgroup of Kind 2 (or of an
    ancestor of it), and the memory used that charged to that cgroup.
    Linux only: elsewhere, and where there is no limit, [check] does
    nothing. *)

(** Check the memory used, at most once every quarter of a second; for
    the polling loop of the supervisor. *)
val check : unit -> unit

(** Was the engine with the given identifier stopped by [check]? Such an
    engine ends as if it terminated normally, and the engines that depend
    on it are to be stopped as if it had crashed. *)
val stopped_for_memory : int -> bool
