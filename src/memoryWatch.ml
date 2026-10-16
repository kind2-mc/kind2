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

(* Stopping the engine whose solvers take the memory of the analysis

   Kind 2 runs its engines in one process and their solvers in processes
   of their own. Under a memory limit on all of them, as a cgroup sets
   it, the first process that exceeds the limit ends the analysis, and
   with it the answers the other engines could still give. An engine
   such as BMC adds to its solver at every step and never gives the
   memory back, so on a property it can neither prove nor falsify it
   exceeds any limit sooner or later.

   The supervisor calls [check] from its polling loop. When Kind 2 and
   its solvers use more than [threshold] of the limit, the engine whose
   solvers use the most is stopped by killing its solvers, as the
   supervisor unblocks an engine stuck in a solver call, and the others
   go on: the engines that depend on it as well, through the supervisor,
   which takes it for an engine that crashed (see [stopped_for_memory]).

   The limit is that of [--memory_limit], against the memory of Kind 2
   and its solvers, or else that of the cgroup v2 of the process, against
   the memory charged to that cgroup. The memory of each solver is that
   of its process: a solver run through a wrapper script is counted only
   if the script [exec]s it. Only Linux is covered: the memory is read
   from /proc and /sys/fs/cgroup. *)

open Lib

(* The fraction of the limit at which an engine is stopped, which leaves
   room for the memory the others take until the solvers of the engine
   are gone *)
let threshold = 0.8

(* The shortest interval between two checks, in seconds *)
let interval = 0.25

(* The time left to the solvers of a stopped engine to be gone and their
   memory to be freed, before another engine is considered, in seconds *)
let settle = 1.

let read_file path =
  try Some (In_channel.with_open_text path In_channel.input_all)
  with Sys_error _ -> None

(* Is the memory of processes to be read from /proc? *)
let linux = lazy (Sys.os_type = "Unix" && Sys.file_exists "/proc/self/status")

(* The smallest memory limit of the cgroup of the process and of its
   ancestors, in bytes, with the directory of the cgroup it is set on, if
   there is one: a tool can be run in a cgroup below the one its limit is
   set on *)
let cgroup_limit =
  lazy (
    match read_file "/proc/self/cgroup" with
    | None -> None
    | Some s ->
      (* The line of cgroup v2 is "0::<path>" *)
      String.split_on_char '\n' s
      |> List.find_opt (String.starts_with ~prefix:"0::")
      |> Option.map (fun l -> String.sub l 3 (String.length l - 3))
      |> Option.map (fun path ->
        let rec ancestors p acc =
          if p = "/" || p = "" then "" :: acc
          else ancestors (Filename.dirname p) (p :: acc)
        in
        ancestors path []
        |> List.filter_map (fun p ->
          let dir = "/sys/fs/cgroup" ^ p in
          read_file (dir ^ "/memory.max")
          |> Option.map String.trim
          |> Fun.flip Option.bind int_of_string_opt
          |> Option.map (fun limit -> limit, dir)))
      |> function
      | Some (_ :: _ as limits) ->
        Some (List.fold_left min (List.hd limits) limits)
      | Some [] | None -> None
  )

(* The memory charged to the cgroup in [dir] that cannot be reclaimed, in
   bytes, if it can be read: what the limit of the cgroup applies to,
   processes outside Kind 2 and kernel memory included, less the pages of
   files no process uses actively, which the kernel reclaims first *)
let cgroup_usage dir =
  match read_file (dir ^ "/memory.current") with
  | None -> None
  | Some current ->
    int_of_string_opt (String.trim current)
    |> Option.map (fun current ->
      let inactive_file =
        match read_file (dir ^ "/memory.stat") with
        | None -> 0
        | Some stat ->
          String.split_on_char '\n' stat
          |> List.find_map (fun l ->
            Scanf.sscanf_opt l "inactive_file %d" Fun.id)
          |> Option.value ~default:0
      in
      current - inactive_file)

(* The resident memory of a process, in bytes, given as a /proc entry:
   a PID, or "self". From [status] rather than [statm]: [statm] counts
   pages, whose size OCaml does not give, and it is not 4 kB everywhere *)
let rss proc =
  match read_file ("/proc/" ^ proc ^ "/status") with
  | None -> 0
  | Some s ->
    String.split_on_char '\n' s
    |> List.find_map (fun l ->
      if String.starts_with ~prefix:"VmRSS:" l then
        Scanf.sscanf_opt l "VmRSS: %d kB" (fun kb -> kb * 1024)
      else None)
    |> Option.value ~default:0

(* The engines stopped, by their identifiers *)
let stopped = Hashtbl.create 7

let stopped_for_memory id = Hashtbl.mem stopped id

let last_check = ref 0.

(* When an engine was last stopped *)
let last_stop = ref neg_infinity

let check () =
  let limit =
    if not (Lazy.force linux) then None
    else
      match Flags.memory_limit () with
      | 0 ->
        Lazy.force cgroup_limit
        |> Option.map (fun (limit, dir) -> limit, Some dir)
      | mb -> Some (mb * 1048576, None)
  in
  match limit with
  | None -> ()
  | Some (limit, cgroup) ->
    let now = Unix.gettimeofday () in
    if now -. !last_check >= interval && now -. !last_stop >= settle then (
      last_check := now ;
      (* The memory of the solvers of each domain *)
      let by_domain = Hashtbl.create 7 in
      SMTSolver.solver_pids_by_domain ()
      |> List.iter (fun (owner, pid) ->
        let m = rss (string_of_int pid) in
        Hashtbl.replace by_domain owner
          (m + Option.value ~default:0 (Hashtbl.find_opt by_domain owner))) ;
      (* What the limit applies to: the memory charged to the cgroup that
         sets it, or else that of Kind 2 and its solvers *)
      let used =
        match Option.bind cgroup cgroup_usage with
        | Some used -> used
        | None -> Hashtbl.fold (fun _ m t -> t + m) by_domain (rss "self")
      in
      let excess = float_of_int used -. threshold *. float_of_int limit in
      if excess > 0. then
        let engines =
          EngineDomains.live ()
          |> List.filter_map (fun c ->
            Hashtbl.find_opt by_domain (EngineDomains.domain_id c)
            |> Option.map (fun m -> m, c))
          |> List.sort (fun (m, _) (m', _) -> compare m' m)
        in
        (* The engine whose solvers use the most memory, if stopping
           engines can free enough: when Kind 2 itself takes the memory,
           it does not help, and would stop them all in turn. When no
           engine frees enough alone, the next one is stopped at the next
           check after the pause *)
        let solvers = List.fold_left (fun t (m, _) -> t + m) 0 engines in
        match engines with
        | (m, c) :: _ when float_of_int solvers >= excess ->
          KEvent.log L_warn
            "@[<hov>Stopping %a:@ its solvers use %d MB,@ and the analysis \
             %d MB of the %d MB it may use.@]"
            pp_print_kind_module (EngineDomains.mdl c)
            (m / 1048576) (used / 1048576) (limit / 1048576) ;
          Hashtbl.replace stopped (EngineDomains.id c) () ;
          last_stop := now ;
          EngineDomains.kill_solvers c
        | _ -> ()
    )
