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
   go on. Only Linux is covered: the limit is that of [--memory_limit],
   or else of the cgroup v2 of the process, and the memory used is read
   from /proc. *)

open Lib

(* The fraction of the limit at which an engine is stopped, which leaves
   room for the memory the others take until the solvers of the engine
   are gone *)
let threshold = 0.8

(* The shortest interval between two checks, in seconds *)
let interval = 0.25

let read_file path =
  try Some (In_channel.with_open_text path In_channel.input_all)
  with Sys_error _ -> None

(* The smallest memory limit of the cgroup of the process and of its
   ancestors, in bytes, if there is one: a tool can be run in a cgroup
   below the one its limit is set on *)
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
          read_file ("/sys/fs/cgroup" ^ p ^ "/memory.max")
          |> Option.map String.trim
          |> Fun.flip Option.bind int_of_string_opt))
      |> function
      | Some (_ :: _ as limits) -> Some (List.fold_left min max_int limits)
      | Some [] | None -> None
  )

(* The resident memory of a process, in bytes, given as a /proc entry:
   a PID, or "self" *)
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

let last_check = ref 0.

let check () =
  let limit =
    match Flags.memory_limit () with
    | 0 -> Lazy.force cgroup_limit
    | mb -> Some (mb * 1048576)
  in
  match limit with
  | None -> ()
  | Some limit ->
    let now = Unix.gettimeofday () in
    if now -. !last_check >= interval then (
      last_check := now ;
      (* The memory of the solvers of each domain *)
      let by_domain =
        SMTSolver.solver_pids_by_domain ()
        |> List.fold_left (fun acc (owner, pid) ->
          let m = rss (string_of_int pid) in
          let m' = Option.value ~default:0 (List.assoc_opt owner acc) in
          (owner, m + m') :: List.remove_assoc owner acc)
          []
      in
      let total =
        List.fold_left (fun t (_, m) -> t + m) (rss "self") by_domain
      in
      if float_of_int total > threshold *. float_of_int limit then
        (* The engine whose solvers use the most memory *)
        EngineDomains.live ()
        |> List.filter_map (fun c ->
          List.assoc_opt (EngineDomains.domain_id c) by_domain
          |> Option.map (fun m -> m, c))
        |> List.sort (fun (m, _) (m', _) -> compare m' m)
        |> function
        | (m, c) :: _ ->
          KEvent.log L_warn
            "@[<hov>Stopping %a:@ its solvers use %d MB,@ and the analysis \
             %d MB of the %d MB it may use.@]"
            pp_print_kind_module (EngineDomains.mdl c)
            (m / 1048576) (total / 1048576) (limit / 1048576) ;
          EngineDomains.kill_solvers c
        | [] -> ()
    )
