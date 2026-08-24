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

open OUnit2

(* A solver gets the pipes it is given and no others.

   The pipes of a solver used to be inheritable, so every solver
   started after it was handed them too. A solver then holds the write
   end of the output pipe of a solver that has died, and Kind 2 waits
   on that pipe for an end that will not come until the last solver
   goes. Counting the pipes a solver holds is the way to see it. *)

open TestSolverCommon

(* The children of this process, in the order they were started, or
   [None] where the kernel does not keep the list. Each thread has a
   file of its own. *)
let children () =
  let of_task acc task =
    let path = Filename.concat "/proc/self/task" (task ^ "/children") in
    match open_in path with
    | exception _ -> acc
    | ic ->
      let line = try input_line ic with End_of_file -> "" in
      close_in ic ;
      let pids =
        String.split_on_char ' ' line |> List.filter (fun pid -> pid <> "")
      in
      Some (match acc with None -> pids | Some acc -> acc @ pids)
  in
  Array.fold_left of_task None (Sys.readdir "/proc/self/task")

(* How many of the descriptors [pid] holds are pipes, or [None] if it is
   already gone *)
let pipes_held pid =
  let dir = Filename.concat "/proc" (pid ^ "/fd") in
  match Sys.readdir dir with
  | exception Sys_error _ -> None
  | fds ->
    Array.to_list fds
    |> List.filter (fun fd ->
           match Unix.readlink (Filename.concat dir fd) with
           | target -> String.starts_with ~prefix:"pipe:" target
           | exception _ -> false)
    |> List.length
    |> Option.some

(* What a solver is given: its own standard input, output and error *)
let given = 3

let solvers = 3

let test_a_solver_holds_only_its_own_pipes _ =
  (* The descriptors of a process are read from /proc, which is Linux
     only, and its children from a file the kernel keeps only when it
     was built to *)
  skip_if (not (Sys.file_exists "/proc/self/task")) "no /proc" ;
  skip_if (children () = None) "the kernel does not list the children" ;
  skip_if (solver_missing ()) "no Z3 on PATH" ;

  for _ = 1 to solvers do ignore (new_solver ()) done ;
  let started = match children () with Some pids -> pids | None -> [] in

  (* Read what they hold before disposing of them, and dispose of them
     whatever the counts turn out to be: a solver handed the pipes of
     another never sees the end of its own standard input, so a failing
     run would leave them behind for good. *)
  let held = List.map (fun pid -> (pid, pipes_held pid)) started in
  SMTSolver.destroy_all_of_process () ;

  assert_equal
    ~msg:"number of solvers started" ~printer:string_of_int
    solvers (List.length held) ;

  held
  |> List.iter (fun (pid, held) ->
         match held with
         | None -> assert_failure (Printf.sprintf "solver %s is gone" pid)
         | Some held ->
           assert_equal
             ~msg:
               (Printf.sprintf
                  "solver %s holds pipes it was not given, the ones of the \
                   solvers before it" pid)
             ~printer:string_of_int given held)

let tests = "SolverPipes" >::: [
  "a solver holds only its own pipes" >:: test_a_solver_holds_only_its_own_pipes ;
]

let () = run_test_tt_main tests
