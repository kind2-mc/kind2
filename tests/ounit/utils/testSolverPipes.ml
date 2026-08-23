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

let new_solver () = SMTSolver.create_instance `None `Z3_SMTLIB

let solver_missing () =
  match Lib.find_on_path (Flags.Smt.z3_bin ()) with
  | _ -> false
  | exception Not_found -> true

(* The children of this process, as reported by the kernel. Each thread
   keeps its own list. *)
let children () =
  let of_task acc task =
    let path = Filename.concat "/proc/self/task" (task ^ "/children") in
    match open_in path with
    | exception _ -> acc
    | ic ->
      let line = try input_line ic with End_of_file -> "" in
      close_in ic ;
      String.split_on_char ' ' line
      |> List.filter (fun pid -> pid <> "")
      |> List.rev_append acc
  in
  Array.fold_left of_task [] (Sys.readdir "/proc/self/task")

(* How many of the descriptors [pid] holds are pipes *)
let pipes_held pid =
  let dir = Filename.concat "/proc" (pid ^ "/fd") in
  Sys.readdir dir
  |> Array.to_list
  |> List.filter (fun fd ->
         match Unix.readlink (Filename.concat dir fd) with
         | target -> String.starts_with ~prefix:"pipe:" target
         | exception _ -> false)
  |> List.length

let test_a_solver_holds_only_its_own_pipes _ =
  (* The fd table of a process is read from /proc, which is Linux only *)
  skip_if (not (Sys.file_exists "/proc/self/task")) "no /proc" ;
  skip_if (solver_missing ()) "no Z3 on PATH" ;

  ignore (new_solver ()) ;
  let first =
    match children () with
    | [ pid ] -> pid
    | pids ->
      assert_failure
        (Printf.sprintf "expected one solver, found %d" (List.length pids))
  in
  let held_by_first = pipes_held first in

  (* Two more, so that the last one could have inherited from three *)
  ignore (new_solver ()) ;
  ignore (new_solver ()) ;
  let last =
    match List.filter (fun pid -> pid <> first) (children ()) with
    | pid :: _ -> pid
    | [] -> assert_failure "the solvers started later are gone"
  in
  let held_by_last = pipes_held last in

  (* What a solver holds does not grow with the ones before it. It was
     three more pipes per earlier solver. *)
  assert_bool
    (Printf.sprintf
       "a solver holds %d pipes where the first holds %d: it was handed \
        the pipes of the solvers before it"
       held_by_last held_by_first)
    (held_by_last <= held_by_first)

let tests = "SolverPipes" >::: [
  "a solver holds only its own pipes" >:: test_a_solver_holds_only_its_own_pipes ;
]

let () = run_test_tt_main tests
