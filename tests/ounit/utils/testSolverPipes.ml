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

(* The pipes [pid] holds, as the kernel names them, or [None] if it is
   already gone. Named rather than counted: a count that comes out wrong
   says nothing about which pipes, and the same pipe under two
   descriptors is the whole point. *)
let pipes_held pid =
  let dir = Filename.concat "/proc" (pid ^ "/fd") in
  match Sys.readdir dir with
  | exception Sys_error _ -> None
  | fds ->
    Array.to_list fds
    |> List.filter_map (fun fd ->
           match Unix.readlink (Filename.concat dir fd) with
           | exception _ -> None
           | target ->
             if String.starts_with ~prefix:"pipe:" target then Some (fd, target)
             else None)
    |> Option.some

(* What a solver is given: its own standard input, output and error *)
let given = 3

let solvers = 3

(* The pipes a solver holds that were not already ours.

   Whatever runs the test may hand it pipes of its own — dune does, on
   some runners — and a solver inherits those exactly as it inherits
   anything else of ours. They say nothing about what Kind 2 hands its
   solvers, so discount them.

   Discounting by the name the kernel gives a pipe is sound only while
   every pipe in [ours] stays open. A closed one could have its name
   taken by a pipe made for a solver later, and that solver would then
   be let off. They all do stay open for the whole test: the one made
   below is held to the end, and the ones from the runner are the
   runner's to close. Being made after the reading is not on its own
   what makes a solver's pipes safe to count.

   What this cannot see is a solver inheriting a pipe Kind 2 held
   before it began making them. There is none here, and a descriptor
   Kind 2 never created is not what closing its own on exec is about. *)
let own_pipes ours held =
  List.filter (fun (_, pipe) -> not (List.mem pipe ours)) held

let describe held =
  held
  |> List.map (fun (fd, pipe) -> Printf.sprintf "%s -> %s" fd pipe)
  |> String.concat ", "

let test_a_solver_holds_only_its_own_pipes _ =
  (* The descriptors of a process are read from /proc, which is Linux
     only, and its children from a file the kernel keeps only when it
     was built to *)
  skip_if (not (Sys.file_exists "/proc/self/task")) "no /proc" ;
  skip_if (children () = None) "the kernel does not list the children" ;
  skip_if (solver_missing ()) "no Z3 on PATH" ;

  (* Start them inside the cleanup rather than before it. A solver
     handed the pipes of another holds the write end of its own standard
     input and so never sees the end of it, which is what a failing run
     of this test used to leave behind. The second one failing to start
     would strand the first the same way. *)
  Fun.protect ~finally:SMTSolver.destroy_all_of_process (fun () ->
    (* Stand in for the pipes the runner may hand us, so that a run here
       covers what a run under CI does. Inheritable on purpose: the
       whole point is that the solvers are handed it. *)
    let stray_r, stray_w = Unix.pipe ~cloexec:false () in
    Fun.protect
      ~finally:(fun () -> Unix.close stray_r ; Unix.close stray_w)
      (fun () ->
        let ours =
          match pipes_held "self" with
          | Some held -> List.map snd held
          | None -> []
        in

        for _ = 1 to solvers do ignore (new_solver ()) done ;
        let started =
          match children () with Some pids -> pids | None -> []
        in

        assert_equal
          ~msg:"number of solvers started" ~printer:string_of_int
          solvers (List.length started) ;

        started
        |> List.iter (fun pid ->
               match pipes_held pid with
               | None -> assert_failure (Printf.sprintf "solver %s is gone" pid)
               | Some held ->
                 let own = own_pipes ours held in
                 let discounted = List.length held - List.length own in
                 (* Both ends of the pipe made above, at least. If a
                    solver was handed none of it, nothing here exercises
                    the discounting, and the test would keep passing
                    without it -- which is how the runner's own pipes
                    reached CI unnoticed. *)
                 assert_bool
                   "the pipe made for the solvers to inherit did not reach \
                    them, so nothing exercises the discounting"
                   (discounted >= 2) ;
                 assert_equal
                   ~msg:
                     (Printf.sprintf
                        "solver %s holds %s, of which %d were already ours"
                        pid (describe held) discounted)
                   ~printer:string_of_int given (List.length own))))

let tests = "SolverPipes" >::: [
  "a solver holds only its own pipes" >:: test_a_solver_holds_only_its_own_pipes ;
]

let () = run_test_tt_main tests
