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
(** Ordering the equations of a node with many locals by dependency
    (see #1809).

    For each state variable of an equation, the ordering looked for its
    array indexes with a traversal of the whole equation, although an
    equation with no select gives none, and merged it into the
    dependencies with a map rebuilt each time. On a node of 1,000
    stateless locals summed in the equation of its output, that allocated
    8.5 GB; it now allocates 0.44 GB.

    The ordering is measured by the bytes it allocates, which do not depend
    on the machine or on what else runs on it, unlike its time. They still
    grow faster than linearly, about 3.7 times for twice the locals, so the
    bound is on the bytes themselves rather than on their growth. *)

open OUnit2

(* A node with [n] stateless locals, b_i = x * i, summed in the equation of
   the output *)
let flat_sum n =
  let buf = Buffer.create (64 * n) in
  let add = Buffer.add_string buf in
  add "node main (x: int) returns (y: int);\nvar " ;
  for i = 1 to n do
    add (Printf.sprintf "%sb%d" (if i > 1 then ", " else "") i)
  done ;
  add ": int;\nlet\n" ;
  for i = 1 to n do add (Printf.sprintf "  b%d = x * %d;\n" i i) done ;
  add "  y = " ;
  for i = 1 to n do
    add (Printf.sprintf "%sb%d" (if i > 1 then " + " else "") i)
  done ;
  add (Printf.sprintf ";\n  check y <> %d;\ntel\n" (n * (n + 1) / 2)) ;
  Buffer.contents buf

(* The top node of the model, as the front end generates it *)
let node_of_model model =
  let file = Filename.temp_file "many_locals" ".lus" in
  Out_channel.with_open_text file (fun oc -> output_string oc model) ;
  Flags.Smt.set_solver `Z3_SMTLIB ;
  let result = LustreInput.of_file false file in
  Sys.remove file ;
  match result with
  | Ok (Some (sub :: _, _, _)) -> sub.SubSystem.source
  | _ -> assert_failure "the model is rejected"

(* The bytes [f] allocates *)
let allocated f =
  let before = Gc.allocated_bytes () in
  f () ;
  Gc.allocated_bytes () -. before

(* Ordering the equations of the initial and of the next states, as the
   translation to a transition system does, allocates less than 2 GB: about
   4.5 times what it takes, and 4.3 times less than the ordering before #1809
   took *)
let test_order_equations _ =
  let node = node_of_model (flat_sum 1000) in
  let bytes =
    allocated (fun () ->
        ignore (LustreSlicing.order_equations true [] node) ;
        ignore (LustreSlicing.order_equations false [] node))
  in
  assert_bool
    (Printf.sprintf "ordering 1,000 locals: %.2f GB" (bytes /. 1e9))
    (bytes < 2e9)

let suite =
  "many locals" >::: [ "order equations" >:: test_order_equations ]

let () = run_test_tt_main suite
