(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020 by the Board of Trustees of the University of Iowa

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
(** Testing the graph implementation
   
   @author Apoorv Ingle *)

module G = Graph
         
open OUnit2
   
let empty_graph_is_empty = assert (G.is_empty G.empty)  

let v0 = G.mk_vertex "0"
let v1 = G.mk_vertex "1"
                         
let singleton_g = G.add_vertex G.empty v0
let dos_g = G.add_vertex singleton_g v1

let dos_connected_g = G.add_edge dos_g (G.mk_edge v0 v1)
let dos_cycle_g = G.add_edge dos_connected_g (G.mk_edge v1 v0)


let basic_tests = "test suite for graph" >::: [
      "sorted dos" >:: (fun _ -> assert_equal (G.topological_sort dos_connected_g) [v0;v1])
    ; "cyclic dos" >:: (fun _ -> assert_raises (G.CyclicGraphException) (fun _ -> G.topological_sort dos_cycle_g))
    ]
let _ = run_test_tt_main basic_tests
