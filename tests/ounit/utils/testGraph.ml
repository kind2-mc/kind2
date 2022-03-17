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

open OUnit2

module G = Graph.Make(struct
               type t = LustreAst.ident
               let compare = HString.compare
               let pp_print_t = LustreAst.pp_print_ident 
             end)

let v0 = HString.mk_hstring "v0"
let v1 = HString.mk_hstring "v1"
let v2 = HString.mk_hstring "v2"
                         
let singleton_g = G.add_vertex G.empty v0
let dos_g = G.add_vertex singleton_g v1

let dos_connected_g = G.add_edge dos_g (G.mk_edge v0 v1)
let dos_cycle_g = G.add_edge dos_connected_g (G.mk_edge v1 v0)

let cycle_and_one_more = G.add_edge (G.add_vertex (dos_cycle_g) v2) (G.mk_edge v1 v2) 
                
let basic_tests =
  [ "empty graph" >:: (fun _-> assert_bool "Empty graph is empty" (G.is_empty G.empty))
  ; "remove vertex to remove all edges" >::
      (fun _ -> assert_bool "unexpected graph" (G.remove_vertex dos_g v0 |> G.is_point_graph))
  
  ; "sorted dos" >:: (fun _ -> assert_equal [v0;v1] (G.topological_sort dos_connected_g))
  ; "cyclic dos" >:: (fun _ -> assert_bool "Cyclic graph is cyclic" (
    try let _ = G.topological_sort dos_cycle_g in false
    with Graph.CyclicGraphException _ -> true))
  ]

let rechability_tests =
  [
    "reachable singleton" >:: (fun _ ->
      let memo = ref G.VMap.empty in
      assert_equal [v0] (G.to_vertex_list (G.memoized_reachable memo singleton_g v0))
        ~printer:(Lib.string_of_t (Format.pp_print_list HString.pp_print_hstring) ))
  ; "reachable cycle graph" >:: (fun _ ->
    let memo = ref G.VMap.empty in
    assert_equal [v0;v1] (G.to_vertex_list (G.memoized_reachable memo dos_cycle_g v0))
      ~printer:(Lib.string_of_t (Format.pp_print_list HString.pp_print_hstring) ))
  ; "reachable cycle graph2" >:: (fun _ ->
    let memo = ref G.VMap.empty in
    assert_equal [v0;v1;v2] (G.to_vertex_list (G.memoized_reachable memo cycle_and_one_more v0))
      ~printer:(Lib.string_of_t (Format.pp_print_list HString.pp_print_hstring)))
  ]
  
let _ = run_test_tt_main ("test suite for graphs" >::: basic_tests @ rechability_tests) 
