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

(** Testing graph extraction from lustre declarations
   
   @author Apoorv Ingle *)

module LI = LustreInput
module LA = LustreAst
open OUnit2

module GA = GraphAdapter

let linear_decls = LI.ast_of_file "test_forward_ref.lus"
let sorted_linear_decls = fun _ -> GA.sort_type_decls linear_decls
                          
let circular_decls = LI.ast_of_file "test_circular_decl_failure.lus"
let failure_circular_decls = fun _ ->  GA.sort_type_decls circular_decls


let print_test = "sample graph" >::: [
      "print acyclic graph" >:: (fun _ ->
        (assert_bool "do not drop declarations"
           (List.length linear_decls = List.length (sorted_linear_decls()))))
    ; "fail on cyclic graph" >:: (fun _ ->
      assert_raises Graph.CyclicGraphException
        (fun _ -> Lib.pp_print_list
                    (Lib.pp_print_pair LA.pp_print_ident LA.pp_print_program ":")
                    "\n" Format.std_formatter (failure_circular_decls ())) )
    ]
let _ = run_test_tt_main print_test
