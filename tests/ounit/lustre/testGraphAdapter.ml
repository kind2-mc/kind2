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

let dp = Lib.dummy_pos
let (>>=) = Res.(>>=)
          
let linear_decls = [
    LA.TypeDecl (dp, LA.AliasType(dp, "t0", LA.UserType (dp, "t1")))
  ; LA.TypeDecl (dp, LA.AliasType(dp, "t1", LA.UserType (dp, "t2")))
  ; LA.TypeDecl (dp, LA.AliasType(dp, "t2", LA.Int dp))
  ; LA.ConstDecl (dp, LA.TypedConst (dp, "c", LA.Const (dp, Num "1"), LA.UserType (dp, "t0")))
  ]
  
let sorted_linear_decls = fun _ -> GA.sort_decls linear_decls


let tests_should_pass = [
    "acyclic graph" >:: (fun _ ->
      (assert_bool "do not drop declarations"
         (Res.safe_unwrap false
            (sorted_linear_decls() >>= (fun sdls -> Res.ok (List.length linear_decls = List.length sdls))))))
  ]



let circular_decls = [
    LA.TypeDecl (dp, LA.AliasType(dp, "t0", LA.UserType (dp, "t1")))
  ; LA.TypeDecl (dp, LA.AliasType(dp, "t1", LA.UserType (dp, "t2")))
  ; LA.TypeDecl (dp, LA.AliasType(dp, "t2", LA.UserType (dp, "t0")))
  ; LA.ConstDecl (dp, LA.TypedConst (dp, "c", LA.Const (dp, Num "1"), LA.UserType (dp, "t0")))  ]


let failure_circular_decls = fun _ ->  GA.sort_decls circular_decls

let tests_should_fail =  [
    "cyclic graph" >:: (fun _ ->
      assert_bool "gives Error"
        (Res.safe_unwrap false
           (match (failure_circular_decls ()) with 
            | Ok _ -> Res.ok false
            | Error _ -> Res.ok true)))
  ]
                      
let _ = run_test_tt_main ("graph adapter tests" >::: tests_should_pass @ tests_should_fail)
