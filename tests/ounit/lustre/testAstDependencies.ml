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

module LA = LustreAst
open OUnit2

module AD = LustreAstDependencies

let dp = Position.dummy_pos
let dspan = { LA.start_pos = dp; LA.end_pos = dp }
let (>>=) = Res.(>>=)
          
let linear_decls = [
    LA.TypeDecl (dspan, LA.AliasType(dp, HString.mk_hstring "t0", LA.UserType (dp, HString.mk_hstring "t1")))
  ; LA.TypeDecl (dspan, LA.AliasType(dp, HString.mk_hstring "t1", LA.UserType (dp, HString.mk_hstring "t2")))
  ; LA.TypeDecl (dspan, LA.AliasType(dp, HString.mk_hstring "t2", LA.Int dp))
  ; LA.ConstDecl (dspan, LA.TypedConst (dp, HString.mk_hstring "c",
    LA.Const (dp, Num (HString.mk_hstring "1")), LA.UserType (dp, HString.mk_hstring "t0")))
  ]
  
let sorted_linear_decls = fun _ -> AD.sort_globals linear_decls


let tests_should_pass = [
    "acyclic graph" >:: (fun _ ->
      (assert_bool "do not drop declarations"
         (Res.safe_unwrap false
            (sorted_linear_decls() >>= (fun sdls -> Res.ok (List.length linear_decls = List.length sdls))))))
  ]



let circular_decls = [
    LA.TypeDecl (dspan, LA.AliasType(dp, HString.mk_hstring "t0", LA.UserType (dp, HString.mk_hstring "t1")))
  ; LA.TypeDecl (dspan, LA.AliasType(dp, HString.mk_hstring "t1", LA.UserType (dp, HString.mk_hstring "t2")))
  ; LA.TypeDecl (dspan, LA.AliasType(dp, HString.mk_hstring "t2", LA.UserType (dp, HString.mk_hstring "t0")))
  ; LA.ConstDecl (dspan, LA.TypedConst (dp, HString.mk_hstring "c",
    LA.Const (dp, Num (HString.mk_hstring "1")), LA.UserType (dp, HString.mk_hstring "t0")))  ]


let failure_circular_decls = fun _ ->  AD.sort_globals circular_decls

let tests_should_fail =  [
    "cyclic graph" >:: (fun _ ->
      assert_bool "gives Error"
        (Res.safe_unwrap false
           (match (failure_circular_decls ()) with 
            | Ok _ -> Res.ok false
            | Error _ -> Res.ok true)))
  ]
                      
let _ = run_test_tt_main ("graph adapter tests" >::: tests_should_pass @ tests_should_fail)
