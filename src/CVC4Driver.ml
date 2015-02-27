(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

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

open Lib

include GenericSMTLIBDriver

(* Configuration for CVC4 *)
let cmd_line () = 

  (* Path and name of CVC4 executable *)
  let cvc4_bin = Flags.cvc4_bin () in

  if Flags.pdr_tighten_to_unsat_core () then 

    (* Use unsat core option *)
    [| cvc4_bin; 
       "--lang"; "smt2";
       "--rewrite-divk";
       "--tear-down-incremental" |]

  else

    (* Omit unsat core option for version older than 1.5 *)
    [| cvc4_bin; 
       "--lang"; "smt2";
       "--rewrite-divk";
       "--incremental" |]


let check_sat_limited_cmd _ = 
  failwith "check-sat with timeout not implemented for CVC4"


let check_sat_assuming_cmd () =
  failwith "No check-sat-assuming command for CVC4"


let check_sat_assuming_supported () = false


let s_lambda = HString.mk_hstring "LAMBDA"

let cvc4_expr_or_lambda_of_string_sexpr' ({ s_define_fun } as conv) bound_vars = 

  function 

    (* (define-fun c () Bool t) *)
    | HStringSExpr.List 
        [HStringSExpr.Atom s; (* define-fun *)
         HStringSExpr.Atom i; (* identifier *)
         HStringSExpr.List []; (* Parameters *)
         _; (* Result type *)
         t (* Expression *)
        ]
      when s == s_define_fun -> 

      Model.Term
        (gen_expr_of_string_sexpr' conv bound_vars t)


    (* (LAMBDA c () Bool t) *)
    | HStringSExpr.List 
        [HStringSExpr.Atom s; (* define-fun *)
         HStringSExpr.List []; (* Parameters *)
         _; (* Result type *)
         t (* Expression *)
        ]
      when s == s_lambda -> 

      Model.Term
        (gen_expr_of_string_sexpr' conv bound_vars t)


    (* (define-fun A ((x1 Int) (x2 Int)) Bool t) *)
    | HStringSExpr.List 
        [HStringSExpr.Atom s; (* define-fun *)
         HStringSExpr.Atom _; (* identifier *)
         HStringSExpr.List v; (* Parameters *)
         _; (* Result type *)
         t (* Expression *)
        ]
      when s == s_define_fun -> 

      (* Get list of variables bound by the quantifier *)
      let vars = gen_bound_vars_of_string_sexpr conv bound_vars [] v in

      (* Convert bindings to an association list from strings to
         variables *)
      let bound_vars' = 
        List.map 
          (function v -> (Var.hstring_of_free_var v, v))
          vars
      in

      Model.Lambda
        (Term.mk_lambda
           vars
           (gen_expr_of_string_sexpr' conv (bound_vars @ bound_vars') t))


    (* (LAMBDA ((_ufmt_1 Int) (_ufmt_2 Int)) (ite (= _ufmt_1 0) (= _ufmt_2 0) false)) *)
    | HStringSExpr.List 
        [HStringSExpr.Atom s; (* LAMBDA *)
         HStringSExpr.List v; (* Parameters *)
         t (* Expression *)
        ]
      when s == s_lambda -> 

      (* Get list of variables bound by the quantifier *)
      let vars = gen_bound_vars_of_string_sexpr conv bound_vars [] v in

      (* Convert bindings to an association list from strings to
         variables *)
      let bound_vars' = 
        List.map 
          (function v -> (Var.hstring_of_free_var v, v))
          vars
      in

      Model.Lambda
        (Term.mk_lambda
           vars
           (gen_expr_of_string_sexpr' conv (bound_vars @ bound_vars') t))

    (* Interpret as a term *)
    | _ -> invalid_arg "cvc4_expr_or_lambda_of_string_sexpr"

      

let lambda_of_string_sexpr = 
  gen_expr_or_lambda_of_string_sexpr smtlib_string_sexpr_conv


let string_of_logic l =
  let open TermLib in
  let open TermLib.FeatureSet in
  (* CVC4 fails to give model when given a non linear arithmetic logic *)
  if mem NA l then "ALL_SUPPORTED"
  else GenericSMTLIBDriver.string_of_logic l

let pp_print_logic fmt l = Format.pp_print_string fmt (string_of_logic l)
