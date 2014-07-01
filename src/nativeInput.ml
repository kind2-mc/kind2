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

(* Distingushed strings in input *)
let s_define_pred = HString.mk_hstring "define-pred"
let s_init = HString.mk_hstring "init"
let s_trans = HString.mk_hstring "trans"
let s_opt_const = HString.mk_hstring ":const"
let s_prime = HString.mk_hstring "prime"
let s_check_prop = HString.mk_hstring "check-prop"


let term_of_sexpr s = Term.t_true



(* Parse from input channel *)
let of_channel in_ch = 
  
  (* Create a lexing buffer on solver's stdout *)
  let lexbuf = Lexing.from_channel in_ch in
  
  (* Parse S-expression and return *)
  let sexps = SExprParser.rev_sexps SExprLexer.main lexbuf in

  (* Properties to prove and predicate definitions *)
  let props, defs = match sexps with 
    
    (* Must have a list at last position *)
    | HStringSExpr.List l :: tl ->

      (match l with
        
        (* List must start with check-prop atom *)
        | HStringSExpr.Atom s :: ltl when s == s_check_prop -> 
          
          (match ltl with
            
            (* List must continue with atom for main node and list of
               properties *)
            | [HStringSExpr.Atom main_node; HStringSExpr.List p] -> 
              
              let props = 
                List.fold_left 
                  (function accum -> function

                     (* Property must be a pair of name and term *)
                     | HStringSExpr.List [HStringSExpr.Atom p; t] -> 
                       
                       (* Convert S-expression to term *)
                       (p, term_of_sexpr t) :: accum

                     | _ -> failwith "Invalid format of property")
                  []
                  p
              in

              props, tl
              
            | _ -> failwith "Invalid format of check-prop statement")
          
        | _ -> failwith "Definitions must end with check-prop statement")

    | _ -> failwith "Invalid file format"
       
  in

  TransSys.mk_trans_sys [] [] [] Term.t_true Term.t_true []


(* Open and parse from file *)
let of_file filename = 

    (* Open the given file for reading *)
    let use_file = open_in filename in
    let in_ch = use_file in

    of_channel in_ch



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
