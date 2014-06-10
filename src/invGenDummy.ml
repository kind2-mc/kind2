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


(* Seconds before sending the next invariant *)
let period = 0.5


(* We don't need to clean up anything *)
let on_exit _ = ()


(* Generate the k-th tautological invariant: a conjunction of k+1
   [true] constants. *)
let mk_inv k = 

  (* Tail-recursive function with accumulator *)
  let rec mk_inv' accum = function 

    (* Base case  *)
    | k when k <= 0 -> 

      (match accum with 
        | [] -> Term.t_true
        | l -> Term.mk_and (Term.t_true :: accum))

    (* Add [true] to accumulator and recurse for k-1 *)
    | k -> mk_inv' (Term.t_true :: accum) (pred k)

  in

  (* Call recursice function with empty accumulator *)
  mk_inv' [] k


(* Send the k-th tautological invariant *)
let rec inv_gen_dummy k = 

  (* Wait before sending an invariant *)
  minisleep period;

  (* Generate the k-th tautological invariant *)
  let inv = mk_inv k in 

  Event.log 
    `INVGEN 
    Event.L_debug 
    "Sending invariant %d: %a" 
    k 
    Term.pp_print_term inv;

  (* Broadcast the invariant *)
  Event.invariant `INVGEN inv;

  (* Recurse for the next invariant *)
  inv_gen_dummy (succ k)


(* Entry point *)
let main _ = 

  (* Run loop *)
  inv_gen_dummy 0


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
