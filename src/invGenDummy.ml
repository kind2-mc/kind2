(*
This file is part of the Kind verifier

* Copyright (c) 2007-2013 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

open Lib


(* Seconds before sending the next invariant *)
let period = 0.5


(* We don't need to clean up anything *)
let on_exit () = ()


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

  Event.log `INVGEN Event.L_debug "Sending invariant %d" k;

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
  
