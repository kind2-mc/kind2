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

type model_t = (Term.term * Term.term) list

let print fmt m =
  Util.fprintf_list ~sep:",@." 
    (fun fmt (var, value) -> 
      Format.fprintf fmt "@[%a: %a@]" Term.pp_print_term var Term.pp_print_term value) 
    fmt m


let is_var_of_id id v = 
  match Term.node_of_term v with 
    | Tree.N (s, [arg]) -> 
      (match Term.node_of_symbol s with 
        | `UF _ ->
          (
            match arg with
              | Tree.L s -> 
                (match Term.node_of_symbol s with 
                  | `NUMERAL i -> (int_of_numeral i) = id
                  | _ -> false)
              | _ -> false
          )
        | _ -> false
      )
    | _ -> false
    
let project m vars_pred = List.filter vars_pred m

let base_project m = project m (fun (v, _) -> is_var_of_id 0 v)
let prime_project m = project m (fun (v, _) -> is_var_of_id 1 v)

(* Unused yet 
let project_on_subset m vars =
  let projection = project m (fun var -> List.mem var vars) in
  if not (List.for_all (fun v -> List.mem v projection) vars) then
    failwith "Invalid model: all variables in vars in not in the resulting model";
  projection
*)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
