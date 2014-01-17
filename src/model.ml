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
