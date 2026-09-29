(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

type t = {
  logic : TermLib.logic ;
  timeout_ms : int ;
  define : SMTSolver.t -> unit ;
  mutable solver : SMTSolver.t option ;
}

let create ~logic ~timeout_ms define =
  { logic ; timeout_ms ; define ; solver = None }

let delete t =
  ( match t.solver with
    | Some solver -> (try SMTSolver.delete_instance solver with _ -> ())
    | None -> () ) ;
  t.solver <- None

(* The per-query timeout options of Z3 and cvc5, in milliseconds; the other
   solvers take a timeout for the whole of their life only *)
let kind_takes_per_query ms = function
  | `Z3_SMTLIB -> Some (":timeout", string_of_int ms)
  | `cvc5_SMTLIB -> Some (":tlimit-per", string_of_int ms)
  | _ -> None

let set_per_query_timeout ~ms solver =
  match kind_takes_per_query ms (SMTSolver.kind solver) with
  | Some (option, value) ->
    SMTSolver.execute_custom_command solver "set-option"
      [ SMTExpr.ArgString option ; SMTExpr.ArgString value ] 0
    |> ignore ;
    true
  | None -> false

let solver_of t =
  match t.solver with
  | Some solver -> solver
  | None ->
    let solver =
      SMTSolver.create_instance ~produce_models:true t.logic
        (Flags.Smt.solver ())
    in
    set_per_query_timeout ~ms:t.timeout_ms solver |> ignore ;
    t.define solver ;
    t.solver <- Some solver ;
    solver

let evaluate t uf args =
  try
    let solver = solver_of t in
    SMTSolver.push solver ;
    let result = UfSymbol.mk_fresh_uf_symbol [] (UfSymbol.res_type_of_uf_symbol uf) in
    SMTSolver.declare_fun solver result ;
    let result = Term.mk_uf result [] in
    SMTSolver.assert_term solver (Term.mk_eq [ result ; Term.mk_uf uf args ]) ;
    let value =
      (* An evaluation the solver gives up on in time is not a reason to
         give up on the solver *)
      try
        SMTSolver.check_sat_and_get_term_values solver
          (fun _ values ->
             match List.assq_opt result values with
             | Some v -> `Value v
             | None -> `Unknown)
          (fun _ -> `Unknown)
          [ result ]
      with SMTSolver.Unknown -> `Unknown
    in
    (* The value must be the only one: a definition may apply symbols that
       are not defined, the value of a call whose termination checks fail,
       or a constant the system shares, such as that of a 'choose', which
       the solver would pick here on its own *)
    let value =
      match value with
      | `Value v ->
        SMTSolver.assert_term solver (Term.mk_not (Term.mk_eq [ result ; v ])) ;
        ( match SMTSolver.check_sat solver with
          | false -> `Value v
          | true -> `Not_unique
          | exception SMTSolver.Unknown -> `Unknown )
      | other -> other
    in
    SMTSolver.pop solver ;
    value
  with
  (* The solver was killed on its timeout, the instance is gone *)
  | SMTSolver.Timeout -> t.solver <- None ; `Unknown
  | SMTSolver.Unknown -> delete t ; `Unknown
  | Failure _ | Unix.Unix_error _ | End_of_file | Sys_error _
  | SMTSolver.Exiting -> delete t ; `Unknown
