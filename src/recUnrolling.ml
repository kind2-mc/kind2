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

module SSet = Set.Make (String)

(* The functions whose cutoff a counterexample reached, and that are below
   the limit *)
let requested_functions = ref Scope.Set.empty

(* The properties whose counterexample reached the cutoff of a function at
   the limit *)
let exhausted = ref SSet.empty

(* The functions at the limit whose cutoff a counterexample reached, and
   that were reported *)
let reported = ref Scope.Set.empty

let depth param f =
  match Analysis.param_unrollings_of_scope param f with
  | Some n -> n
  | None -> 1

let reset () =
  requested_functions := Scope.Set.empty ;
  exhausted := SSet.empty ;
  reported := Scope.Set.empty

let clear_requested () = requested_functions := Scope.Set.empty

let request param prop reached =
  let limit = Flags.Contracts.rec_unrollings () in
  match List.filter (fun f -> depth param f < limit) reached with
  | [] ->
    exhausted := SSet.add prop !exhausted ;
    let unreported =
      List.filter (fun f -> not (Scope.Set.mem f !reported)) reached
    in
    reported :=
      List.fold_left (fun s f -> Scope.Set.add f s) !reported unreported ;
    `At_limit unreported
  | below ->
    requested_functions :=
      List.fold_left (fun s f -> Scope.Set.add f s) !requested_functions below ;
    `Requested

let requested () = Scope.Set.elements !requested_functions

(* Whether the property can hold at the last step of the counterexample
   with the inputs of the counterexample: the system is unrolled along the
   counterexample, its inputs and constants are fixed to the values of the
   counterexample, and the property is asserted at the last step. If that is
   satisfiable, the violation depends on values the inputs do not determine,
   the outputs of the cutoffs among them. The query is that of bounded model
   checking at the length of the counterexample, with the inputs fixed. *)
(* The time given to the solver for the query, in seconds. A query the
   solver cannot decide in time is taken to depend on free values: the
   counterexample is not reported, and the function is unrolled further. *)
let query_timeout = 2

let violation_depends_on_free_values sys prop cex =
  let path = Model.path_of_list cex in
  let k = Numeral.of_int (Model.path_length path - 1) in
  let solver =
    SMTSolver.create_instance ~timeout:query_timeout ~produce_models:false
      (TransSys.get_logic sys) (Flags.Smt.solver ())
  in
  let result =
    try
      TransSys.define_and_declare_of_bounds sys
        (SMTSolver.define_fun solver)
        ~define_rec:(SMTSolver.define_funs_rec solver)
        (SMTSolver.declare_fun solver)
        (SMTSolver.declare_sort solver)
        Numeral.zero k ;
      TransSys.assert_global_constraints sys (SMTSolver.assert_term solver) ;
      TransSys.init_of_bound (Some (SMTSolver.declare_fun solver)) sys Numeral.zero
      |> SMTSolver.assert_term solver ;
      let rec assert_trans i =
        if Numeral.(i <= k) then (
          TransSys.trans_of_bound (Some (SMTSolver.declare_fun solver)) sys i
          |> SMTSolver.assert_term solver ;
          assert_trans Numeral.(succ i))
      in
      assert_trans Numeral.one ;
      (* The inputs and the constants at every step of the counterexample *)
      cex |> List.iter (fun (sv, values) ->
        if StateVar.is_input sv || StateVar.is_const sv then
          values |> List.iteri (fun i value ->
            match value with
            | Model.Term t ->
              Term.mk_eq
                [ Term.mk_var (Var.mk_state_var_instance sv (Numeral.of_int i)) ;
                  t ]
              |> SMTSolver.assert_term solver
            | Model.Lambda _ | Model.Map _ -> ())) ;
      TransSys.get_prop_term sys prop
      |> Term.bump_state k
      |> SMTSolver.assert_term solver ;
      `Result (SMTSolver.check_sat solver)
    with
    | SMTSolver.Timeout ->
      (* The solver was killed on the timeout, the instance is gone *)
      `Timeout
    | SMTSolver.Unknown -> `Result true
    | e ->
      (* A solver that stops on its own timeout answers in its own way,
         which reads as a failure: the query is undecided, as well *)
      KEvent.log L_debug
        "Query on the counterexample to %s failed: %s" prop
        (Printexc.to_string e) ;
      `Failed
  in
  match result with
  | `Result r -> SMTSolver.delete_instance solver ; r
  | `Timeout -> true
  | `Failed -> (try SMTSolver.delete_instance solver with _ -> ()) ; true

(* The recursive functions the counterexample to the property may be
   spurious for: a cutoff of theirs is reached, and the violation depends on
   values the inputs do not determine *)
let suspect sys prop cex =
  match TransSys.cutoffs_reached sys cex with
  | [] -> []
  | reached ->
    if violation_depends_on_free_values sys prop cex then reached else []

let is_exhausted prop = SSet.mem prop !exhausted

let all_settled sys =
  TransSys.get_properties sys
  |> List.for_all (fun ({ Property.prop_name ; Property.prop_status } as p) ->
    Property.is_candidate p
    || (match prop_status with
        | Property.PropInvariant _ | Property.PropFalse _ -> true
        | _ -> SSet.mem prop_name !exhausted))
