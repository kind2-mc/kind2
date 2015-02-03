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
open SolverResponse


exception Unknown


let gentag =
  let r = ref 0 in
  fun () -> incr r; !r


type expr = SMTExpr.t

(* type solver = YicesNative.S.t *)

module Z3SMTLIB : SolverSig.S = SMTLIBSolver.Make (Z3Driver)
module CVC4SMTLIB : SolverSig.S = SMTLIBSolver.Make (CVC4Driver)
module MathSat5SMTLIB : SolverSig.S = SMTLIBSolver.Make (MathSAT5Driver)
module Yices2SMTLIB : SolverSig.S = SMTLIBSolver.Make (Yices2SMT2Driver)

type t =
  { solver_kind : Flags.smtsolver;
    solver_inst : (module SolverSig.Inst);
    (* Hashtable associating generated names to terms *)
    term_names : (int, expr) Hashtbl.t;
    id : int
  }


(* Raise an exception on error responses from the SMT solver *)
let fail_on_smt_error = function       

  | `Error e -> 
    raise 
      (Failure ("SMT solver failed: " ^ e))
  | `Unsupported -> 
    raise 
      (Failure 
         ("SMT solver reported not implemented"))
  | `NoResponse ->
    raise 
      (Failure 
         ("SMT solver did not produce a reply"))
  | _ -> () 


(* ******************************************************************** *)
(* Creating and finalizing a solver instance                            *)
(* ******************************************************************** *)

let bool_of_bool_option = function
  | None -> false
  | Some b -> b

(* Create a new instance of an SMT solver, declare all currently created
   uninterpreted function symbols *)
let create_instance
    ?produce_assignments
    ?produce_proofs
    ?produce_cores
    l
    kind =
      
  let id = gentag () in

  let module Params = struct
    let produce_assignments = bool_of_bool_option produce_assignments
    let produce_proofs = bool_of_bool_option produce_proofs
    let produce_cores = bool_of_bool_option produce_cores
    let logic = l
    let id = id
  end
  in
  
  let fomodule =
    match kind with
    | `Z3_SMTLIB -> (module Z3SMTLIB.Create(Params) : SolverSig.Inst)
    | `CVC4_SMTLIB -> (module CVC4SMTLIB.Create(Params) : SolverSig.Inst)
    | `MathSat5_SMTLIB -> (module MathSat5SMTLIB.Create(Params) : SolverSig.Inst)
    | `Yices_SMTLIB ->  (module Yices2SMTLIB.Create(Params) : SolverSig.Inst)
    | `Yices_native -> (module YicesNative.Create(Params) : SolverSig.Inst)
    | `detect -> assert false
  in

  { solver_kind = kind;
    solver_inst = fomodule;
    term_names = Hashtbl.create 19;
    id = id }

(* Delete a solver instance *)
let delete_instance s =
  let module S = (val s.solver_inst) in
  S.delete_instance ()


(* ******************************************************************** *)
(* Declarations                                                         *)
(* ******************************************************************** *)

let declare_fun s uf_symbol =
  let module S = (val s.solver_inst) in

  fail_on_smt_error 
    (S.declare_fun
       (UfSymbol.string_of_uf_symbol uf_symbol)
       (UfSymbol.arg_type_of_uf_symbol uf_symbol)
       (UfSymbol.res_type_of_uf_symbol uf_symbol))


let define_fun s uf_symbol vars term =
  let module S = (val s.solver_inst) in

  fail_on_smt_error 
    (S.define_fun
       (UfSymbol.string_of_uf_symbol uf_symbol)
       vars
       (UfSymbol.res_type_of_uf_symbol uf_symbol)
       term)



(* ******************************************************************** *)
(* Primitives                                                           *)
(* ******************************************************************** *)

let assert_expr s expr =
  let module S = (val s.solver_inst) in
  (* Assert SMT expression in solver instance and fail on error *)
  fail_on_smt_error (S.assert_expr expr)


(* Assert a formula in the current context *)
let assert_term s term =
  let module S = (val s.solver_inst) in

  (* Convert term to SMT expression *)
  let expr = S.Conv.smtexpr_of_term term in

  (* Assert SMT expression in solver instance and fail on error *)
  fail_on_smt_error (S.assert_expr expr)


let assert_named_term s term = 

  let term_name, term' = Term.mk_named term in

  Hashtbl.add s.term_names term_name term;

  assert_term s term'


(* Push a new scope to the context and fail on error *)
let push ?(n = 1) s =
  let module S = (val s.solver_inst) in
  fail_on_smt_error (S.push n)


(* Pop a new scope from the context and fail on error *)
let pop ?(n = 1) s =
  let module S = (val s.solver_inst) in
  fail_on_smt_error (S.pop n)


(* ******************************************************************** *)
(* Satisfiability checks                                                *)
(* ******************************************************************** *)

let prof_check_sat ?(timeout = 0) s =
  let module S = (val s.solver_inst) in
  Stat.start_timer Stat.smt_check_sat_time;
  let res = S.check_sat ~timeout () in
  Stat.record_time Stat.smt_check_sat_time;
  res

let prof_check_sat_assuming s exprs =
  let module S = (val s.solver_inst) in
  Stat.start_timer Stat.smt_check_sat_time;
  let res = S.check_sat_assuming exprs in
  Stat.record_time Stat.smt_check_sat_time;
  res

let prof_get_value s e =
  let module S = (val s.solver_inst) in
  Stat.start_timer Stat.smt_get_value_time;
  let res = S.get_value e in
  Stat.record_time Stat.smt_get_value_time;
  res


(* Check satisfiability of current context *)
let check_sat ?(timeout = 0) s = 

  (* Check satisfiability *)
  match prof_check_sat ~timeout s with 

  (* Return true if satisfiable *)
  | `Sat -> true

  (* Return false if unsatisfiable *)
  | `Unsat -> false

  (* Fail on unknown *)
  | `Unknown -> raise Unknown

  (* Fail on error *)
  | `Error _ as r -> 
    fail_on_smt_error r; 
    failwith "SMT solver returned Success on check-sat"


(* Convert models given as pairs of SMT expressions to pairs of variables and
   terms *)
let values_of_smt_model conv_left type_left s smt_values =
  let module S = (val s.solver_inst) in
  List.map
    (function (v, e) -> 
      (let v', e' = 
        conv_left v, S.Conv.term_of_smtexpr e 
       in
       let tv', te' = 
         type_left v', Term.type_of_term e'
       in
       if
         Type.equal_types tv' te'
       then 
         (v', e') 
       else if 
         Type.equal_types tv' Type.t_real && 
         Type.equal_types te' Type.t_int 
       then
         (v', Term.mk_to_real e')
       else
         (v', e')))
    smt_values



(* Get model of the current context *)
let get_model s vars =
  let module S = (val s.solver_inst) in

  match 
    (* Get values of SMT expressions in current context *)
    prof_get_value s (List.map S.Conv.smtexpr_of_var vars)
  with 
  | `Error e -> 
      raise 
        (Failure ("SMT solver failed: " ^ e))
        
  | `Values m -> values_of_smt_model S.Conv.var_of_smtexpr Var.type_of_var s m



(* Get values of state variables in the current context *)
let get_values s terms =
  let module S = (val s.solver_inst) in

  match 
    (* Get values of SMT expressions in current context *)
    prof_get_value s (List.map S.Conv.smtexpr_of_term terms) 
  with 
  | `Error e -> 
    raise 
      (Failure ("SMT solver failed: " ^ e))

  | `Values m -> values_of_smt_model S.Conv.term_of_smtexpr Term.type_of_term s m


(* Get unsat core of the current context *)
let get_unsat_core_of_names s =
  let module S = (val s.solver_inst) in

  match S.get_unsat_core () with 

  | `Error e -> 
    raise 
      (Failure ("SMT solver failed: " ^ e))

  | `Unsat_core c -> 

    try 

      (* Convert strings t<int> to integer *)
      let core_names = 
        List.map 
          (function s -> Scanf.sscanf s "t%d" (function x -> x)) 
          c
      in

      List.fold_left 
        (fun a n -> Hashtbl.find s.term_names n :: a)
        []
        core_names

    with

    (* Raise exception if scanning fails *)
    | Scanf.Scan_failure _
    | End_of_file
    | Failure _ -> 
      raise (Failure "Invalid string in reply from SMT solver")

        
(* Get unsat core of the current context *)
let get_unsat_core_lits s =
  let module S = (val s.solver_inst) in

  match S.get_unsat_core () with 

  | `Error e -> 
    raise 
      (Failure ("SMT solver failed: " ^ e))

  | `Unsat_core c -> 

    (* Convert strings to literals *)
    List.fold_left  
      (fun a s -> 
        try 
          (Term.mk_uf 
             (UfSymbol.uf_symbol_of_string s)
             []) :: a
        with Not_found -> assert false)
      []
      c

      
(* ******************************************************************** *)
(* Higher level functions                                               *)
(* ******************************************************************** *)

(* Check satisfiability of formula in current context *)
let check_sat_term ?(timeout = 0) solver terms = 

  (* Push context *)
  push solver;

  (* Assert formulas *)
  List.iter (assert_term solver) terms;

  (* Result of check-sat was Sat? *)
  let res = check_sat ~timeout solver in

  (* Pop context *)
  pop solver;

  res


(* Checks satisfiability of some literals, runs if_sat if sat and if_unsat if
   unsat. *)
let check_sat_assuming s if_sat if_unsat literals =
  let module S = (val s.solver_inst) in
  if S.check_sat_assuming_supported ()

  then
    (* Solver supports check-sat-assuming, let's do this. *)
    let sat =
      match
        (* Performing the check-sat. *)
        S.check_sat_assuming literals
      with

      (* Fail on error *)
      | `Error e -> 
        raise 
          (Failure ("SMT solver failed: " ^ e))

      (* Return true if satisfiable *)
      | `Sat -> true

      (* Return false if unsatisfiable *)
      | `Unsat -> false

      (* Fail on unknown *)
      | `Unknown -> raise Unknown
    in

    (* Executing user-provided functions. *)
    let res = if sat then if_sat () else if_unsat () in

    res

  else
    (* Solver does not support check-sat-assuming, doing
       push/pop. *)

    (* Pushing. *)
    let _ = push s in

    (* Asserting literals. *)
    literals |> Term.mk_and |> assert_term s ;

    (* Performing check-sat. *)
    let sat = check_sat s in

    (* Executing user-defined functions. *)
    let res = if sat then if_sat () else if_unsat () in

    (* Popping literals. *)
    pop s;

    res


(* Check satisfiability of formula in current context and return a
   model for variables in formula if satisfiable *)
let check_sat_term_model ?(timeout = 0) solver terms = 

  (* Push context *)
  push solver;

  (* Assert formula *)
  List.iter (assert_term solver) terms;

  (* Result of check-sat was Sat? *)
  let res = check_sat ~timeout solver in

  (* Model of context *)
  let model = 

    (* Context is satisfiable? *)
    if res then 

      (* Get variables of term *)
      let vars = Var.VarSet.elements (Term.vars_of_term (Term.mk_and terms)) in

      (* Get model of context *)
      get_model solver vars 

    else

      (* Return an empty model *)
      []

  in

  (* Pop context *)
  pop solver;

  (* Return result and model *)
  res, model


(* Check satisfiability of formula in current context *)
let check_entailment ?(timeout = 0) solver prems conc = 

  (* Push context *)
  push solver;

  (* Assert premise and negated conclusion *)
  List.iter (assert_term solver) prems;
  assert_term solver (Term.mk_not conc);

  (* Result of check-sat was Sat? *)
  let res = not (check_sat ~timeout solver) in

  (* Pop context *)
  pop solver;

  res


(* Check satisfiability of formula in current context *)
let check_entailment_cex ?(timeout = 0) solver prems conc = 

  (* Push context *)
  push solver;

  (* Assert premise and negated conclusion *)
  List.iter (assert_term solver) prems;
  assert_term solver (Term.mk_not conc);

  (* Result of check-sat was Sat? *)
  let res = not (check_sat ~timeout solver) in

  (* Model of context *)
  let model = 

    (* Entailment holds? *)
    if res then 

      (* Return an empty model *)
      []

    else

      (* Get variables of term *)
      let vars = 
        Var.VarSet.elements 
          (Term.vars_of_term 
             (Term.mk_and ((Term.mk_not conc) :: prems)))
      in

      (* Get model of context *)
      get_model solver vars 

  in

  (* Pop context *)
  pop solver;

  (* Return result and model *)
  res, model

let execute_custom_command s cmd args num_res =
  let module S = (val s.solver_inst) in
  S.execute_custom_command cmd args num_res

let execute_custom_check_sat_command cmd s =
  let module S = (val s.solver_inst) in
  S.execute_custom_check_sat_command cmd



(* ******************************************************************** *)
(* Utiliy functions                                                     *)
(* ******************************************************************** *)


(* For a model return a conjunction of equations representing the model *)
let term_of_model model = 

  Term.mk_and
    (List.map 
       (function (v, e) -> Term.mk_eq [Term.mk_var v; e])
       model)


let converter s =
  let module S = (val s.solver_inst) in
  (module S.Conv : SMTExpr.Conv)


let kind s = s.solver_kind


let trace_comment s c =
  let module S = (val s.solver_inst) in
  S.trace_comment c


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
