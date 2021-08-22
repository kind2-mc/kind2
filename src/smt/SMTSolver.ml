(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015-2018 by the Board of Trustees of the University of Iowa

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


exception Unknown
exception Timeout


module IntMap = Map.Make(
  struct type t = int let compare = compare end
)


(* Generate next unique identifier *)
let gentag =
  let r = ref 0 in
  fun () -> incr r; !r


(* Instantiate module for SMTLIB2 solvers with drivers *)
module BoolectorSMTLIB : SolverSig.S = SMTLIBSolver.Make (BoolectorDriver)
module Z3SMTLIB : SolverSig.S = SMTLIBSolver.Make (Z3Driver)
module CVC4SMTLIB : SolverSig.S = SMTLIBSolver.Make (CVC4Driver)
module Yices2SMTLIB : SolverSig.S = SMTLIBSolver.Make (Yices2SMT2Driver)
module MathSATSMTLIB : SolverSig.S = SMTLIBSolver.Make (MathSATDriver)

(* SMT expression *)
type expr = SMTExpr.t


(* Solver instance *)
type t = { 
  (* Type of SMT solver *)
  solver_kind : Flags.Smt.solver ;
  (* Solver instance *)
  solver_inst : (module SolverSig.Inst) ;
  (* Hashtable associating generated names to terms *)
  term_names : (int, expr) Hashtbl.t ;
  (* Unique identifier for solver instance *)
  id : int ;
  mutable next_assumption_id : int ;
  mutable last_assumptions : Term.t array ;
  mutable next_getvalue_id : int ;
}

(** All solver instances created are stored in this map from solver id to
solver. The main goal of this is to have all the live solver instances in one
place so that we can kill everyone easily in case of unexpected shutdown.

See [destroy_all]. *)
let all_solvers = ref IntMap.empty

(** Registers a solver. *)
let add_solver ( { id } as solver ) =
  all_solvers := IntMap.add id solver !all_solvers

(** Forgets a solver. *)
let drop_solver { id } =
  all_solvers := IntMap.remove id !all_solvers

(* Destroys a solver instance. *)
let destroy s =
  let module S = (val s.solver_inst) in
  S.delete_instance ()

(* Raise an exception on error responses from the SMT solver *)
let fail_on_smt_error s = function

  | `Timeout -> drop_solver s ; destroy s ; raise Timeout

  | `Error e -> 
    raise (Failure ("SMT solver failed: " ^ e))

  | `Unsupported -> 
    raise 
      (Failure 
         ("SMT solver reported not implemented"))

  | `NoResponse ->
    raise 
      (Failure 
         ("SMT solver did not produce a reply"))

  | _ -> ()

let smt_error s = function

  | `Timeout -> drop_solver s ; destroy s ; raise Timeout

  | `Error e -> 
    raise (Failure ("SMT solver failed: " ^ e))

  | _ -> assert false

(* Format for named literals in unsat core for check-sat with
   assumptions *)
let unsat_core_namespace = "c"
    
(* ******************************************************************** *)
(* Creating and finalizing a solver instance                            *)
(* ******************************************************************** *)

let bool_of_bool_option = function
  | None -> false
  | Some b -> b

let bool_of_int_option = function
  | None -> 0
  | Some i -> i

(* Create a new instance of an SMT solver, declare all currently created
   uninterpreted function symbols *)
let [@ocaml.warning "-27"] create_instance
    ?timeout
    ?produce_assignments
    ?produce_proofs
    ?produce_cores
    ?minimize_cores
    ?produce_interpolants
    l
    kind =

  (* New identifier for solver instance *)
  let id = gentag () in

  (* Module for parameters of solver instance *)
  let module Params = 
  struct
    let timeout = bool_of_int_option timeout
    let produce_assignments = bool_of_bool_option produce_assignments
    let produce_proofs = bool_of_bool_option produce_proofs
    let produce_cores = bool_of_bool_option produce_cores
    let minimize_cores = bool_of_bool_option minimize_cores
    (*let produce_interpolants = bool_of_bool_option produce_interpolants*)
    let logic = l
    let id = id
  end
  in

  (* Module for solver from options *)
  let fomodule =
    match kind with
    | `Boolector_SMTLIB -> (module BoolectorSMTLIB.Create(Params) : SolverSig.Inst)
    | `MathSAT_SMTLIB -> (module MathSATSMTLIB.Create(Params) : SolverSig.Inst)
    | `Z3_SMTLIB -> (module Z3SMTLIB.Create(Params) : SolverSig.Inst)
    | `CVC4_SMTLIB -> (module CVC4SMTLIB.Create(Params) : SolverSig.Inst)
    | `Yices_SMTLIB ->  (module Yices2SMTLIB.Create(Params) : SolverSig.Inst)
    | `Yices_native -> (module YicesNative.Create(Params) : SolverSig.Inst)
    | `detect -> assert false
  in

  (* Return solver instance *)
  let solver =
    { solver_kind = kind;
      solver_inst = fomodule;
      term_names = Hashtbl.create 19;
      id = id;
      next_assumption_id = 0;
      last_assumptions = [| |];
      next_getvalue_id = 0; }
  in

  add_solver solver ;

  solver

(* Delete a solver instance *)
let delete_instance s =
  if (IntMap.mem s.id !all_solvers) then (
    drop_solver s ;
    destroy s
  )

(* Destroys all live solvers. *)
let destroy_all () =
  !all_solvers
  |> IntMap.iter (
    fun _ s -> destroy s
  ) ;
  all_solvers := IntMap.empty

(** Delete instance entries (should be called after forking, on child processes). *)
let delete_instance_entries () =
  all_solvers := IntMap.empty

(* Return the unique identifier of the solver instance *)
let id_of_instance { id } = id

(* ******************************************************************** *)
(* Declarations                                                         *)
(* ******************************************************************** *)

(* Declare an uninterpreted sort symbol *) 
let declare_sort s sort =
  let module S = (val s.solver_inst) in
  fail_on_smt_error s (S.declare_sort sort)


(* Declare an uninterpreted function symbol *) 
let declare_fun s uf_symbol =
  let module S = (val s.solver_inst) in

  fail_on_smt_error s
    (S.declare_fun
       (UfSymbol.string_of_uf_symbol uf_symbol)
       (UfSymbol.arg_type_of_uf_symbol uf_symbol)
       (UfSymbol.res_type_of_uf_symbol uf_symbol))


(* Define an uninterpreted function symbol *)
let define_fun s uf_symbol vars term =
  let module S = (val s.solver_inst) in

  fail_on_smt_error s
    (S.define_fun
       (UfSymbol.string_of_uf_symbol uf_symbol)
       vars
       (UfSymbol.res_type_of_uf_symbol uf_symbol)
       term)



(* ******************************************************************** *)
(* Primitives                                                           *)
(* ******************************************************************** *)

(* Assert an SMT expression *)
let assert_expr s expr =
  let module S = (val s.solver_inst) in
  (* Assert SMT expression in solver instance and fail on error *)
  fail_on_smt_error s (S.assert_expr expr)

(* Assert-soft an SMT expression *)
let assert_soft_expr s expr weight =
  let module S = (val s.solver_inst) in
  (* Assert-soft SMT expression in solver instance and fail on error *)
  fail_on_smt_error s (S.assert_soft_expr expr weight)

(* Convert a term to an SMT expression and assert *)
let assert_term s term =
  let module S = (val s.solver_inst) in

  (* Convert term to SMT expression *)
  let expr = S.Conv.smtexpr_of_term term in

  (* Assert SMT expression in solver instance and fail on error *)
  fail_on_smt_error s (S.assert_expr expr)

(* Convert a term to an SMT expression and assert-soft *)
let assert_soft_term s term weight =
  let module S = (val s.solver_inst) in

  (* Convert term to SMT expression *)
  let expr = S.Conv.smtexpr_of_term term in

  (* Assert SMT expression in solver instance and fail on error *)
  fail_on_smt_error s (S.assert_soft_expr expr weight)


(* Name a term with a fresh name, convert to an SMT expression and
   assert, returning the name *)
let assert_named_term s term = 

  let term_name, term' = Term.mk_named term in

  Hashtbl.add s.term_names term_name term;

  assert_term s term'


let assert_named_term_wr s term =
  
  let term_name, term' = Term.mk_named term in
  
  Hashtbl.add s.term_names term_name term;
  
  assert_term s term';
  
  "t" ^ (string_of_int term_name)



(* Push a new scope to the context and fail on error *)
let push ?(n = 1) s =
  let module S = (val s.solver_inst) in
  fail_on_smt_error s (S.push n) 

(* Pop a new scope from the context and fail on error *)
let pop ?(n = 1) s =
  let module S = (val s.solver_inst) in
  fail_on_smt_error s (S.pop n)


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

let prof_get_model s e =
  let module S = (val s.solver_inst) in
  Stat.start_timer Stat.smt_get_value_time;
  let res = S.get_model e in
  Stat.record_time Stat.smt_get_value_time;
  res

let prof_get_unsat_core s =
  let module S = (val s.solver_inst) in
  Stat.start_timer Stat.smt_get_unsat_core_time;
  let res = S.get_unsat_core () in
  Stat.record_time Stat.smt_get_unsat_core_time;
  res

let trace_comment s c =
  let module S = (val s.solver_inst) in
  S.trace_comment c



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
  | r -> smt_error s r


(* Convert models given as pairs of SMT expressions to pairs of
   variables and terms *)
let values_of_smt_values conv_left type_left s smt_values =
  let module S = (val s.solver_inst) in

  (* Convert association list for get-value call to an association
     list of variables to terms *)
  List.map

    (* Map pair of SMT expressions to a pair of variable and term *)
    (function (v, e) -> 

      (* Convert to variable or term and term *)
      let v', e' = 
        conv_left v, S.Conv.term_of_smtexpr e 
      in

      (* Get type of variable or term and term *)
      let tv', te' = 
        type_left v', Term.type_of_term e'
      in

      if 
        (* Assignment of integer value to a real variable or term? *)
        Type.equal_types tv' Type.t_real && 
        Type.equal_types te' Type.t_int 

      then

        (* Convert integer to real *)
        (v', Term.mk_to_real e')

      else

        (* Keep assignment *)
        (v', e'))

    smt_values


let [@ocaml.warning "-27"] model_of_smt_values conv_left type_left s smt_values = 
  let module S = (val s.solver_inst) in

  (* Create hash table with size matching the number of values *)
  let model = Var.VarHashtbl.create (List.length smt_values) in

  (* Add all variable term pairs to the hash table *)
  List.iter

    (* Convert a pair of SMT expressions to a variable and a term, and
       add to the hash table *)
    (function (v, e) ->

      (* Convert expression on lhs to a variable and expression on rhs
         to a term *)
      let v', e' = 
        let t = S.Conv.var_term_of_smtexpr v in
        (* TODO: deal with arrays *)
        assert (Term.is_free_var t);
        Term.free_var_of_term t, S.Conv.term_of_smtexpr e 
      in

      (* Get types of variable and term *)
      let tv', te' = 
        Var.type_of_var v', Term.type_of_term e'
      in

      (* Hack to make integer values match reals *)
      let e'' =

        if 

          (* Rhs is of type real, variable is of type integer? *)
          Type.is_real tv' && 
          (Type.is_int te' || Type.is_int_range te')
          
        then

          (* Convert term to a real *)
          if Term.is_numeral e' then (
            let bint = Numeral.to_big_int (Term.numeral_of_term e') in
            Term.mk_dec (Decimal.of_big_int bint)
          )
          else Term.mk_to_real e'

        else
          
          (* Return term as is *)
          e'

      in        

      (* Add assignment to hash table *)
      Var.VarHashtbl.add model v' (Model.Term e''))

    (* Iterate over all pairs from get-value call *)
    smt_values;

  (* Return hash table *)
  model


(*let eval_array_vars v smt_model =

  let uf_sym = Var.unrolled_uf_of_state_var_instance v in

  (* let ty = Var.type_of_var v in *)
  (* match Type.node_of_type ty with *)
  (* | Type.Array (te, ti) -> *)
  (*   let select_s = *)
  (*     Format.asprintf "|uselect(%a,%a)|" *)
  (*       Type.pp_print_type ti Type.pp_print_type te in *)
  (*   let select_uf = UfSymbol.mk_uf_symbol select_s [ty; ti] te in *)
  (*   let select_lambda = *)
  (*     match List.assq select_uf smt_model with *)
  (*     | Model.Lambda l -> l | Model.Term _ -> assert false in *)
  (*   (match List.assq uf_sym smt_model with *)
  (*    | Model.Term t -> Model.Lambda (Term.partial_eval_lambda select_lambda [t]) *)
  (*    | Model.Lambda  _ -> assert false) *)

  (* | _ -> *) List.assq uf_sym smt_model


let model_of_smt_model s smt_model vars = 

  (* Create hash table with size matching the number of values *)
  let model = Var.VarHashtbl.create (List.length smt_model) in

  (* Add all variable term pairs to the hash table *)
  List.iter
    (fun v ->
       let uf_sym = Var.unrolled_uf_of_state_var_instance v in
       try Var.VarHashtbl.add model v (List.assq uf_sym smt_model)
       with Not_found -> ()

(*
         KEvent.log L_debug "No assignment to %a" Var.pp_print_var v;

         assert false
*)
    )
    vars;

  model*)
  

let [@ocaml.warning "-27"] partial_model_of_smt_model s smt_model =

  (* Create hash table with size matching the number of values *)
  let model = Var.VarHashtbl.create (List.length smt_model) in

  (* Add all variable term pairs to the hash table *)
  List.iter
    (fun (uf_sym, t_or_l) -> 
       
       try 

         let var = Var.state_var_instance_of_uf_symbol uf_sym in
         
         Var.VarHashtbl.add model var t_or_l

       with Not_found -> ())
    smt_model;

  model
  

(* Raise when encountering an array variable to switch to get-model
   instead of get-value *)
(* exception Var_is_array *)


(* range as list of integers *)
let range (l, u) =
  let rec aux acc u =
    if u < l then acc
    else
      aux (u :: acc) (u - 1) in
  aux [] u


(* Cross product between lists of elements *)

let cross_2 l1 l2 =
  List.fold_left (fun acc i1 ->
      List.fold_left (fun acc i2 -> (i1 :: i2) :: acc) acc l2
    ) [] l1
    
let cross ll = List.fold_left (fun acc l -> cross_2 l acc) [[]] ll


(* Get model of the current context *)
let get_var_values s state_var_indexes vars =
  let module S = (val s.solver_inst) in

  (* separate array variables *)
  let sexpr_vars, array_vars =
    List.fold_left (fun (sexpr_vars, array_vars) v ->
        if Var.type_of_var v |> Type.is_array then
          sexpr_vars, v :: array_vars
        else
          (S.Conv.smtexpr_of_var v []) :: sexpr_vars, array_vars
      ) ([], []) vars
  in

  (* Get values of SMT expressions in current context *)
  let model =
    match prof_get_value s sexpr_vars with 
    | `Values v -> 

      model_of_smt_values 

        (* Convert an SMT term back to a variable *)
        (fun v -> 
           let t = S.Conv.var_term_of_smtexpr v in

           (* We are sure that there are no array typed variables *)
           assert (Term.is_free_var t); 
           (Term.free_var_of_term t)
        )
        Var.type_of_var s v

      | r -> smt_error s r
  in

  (* Get model for arrays *)
  (* We obtain the model by first evaluating the bound of the array in the
     current model when it is not fixed. Then we evaluate A[0], ..., A[n] in the
     solver and return a map that represent this as the model *)
  List.iter (fun v ->
      let ty = Var.type_of_var v in 
      assert (Type.is_array ty);
      let offset =
        if Var.is_state_var_instance v then Var.offset_of_state_var_instance v
        else Numeral.zero in
      let indexes = StateVar.StateVarHashtbl.find state_var_indexes
          (Var.state_var_of_state_var_instance v) in

      let bnds = try
          List.map (function
          | LustreExpr.Unbound _ ->
            raise Exit
            (* assert false *) (* no models for unbounded arrays *)
          | LustreExpr.Fixed eu
          | LustreExpr.Bound eu ->
            if LustreExpr.is_numeral eu then
              0, LustreExpr.numeral_of_expr eu |> Numeral.to_int |> pred
            else
              (* evaluate value of bound in current model *)
              (* assert (StateVar.is_const svub); *)
              let ub = LustreExpr.unsafe_term_of_expr eu
                       |> Term.bump_state offset
                       |> Eval.eval_term [] model in
              (match ub with
               | Eval.ValNum nu -> 0, Numeral.to_int nu |> pred
               | _ -> assert false)
            ) indexes
        with Exit -> []
      in
      
      let args_list = cross (List.map range bnds) in
      let vt = Term.mk_var v in
      let sexprs =
        List.map (fun args ->
            List.fold_left Term.mk_select
              vt (List.rev_map Term.mk_num_of_int args)
            |> Term.convert_select
            |> S.Conv.smtexpr_of_term
          ) args_list in
      
      let values =
        if sexprs = [] then [] (* when the size of the array is 0 in the model *)
        else match prof_get_value s sexprs with
          | `Values v -> v
          | r -> smt_error s r
      in
      let m =
        List.fold_left (fun acc (t, e) ->
            let t = S.Conv.term_of_smtexpr t in
            assert (Term.is_select t);
            let v', args_t = Term.indexes_and_var_of_select t in
            assert (Var.equal_vars v v');
            let args = List.map
                (fun x -> Numeral.to_int (Term.numeral_of_term x)) args_t in
            Model.MIL.add args (S.Conv.term_of_smtexpr e) acc
          ) Model.MIL.empty values in
      Var.VarHashtbl.add model v (Model.Map m)
    ) array_vars;
      
  model


(* Get model of the current context *)
let get_model s =
  match 
    (* Get model in current context *)
    prof_get_model s ()
  with 
    | `Model m -> partial_model_of_smt_model s m 
    | r -> smt_error s r


(* Get unsat core of the current context *)
let get_unsat_core_of_names s =

  match prof_get_unsat_core s with 

  | `Unsat_core c -> 

    begin try 

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
    end

  | r -> smt_error s r

        
(* Get unsat core of the current context *)
let get_unsat_core_lits s =
  let module S = (val s.solver_inst) in
  
  match prof_get_unsat_core s with 

    | `Unsat_core c -> 

      (* If check-sat with assumptions is enabled, the names of core
         assertions are the names of the assumption
         literals. Otherwise, we have asserted the assumption literals
         with names and need to retrieve literals by name. *)
      if S.check_sat_assuming_supported () then
        
        (* Interpret name as atom *)
        List.fold_left  
          (fun a s ->
            try 
              (Term.mk_uf 
                 (UfSymbol.uf_symbol_of_string s)
                 []) :: a
            with Not_found -> assert false)
          []
          c

      else

        (* Look up name assumption literal by name *)
        List.fold_left
          (fun a n ->
            try

              (* Get identifier from name *)
              let i = Scanf.sscanf n "c%d" identity in

              (* Get term of name 

                 Terms are stored in the array with the highest
                 identifier at index zero *)
              let t = (s.last_assumptions).(s.next_assumption_id - i - 1) in

              t :: a

            (* Skip if name is not the name of an assumption literal *)
            with Failure _ -> a)
          []
          c

    | r -> smt_error s r
      
      
(* ******************************************************************** *)
(* Higher level functions                                               *)
(* ******************************************************************** *)

(* Checks satisfiability of some literals, runs if_sat if sat and if_unsat if unsat.
   Any call to get_unsat_core_lits should be done INSIDE the continutation if_unsat,
   and NOT in AFTER the call to check_sat_assuming. *)
let check_sat_assuming s if_sat if_unsat literals =

  (* Calling check_sat_assuming with no litteral fails with CVC4,
    so it is better to put this verification here *)
  assert (literals <> []) ;

  let module S = (val s.solver_inst) in

  (* Does the solver suport check-sat with assumptions? *)
  if S.check_sat_assuming_supported () then

    (* Solver supports check-sat-assuming, let's do this. *)
    let sat =

      match

        (* Performing the check-sat. *)
        prof_check_sat_assuming s literals

      with
            
        (* Return true if satisfiable *)
        | `Sat -> true
          
        (* Return false if unsatisfiable *)
        | `Unsat -> false
          
        (* Fail on unknown *)
        | `Unknown -> raise Unknown

        | r -> smt_error s r
                        
    in
    
    (* Executing user-provided functions. *)
    if sat then if_sat s else if_unsat s 
      
  else
    
    (* Solver does not support check-sat-assuming, doing
       push/pop. *)

    (* Pushing. *)
    let _ = push s in

    (* Simulate by asserting each literals with a unique name, keep
       associations from names to literals to return unsat core
       later. Number each activation literal, keep reference with highest
       index. To map back, take difference between highest number and
       literal number as index into array. *)

    (* Create array of assumption literals with the literal the gets
       the highest indentifier at index zero *)
    let names_array = List.rev literals |> Array.of_list in

    (* Assert literals with unique name *)
    let next_assumption_id' =
      List.fold_left
        (fun i l ->

          (* Name literal in custom namespace *)
          let l' =
            Term.mk_named_unsafe l unsat_core_namespace i 
          in

          (* Assert named literal *)
          assert_term s l';

          (* Increment counter of literals *)
          succ i)

        s.next_assumption_id
        literals

    in

    (* Update identifier for assumption literals for next check-sat *)
    s.next_assumption_id <- next_assumption_id';

    (* Save array of assumptions *)
    s.last_assumptions <- names_array;
    
    (* Perform check-sat *)
    let sat = check_sat s in
    
    (* Evaluate continuations *)
    let res = if sat then if_sat s else if_unsat s in

    (* Pop assumption literals from stack *)
    pop s;

    (* Return result of respective continuation *)
    res


(* Get values of terms in the current context *)
let get_term_values s terms =

  let module S = (val s.solver_inst) in

  match
    (* Get values of SMT expressions in current context *)
    prof_get_value s (List.map S.Conv.smtexpr_of_term terms)
  with

  | `Values m ->
    values_of_smt_values S.Conv.term_of_smtexpr Term.type_of_term s m

  | r -> smt_error s r

(* In some cases, CVC4 returns syntactically different terms
   to the ones sent in a get-value query. For instance:
   Query: ( get-value ((< x 10.0) (>= y 10.5)) )
   Reply: ( ((< x 10) true) ((>= y (/ 21 2)) false) )
   To avoid post-processing the terms, a constant is defined
   and used as an abbreviation for each term.
   If the term is a single variable, no constant is created.
*)
let create_proxy_constants_for_terms s terms =

  let module S = (val s.solver_inst) in

  (* Unique identifier for a get-value constant (UfSymbol)

     NB: UfSymbols are global, but id is the current value of
     a solver instance counter; type_uf is used to disambiguate
  *)
  let mk_gv_name prefix type_uf id =

    let rec pp_print_type_suffix ppf t = let open Type in
      match node_of_type t with
      | Bool -> Format.pp_print_string ppf "bool"
      | Int -> Format.pp_print_string ppf "int"
      | UBV i ->
        begin match i with
        | 8 -> Format.pp_print_string ppf "uint8"
        | 16 -> Format.pp_print_string ppf "uint16"
        | 32 -> Format.pp_print_string ppf "uint32"
        | 64 -> Format.pp_print_string ppf "uint64"
        | _ -> raise 
              (Invalid_argument "pp_print_type_suffix: BV size not allowed")
        end
      | BV i ->
        begin match i with
        | 8 -> Format.pp_print_string ppf "int8"
        | 16 -> Format.pp_print_string ppf "int16"
        | 32 -> Format.pp_print_string ppf "int32"
        | 64 -> Format.pp_print_string ppf "int64"
        | _ -> raise 
              (Invalid_argument "pp_print_type_suffix: BV size not allowed")
        end
      | IntRange (i, j, Range) ->
        Format.fprintf ppf
          "int_range_%a_%a"
          Numeral.pp_print_numeral i
          Numeral.pp_print_numeral j
      | IntRange (i, j, Enum) ->
        Format.fprintf ppf
          "enum_%a_%a"
          Numeral.pp_print_numeral i
          Numeral.pp_print_numeral j
      | Real -> Format.pp_print_string ppf "real"
      | Array (s, t) ->
        Format.fprintf ppf
          "array_%a_%a"
          pp_print_type_suffix s
          pp_print_type_suffix t
      | Abstr s -> Format.pp_print_string ppf s
    in

    Format.asprintf "%s_%a_%d"
      prefix
      pp_print_type_suffix type_uf
      id
  in

  terms |> List.map (fun term ->
    match Term.destruct term with
    | Term.T.Var _ -> (term, term)
    | Term.T.Const s when Symbol.is_uf s -> (term, term)
    | _ -> (
      let type_expr = term |> Term.type_of_term in
      let id = s.next_getvalue_id in
      (* Name of uninterpreted function symbol *)
      let uf_symbol_name = mk_gv_name "__gv" type_expr id in
      (* Create or retrieve uninterpreted constant *)
      let uf_symbol = UfSymbol.mk_uf_symbol uf_symbol_name [] type_expr in
      s.next_getvalue_id <- s.next_getvalue_id + 1;
      (* Define an uninterpreted constant *)
      define_fun s uf_symbol [] (S.Conv.smtexpr_of_term term);
      (* Return new constant and expression *)
      (Term.mk_uf uf_symbol [], term)
    )
  )


let get_term_values_through_proxy_values s = function
  | [] -> []
  | proxy_term_alist -> (
    get_term_values s (List.map fst proxy_term_alist)
    |> List.map (fun (const, value) ->
      (List.assq const proxy_term_alist, value)
    )
  )

(* Checks satisfiability of the current context, and evaluate one of
   two continuation functions depending on the result *)
let check_sat_and_get_term_values s if_sat if_unsat terms =

  let proxy_term_alist = create_proxy_constants_for_terms s terms in

  if check_sat s then
    let tv = get_term_values_through_proxy_values s proxy_term_alist in
    if_sat s tv
  else
    if_unsat s


(* Checks satisfiability of some literals, and either gets term values and
   runs if_sat if sat or runs if_unsat if unsat. *)
let check_sat_assuming_and_get_term_values s if_sat if_unsat literals terms =

  let proxy_term_alist = create_proxy_constants_for_terms s terms in

  check_sat_assuming s (fun s ->
    let tv = get_term_values_through_proxy_values s proxy_term_alist in
    if_sat s tv
  )
  if_unsat literals


(* Alternative between type 'a and 'b *)
type ('a, 'b) sat_or_unsat =
  | Sat of 'a
  | Unsat of 'b

(* Check satisfiability under assumptions and return different results
   in either case *)
let check_sat_assuming_ab s if_sat if_unsat literals =
  check_sat_assuming
    s 
    (fun s -> Sat (if_sat s))
    (fun s -> Unsat (if_unsat s))
    literals
        
(* Check satisfiability under assumptions and return [true] or [false] *)
let check_sat_assuming_tf s literals =
  check_sat_assuming
    s
    (fun _ -> true)
    (fun _ -> false)
    literals

    
let execute_custom_command s cmd args num_res =
  let module S = (val s.solver_inst) in
  S.execute_custom_command cmd args num_res

let execute_custom_check_sat_command cmd s =
  let module S = (val s.solver_inst) in
  S.execute_custom_check_sat_command cmd



(* ******************************************************************** *)
(* Utiliy functions                                                     *)
(* ******************************************************************** *)

let converter s =
  let module S = (val s.solver_inst) in
  (module S.Conv : SMTExpr.Conv)


let kind s = s.solver_kind


let get_interpolants solver args =
  let module S = (val solver.solver_inst) in
  
  match execute_custom_command solver "compute-interpolant" args (List.length args) with
  | `Custom i ->
     List.map
       (fun sexpr ->
        (S.Conv.term_of_smtexpr
           (GenericSMTLIBDriver.expr_of_string_sexpr sexpr)))
       (List.tl i)

  | _ (* error_response *) -> []


(* Static hashconsed strings *)
let s_goal = HString.mk_hstring "goal"
let s_goals = HString.mk_hstring "goals"

let rec conj_of_goal accum = function

  (* At the end of the goal list *)
  | [] -> List.rev accum

  (* Parameters ":precision" or ": depth" also mark end of goal list *)
  | HStringSExpr.Atom a :: _
      when HString.sub a 0 1 = ":" -> List.rev accum

  (* Take first goal and convert to term, recurse for next goal in list *)
  | t :: tl -> conj_of_goal (t :: accum) tl

(* Extract the goal term from a goal

   (goal {term}+ :precision precise :depth 1)

*)
let goal_to_term = function

  | HStringSExpr.List (HStringSExpr.Atom s :: c) when s == s_goal ->

    conj_of_goal [] c

  (* Invalid S-expression as result *)
  | _ -> failwith "SMT solver returned unexpected result for goal"


(* Extract the goal terms from a list of goals

   (goals (goal {term} :precision precise :depth 1) )

*)
let goals_to_terms solver = function

  (*   (goals (goal true :precision precise :depth 1) ) *)
  | HStringSExpr.List
      [HStringSExpr.Atom s; HStringSExpr.List g] when s == s_goals -> (

    let module S = (val solver.solver_inst) in

    goal_to_term (HStringSExpr.List g)
    |> List.map
         (fun t ->
           S.Conv.term_of_smtexpr
             (GenericSMTLIBDriver.expr_of_string_sexpr t))

  )
  (* Invalid S-expression as result *)
  | _ -> failwith "SMT solver returned unexpected result for goals"


(* SMTLIB commands for Z3

     (declare-fun y (Int) Int)
     (assert (exists ((x Int)) (> x (y 0))))
     (apply qe)

     Output:

     (goals (goal true :precision precise :depth 1) )

*)
let get_qe_z3 solver expr =
  (* Increment scope level *)
  push solver;
  (* Assert expression to eliminate quantifiers from *)
  assert_expr solver expr;
  (* Eliminate quantifiers *)
  let res =
    (* Execute custom command *)
    let arg =
      if Flags.Smt.z3_qe_light () then "(and-then qe-light qe)" else "qe"
    in
    match execute_custom_command solver "apply" [SMTExpr.ArgString arg] 1 with
    | `Custom r ->
       (* Take first goal as quantifier eliminated term *)
       goals_to_terms solver (List.hd r)
    | r -> smt_error solver r
  in
  (* Decrement scope level to remove assertion *)
  pop solver;
  res


let get_qe_cvc4 solver expr =
  let module S = (val solver.solver_inst) in

  match execute_custom_command solver "get-qe" [SMTExpr.ArgExpr expr] 1 with
  | `Custom r -> [S.Conv.term_of_smtexpr
      (GenericSMTLIBDriver.expr_of_string_sexpr (List.hd r))]
  | r -> smt_error solver r


let get_qe_expr solver quantified_expr =

  (* Quantifier elimination is not part of the SMTLIB standard.
     Until then, we handle each particular case here... *)
  match solver.solver_kind with
  | `Z3_SMTLIB -> get_qe_z3 solver quantified_expr
  | `CVC4_SMTLIB -> get_qe_cvc4 solver quantified_expr
  | _ -> failwith "Quantifier elimination is not supported by SMT solver or \
                   implementation is not available"


let get_qe_term solver quantified_term =
  let module S = (val solver.solver_inst) in
  get_qe_expr solver (S.Conv.smtexpr_of_term quantified_term)


let simplify_z3 solver expr =
  (* Increment scope level *)
  push solver;
  assert_expr solver expr;
  let res =
    (* Execute custom command *)
    let arg = "ctx-solver-simplify" in
    match execute_custom_command solver "apply" [SMTExpr.ArgString arg] 1 with
    | `Custom r ->
       (* Take first goal *)
       goals_to_terms solver (List.hd r) |> Term.mk_and
    | r -> smt_error solver r
  in
  (* Decrement scope level to remove assertion *)
  pop solver;
  res

let simplify_expr solver expr =
  let module S = (val solver.solver_inst) in
  (* Simplify is not part of the SMTLIB standard.
     Until then, we handle each particular case here... *)
  match solver.solver_kind with
  | `Z3_SMTLIB -> simplify_z3 solver expr
  | _ ->  (S.Conv.term_of_smtexpr expr)

let simplify_term solver term =
  let module S = (val solver.solver_inst) in
  simplify_expr solver (S.Conv.smtexpr_of_term term)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
