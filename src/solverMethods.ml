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

module type S =
sig

  exception Unknown

  module T : SMTSolver.S

  type t

  val new_solver : ?produce_assignments:bool -> ?produce_models:bool -> ?produce_proofs:bool -> ?produce_cores:bool -> SMTExpr.logic -> t
                                                                                                                                          
  val delete_solver : t -> unit
                             
  val declare_fun : t -> UfSymbol.t -> unit

  val define_fun : t -> UfSymbol.t -> Var.t list -> Term.t -> unit

  val fail_on_smt_error : SMTExpr.response -> unit

  val assert_term : t -> Term.t -> unit

  val assert_named_term_wr : t -> SMTExpr.t -> string

  val assert_named_term : t -> SMTExpr.t -> unit

  val push : ?n:int -> t -> unit

  val pop : ?n:int -> t -> unit

  val check_sat : ?timeout:int -> t -> bool

  val get_model : t -> Var.t list -> (Var.t * Term.t) list

  val get_values : t -> Term.t list -> (Term.t * Term.t) list

  val get_unsat_core : t -> Term.t list

  val check_sat_term : ?timeout:int -> t -> Term.t list -> bool

  val check_sat_assuming : t ->
                           (* If sat. *)
                           (unit -> 'a) ->
                           (* If unsat. *)
                           (unit -> 'a) ->
                           (* Literals to assert. *)
                           Term.t list ->
                           'a

  val check_sat_term_model : ?timeout:int -> t -> Term.t list -> bool * (Var.t * Term.t) list 

  val check_entailment : ?timeout:int -> t -> Term.t list -> Term.t -> bool

  val check_entailment_cex : ?timeout:int -> t -> Term.t list -> Term.t -> bool * (Var.t * Term.t) list 

  val term_of_model : (Var.t * Term.t) list -> Term.t
                                                 
  val get_interpolants : t -> SMTExpr.custom_arg list -> Term.t 

  val trace_comment : t -> string -> unit

end

module Make (S : SMTSolver.S) : S with type t = S.t and type T.t = S.t =
struct

  exception Unknown
  
  (* The encapsulated module for lower level access to the solver *)
  module T = struct include S end

  (* Hashtable associating generated names to terms *)
  let term_names = Hashtbl.create 7 

  (* Type of a solver instance *)
  type t = S.t


  (* Raise an exception on error responses from the SMT solver *)
  let fail_on_smt_error = function       

    | SMTExpr.Error e -> 
      raise 
        (Failure ("SMT solver failed: " ^ e))
    | SMTExpr.Unsupported -> 
      raise 
        (Failure 
           ("SMT solver reported not implemented"))
    | SMTExpr.NoResponse ->
      raise 
        (Failure 
           ("SMT solver did not produce a reply"))
    | SMTExpr.Success -> () 
      



  (* ******************************************************************** *)
  (* Creating and finalizing a solver instance                            *)
  (* ******************************************************************** *)


  (* Create a new instance of an SMT solver, declare all currently
     created uninterpreted function symbols *)
  let new_solver 
      ?produce_assignments
      ?produce_models
      ?produce_proofs
      ?produce_cores
      logic =

    (* Create solver instance *)
    let solver =     
      S.create_instance 
        ?produce_assignments
        ?produce_models
        ?produce_proofs
        ?produce_cores
        logic
    in

    (* Return solver instance *)
    solver


  (* Delete a solver instance *)
  let delete_solver solver = 

    (* Delete solver instance *)
    S.delete_instance solver 


  (* Output a comment into the trace *)
  let trace_comment solver comment = S.trace_comment solver comment


  (* ******************************************************************** *)
  (* Declarations                                                         *)
  (* ******************************************************************** *)

  let declare_fun solver uf_symbol = 

    fail_on_smt_error 
      (S.declare_fun
         solver
         (UfSymbol.string_of_uf_symbol uf_symbol)
         (UfSymbol.arg_type_of_uf_symbol uf_symbol)
         (UfSymbol.res_type_of_uf_symbol uf_symbol))


  let define_fun solver uf_symbol vars term =

    fail_on_smt_error 
      (S.define_fun
         solver
         (UfSymbol.string_of_uf_symbol uf_symbol)
         vars
         (UfSymbol.res_type_of_uf_symbol uf_symbol)
         term)


  (* ******************************************************************** *)
  (* Primitives                                                           *)
  (* ******************************************************************** *)

  (* Assert a formula in the current context *)
  let assert_term solver term = 

    (* Convert term to SMT expression *)
    let expr = SMTExpr.smtexpr_of_term term in
    
    (* Assert SMT expression in solver instance and fail on error *)
    fail_on_smt_error (S.assert_expr solver expr)

  let  assert_named_term_wr solver term = 

    let term_name, term' = Term.mk_named term in

    Hashtbl.add term_names term_name term;

    assert_term solver term';
    
    "t" ^ (string_of_int term_name)
      

  let assert_named_term solver term = 

    let term_name, term' = Term.mk_named term in

    Hashtbl.add term_names term_name term;

    assert_term solver term'

  (* Push a new scope to the context and fail on error *)
  let push ?(n = 1) solver = fail_on_smt_error (S.push solver n)


  (* Pop a new scope from the context and fail on error *)
  let pop ?(n = 1) solver = fail_on_smt_error (S.pop solver n)


  (* Check satisfiability of current context *)
  let check_sat ?(timeout = 0) solver = 

    (* Check satisfiability *)
    match S.check_sat ~timeout solver with 
        
      (* Fail on error *)
      | SMTExpr.Response r -> 
        fail_on_smt_error r; 
        failwith "SMT solver returned Success on check-sat" 
          
      (* Return true if satisfiable *)
      | SMTExpr.Sat -> true

      (* Return false if unsatisfiable *)
      | SMTExpr.Unsat -> false

      (* Fail on unknown *)
      | SMTExpr.Unknown -> raise Unknown


  (* Get model of the current context *)
  let get_model solver vars =  

    (* Model as pairs of SMT expressions *)
    let smt_model = 

      match 
    
        (* Get values of SMT expressions in current context *)
        S.get_value solver
          (List.map
             SMTExpr.smtexpr_of_var
             vars)
          
      with 

        | SMTExpr.Error e, _ -> 
          
          raise 
            (Failure ("SMT solver failed: " ^ e))
            
        | SMTExpr.Unsupported, _ -> 
          raise 
            (Failure 
               ("SMT solver reported not implemented"))
            
        | SMTExpr.NoResponse, _ ->
          raise 
            (Failure 
               ("SMT solver did not produce a reply"))
            
        | SMTExpr.Success, m -> m
          
    in
    
    (* Map pairs of SMT expressions to pairs of variables and terms *)
    let model =
      List.map
        (function (v, e) -> 
          (let v', e' = 
            SMTExpr.var_of_smtexpr v, SMTExpr.term_of_smtexpr e 
           in
           let tv', te' = 
             Var.type_of_var v', Term.type_of_term e'
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
        smt_model
    in

    (* Return model *)
    model


  (* Get model of the current context *)
  let get_values solver terms =  

    (* Model as pairs of SMT expressions *)
    let smt_values = 

      match 
    
        (* Get values of SMT expressions in current context *)
        S.get_value solver
          (List.map SMTExpr.smtexpr_of_term terms)
          
      with 

        | SMTExpr.Error e, _ -> 
          
          raise 
            (Failure ("SMT solver failed: " ^ e))
            
        | SMTExpr.Unsupported, _ -> 
          raise 
            (Failure 
               ("SMT solver reported not implemented"))
            
        | SMTExpr.NoResponse, _ ->
          raise 
            (Failure 
               ("SMT solver did not produce a reply"))
            
        | SMTExpr.Success, m -> m
          
    in
    
    (* Map pairs of SMT expressions to pairs of variables and terms *)
    let values =
      List.map
        (function (v, e) -> 
          (let v', e' = 
            SMTExpr.term_of_smtexpr v, SMTExpr.term_of_smtexpr e 
           in
           let tv', te' = 
             Term.type_of_term v', Term.type_of_term e'
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
    in

    (* Return model *)
    values


  (* Get model of the current context *)
  let get_unsat_core solver =  

    match 

      (* Get values of SMT expressions in current context *)
      S.get_unsat_core solver

    with 

      | SMTExpr.Error e, _ -> 

        raise 
          (Failure ("SMT solver failed: " ^ e))

      | SMTExpr.Unsupported, _ -> 
        raise 
          (Failure 
             ("SMT solver reported not implemented"))

      | SMTExpr.NoResponse, _ ->
        raise 
          (Failure 
             ("SMT solver did not produce a reply"))

      | SMTExpr.Success, c -> 

        try 

          (* Convert strings t<int> to integer *)
          let core_names = 
            List.map 
              (function s -> Scanf.sscanf s "t%d" (function x -> x)) 
              c
          in

          List.fold_left 
            (fun a n -> Hashtbl.find term_names n :: a)
            []
            core_names

        with

          (* Raise exception if scanning fails *)
          | Scanf.Scan_failure _
          | End_of_file
          | Failure _ -> 
            raise (Failure "Invalid string in reply from SMT solver")

          

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

  (* Checks satisfiability of some literals, runs if_sat if sat and
     if_unsat if unsat. *)
  let check_sat_assuming solver if_sat if_unsat literals =

    if SMTLIBSolver.check_sat_assuming_supported ()

    then
      (* Solver supports check-sat-assuming, let's do this. *)
      let sat =
        match
          (* Performing the check-sat. *)
          S.check_sat_assuming solver literals
        with
          
        (* Fail on error *)
        | SMTExpr.Response r -> 
           fail_on_smt_error r; 
           failwith
             "SMT solver returned Success on check-sat"
             
        (* Return true if satisfiable *)
        | SMTExpr.Sat -> true

        (* Return false if unsatisfiable *)
        | SMTExpr.Unsat -> false

        (* Fail on unknown *)
        | SMTExpr.Unknown -> raise Unknown
      in

      (* Executing user-provided functions. *)
      let res = if sat then if_sat () else if_unsat () in

      res

    else
      (* Solver does not support check-sat-assuming, doing
         push/pop. *)

      (* Pushing. *)
      let _ = push solver in
      
      (* Asserting literals. *)
      literals |> Term.mk_and |> assert_term solver ;

      (* Performing check-sat. *)
      let sat = check_sat solver in

      (* Executing user-defined functions. *)
      let res = if sat then if_sat () else if_unsat () in

      (* Popping literals. *)
      pop solver ;

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


  (* ******************************************************************** *)
  (* Utiliy functions                                                     *)
  (* ******************************************************************** *)


  (* For a model return a conjunction of equations representing the model *)
  let term_of_model model = 

    Term.mk_and
      (List.map 
         (function (v, e) -> Term.mk_eq [Term.mk_var v; e])
         model)

  let get_interpolants solver args =
    
    let r,i = T.execute_custom_command solver "get-interpolants" args 1 in

    Term.mk_and (List.map (fun h -> SMTExpr.term_of_smtexpr (SMTExpr.expr_of_string_sexpr h)) i)

end
      
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
