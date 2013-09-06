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

module type S =
sig

  exception Unknown

  module T : SMTSolver.S

  type t 

  val new_solver : ?produce_assignments:bool -> ?produce_models:bool -> ?produce_proofs:bool -> ?produce_cores:bool -> SMTExpr.logic -> t
    
  val delete_solver : t -> unit
    
  val fail_on_smt_error : SMTExpr.response -> unit

  val assert_term : t -> Term.t -> unit

  val push : ?n:int -> t -> unit

  val pop : ?n:int -> t -> unit

  val check_sat : ?timeout:int -> t -> bool

  val get_model : t -> Var.t list -> (Var.t * Term.t) list

  val get_unsat_core : t -> int list

  val check_sat_term : ?timeout:int -> t -> Term.t list -> bool

  val check_sat_term_model : ?timeout:int -> t -> Term.t list -> bool * (Var.t * Term.t) list 

  val check_entailment : ?timeout:int -> t -> Term.t list -> Term.t -> bool

  val check_entailment_cex : ?timeout:int -> t -> Term.t list -> Term.t -> bool * (Var.t * Term.t) list 

  val term_of_model : (Var.t * Term.t) list -> Term.t

end

module Make (S : SMTSolver.S) : S with type t = S.t and type T.t = S.t =
struct

  exception Unknown
  
  (* The encapsulated module for lower level access to the solver *)
  module T = struct include S end


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
      ?(produce_assignments = false)
      ?(produce_models = false) 
      ?(produce_proofs = false) 
      ?(produce_cores = false)
      logic =

    (* Create solver instance *)
    let solver =     
      S.create_instance 
        ~produce_assignments
        ~produce_models
        ~produce_proofs
        ~produce_cores
        logic
    in

(*

    (

      match 

        (* Declare uninterpreted function symbols *)
        SMTExpr.declare_smt_symbols (S.declare_fun solver)

      with

        | SMTExpr.NoResponse -> 
          (Event.log 
             0 
             ("Error: Could not initialize SMT Solver." ^^ 
                 "No response when declaring uninterpreted symbols"))

        | SMTExpr.Unsupported -> 
          (Event.log 
             0 
             ("Error: Could not initialize SMT Solver." ^^ 
                 "Solve replied unsupported when declaring uninterpreted symbols"))

        | SMTExpr.Error e -> 
          (Event.log 
             0 
             ("Error: Could not initialize SMT Solver." ^^ 
                 "%s when declaring uninterpreted symbols")
             e)

        | SMTExpr.Success -> ()

    );
*)

    (* Declare uninterpreted function symbols *)
    fail_on_smt_error 
      (SMTExpr.declare_smt_symbols (S.declare_fun solver));

    (* Return solver instance *)
    solver


  (* Delete a solver instance *)
  let delete_solver solver = 

    (* Delete solver instance *)
    S.delete_instance solver 


  (* ******************************************************************** *)
  (* Primitives                                                           *)
  (* ******************************************************************** *)

  (* Assert a formula in the current context *)
  let assert_term solver term = 

    (* Convert term to SMT expression *)
    let expr = SMTExpr.smtexpr_of_term term in
    
    (* Assert SMT expression in solver instance and fail on error *)
    fail_on_smt_error (S.assert_expr solver expr)
      

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
        S.get_value solver (List.map SMTExpr.smtexpr_of_var vars) 
          
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
          (SMTExpr.var_of_smtexpr v, SMTExpr.term_of_smtexpr e))
        smt_model
    in

    (* Return model *)
    model


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
          List.map (function s -> Scanf.sscanf s "t%d" (function x -> x)) c

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
        let vars = TransSys.vars_of_term (Term.mk_and terms) in
        
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
          TransSys.vars_of_term 
            (Term.mk_and ((Term.mk_not conc) :: prems)) 
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


end
      
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
