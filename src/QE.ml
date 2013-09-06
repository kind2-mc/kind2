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

(* Use configured SMT solver *)
module ConfiguredSolver = SMTSolver.Make (Config.SMTSolver)

(* Extended functions *)
module Solver = SolverMethods.Make (ConfiguredSolver)


(* The current solver instance in use *)
let solver_qe = ref None 

(* The current solver instance in use *)
let solver_check = ref None 

(* Get the current solver instance or create a new instance *)
let get_solver_instance () = 

  (* Solver instance created before? *)
  match !solver_qe with 

    (* Need to create a new instance *)
    | None -> 
 
      (* Create solver instance *)
      let solver =     
        Solver.new_solver 
          ~produce_assignments:true
          `UFLIA
      in
      
      (* Save instance *)
      solver_qe := Some solver;

      (* Z3 needs this option, default is 5 and we get let definitions
         for deeper terms *)
      ignore
        (Solver.T.execute_custom_command 
           solver
           "set-option"
           [SMTExpr.ArgString ":PP_MAX_DEPTH"; 
            SMTExpr.ArgString "65536"]
           0);

      (* Return instance *)
      solver

    (* Return existing instance *)
    | Some s -> s 
  



(* Get the current solver instance or create a new instance *)
let get_checking_solver_instance () = 

  (* Solver instance created before? *)
  match !solver_check with 

    (* Need to create a new instance *)
    | None -> 

      (* Create solver instance *)
      let solver =     
        Solver.new_solver 
          ~produce_assignments:true
          `UFLIA
      in
      
      (* Save instance *)
      solver_check := Some solver;

      (* Return instance *)
      solver

    (* Return existing instance *)
    | Some s -> s 
  

(* Kill created solver instances *)
let on_exit () = 

  (* Delete solver instance if created *)
  (try 
     match !solver_qe with 
       | Some s -> 
         Solver.delete_solver s; 
         solver_qe := None
       | None -> ()
   with 
     | e -> 
       Event.log `PDR Event.L_error 
         "Error deleting solver_qe: %s" 
         (Printexc.to_string e));


  (* Delete solver instance if created *)
  (try 
     match !solver_check with 
       | Some s -> 
         Solver.delete_solver s; 
         solver_check := None
       | None -> ()
   with 
     | e -> 
       Event.log `PDR Event.L_error
         "Error deleting solver_check: %s" 
         (Printexc.to_string e))


(* Static hashconsed strings *)
let s_goal = HString.mk_hstring "goal"    
let s_goals = HString.mk_hstring "goals"    

let rec conj_of_goal accum = function 

  (* At the end of the goal list *)
  | [] -> List.rev accum

  (* Parameters ":precision" or ": depth" also mark end of goal list *)
  | HStringSExpr.Atom a :: tl 
      when HString.sub a 0 1 = ":" -> List.rev accum
      
  (* Take first goal and convert to term, recurse for next goal in list *)
  | t :: tl -> 

     conj_of_goal 
       (SMTExpr.term_of_smtexpr (SMTExpr.expr_of_string_sexpr t) :: accum)
       tl


(* Extract the goal term from a goal 

   (goal {term}+ :precision precise :depth 1)

*)
let goal_to_term = function 

  | HStringSExpr.List (HStringSExpr.Atom s :: c) when s == s_goal -> 

    conj_of_goal [] c

(*
    (* Return [true] for empty list of goals, the goal atom for a
       singleton list and a conjunction of goals otherwise *)
    (match conj_of_goal [] c with 
      | [] -> Term.mk_true ()
      | [g] -> g
      | l -> Term.mk_and l)
  *)
    
  (* Invalid S-expression as result *)
  | e -> 

    raise 
      (Failure 
         ("SMT solver returned unexpected result for goal"))


(* Extract the goal terms from a list of goals 

   (goals (goal {term} :precision precise :depth 1) ) 

*)
let goals_to_terms = function 

  (*   (goals (goal true :precision precise :depth 1) ) *)
  | HStringSExpr.List 
      [HStringSExpr.Atom s; HStringSExpr.List g] when s == s_goals -> 
    
    goal_to_term (HStringSExpr.List g)
      
  (* Invalid S-expression as result *)
  | _ -> 
    raise 
      (Failure 
         ("SMT solver returned unexpected result for goals"))

(* Create a formula from the assignments in a model *)
let formula_of_model model = 

  (* Create conjunctions of equations *)
  Term.mk_and 
    (List.map (function (v, e) -> Term.mk_eq [Term.mk_var v; e]) model)
  

let term_of_psummand = function 
  | (c, Some v) -> Term.mk_times [Term.mk_num_of_int c; v]
  | (c, None) -> Term.mk_num_of_int c

let term_of_pterm = function 
  | [] -> Term.mk_false ()
  | l -> 
    let l' =
      match List.map term_of_psummand l with
        | [] -> Term.mk_num_of_int 0 
        | [t] -> t
        | l -> Term.mk_plus l
    in

    Term.mk_gt [l'; Term.mk_num_of_int 0]

let term_of_pformula = function 
  | [] -> Term.mk_true ()
  | [t] -> term_of_pterm t
  | l -> Term.mk_and (List.map term_of_pterm l)


let check_implication prem_str conc_str prem conc = 

  (* Get or create a Z3 instance to check the results *)
  let solver_check = get_checking_solver_instance () in

  (* Push context *)
  Solver.push solver_check;

  (* Assert constraint for premise *)
  Solver.fail_on_smt_error 
    (Solver.T.assert_expr 
       solver_check 
       prem);

  (* Assert negation of conclusion *)
  Solver.fail_on_smt_error 
    (Solver.T.assert_expr 
       solver_check 
       (Term.mk_not conc));

  (match 
      Solver.T.execute_custom_check_sat_command 
        "(check-sat-using (then qe smt))" 
        solver_check 
   with
     | SMTExpr.Unsat -> (debug qe "%s implies %s" prem_str conc_str end)
     | SMTExpr.Sat -> failwith (prem_str ^ " does not imply " ^ conc_str)
     | _ -> failwith "Failed to check implication");
  
  
(*
  (* Check if premise implies conclusion *)
  (match CheckSolver.check_sat solver_check with 
    | SMTExpr.Unsat -> (debug qe "%s implies %s" prem_str conc_str end)
    | SMTExpr.Sat -> failwith (prem_str ^ " does not imply " ^ conc_str)
    | _ -> failwith "Failed to check implication");
*)

  (* Pop context *)
  Solver.pop solver_check
  
(* Check generalization: model must imply quantifier eliminated term
   and quantifier eliminated term must imply the original quantifier
   term *)
let check_generalize model elim term term' = 

  (* Substitute fresh variables for terms to be eliminated and
     existentially quantify formula *)
  let qe_term = 
    SMTExpr.quantified_smtexpr_of_term true elim term
  in

  check_implication 
    "model"
    "exact generalization" 
    (SMTExpr.smtexpr_of_term (formula_of_model model))
    (SMTExpr.smtexpr_of_term term');

  check_implication
    "exact generalization" 
    "formula"
    (SMTExpr.smtexpr_of_term term') 
    qe_term
    


(* From a conjunction of Boolean state variables return a conjunction
   only containing the state variables not to be eliminated *)
let qe_bool elim term = 

  (* Get node of hashconsed term and flatten *)
  let term_flat = Term.destruct term in

  (* Get conjuncts from conjunction *)
  let conjs = match term_flat with 

    (* Top node is a conjunction *)
    | Term.T.App (s, l) when Symbol.node_of_symbol s = `AND -> l

    (* Extract returns a conjunction *)
    | l -> [term]

  in
  
  let elim_as_term = List.map Term.mk_var elim in

  let conjs' = 
    List.filter 
      (function t -> not (List.memq (Term.unnegate t) elim_as_term))
      conjs
  in

(*
  (* Only keep terms T or ~T where T = S evaluates to false for all
     terms S to be eliminated *)
  let conjs' = 
    List.filter 
      (function t -> 
        List.for_all
          (function s -> 
            not 
              (Eval.bool_of_value 
                 (Eval.eval_term 
                    (Term.mk_eq [Term.unnegate t; Term.mk_var s]) []))  )
          elim)
      conjs
  in
*)

  (* Return conjunction *)
  conjs'

(*

    (* Rebuild a conjunction *)
    Term.mk_and 
    (* Destruct the given term *)
    (Term.apply_top
       term
       (function 
         (* We only expect a conjunction *)
         | `AND -> 
           (function l -> 

             (* Filter the arguments of the conjunction *)
             List.filter 
               (function t -> 

                 (* Only keep terms T or ~T where T = S evaluates to
                    false for all terms S to be eliminated *)
                 List.for_all
                   (function s -> 
                     not 
                       (Eval.bool_of_value 
                          (Eval.eval_term 
                             (Term.mk_eq [Term.unnegate t; s]) []))  )
                   elim)
               l)
         | _ -> (function _ -> failwith "Extracted term must be a conjunction"))
    )
    
*)

let generalize model (elim : Var.t list) term =

  (debug qe
     "@[<hv>Generalizing@ @[<hv>%a@]@]@."
     Term.pp_print_term 
     term end);

  (debug qe
     "@[<hv>with the model@ @[<hv>%a@]@]@."
     Term.pp_print_term (Solver.term_of_model model)
     end);
  
  (* Extract active path from term and model *)
  let extract_bool, extract_int = Extract.extract model term in

  (debug qe
     "@[<hv>Extracted term:@ @[<hv>%a@]@]@."
     Term.pp_print_term 
     extract_int end);

  (debug qe
     "@[<hv>Extracted term Booleans:@ @[<hv>%a@]@]@."
     Term.pp_print_term 
     extract_bool end);
(*
  check_implication 
    "extract"
    "term"
    (SMTExpr.smtexpr_of_term (Term.mk_and [extract_bool; extract_int]))
    (SMTExpr.smtexpr_of_term term);
*)
  (* Partition list of state variables into Boolean and integer variables *)
  let elim_bool, elim_int =
    List.partition
      (function v -> 
        match Type.node_of_type (Var.type_of_var v) with 
          | Type.Bool -> true
          | Type.IntRange _
          | Type.Int -> false
          | Type.Real -> false
          | _ -> 
            (invalid_arg 
              ("Can only generalize terms with integer or Boolean " ^
                  "state variables")))
      elim
  in
  
  (* Eliminate from extracted Boolean conjunction *)
  let term'_bool = qe_bool elim_bool extract_bool in

  (debug qe
     "@[<hv>QE for Booleans:@ @[<hv>%a@]@]@."
     Term.pp_print_term 
     (Term.mk_and term'_bool) end);

  let term' = match Flags.pdr_qe () with 
    
    | `Z3 ->

      (

        (* Substitute fresh variables for terms to be eliminated and
           existentially quantify formula *)
        let qe_term = 
          SMTExpr.quantified_smtexpr_of_term true elim term
          (* SMTExpr.quantified_smtexpr_of_term true elim extract_int *)
        in
        
        let solver_qe = get_solver_instance () in

  (* SMTLIB commands for Z3
     
     (declare-fun y (Int) Int)
     (assert (exists ((x Int)) (> x (y 0))))
     (apply qe)
     
     Output:
     
     (goals (goal true :precision precise :depth 1) )
     
  *)
        
        (* Increment scope level *)
        Solver.push solver_qe;
        
        (* Assert expression to eliminate quantifiers from *)
        Solver.fail_on_smt_error 
          (Solver.T.assert_expr solver_qe qe_term);
        
        (* Eliminate quantifiers *)
        let res = 
          match 
            
            (* Execute custom command (apply qe) *)
            Solver.T.execute_custom_command 
              solver_qe 
              "apply"
              [SMTExpr.ArgString "qe"]
              1
              
          with

            (* Catch error *)
            | SMTExpr.Error e, _ -> 
              raise 
                (Failure ("SMT solver failed: " ^ e))

            (* Catch unsupported command *)
            | SMTExpr.Unsupported, _ -> 
              raise 
                (Failure 
                   ("SMT solver reported not implemented"))
                
            (* Catch silence *)
            | SMTExpr.NoResponse, _ ->
              raise 
                (Failure 
                   ("SMT solver did not produce a reply"))
                
            (* Return result on success *)
            | SMTExpr.Success, r -> r
        in
        
        (* Take first goal as quantifier eliminated term *)
        let term'_int = goals_to_terms (List.hd res) in
        
        (* Decrement scope level to remove assertion *)
        Solver.pop solver_qe;
(*
        (* Check generalizations *)
        check_generalize 
          model 
          elim 
          term 
          (Term.mk_and [term'_bool; term'_int]);
*)

        (* Return quantifier eliminated term *)
        (* Term.mk_and [term'_bool; term'_int] *)

        term'_int

      )

    | `Cooper ->

      (

        (* Convert term to Presburger formula *)
        let cf = Presburger.to_presburger elim_int extract_int in
        
        (debug qe
           "@[<hv>In Presburger:@ @[<v>%a@]@]@."
           Poly.pp_print_cformula
           cf 
         end);

        (*
        check_implication 
          "presburger normalization"
          "integer extract"
          (SMTExpr.smtexpr_of_term (Presburger.term_of_cformula cf))
          (SMTExpr.smtexpr_of_term extract_int);


        check_implication 
          "integer extract"
          "presburger normalization"
          (SMTExpr.smtexpr_of_term extract_int)
          (SMTExpr.smtexpr_of_term (Presburger.term_of_cformula cf));
        *)


        (* Eliminate quantifiers *)
        let elim_pformula = 
          CooperQE.eliminate model elim_int cf  
        in
        
        (debug qe
           "@[<hv>Cooper QE:@ @[<v>%a@]@]"
           Poly.pp_print_cformula
           elim_pformula
         end);

        (* Convert quantifier eliminated Presburger formula to term *)
        let term'_int = Presburger.term_of_cformula elim_pformula in

        (*
        (* Check generalizations *)
        check_generalize 
          model 
          elim 
          term 
          (Term.mk_and [term'_bool; term'_int]);
        *)

        (* Return quantifier eliminated term *)
        term'_bool @ term'_int

      )


  in

  (debug qe "QE term %a" Term.pp_print_term (Term.mk_and term') end);

  (* Return quantifier eliminated term *)
  term'

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
