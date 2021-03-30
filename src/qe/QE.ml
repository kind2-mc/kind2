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

module VS = Var.VarSet

exception QuantifiedTermFound of Term.t

(* The current solver instance in use *)
let solver_qe = ref None 

(* The current solver instance in use *)
let solver_check = ref None

let initial_ubound = Numeral.zero

let ubound = ref initial_ubound

let get_ubound () = !ubound

let set_ubound bound = ubound := bound

let get_qe_solver () =
  match Flags.Smt.qe_solver () with
  | `Z3_SMTLIB -> `Z3_SMTLIB
  | `CVC4_SMTLIB -> `CVC4_SMTLIB
  | _ -> failwith "No QE solver found"

(* Get the current solver instance or create a new instance *)
let get_solver_instance trans_sys = 

  (* Solver instance created before? *)
  match !solver_qe with 

    (* Need to create a new instance *)
    | None -> 
 
      (* Create solver instance *)
      let solver = SMTSolver.create_instance
          ~produce_assignments:true
          (TermLib.add_quantifiers (TransSys.get_logic trans_sys))
          (get_qe_solver ())
      in

      SMTSolver.trace_comment 
        solver
        (Format.sprintf 
           "Declaring state variables: %s@."
           (string_of_t 
              (pp_print_list Var.pp_print_var ",@ ") 
              (TransSys.vars_of_bounds trans_sys Numeral.zero !ubound)));
      
      (* Defining uf's and declaring variables. *)
      TransSys.define_and_declare_of_bounds
        trans_sys
        (SMTSolver.define_fun solver)
        (SMTSolver.declare_fun solver)
        (SMTSolver.declare_sort solver)
        Numeral.zero !ubound;
      
      SMTSolver.trace_comment solver "Defining predicates";

      (*
      (* Define functions *)
      TransSys.iter_uf_definitions 
        trans_sys
        (SMTSolver.define_fun solver); 
      *)
      
      (* Save instance *)
      solver_qe := Some solver;

(*
      (* Z3 needs this option, default is 5 and we get let definitions
         for deeper terms *)
      ignore
        (SMTSolver.T.execute_custom_command 
           solver
           "set-option"
           [SMTExpr.ArgString ":pp.max_depth"; 
            SMTExpr.ArgString "65536"]
           0);
*)

      (* Return instance *)
      solver

    (* Return existing instance *)
    | Some s -> s 
  



(* Get the current solver instance or create a new instance *)
let get_checking_solver_instance trans_sys = 

  (* Solver instance created before? *)
  match !solver_check with 

    (* Need to create a new instance *)
    | None -> 

      (* Create solver instance with support for quantifiers *)
      let solver =     
        SMTSolver.create_instance 
          ~produce_assignments:true
          (* add quantifiers to system logic *)
          (TermLib.add_quantifiers (TransSys.get_logic trans_sys))
          (Flags.Smt.solver ())
      in
(*
      (* Declare uninterpreted function symbols *)
      TransSys.declare_vars_of_bounds
        trans_sys
        (SMTSolver.declare_fun solver)
        Numeral.zero
        Numeral.one;

      (* Define functions *)
      TransSys.iter_uf_definitions 
        trans_sys
        (SMTSolver.define_fun solver); 
*)
  (* Defining uf's and declaring variables. *)
      TransSys.define_and_declare_of_bounds
        trans_sys
        (SMTSolver.define_fun solver)
        (SMTSolver.declare_fun solver)
        (SMTSolver.declare_sort solver)
        Numeral.zero !ubound;

      (* Save instance *)
      solver_check := Some solver;

      (* Return instance *)
      solver

    (* Return existing instance *)
    | Some s -> s 
  

(* Kill created solver instances and reset ubound *)
let on_exit () = 

  ubound := initial_ubound ;

  (* Delete solver instance if created *)
  (try 
     match !solver_qe with 
       | Some s -> 
         SMTSolver.delete_instance s; 
         solver_qe := None
       | None -> ()
   with 
     | e -> 
       KEvent.log L_error 
         "Error deleting solver_qe: %s" 
         (Printexc.to_string e));


  (* Delete solver instance if created *)
  (try 
     match !solver_check with 
       | Some s -> 
         SMTSolver.delete_instance s; 
         solver_check := None
       | None -> ()
   with 
     | e -> 
       KEvent.log L_error
         "Error deleting solver_check: %s" 
         (Printexc.to_string e))


(* Create a formula from the assignments in a model *)
let formula_of_model model = 

  (* Create conjunctions of equations *)
  Term.mk_and 
    (List.map (function (v, e) -> Term.mk_eq [Term.mk_var v; e]) model)



(*
let check_implication trans_sys prem_str conc_str prem conc = 

  (* Get or create a solver instance to check the results *)
  let solver_check = get_checking_solver_instance trans_sys in

  (* Push context *)
  SMTSolver.push solver_check;

  (* Assert constraint for premise *)
  SMTSolver.assert_expr solver_check prem;

  (* Assert negation of conclusion *)
  SMTSolver.assert_expr solver_check (Term.mk_not conc);

  (match 
     SMTSolver.execute_custom_check_sat_command 
       "(check-sat-using (then qe smt))" 
       solver_check 
   with
     | `Unsat -> (Debug.qe "%s implies %s" prem_str conc_str)
     | `Sat -> failwith (prem_str ^ " does not imply " ^ conc_str)
     | _ -> failwith "Failed to check implication");
  
  
(*
  (* Check if premise implies conclusion *)
  (match SMTSolver.check_sat solver_check with 
    | false -> (Debug.qe "%s implies %s" prem_str conc_str)
    | true -> failwith (prem_str ^ " does not imply " ^ conc_str));
*)

  (* Pop context *)
  SMTSolver.pop solver_check
  
(* Check generalization: model must imply quantifier eliminated term
   and quantifier eliminated term must imply the original quantifier
   term *)
let check_generalize trans_sys model elim term term' =

  (* Substitute fresh variables for terms to be eliminated and
     existentially quantify formula *)
  let qe_term = 
    Conv.quantified_smtexpr_of_term true elim term
  in

  check_implication 
    trans_sys
    "model"
    "exact generalization" 
    (Conv.smtexpr_of_term (formula_of_model model))
    (Conv.smtexpr_of_term term');

  check_implication
    trans_sys
    "exact generalization" 
    "formula"
    (Conv.smtexpr_of_term term')
    qe_term
    
*)

(* From a conjunction of Boolean state variables return a conjunction
   only containing the state variables not to be eliminated *)
let qe_bool elim terms = 

  let elim_as_term = List.map Term.mk_var elim in

  List.filter 
    (function t -> not (List.memq (Term.unnegate t) elim_as_term))
    terms

(*

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

  (* Return conjunction *)
  conjs'

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


(* Split a list of terms into a list of equational definitions of
   given variables and a list of the remaining terms *)
let rec collect_eqs vars (eqs, terms) = function 

  (* All elements processed *)
  | [] -> (eqs, terms)

  (* Head element of list *)
  | term :: tl -> match Term.destruct term with

    (* FIXME: Do this on both sides, and be careful to not produce cycles *)

    (* Term is an equation with a variable in [vars] on left-hand side *)
    | Term.T.App (s, [v; e]) when
        (Symbol.equal_symbols s Symbol.s_eq)
        && (Term.is_free_var v)
        && (List.exists (Var.equal_vars (Term.free_var_of_term v)) vars) -> 

      (* Variable on left- or right-hand side *)
      let v = Term.free_var_of_term v in

      (try 

         (* Find previous equation for variable 

            If there are two equations for one variable, v = e1 and 
            v = e2, rewrite v to e1 in v = e2 to e1 = e2 *)
         let _, e' = 
           List.find
             (fun (u, e') -> Var.equal_vars v u)
             eqs
         in

         (* Rewrite second equation to e = e' *)
         let term' = Term.mk_eq [e; e'] in

         (* Add rewritten equation to list of equations *)
         collect_eqs vars (eqs, (term' :: terms)) tl

       (* No previous equation for variable *)
       with Not_found ->

         (* Left-hand side must not be equal to right-hand side *)
         if Term.equal (Term.mk_var v) e then

           (* Remove reflexive equation *)
           collect_eqs vars (eqs, terms) tl

         else

           (* Add equation as rewrite rule *)
           collect_eqs vars ((v, e) :: eqs, terms) tl)

    | _ -> 

      (* Add term to constraints *)
      collect_eqs vars (eqs, term :: terms) tl


(* 

   TODO: Check for cyclic definitions. Lustre input should be safe. *)
let rec order_defs accum = function 

  | [] -> accum

  | (v, e) :: tl -> 

    if 

      (* Definition is already in the accumulator? *)
      List.exists (fun (u, _) -> Var.equal_vars u v) accum

    then

      (* Drop duplicate definition and continue *)
      (* order_defs accum tl *)
      assert false 

    else
      
      (* Get all variables of term whose definitions are on the stack
         below *)
      let dep =
        VS.filter
          (fun v -> 
             List.exists (fun (u, _) -> Var.equal_vars v u) tl)
          (Term.vars_of_term e)
      in

      (* No definitions is on the stack below *)
      if VS.is_empty dep then 

        (* Add definition to accumulator and continue *)
        order_defs ((v, e) :: accum) tl
            
      else
          
          (* Filter out all definitions *)
          let defs_hd, defs_tl = 
            List.partition
              (fun (u, _) -> VS.exists (Var.equal_vars u) dep) 
              tl
          in

          (* Continue with definitions the variable depends on top of
             the stack *)
          order_defs 
            accum
            (defs_hd @ (v, e) :: defs_tl)


let solve_eqs vars terms = 

  (* Split list of definitions from list of terms *)
  let eqs, terms' = collect_eqs vars ([], []) terms in 

  (* Order list of definitions by dependency *)
  let eqs' = order_defs [] eqs in

  Debug.qe
    "@[<v>@[<hv>Equations:@ @[<hv>%a@]@]@,@[<hv>Terms:@ @[<hv>%a@]@]@]"
    (pp_print_list 
       (fun ppf (v, t) -> Format.fprintf ppf "%a = %a" Var.pp_print_var v Term.pp_print_term t)
       ",@ ")
    eqs'
    (pp_print_list Term.pp_print_term ",@ ")
    terms';

  let rec subst_defs term = 

    (* Variables of term *)
    let vars = Term.vars_of_term term in
    
    match 
      
      (* Get definitions for variables of term *)
      List.filter
        (fun (v, _) -> VS.exists (Var.equal_vars v) vars) 
        eqs' 

    with

      (* Return term if no variable can be substituted *)
      | [] -> term

      | defs -> 

        (* Let-bind variables to definitions *)
        let term' = Term.mk_let defs term in

        (* Recurse to substitute introduced variables *)
        subst_defs term'

  in
    
  List.map subst_defs terms'
         






let generalize trans_sys uf_defs model elim term =

  let qe_method = Flags.QE.qe_method () in

  (* Partition list of state variables into Boolean and integer variables *)
  let elim_bool, elim_rest =
    match qe_method with
    | `Cooper -> (
      List.partition
        (fun v ->
          match Type.node_of_type (Var.type_of_var v) with
          | Type.Bool -> true
          | Type.IntRange _
          | Type.Int -> false
          | _ -> raise Presburger.Not_in_LIA
        )
        elim
    )
    | _ -> (
      List.partition
        (fun v ->
          match Type.node_of_type (Var.type_of_var v) with
          | Type.Bool -> true
          | _ -> false
        )
        elim
    )
  in

  Debug.qe
    "@[<hv>Generalizing@ @[<hv>%a@]@]@ for variables@ @[<hv>%a@]@."
    Term.pp_print_term term
    (pp_print_list Var.pp_print_var ",@ ") elim;

  Debug.qe
    "@[<hv>with the model@ @[<hv>%a@]@]@."
    Model.pp_print_model model;

  if Term.has_quantifier term then begin
    raise (QuantifiedTermFound term)
  end;

  (* Extract active path from term and model *)
  let extract_bool, extract_rest = Extract.extract uf_defs model term in

  Debug.qe
    "@[<hv>Extracted term:@ @[<hv>%a@]@]@."
    (pp_print_list Term.pp_print_term "@ ")
    extract_rest;

  Debug.qe
    "@[<hv>Extracted term Booleans:@ @[<hv>%a@]@]@."
    (pp_print_list Term.pp_print_term "@ ")
    extract_bool;

  (* Eliminate from extracted Boolean conjunction *)
  let term'_bool = qe_bool elim_bool extract_bool in

  let extract_rest = Term.mk_and (solve_eqs elim_rest extract_rest) in

  Debug.qe
    "@[<hv>Extracted term simplified:@ @[<hv>%a@]@]@."
    Term.pp_print_term
    extract_rest;
(*
  check_implication 
    trans_sys
    "extract"
    "term"
    (SMTExpr.smtexpr_of_term 
       (Term.mk_and [Term.mk_and extract_bool; extract_rest]))
    (SMTExpr.smtexpr_of_term term);
*)
  Debug.qe
    "@[<hv>QE for Booleans:@ @[<hv>%a@]@]@."
    Term.pp_print_term 
    (Term.mk_and term'_bool);

  let term' = match qe_method with
    
    | `Precise
    | `Impl
    | `Impl2 ->
      
      (
        let solver_qe = get_solver_instance trans_sys in

        (* Substitute fresh variables for terms to be eliminated and
           existentially quantify formula *)
        let qe_term =
          let module Conv = (val SMTSolver.converter solver_qe) in
          match qe_method with
            | `Cooper -> assert false
            | `Precise -> 
              Conv.quantified_smtexpr_of_term true elim term
            | `Impl
            | `Impl2 -> 
              Conv.quantified_smtexpr_of_term true elim extract_rest
        in

        let term'_rest = SMTSolver.get_qe_expr solver_qe qe_term in
(*
        (* Check generalizations *)
        check_generalize 
          trans_sys
          (Model.to_list model |> List.map (fun (vr, vl) -> 
             match vl with
             | Model.Term t -> (vr, t)
             | _ -> assert false)
          )
          elim 
          term 
          (Term.mk_and [Term.mk_and term'_bool; Term.mk_and term'_rest]);
*)
        (* Return quantifier eliminated term *)
        (match qe_method with
          | `Cooper -> assert false
          | `Precise -> term'_rest
          | `Impl -> term'_bool @ term'_rest
          | `Impl2 -> 

            (* Extract again from result *)
            let term''_rest, term''_bool = 
                Extract.extract uf_defs model (Term.mk_and term'_rest) 
            in
            
            term'_bool @ [Term.mk_and term''_rest; Term.mk_and term''_bool])
        
      )

    | `Cooper ->

      let elim_int = elim_rest in
      let extract_int = extract_rest in

      if extract_int = Term.t_true then (

        term'_bool

      )

      else

      (
        (* Convert term to Presburger formula *)
        let cf = Presburger.to_presburger elim_int extract_int in
        
        Debug.qe
          "@[<hv>In Presburger:@ @[<v>%a@]@]@."
          Poly.pp_print_cformula
          cf;
(*
        check_implication 
          trans_sys
          "presburger normalization"
          "integer extract"
          (SMTExpr.smtexpr_of_term (Presburger.term_of_cformula cf))
          (SMTExpr.smtexpr_of_term extract_int);


        check_implication 
          trans_sys
          "integer extract"
          "presburger normalization"
          (SMTExpr.smtexpr_of_term extract_int)
          (SMTExpr.smtexpr_of_term (Presburger.term_of_cformula cf));
*)
        (* Eliminate quantifiers *)
        let elim_pformula = 
          CooperQE.eliminate model elim_int cf  
        in
        
        Debug.qe
          "@[<hv>Cooper QE:@ @[<v>%a@]@]"
          Poly.pp_print_cformula
          elim_pformula;

        (* Convert quantifier eliminated Presburger formula to term *)
        let term'_int = Presburger.term_of_cformula elim_pformula in
(*
        (* Check generalizations *)
        check_generalize 
          trans_sys
          model 
          elim 
          term 
          (Term.mk_and [Term.mk_and term'_bool; Term.mk_and term'_int]);
*)
        (* Return quantifier eliminated term *)
        term'_bool @ term'_int

      )


  in

  Debug.qe "QE term %a" Term.pp_print_term (Term.mk_and term');

  (* Return quantifier eliminated term *)
  term'


type response = Valid of Term.t | Invalid of Term.t

let ae_val_gen trans_sys premise elim conclusion =

  (* Create new solver instance *)
  let solver =
    SMTSolver.create_instance
      ~produce_assignments:true
      (TransSys.get_logic trans_sys)
      (Flags.Smt.solver ())
  in

  TransSys.define_and_declare_of_bounds
    trans_sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.zero Numeral.one;

  SMTSolver.assert_term solver premise ;

  let rec loop valid_region =

    if not (SMTSolver.check_sat solver) then (

      Valid (Term.mk_or valid_region)

    )

    else (
      SMTSolver.push solver;

      SMTSolver.assert_term solver conclusion;

      if not (SMTSolver.check_sat solver) then

        Invalid (Term.mk_or valid_region)

      else (

        let m = SMTSolver.get_model solver in

        let gen_term =
          try
            generalize
              trans_sys
              (TransSys.uf_defs trans_sys)
              m
              elim
              conclusion
          with Presburger.Not_in_LIA -> (

            KEvent.log
              L_info
              "Problem contains real valued variables, \
               switching off approximate QE";

            Flags.QE.set_qe_method `Impl;

            generalize
              trans_sys
              (TransSys.uf_defs trans_sys)
              m
              elim
              conclusion
          )
        in

        let projection = Term.mk_and gen_term in

        (* Format.printf "MBP: %a@." Term.pp_print_term projection; *)

        SMTSolver.pop solver;

        SMTSolver.assert_term solver (Term.negate projection) ;

        loop (projection :: valid_region)
      )

    )

  in

  let res = loop [] in

  SMTSolver.delete_instance solver;

  res


let ae_val_prec trans_sys premise elim conclusion =

  (* Create new solver instance *)
  let solver =
    SMTSolver.create_instance
      (TermLib.add_quantifiers (TransSys.get_logic trans_sys))
      (Flags.Smt.solver ())
  in

  TransSys.define_and_declare_of_bounds
    trans_sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.zero Numeral.one;

  SMTSolver.push solver;

  SMTSolver.assert_term solver premise ;

  let res =

    if not (SMTSolver.check_sat solver) then (

      Valid (Term.t_false)

    )

    else (

      SMTSolver.assert_term solver conclusion;

      if not (SMTSolver.check_sat solver) then

        Invalid (Term.t_false)

      else (

        SMTSolver.pop solver;

        let impl = Term.mk_implies [premise; conclusion] in

        let ex_term = Term.mk_exists elim impl in

        let term =
          SMTSolver.get_qe_term solver ex_term
          |> Term.mk_and
        in

        let simpl_term =
          SMTSolver.simplify_term solver (Term.mk_and [premise; term])
        in

        SMTSolver.assert_term solver (Term.negate term) ;

        if not (SMTSolver.check_sat solver) then
          Valid simpl_term
        else
          Invalid simpl_term

      )

    )
  in

  SMTSolver.delete_instance solver;

  res

let ae_val trans_sys premise elim conclusion =
  if Flags.QE.ae_val_use_ctx () then
    ae_val_prec trans_sys premise elim conclusion
  else
    ae_val_gen trans_sys premise elim conclusion

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
