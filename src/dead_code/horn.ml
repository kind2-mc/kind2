(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

module SVS = StateVar.StateVarSet


let s_set_info = HString.mk_hstring "set-info"

let s_set_logic = HString.mk_hstring "set-logic"

let s_horn = HString.mk_hstring "HORN"

let s_declare_fun = HString.mk_hstring "declare-fun"

let s_pred = HString.mk_hstring "p"

let s_assert = HString.mk_hstring "assert"

let s_check_sat = HString.mk_hstring "check-sat"

(*

horn ::= 
  |   (forall (quantified-variables) body) 
  |   (not (exists (quantified-variables) co-body)) 

body ::= 
  |   (=> co-body body)
  |   (or literal* )
  |   literal

co-body ::=
  |   (and literal* )
  |   literal

literal ::=
  |   formula over interpreted relations (such as =, <=, >, ...)
  |   (negated) uninterpreted predicate with arguments

A body has at most one uninterpreted relation with positive polarity, 
and a co-body uses only uninterpreted relations with positive polarity.

*)

module H = Hashcons


(* Collect literals from a horn clause body *)
let rec literals_of_body accum = function

  (* All expressions parsed, return *)
  | [] -> accum

  (* Take first expression *)
  | (polarity, expr) :: tl -> match Term.destruct expr with 

    (* Expression is a disjunction in a body or a conjunction in a
       co-body *)
    | Term.T.App (s, l) 
      when 
        (polarity && s == Symbol.s_or) ||
        (not polarity && s == Symbol.s_and) -> 

      (* Parse disjuncts or conjuncts as body or co-body, respectively *)
      literals_of_body 
        accum 
        ((List.map (function d -> (polarity, d)) l) @ tl)

    (* Expression is an implication of arity zero *)
    | Term.T.App (s, []) when polarity && s == Symbol.s_implies -> 

      assert false

    (* Expression is an implication in a body *)
    | Term.T.App (s, l :: r) when polarity && s == Symbol.s_implies -> 

      (* Parse *)
      literals_of_body 
        accum
        ((false, l) :: 
         (polarity, 
          match r with 
            | [] -> assert false 
            | [d] -> d
            | _ -> Term.mk_implies r) :: 
         tl)

    (* Expression is a literal, add to accumulator *)
    | _ -> 

      literals_of_body
        ((if not polarity then Term.negate expr else expr) :: accum) 
        tl


(* Return list of literals of a horn clause *)
let clause_of_expr expr = 

  (* Return a list of temporary variables to instantiate a lambda
     abstraction with *)
  let instantiate_lambda lambda =

    (* Get sorts of binders in lambda abstraction *)
    let sorts = Term.T.sorts_of_lambda lambda in 

    (* For each sort create a temporary variable *)
    let vars = 
      List.map
        (function t -> Term.mk_var (Var.mk_fresh_var t)) 
        sorts 
    in

    (* Instantiate bound variables in lambda abstraction with fresh
       variables *)
    Term.T.instantiate lambda vars 

  in

  (* Get node of term *)
  match Term.T.node_of_t expr with 

    (* Universally quantified expression *)
    | Term.T.Forall l -> 

      (* Instantiate bound variables in lambda abstraction with fresh
         variables *)
      let l' = instantiate_lambda l in

      (* Get literals in body of horn clause *)
      let literals = literals_of_body [] [(true, l')] in

      literals

    (* Negated expression *)
    | Term.T.Node (s, [t]) when s == Symbol.s_not -> 

      (match Term.T.node_of_t t with 

        (* Negated existentially quantified expression *)
        | Term.T.Exists l -> 

          (* Instantiate bound variables in lambda abstraction with fresh
             variables *)
          let l' = instantiate_lambda l in

          (* Get literals in co-body of horn clause *)
          let literals = 
            literals_of_body
              [] 
              [(false, l')]
          in

          literals

        | _ -> 

          raise 
            (Invalid_argument 
               (Format.asprintf 
                  "Expression is not a horn clause: %a"
                  SMTExpr.pp_print_expr expr)))

    | _ -> 

      raise 
        (Invalid_argument 
           (Format.asprintf 
              "Expression is not a horn clause: %a"
              SMTExpr.pp_print_expr expr))

(*

   I(s) => p(s)
   p(s) & T(s, s') => p(s')
   p(s) & !Prop(s) => false

*)

(* Return the polarity of the monolithic predicate in a literal as
   Some true ot Some false. If the literal does not contain the
   predicate, return None. *)
let rec polarity_of_pred sym_p polarity expr = match Term.destruct expr with 

  | Term.T.App (s, a) when s == sym_p -> 

    Some 
      (polarity, 

       (* Extract variables from arguments to predicate *)
       List.map 
         (function t -> match Term.destruct t with 
            | Term.T.Var v -> v
            | _ -> 
              raise 
                 (Invalid_argument 
                    (Format.asprintf 
                       "Arguments of predicate must be variables %a"
                       Term.pp_print_term t)))
           a)
      
  | Term.T.App (s, [e]) when s == Symbol.s_not -> 
    polarity_of_pred sym_p (not polarity) e

  | _ -> None


(* Classify a clause, return a pair of Booleans indicating whether the
   clause contains the monolithic predicate with positive or negative
   polarity, respectively *)
let classify_clause sym_p literals =

  List.fold_left 
    (fun (pos, neg, accum) expr -> 

       (* Get polarity of predicate in literal *)
       match polarity_of_pred sym_p true expr with 
         | Some (true, args) -> 

           if pos = [] then (args, neg, accum) else

             raise 
               (Invalid_argument 
                  "Predicate must occur at most once positvely")

         | Some (false, args) -> 
           
           if neg = [] then (pos, args, accum) else 

             raise 
               (Invalid_argument 
                  "Predicate must occur at most once positvely")

         | None -> (pos, neg, (expr :: accum)))

    ([], [], [])
    literals


(* Return the list of temporary variables in the term *)
let temp_vars_of_term term = 

  Var.VarSet.elements
    (Term.eval_t
       (function 
         | Term.T.Var v when Var.is_temp_var v -> 
           (function [] -> Var.VarSet.singleton v | _ -> assert false)
         | Term.T.Var _
         | Term.T.Const _ -> 
           (function [] -> Var.VarSet.empty | _ -> assert false)
         | Term.T.App _ -> List.fold_left Var.VarSet.union Var.VarSet.empty
         | Term.T.Attr (t, _) -> 
           (function [s] -> s | _ -> assert false))
       term)
    

(* Bind each temporary variable to a fresh constant *)
let temp_vars_to_consts term = 

  let vars = temp_vars_of_term term in

  let consts = 
    List.map
      (function v -> 
        Term.mk_uf (UfSymbol.mk_fresh_uf_symbol [] (Var.type_of_var v)) [])
      vars
  in

  Term.mk_let 
    (List.combine vars consts)
    term


let next_fresh_state_var_id = ref 1

let mk_fresh_state_var var_type = 

  let res = 
    StateVar.mk_state_var 
      (Format.sprintf "I%d" !next_fresh_state_var_id)
      true
      var_type
  in

  incr next_fresh_state_var_id;

  res


(* Bind each temporary variable to a fresh state variable *)
let temp_vars_to_state_vars term = 

  let vars = temp_vars_of_term term in

  let _, state_vars = 
    List.fold_left
      (fun (i, a) v -> 
         (succ i,
          Term.mk_var
            (Var.mk_state_var_instance
               (mk_fresh_state_var (Var.type_of_var v))
               Numeral.zero) :: a))
      (1, [])
      vars
  in
  
  Term.mk_let 
    (List.combine vars (List.rev state_vars))
    term
       

let unlet_term term = Term.construct (Term.eval_t (fun t _ -> t) term)

(*

   I(s) => p(s)
   p(s) & T(s, s') => p(s')
   p(s) & !Prop(s) => false

*)



let rec let_for_args accum = function 

  (* No more terms in list *)
  | [] -> List.rev accum

  (* Term without equations *)
  | (t, []) :: tl -> let_for_args (t :: accum) tl

  (* Add term with let binding to accumulator *)
  | (t, e) :: tl -> let_for_args (Term.mk_let e t :: accum) tl

  (* Lists must be of equal length *)
  | _ -> raise (Invalid_argument "let_for_args")


let eq_to_let state_vars term accum = match term with

  (* An equation *)
  | Term.T.App (s, [l; r]) when s == Symbol.s_eq -> 

    (* Match left-hand side and right-hand side of equation *)
    (match Term.destruct l, Term.destruct r with

      (* Equation between state variable and free variable *)
      | Term.T.Var v1, Term.T.Var v2 when 
          SVS.mem 
            (Var.state_var_of_state_var_instance v1) 
            state_vars && 
          (not 
             (SVS.mem
                (Var.state_var_of_state_var_instance v2) 
                state_vars)) -> 
        
        (* Initialize accumulator with single equation, binding the
           free variable to the state variable *)
        (Term.construct term, [(v2, Term.mk_var v1)])

      (* Equation between state variable and free variable *)
      | Term.T.Var v1, Term.T.Var v2 when 
          SVS.mem
            (Var.state_var_of_state_var_instance v2)
            state_vars
          && 
          (not
             (SVS.mem
                (Var.state_var_of_state_var_instance v1)
                state_vars)) -> 
        
        (* Initialize accumulator with single equation, binding the
           free variable to the state variable *)
        (Term.construct term, [(v1, Term.mk_var v2)])
        
      (* Other equation, add let binding for collected equations *)
      | _ -> (Term.mk_eq (let_for_args [] accum), [])
        
    )

  (* Conjunction, can join equations from all conjuncts *)
  | Term.T.App (s, l) when s == Symbol.s_and -> 

    (* Keep term unchanged and concatenate lists of equations *)
    (Term.mk_and (List.map fst accum),
     List.concat (List.map snd accum))

  (* Neither conjunction nor equation, add respective collected
     equations as let binding to each subterm *)
  | Term.T.App (s, l) -> (Term.mk_app s (let_for_args [] accum), [])

  (* No equations for constants and variables *)
  | Term.T.Const s -> (Term.mk_const s, [])
  | Term.T.Var v -> (Term.mk_var v, [])

  (* Remove attributed terms *)
  | Term.T.Attr (t, _) -> (t, snd (List.hd accum))


let solve_eqs state_vars term =

  unlet_term
    (match Term.eval_t (eq_to_let state_vars) term with
      | t, [] -> t
      | t, e -> Term.mk_let e t)
                

let add_expr_to_trans_sys transSys literals vars_0 vars_1 var_pos var_neg = 

  let state_vars = 
    List.fold_left
      (fun a e -> SVS.add e a)
      SVS.empty
      (List.map Var.state_var_of_state_var_instance vars_0)
  in

  match var_pos, var_neg with 

    | [], [] -> 

      raise 
        (Failure 
           (Format.asprintf 
              "Clause without occurrence of predicate %a"
              HString.pp_print_hstring s_pred))


    (* Predicate occurs only negated: property clause 

       p(s) & !Prop(s) => false

    *)
    | [], _ -> 

      let term = 
        unlet_term
          (temp_vars_to_state_vars
             (Term.mk_let 
                (List.combine var_neg (List.map Term.mk_var vars_0))
                (Term.mk_or literals)))
      in

      let term' = if true then solve_eqs state_vars term else term in

      transSys.TransSys.props <- ("P", term') :: transSys.TransSys.props


    (* Predicate occurs only positive: initial state constraint

       I(s) => p(s)
       
    *)
    | _, [] -> 

      let term = 
        unlet_term
          (temp_vars_to_state_vars
             (Term.mk_let 
                (List.combine var_pos (List.map Term.mk_var vars_0))
                (Term.mk_and (List.map Term.negate literals))))
      in

      let term' = if true then solve_eqs state_vars term else term in

      transSys.TransSys.init_constr <- term' :: transSys.TransSys.init_constr


    (* Predicate occurs positive and negative: transition relation

        p(s) & T(s, s') => p(s')
       
    *)
    | _, _ -> 

      let term = 
        unlet_term
          (temp_vars_to_state_vars
             (Term.mk_let 
                (List.combine var_neg (List.map Term.mk_var vars_0))
                (Term.mk_let 
                   (List.combine var_pos (List.map Term.mk_var vars_1))
                   (Term.mk_and (List.map Term.negate literals)))))
      in

      let term' = if true then solve_eqs state_vars term else term in

      transSys.TransSys.constr_constr <- term' :: transSys.TransSys.constr_constr


let rec parse sym_p_opt lexbuf transSys = 

  (* Parse S-expression *)
  match 
    
    (try
       
       Some (SExprParser.sexp SExprLexer.main lexbuf) 
         
     with End_of_file -> None)

  with 

    | None -> transSys

    | Some s -> match s with 

      (* (set-info ...) *)
      | HStringSExpr.List (HStringSExpr.Atom s :: _) when s == s_set_info -> 
        
        (* Skip *)
        parse sym_p_opt lexbuf transSys

      (* (set-logic HORN) *)
      | HStringSExpr.List [HStringSExpr.Atom s; HStringSExpr.Atom l]
        when s == s_set_logic && l == s_horn -> 

        (* Skip *)
        parse sym_p_opt lexbuf transSys

      (* (set-logic ...) *)
      | HStringSExpr.List [HStringSExpr.Atom s; e] when s == s_set_logic -> 

        raise 
          (Failure 
             (Format.asprintf 
                "@[<hv>Invalid logic %a, must be HORN" 
                HStringSExpr.pp_print_sexpr e))

      (* (declare-fun p a r) *)
      | HStringSExpr.List 
          [HStringSExpr.Atom s; 
           HStringSExpr.Atom p; 
           HStringSExpr.List a; 
           (HStringSExpr.Atom _ as r)]
        when s == s_declare_fun && p == s_pred -> 

        (* Types of argument of monolithic predicate *)
        let arg_types = List.map SMTExpr.type_of_string_sexpr a in

        (* Types of result of monolithic predicate *)
        let res_type = SMTExpr.type_of_string_sexpr r in

        (* Declare predicate *)
        let sym_p = 
          Symbol.mk_symbol 
            (`UF 
               (UfSymbol.mk_uf_symbol
                  (HString.string_of_hstring p) 
                  arg_types 
                  res_type))
        in

        let _, vars_0, vars_1 =
          List.fold_left 
            (fun (i, vars_0, vars_1) t -> 
               
               let sv = 
                 StateVar.mk_state_var
                   (Format.sprintf "Y%d" i)
                   true
                   t
               in
               
               (succ i, 
                (Var.mk_state_var_instance sv Numeral.zero) :: vars_0, 
                (Var.mk_state_var_instance sv Numeral.one) :: vars_1))
            (1, [], [])
            arg_types
        in

        (* Continue *)
        parse 
          (Some (sym_p, List.rev vars_0, List.rev vars_1)) 
          lexbuf 
          transSys

      (* (declare-fun ...) *)
      | HStringSExpr.List (HStringSExpr.Atom s :: e :: _) 
        when s == s_declare_fun -> 

        raise 
          (Failure 
             (Format.asprintf 
                "@[<hv>Invalid predicate declaration %a, only the monolithic predicate %a allowed@]" 
                HStringSExpr.pp_print_sexpr e
                HString.pp_print_hstring s_pred))

      (* (assert ...) *)
      | HStringSExpr.List [HStringSExpr.Atom s; e] when s == s_assert -> 

        (match sym_p_opt with 

          | None -> 

            raise 
              (Failure 
                 (Format.asprintf 
                    "Predicate %a must be declared before assert"
                    HString.pp_print_hstring s_pred))

          | Some (sym_p, vars_0, vars_1) -> 

            let expr = SMTExpr.expr_of_string_sexpr e in

            let clause = clause_of_expr expr in

            let var_pos, var_neg, clause' = classify_clause sym_p clause in

            add_expr_to_trans_sys
              transSys 
              clause' 
              vars_0 
              vars_1 
              var_pos 
              var_neg;

         (* Continue *)
         parse sym_p_opt lexbuf transSys)


      (* (check-sat) *)
      | HStringSExpr.List [HStringSExpr.Atom s] when s == s_check_sat -> 

        (* Skip *)
        parse sym_p_opt lexbuf transSys

      | e -> 

        raise 
          (Failure 
             (Format.asprintf 
                "@[<hv>Unexpected S-expression@ @[<hv 1>%a@]@]" 
                HStringSExpr.pp_print_sexpr e))


(* Parse SMTLIB2 Horn format from channel *)
let of_channel in_ch =   

  (* Initialise buffer for lexing *)
  let lexbuf = Lexing.from_channel in_ch in

  parse None lexbuf TransSys.empty


(* Parse SMTLIB2 Horn format from file *)
let of_file filename = 

  (* Open the given file for reading *)
  let use_file = open_in filename in
  let in_ch = use_file in

  let transSys = of_channel in_ch in

  debug horn
     "%a"
     TransSys.pp_print_trans_sys transSys
  in

  transSys

      
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
