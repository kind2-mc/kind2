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


(* Construct a set of variables of a list *)
let var_set_of_list = 
  List.fold_left (fun a e -> Var.VarSet.add e a) Var.VarSet.empty 
    

(* Cache for variables of terms *)
let vars_of_term_cache = Term.TermHashtbl.create 101


(* Return variables of term *)
let vars_of_term term =

  try 

    (* Return variables of term from cache *)
    Term.TermHashtbl.find vars_of_term_cache term 

  with Not_found -> 

    (* Return variables of term as a list *)
    Var.VarSet.elements 

      (* Return variables of term and add variables of all subterms to
         cache *)
      (Term.eval_t 
         (function 
           | Term.T.Var v -> 
             (function
               |  [] -> 

                 (* Start with singleton set *)
                 let var_set = Var.VarSet.singleton v in
                 
                 (* Add to hash table as a list of variables, this
                    probably takes up less memory than storing the set *)
                 Term.TermHashtbl.replace 
                   vars_of_term_cache 
                   term 
                   (Var.VarSet.elements var_set);
                 
                 (* Return set as accumulator *)
                 var_set

            | _ -> assert false)

        | Term.T.Const _ -> 
          
          (function 
            | [] -> 

              (* Add to hash table as a list of variables, this
                 probably takes up less memory than storing the set *)
              Term.TermHashtbl.replace 
                vars_of_term_cache 
                term 
                [];

              (* Start with empty set in accumulator *)
              Var.VarSet.empty 

            | _ -> assert false)

        | Term.T.App _ -> 

          (function l -> 

            (* Take union of set of variables of subterms *)
            let var_set = 
              List.fold_left 
                Var.VarSet.union 
                Var.VarSet.empty 
                l 
            in
            
            (* Add to hash table as a list of variables, this probably
               takes up less memory than storing the set *)
            Term.TermHashtbl.replace 
              vars_of_term_cache 
              term 
              (Var.VarSet.elements var_set);
            
            (* Return set as accumulator *)
            var_set

          )
          
        | Term.T.Attr (t, _) -> 
          (function [s] -> s | _ -> assert false))
         
         term)



let choose_term (bool_terms, int_terms) = 

  function 

    (* No candidate terms *)
    | [] -> raise Not_found 

    | h :: tl as terms -> 

      (* Heuristic to choose terms *)
      match Flags.pdr_extract () with 

        (* Always pick the first term *)
        | `First -> List.hd terms 

        (* Pick the term with the fewest new integer variables *)
        | `Vars -> 

          (debug extract
              "choose_term candidates:@ @[<hv 1>[%a]@]"
              (pp_print_list Term.pp_print_term ";@ ") terms
           in

          (* Collect variables in accumulator in a set *)
          let vars_accum = 
            Term.TermSet.fold 
              (fun t a -> 
                Var.VarSet.union a (var_set_of_list (vars_of_term t)))
              (Term.TermSet.union int_terms bool_terms) 
              Var.VarSet.empty 
          in

          (* Calculate number of variables if term was added to 
             accumulator *)
          let num_of_vars_of_union term = 
            let res = 
              Var.VarSet.cardinal 
                (Var.VarSet.union
                   vars_accum 
                   (var_set_of_list (vars_of_term term)))
            in

            debug extract
                "Number of variables with@ %a@ is %d"
                Term.pp_print_term term
                res
            in

            res

          in
          
          let term, _ = 
            List.fold_left
              (fun (t, s) t' -> 
                 let s' = num_of_vars_of_union t' in
                 if s' < s then (t', s') else (t, s))
              (h, num_of_vars_of_union h)
              tl
          in

          (debug extract
              "choose_term picked@ %a"
              Term.pp_print_term term
           in
           
           term))


let extract uf_defs env term = 

  let eval_term t = 
    let res = Eval.eval_term uf_defs env t in

    debug extract 
        "@[<v>%a@ evaluates to@ @[<hv>%a@]@]" 
        Term.pp_print_term t
        Term.pp_print_term (Eval.term_of_value res)
    in

    res

  in

  (* Extract active path from a term *)
  let rec extract_term ((bool, int) as accum) = function 

    (* No more terms to extract from *)
    | [] -> (Term.TermSet.elements bool, Term.TermSet.elements int)

    (* Extract from top element on stack *)
    | (term, env, polarity) :: tl ->

      (* Obtain new accumulator and new terms to extract *)
      let accum', stack' = 
        extract_term_flat accum polarity env (Term.T.destruct term) 
      in

      (* Continue extracting with changed accumulator *)
      extract_term accum' (List.rev_append stack' tl)

  and extract_term_flat ((bool, int) as accum) polarity env = function 

    (* Constant *)
    | Term.T.Const s as term -> 

      (match Symbol.node_of_symbol s with

        (* Propositional constant true to be true *)
        | `TRUE when polarity -> 

          (* No need to add "true" to conjunction *)
          (accum, [])


        (* Propositional constant true to be false *)
        | `TRUE -> 

          (debug extract 
              "@[<hv 1>%a@]@ to be@ %B" 
              Term.pp_print_term (Term.T.construct term)
              polarity
           in

           (* Fail on an unsatisfiable formula *)
           raise (Invalid_argument "Extract on unsatisfiable formula"))


        (* Propositional constant false to be true *)
        | `FALSE when polarity -> 

          (debug extract 
              "@[<hv 1>%a@]@ to be@ %B" 
              Term.pp_print_term (Term.T.construct term)
              polarity
           in

           (* Fail on an unsatisfiable formula *)
           raise (Invalid_argument "Extract on unsatisfiable formula"))


        (* Propositional constant false to be false *)
        | `FALSE -> 

          (* No need to add "true" to conjunction *)
          (accum, [])


        (* No other constants are Boolean *)
        | _ -> assert false

      )

    (* Function application *)
    | Term.T.App (s, l) as term -> 

      (match Symbol.node_of_symbol s with

        (* Boolean negation *)
        | `NOT -> 

          (* Extract from subterm with negated polarity *)
          (match l with 
            | [] -> assert false
            | [t] -> (accum, [(t, env, not polarity)])
            | _ -> assert false)


        (* Boolean implication to be true *)
        | `IMPLIES when polarity ->

          (

            (* Implication is right-associative, a -> b -> ... -> c is
               equivalent to ~a | ~b | ... | c. An implication is true
               if one of the premises is false or the conclusion is
               true.

               Reverse list of arguments to obtain conclusion [c] and
               premises [p]. *)
            match List.rev l with 

              (* Nullary implication not allowed *)
              | [] -> assert false 

              | c :: p -> 

                (* Candidate terms are premises that are false *)
                let cand_terms_prem = 
                  List.filter
                    (function t -> 
                      let v = eval_term t in 
                      not (Eval.bool_of_value v))
                    p
                in

                (* Candidiate terms from premise and conclusion *)
                let cand_terms = 

                  (* Check if the conclusion is true *)
                  if Eval.bool_of_value (eval_term c) then 

                    (* Conclusion is a candidate term *)
                    c :: cand_terms_prem 

                  else

                    (* Conclusion is not a candidate term *)
                    cand_terms_prem 

                in

                (* Choose term to extract from *)
                let term' = 

                  try 

                    (* Use heuristic to choose term from candidates *)
                    choose_term accum cand_terms 

                  with Not_found -> 

                    (debug extract 
                        "@[<hv 1>%a@]@ to be@ %B" 
                        Term.pp_print_term (Term.T.construct term)
                        polarity
                     in

                     (* Fail on an unsatisfiable formula *)
                     raise 
                       (Invalid_argument
                          "Extract on unsatisfiable formula"))

                in

                (* Extract with positive polarity if chosen term is
                     conclusion, otherwise with negative polarity *)
                (accum,
                 [(term', env, Term.equal term' c)])

          )


        (* Boolean implication to be false *)
        | `IMPLIES -> 

          (

            (* Implication is right-associative, a -> b -> ... -> c is
               equivalent to ~a | ~b | ... | c. An implication is
               false if all premises are true and the conclusion is
               false.

               Reverse list of arguments to obtain conclusion [c] and
               premises [p]. *)
            match List.rev l with 

              (* Nullary implication is syntactically not allowed *)
              | [] -> assert false 

              | c :: p -> 

                (* Return conjunction of premises and negated conclusion
                   in original order *)
                (accum,
                 (List.rev
                    ((c, env, false) ::
                     (List.map 
                        (function e -> 
                          (e, env, true))
                        p))))

          )


        (* Boolean conjunction to be true *)
        | `AND when polarity ->

          (* Extract from each conjunct *)
          (accum, (List.map (function c -> (c, env, true)) l))


        (* Boolean conjunction to be false *)
        | `AND -> 

          (

            (* Candidate terms are conjuncts that are false *)
            let cand_terms = 
              List.filter
                (function t -> not (Eval.bool_of_value (eval_term t))) 
                l
            in

            (* Choose term to extract from *)
            let term' = 

              try 

                (* Use heuristic to choose term from candidates *)
                choose_term accum cand_terms 

              with Not_found -> 

                (debug extract 
                    "@[<hv 1>%a@]@ to be@ %B" 
                    Term.pp_print_term (Term.T.construct term)
                    polarity
                 in

                 (* Fail on an unsatisfiable formula *)
                 raise 
                   (Invalid_argument
                      "Extract on unsatisfiable formula"))

            in

            (* Extract with negative polarity from chosen term *)
            (accum, [(term', env, false)])

          )

        (* Boolean disjunction to be true *)
        | `OR when polarity -> 

          (

            (* Candidate terms are disjuncts that are true *)
            let cand_terms = 
              List.filter
                (function t -> Eval.bool_of_value (eval_term t)) 
                l
            in

            (* Choose term to extract from *)
            let term' = 

              try 

                (* Use heuristic to choose term from candidates *)
                choose_term accum cand_terms 

              with Not_found -> 

                (debug extract 
                    "@[<hv 1>%a@]@ to be@ %B" 
                    Term.pp_print_term (Term.T.construct term)
                    polarity
                 in

                 (* Fail on an unsatisfiable formula *)
                 raise 
                   (Invalid_argument
                      "Extract on unsatisfiable formula"))

            in

            (* Extract with positive polarity from chosen term *)
            (accum, [(term', env, true)])

          )

        (* Boolean disjunction to be false *)
        | `OR -> 

          (* Extract from each disjunct *)
          (accum, (List.map (function c -> (c, env, false)) l))

        (* TODO: Boolean exclusive disjunction to be true *)
        | `XOR when polarity = true -> assert false

        (* TODO: Boolean exclusive disjunction to be false  *)
        | `XOR -> assert false

        (* Equality *)
        | `EQ as s -> 

          (debug extract 
              "@[<hv 1>%a@]@ %a to be@ %B" 
              Term.pp_print_term (Term.T.construct term)
              Type.pp_print_type (Term.type_of_term (Term.T.construct term))
              polarity
           in

           match l with

             (* Equality cannot be nullary *)
             | []  -> assert false
             | h :: tl -> 

               (* Equality is between Boolean terms? *)
               if Term.type_of_term h == Type.t_bool then 

                 (

                   match polarity with 

                     (* Equality to be true *)
                     | true ->

                       (* First argument is true? *)
                       if Eval.bool_of_value (eval_term h) then

                         (* All arguments must be true *)
                         (accum, 
                          (List.map 
                             (function c -> (c, env, true))
                             l))

                       else

                         (* All arguments must be false *)
                         (accum, 
                          (List.map 
                             (function c -> (c, env, false))
                             l))

                     (* Equality to be false *)
                     | false ->

                       (* Choose one true and one false term *)
                       (accum,
                        [((List.find 
                             (function t -> Eval.bool_of_value (eval_term t)) 
                             l),
                          env,
                          true);
                         ((List.find 
                             (function t -> 
                               not (Eval.bool_of_value (eval_term t)))
                             l),
                          env,
                          false)])

                 )

               else 

                 (match l with 

                   (* Comparison functions must have arity greater than one *)
                   | [] 
                   | _ :: [] -> assert false 

                   (* Comparison of arity two *)
                   | [l; r] -> 

                     extract_term_atom accum polarity env term 

(*
                    (* Split equation into l <= r && l >= r and extract
                       from the conjunction for conversion to Presburger
                       arithmetic *)
                    (accum, 
                     [(Term.T.mk_app 
                         (Symbol.mk_symbol `AND) 
                         [Term.T.mk_app (Symbol.mk_symbol `LEQ) [l; r];
                          Term.T.mk_app (Symbol.mk_symbol `GEQ) [l; r]], 
                       env, 
                       polarity)])
*)                    

                   | l -> 

                     let l' = chain_list l in 

                     (accum, 
                      [(Term.T.mk_app (Symbol.mk_symbol `AND) 
                          (List.map (Term.T.mk_app (Symbol.mk_symbol s)) l'), 
                        env, 
                        polarity)])

                 )

          )

        (* TODO: Boolean exclusive disjunction to be true *)
        | `DISTINCT ->  assert false

        (* if-then-else *)
        | `ITE -> 

          (match l with

            (* ite must be ternary *)
            | [p; t; f]  -> 

              if Term.type_of_term t == Type.t_bool then 

                (* Condition is true? *)
                if Eval.bool_of_value (eval_term p) then

                  (* Extract from term for true and positive condition *)
                  (accum, [(p, env, true); (t, env, polarity)])

                (* Condition is false? *)
                else

                  (* Extract from term for false and negative condition *)
                  (accum, [(p, env, false); (f, env, polarity)])

              else

                extract_term_atom accum polarity env term 

            (* Non-ternary ite *)
            | _ -> assert false 

          )

        (* Chainable Boolean atoms, to be regarded as a conjunction *)
        | `LEQ
        | `LT
        | `GEQ
        | `GT as s ->

          (match l with

            (* Comparison functions must have arity greater than one *)
            | [] 
            | _ :: [] -> assert false 

            (* Comparison of arity two *)
            | [_; _] -> extract_term_atom accum polarity env term 

            (* Comparison of arity greater than two *)
            | l -> 

              (* Turn list into a list of binary lists *)
              let l' = chain_list l in 

              (* Extract from conjunction of binary comparisons *)
              (accum, 
               [(Term.T.mk_app 
                   (Symbol.mk_symbol `AND) 
                   (List.map (Term.T.mk_app (Symbol.mk_symbol s)) l'), 
                 env, 
                 polarity)])

          )

        | `UF uf_symbol ->

          (try 

             let (vars, uf_def) = 
               List.assq uf_symbol uf_defs 
             in

             debug extract1
                 "@[<v>Definition of %a:@,variables@ %a@,term@ %a@]"
                 UfSymbol.pp_print_uf_symbol uf_symbol
                 (pp_print_list Var.pp_print_var "@ ") vars
                 Term.pp_print_term uf_def
             in

             let term' = 
               Term.mk_let 
                 (List.fold_right2
                    (fun var def accum -> (var, def) :: accum)
                    vars
                    l
                    [])
                 uf_def
             in

             debug extract
                 "@[<v>Substituted definition for %a in@,%a@,yields@,%a@]" 
                 UfSymbol.pp_print_uf_symbol uf_symbol
                 Term.pp_print_term (Term.construct term)
                 Term.pp_print_term term'
             in

             (accum, [term', env, polarity])

           with Not_found -> 

             (* Extract from subterms with undefined polarity *)
             extract_term_atom accum polarity env term 

          )

        (* Boolean atoms *)
        | `IS_INT 
        | `TO_REAL
        | `TO_INT 
        | `DIVISIBLE _ ->

          (match l with 

            (* Terms must not be nullary *)
            | [] -> assert false 

            (* Term is an application to subterms *)
            | l -> 

              (* Extract from subterms with undefined polarity *)
              extract_term_atom accum polarity env term 

          )

        | _ -> assert false

      )

    (* Variable *)
    | Term.T.Var v -> 

      let term' = Term.mk_var v in

      (* Add boolean variable to accumulator *)
      ((Term.TermSet.add
          (if polarity then term' else Term.mk_not term')
          bool, 
        int), 
       [])


    | Term.T.Attr (t, _) -> (accum, [t, env, polarity])




  and extract_term_atom (bool, int) polarity env term = 

    let extract_term_atom_node fterm args =

      match fterm with 

        (* Lift if-then-else *)
        | Term.T.App (sym, _) when Symbol.node_of_symbol sym = `ITE -> 

          (

            match args with 

              | [(_, p); (t', t); (f', f)] -> 

                (* Evaluate predicate to true or false *)
                if 

                  try 
                    
                    Eval.bool_of_value (eval_term p) 

                  with Invalid_argument s -> 

                    debug extract2
                        "%s for@ %a@ evaluating@ %a"
                        s
                        Term.pp_print_term p
                        Term.pp_print_term (Term.construct fterm)
                    in
                    
                    assert false

                then 

                  (* Extract from p and t, return left branch *)
                  ((p, env, true) :: t', t)

                else 

                  (* Extract from p and f, return right branch *)
                  ((p, env, false) :: f', f)

              (* if-then-else must be ternary *)
              | _ -> assert false

          )

        (* Construct new term *)
        | Term.T.App (sym, _) -> 

          let (accum', args') = List.split args in 
          (List.concat accum', Term.T.mk_app sym args')

        (* Keep other terms *)
        | Term.T.Var _ 
        | Term.T.Const _ -> ([], Term.T.construct fterm)

        | Term.T.Attr (t, _) -> 
          match args with [(a, _)] -> (a, t) | _ -> assert false

    in

    (* Lift ites from term *)
    let stack', term' = 
      (try 

         Term.T.eval_t
           extract_term_atom_node 
           (Term.T.construct term)

       with Invalid_argument s -> 

         debug extract2
             "%s for@ %a"
             s
             Term.pp_print_term (Term.T.construct term)
         in

         assert false)


    in

    debug extract
        "@[<hv>extract_term_atom_node: term' = @ %a@]" 
        Term.pp_print_term term'
    in

    let term'' = term' in

    ((bool, 
      Term.TermSet.add 
        (if polarity then term'' else Term.mk_not term'') 
        int), 
     stack')

  in

  let literals_bool, literals_int = 
    extract_term 
      (Term.TermSet.empty, Term.TermSet.empty)
      [(term, env, true)] 
  in

  (literals_bool, literals_int)

(*

let main () = 

  let print_term = Format.printf "%a@." Term.pp_print_term in
  let v_x = StateVar.mk_state_var "X" (Type.mk_int ()) in
  let v_y = StateVar.mk_state_var "Y" (Type.mk_bool ()) in
  let v_x_0 = Var.mk_state_var_instance v_x (numeral_of_int 0) in
  let v_y_1 = Var.mk_state_var_instance v_y (numeral_of_int 1) in
  let v_y_2 = Var.mk_state_var_instance v_y (numeral_of_int 2) in
  let v_y_3 = Var.mk_state_var_instance v_y (numeral_of_int 3) in
  let v_y_4 = Var.mk_state_var_instance v_y (numeral_of_int 4) in

  let t = 
    Term.mk_ite 
      (Term.mk_implies [Term.mk_var v_y_3; Term.mk_var v_y_4]) 
      (Term.mk_ite 
         (Term.mk_leq [Term.mk_var v_x_0; Term.mk_num_of_int 2]) 
         (Term.mk_var v_y_1) 
         (Term.mk_var v_y_2)) 
      (Term.mk_var v_y_3) 
  in

  let b, i = 
    extract 
      [(v_x_0, Term.mk_num_of_int 3);
       (v_y_1, Term.mk_true ());
       (v_y_2, Term.mk_true ());
       (v_y_3, Term.mk_true ()); 
       (v_y_4, Term.mk_false ())]
      t in

  print_term t; 
  print_term b; 
  print_term i


;;

main ()

*)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
