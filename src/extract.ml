(*
This file is part of the Kind verifier

* Copyright (c) 2007-2012 by the Board of Trustees of the University of Iowa, 
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

let extract env term = 

  let eval_term t = Eval.eval_term t env in

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
              "%a@ to be@ %B" 
              Term.pp_print_term (Term.T.construct term)
              polarity
           in

           (* Fail on an unsatisfiable formula *)
           raise (Invalid_argument "Extract on unsatisfiable formula"))


        (* Propositional constant false to be true *)
        | `FALSE when polarity -> 

          (debug extract 
              "%a@ to be@ %B" 
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

                try 

                  (* Try to find one of the premises to be false and
                     return the extracted term from the first false
                     premise negated *)
                  (accum,
                   [((List.find 
                        (function t -> 
                          let v = eval_term t in 
                          Eval.value_is_unknown v || not (Eval.bool_of_value v))
                        p),
                     env,
                     false)])

                with Not_found -> 

                  (* Otherwise check if the conclusion is true *)
                  if Eval.bool_of_value (eval_term c) then 

                    (* Return conclusion *)
                    (accum, [(c, env, true)])

                  else 

                    (debug extract 
                        "%a@ to be@ %B" 
                        Term.pp_print_term (Term.T.construct term)
                        polarity
                     in

                     (* Fail on an unsatisfiable formula *)
                     raise 
                       (Invalid_argument "Extract on unsatisfiable formula"))

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

          (try 

             (* Extract from first false conjunct

                LATER: Optimize this by using some better heuristic for
                choosing one of the false conjuncts. We have terms that
                are already in the final conjunction in [accum], but it
                is probably not worth to extract from all false conjuncts
                and then hope that one of them is already in [accum]. *)
             (accum, 
              [((List.find 
                   (function t -> not (Eval.bool_of_value (eval_term t))) 
                   l),
                env,
                false)])


           (* All conjuncts are true *)
           with Not_found -> 

             (debug extract 
                 "%a@ to be@ %B" 
                 Term.pp_print_term (Term.T.construct term)
                 polarity
              in

              (* Fail on an unsatisfiable formula *)
              raise (Invalid_argument "Extract on unsatisfiable formula")))


        (* Boolean disjunction to be true *)
        | `OR when polarity -> 

          (try 

             (* Extract from first true disjunct 

                LATER: Optimize this by using some better heuristic for
                choosing one of the true disjuncts. We have terms that
                are already in the final conjunction in [accum], but it
                is probably not worth to extract from all true disjuncts
                and then hope that one of them is already in [accum]. *)
             (accum,
              [((List.find (function t -> Eval.bool_of_value (eval_term t)) l),
                env,
                true)])

           (* All disjuncts are false *)
           with Not_found -> 

             (debug extract 
                 "%a@ to be@ %B" 
                 Term.pp_print_term (Term.T.construct term)
                 polarity
              in

              (* Fail on an unsatisfiable formula *)
              raise (Invalid_argument "Extract on unsatisfiable formula")))

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

          (match l with

            (* Equality cannot be nullary *)
            | []  -> assert false
            | h :: tl -> 

              (* Equality is between Boolean terms? *)
              if Term.type_of_term h == Type.mk_bool () then 

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

              (* Condition is true? *)
              if Eval.bool_of_value (eval_term p) then

                (* Extract from term for true and positive condition *)
                (accum, [(p, env, true); (t, env, polarity)])

                (* Condition is false? *)
              else

                (* Extract from term for false and negative condition *)
                (accum, [(p, env, false); (f, env, polarity)])

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

        (* Boolean atoms *)
        | `IS_INT 
        | `TO_REAL
        | `TO_INT 
        | `DIVISIBLE _
        | `UF _ ->

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


  and extract_term_atom (bool, int) polarity env term = 

    let extract_term_atom_node fterm args =

      match fterm with 

        (* Lift if-then-else *)
        | Term.T.App (sym, _) when Symbol.node_of_symbol sym = `ITE -> 

          (

            match args with 

              | [(_, p); (t', t); (f', f)] -> 

                (* Evaluate predicate to true or false *)
                if Eval.bool_of_value (eval_term p) then 

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

    in

    (* Lift ites from term *)
    let stack', term' = 
      Term.T.eval_t
        extract_term_atom_node 
        (Term.T.construct term)
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

  (Term.mk_and literals_bool, Term.mk_and literals_int)

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
