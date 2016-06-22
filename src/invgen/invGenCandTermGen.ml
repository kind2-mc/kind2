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
module TSet = Term.TermSet

module CandidateTermGen = struct

  (* Short name for sets of terms. *)
  module TSet = Term.TermSet


  (* Bool type. *)
  let bool_type = Type.t_bool

  (* Constructs a term. *)
  let flat_to_term = Term.construct

  (* The name of a transition system. *)
  let name_of_sys sys =
    TransSys.scope_of_trans_sys sys |> String.concat "/"



  (* Aggregates state var rules. *)
  module StateVarRules : sig

    (* Applies the state var rules. *)
    val apply: StateVar.t list -> TSet.t -> TSet.t

  end = struct

    (* If svar is an IntRang(low,up) and low < up, generates terms low
     <= x, x <= up, and x=n where x is an IntRange (low,up)
     (n\in[low,up]). *)
    let rec unroll_ranges svar set =
      
      (* Creates the terms for an intrange. *)
      let rec unroll_range set low up var =
        if Numeral.(low > up)
        then set
        else
          unroll_range
            (TSet.add (Term.mk_eq [var ; Term.mk_num low]) set)
            (Numeral.succ low)
            up
            var
      in

      let var =
        Var.mk_state_var_instance svar Numeral.zero
        |> Term.mk_var
      in

      match StateVar.type_of_state_var svar |> Type.node_of_type with

      | Type.IntRange (low,up) when not Numeral.(low = up) ->
         
         unroll_range set low up var
         |> TSet.add
              (Term.mk_leq [ Term.mk_num low ; var ])
         |> TSet.add
              (Term.mk_leq [ var ; Term.mk_num up ])

      | _ -> set

               
    (* Generates x>=0 for int and real variables. *)
    let arith_zero_eqs svar set =

      match StateVar.type_of_state_var svar |> Type.node_of_type with

      | Type.Int ->

         (* Variable at 0. *)
         let var =
           Var.mk_state_var_instance svar Numeral.zero
           |> Term.mk_var
         in

         TSet.add
           (Term.mk_geq [ var ; Term.mk_num Numeral.zero ])
           set

      | Type.Real ->

         (* Variable at 0. *)
         let var =
           Var.mk_state_var_instance svar Numeral.zero
           |> Term.mk_var
         in

         TSet.add
           (Term.mk_geq [ var ; Term.mk_dec Decimal.zero ])
           set

      | _ -> set


    (* Add boolean variables and their negation. *)
    let bool_vars svar set =
      match StateVar.type_of_state_var svar |> Type.node_of_type with

      | Type.Bool ->

         (* Variable at 0. *)
         let var =
           Var.mk_state_var_instance svar Numeral.zero
           |> Term.mk_var
         in
         
         set
         (* Adding variable. *)
         |> TSet.add var
         (* Adding negation of the variable. *)
         |> TSet.add (Term.mk_not var)

      | _ -> set



    let rule_list =
      [ unroll_ranges, true_of_unit ;
        arith_zero_eqs, true_of_unit ;
        bool_vars, true_of_unit ]

    let apply svars set =
      svars
      (* To all svars... *)
      |> List.fold_left
           ( fun set' svar ->
             if StateVar.for_inv_gen svar
             then
               rule_list
               (* ...apply all rules... *)
               |> List.fold_left
                    ( fun set'' (rule,condition) ->
                      (* ...if their condition is true. *)
                      if condition ()
                      then rule svar set''
                      else set'' )
                    set'
             else set')
           set

  end


  (* Aggregate rules on flat terms. *)
  module FlatTermsRules : sig

    (* Applies the state var rules. *)
    val apply: Term.T.flat -> TSet.t -> TSet.t

  end = struct

    (* Adds term to set if term has type bool. *)
    let must_be_bool term set =
      if Term.type_of_term term == bool_type
      then TSet.add term set
      else set

    (* Returns true if the term mentions at least a non-constant
       variable. *)
    let has_var term =
      Term.vars_of_term term
      |> Var.VarSet.exists
           ( fun var -> not (Var.is_const_state_var var) )

    let rec is_var_or_const term =
      match Term.destruct term with
      | Term.T.App (_,_) -> false
      | Term.T.Attr (kid,_) -> is_var_or_const kid
      | _ -> true

    let rec is_const term =
      match Term.destruct term with
      | Term.T.App (_,_) -> false
      | Term.T.Var _ -> false
      | Term.T.Attr (kid,_) -> is_const kid
      | _ -> true

    let rec is_var term =
      match Term.destruct term with
      | Term.T.App (_,_) -> false
      | Term.T.Const _ -> false
      | Term.T.Attr (kid,_) -> is_var kid
      | _ -> true

    (* Adds term to set if term is bool and is not [AND|NOT]. *)
    let bool_terms flat set = match flat with

      | Term.T.App (sym, kids) ->

         (* if ( (is_var kid1) && (is_const kid2) ) *)
         (*   || ( (is_var kid2) && (is_const kid1) ) then *)
         if List.for_all is_var_or_const kids then
           
           ( match Symbol.node_of_symbol sym with

             | `GT
             | `LT
             | `OR
             | `XOR
             | `DISTINCT
(*
             | `BVULT
*)
             | `IS_INT ->
                TSet.add (flat_to_term flat) set

             | _ -> set )

         else set

      | _ -> set


    (* If term is an arithmetic atom "lhs op rhs" add "lhs >= rhs" and
       "lhs <= rhs". *)
    let arith_atoms flat set = match flat with

      | Term.T.App (sym, ((kid1 :: kid2 :: []) as kids)) ->

        (* The inequality has to be a 'small' one. Either var op
           const, const op var, orr var op var. *)
        if ( (is_var kid1) && (is_const kid2) )
           || ( (is_var kid2) && (is_const kid1) )
           (*|| ( (is_var kid1) && (is_var kid2) )*)
        then

          ( match Symbol.node_of_symbol sym with

            | `EQ ->

                (* Making sure it's an arith equality. *)
              ( match
                  kid1 |> Term.type_of_term |> Type.node_of_type
                with

                  | Type.Int
                  | Type.Real ->
                     (* It is, adding >= and <=. *)
                    set
                    (* |> TSet.add (flat_to_term term) *)
                    |> TSet.add (Term.mk_geq kids)
                    |> TSet.add (Term.mk_leq kids)
                  | _ -> set )

            | `LEQ -> set
              |> TSet.add (Term.mk_geq kids)
              |> TSet.add (Term.mk_leq kids)

            | `GEQ -> set
              |> TSet.add (Term.mk_geq kids)
              |> TSet.add (Term.mk_leq kids)

            | `GT  -> set
              |> TSet.add (flat_to_term flat)
              |> TSet.add (Term.mk_geq kids)
              |> TSet.add (Term.mk_leq kids)

            | `LT  -> set
              |> TSet.add (flat_to_term flat)
              |> TSet.add (Term.mk_geq kids)
              |> TSet.add (Term.mk_leq kids)

            | _ -> set )

        else set
             
      | _ -> set


    (* List of rules over flat terms and their activation
       condition. *)
    let rule_list =
      [ bool_terms, false_of_unit ;
        arith_atoms, true_of_unit ]

    let apply flat set =
      
      rule_list
      (* Apply all rules... *)
      |> List.fold_left
           ( fun set' (rule, condition) ->
             (* If their condition is true. *)
             if condition ()
             then rule flat set'
             else set' )
           set

  end

  (* The numeral -1. *)
  let minus_one_num = Numeral.(~- one)

  (* Inserts or updates a sys/terms binding in an associative list
     sorted by topological order.  If sys is already in the list, then
     its terms are updated with the union of the old ones and the new
     ones. If it's not then it is inserted at the right place wrt
     topological order. *)
  let insert_sys_terms ((sys,terms) as pair) =

    (* Checks if 'sys' is a subsystem of 'sys''. *)
    let shall_insert_here sys' =
      TransSys.get_subsystems sys'
      |> List.mem sys
    in

    let rec loop prefix = function

      (* System is already in the list. *)
      | (sys',terms') :: tail when sys == sys' ->
         List.rev_append
           prefix
           (* Updating the term list. *)
           ( (sys, TSet.union terms terms') :: tail )
           
      (* sys' has sys as a subsystem, we insert here. *)
      | ((sys',_) :: _) as l when shall_insert_here sys' ->
         List.rev_append prefix (pair :: l)

      (* Looping. *)
      | head :: tail ->
         loop (head :: prefix) tail

      (* Could not find sys, adding it at the end. *)
      | [] -> pair :: prefix |> List.rev
    in

    loop []


  (* If all vars in term have offset 0, adds term bumped at -1 to set. *)
  let add_offset_complement term set =
    match Term.var_offsets_of_term term with
    | Some(low), Some(up) when Numeral.(low = zero)
                               && Numeral.(up = zero) ->
       (* Term is one state @0, adding -1 version. *)
       TSet.add
         (Term.bump_state minus_one_num term)
         set
         
    | Some(low), Some(up) when Numeral.(low = minus_one_num)
                               && Numeral.(up = minus_one_num) ->
       (* Term is one state @-1, adding 0 version. *)
       TSet.add
         (Term.bump_state Numeral.one term)
         set
         
    | _ -> set


  (* If term is one state @0, adds term to set. If term is one state
     @-1, bumps the term to 0 and adds it to set. If term is two states,
     it is dismissed. *)
  let one_statify term set =
    match Term.var_offsets_of_term term with
    | Some(low), Some(up) when Numeral.(low = zero)
                               && Numeral.(up = zero) ->
       (* Term is one state @0, adding it. *)
       TSet.add term set
         
    | Some(low), Some(up) when Numeral.(low = minus_one_num)
                               && Numeral.(up = minus_one_num) ->
       (* Term is one state @-1, adding 0 version. *)
       TSet.add
         (Term.bump_state Numeral.one term)
         set

    | _ -> set

  (* Term set with true and false. *)
  let true_false_set = TSet.of_list [ Term.t_true ; Term.t_false ]

  (* Adds the -1 (resp. 0) version of terms mentioning only variables
     of offset 0 (resp. -1). *)
  let two_state_complement set =
    TSet.fold add_offset_complement set set

  (* Removes all two state candidate terms from a set of terms. *)
  let one_state_only set =
    TSet.fold one_statify set true_false_set

  (* Builds a set of candidate terms from a term. Basically applies
       flat rules on all subterms. *)
  let set_of_term term set =
    let set_ref = ref set in
    (* Updates the set reference. *)
    let set_update set' = set_ref := set' in
    
    ( Term.eval_t
        ( fun flat_term _ ->
          (* Applying rules and updating set reference. *)
          set_update
            (FlatTermsRules.apply flat_term !set_ref) )
        
        term ) ;

    !set_ref

  (* Generates sets of candidate terms from a transition system, and
     its subsystems if the flags require it. *)
  let candidate_terms_of_trans two_state top_sys trans_sys =
    
    let rec get_last = function
      | head :: [] -> [head]
      | [] ->
        Event.log L_fatal "can't get last" ;
        assert false ;
      | _ :: t -> get_last t
    in

    (* Creates an associative list between systems and their
       implication graph. Even when running in top system only, we
       need to look at the subsystems and instantiate their candidate
       terms. *)
    let rec sys_graphs_map result = function

      | system :: tail ->
         (* Getting the scope of the system. *)
         let scope = TransSys.scope_of_trans_sys system in

         (* Do we know that system already?. *)
         if List.exists
              ( fun (sys,_) ->
                TransSys.scope_of_trans_sys sys = scope )
              result
              
         then
           (* We do, discarding it. *)
           sys_graphs_map result tail

         else (

           Debug.invgencand "Looking at [%s]."
                 (TransSys.scope_of_trans_sys system |> String.concat "/");
           
           (* We don't, getting init and trans. *)
           let init, trans =
             TransSys.init_of_bound system Numeral.zero,
             (* Getting trans at [-1,0]. *)
             TransSys.trans_of_bound system Numeral.zero
           in

           Debug.invgencand "Generating candidates.";

           let user_candidates =
             if two_state then TSet.empty
             else TSet.of_list (TransSys.get_unknown_candidates system) in
  
           let candidates' =

             if Flags.Certif.only_user_candidates () then user_candidates
             else
               user_candidates

               (* Synthesizing candidates. *)
               |> StateVarRules.apply (TransSys.state_vars system)

               (* Candidates from init. *)
               |> set_of_term init

               (* Candidates from trans. *)
               |> if Flags.Invgen.mine_trans ()
               then set_of_term trans else identity
  in

           let candidates =
             (* Adding two state complement if
                required. One-state-ification will take place at the
                very end to avoid missing candidate terms through
                instantiation. *)
             if two_state then two_state_complement candidates'
             else candidates'
           in

           let sorted_result =
             result
             |> ( if Flags.Invgen.lift_candidates () then
                    TSet.fold
                      ( fun term map ->
                        TransSys.instantiate_term_all_levels
                          top_sys TransSys.trans_base scope term
                          |> (function | (top,others) -> top :: others)
                          |> List.fold_left
                              ( fun map (sys,terms) ->
                                insert_sys_terms
                                  (sys, TSet.of_list terms) map )
                              map )
                      candidates
                  else identity )
             |> insert_sys_terms (system, candidates)
           in

           sys_graphs_map
             sorted_result
             (List.concat [ TransSys.get_subsystems system ; tail ])
         )

      | [] ->

        let final =
          (* Only getting to system if required. *)
          ( if Flags.Invgen.top_only ()
            then get_last result else result )
          |> (
            (* One state-ing everything if required. *)
            if two_state then
              identity
            else
              List.map
                (fun (sys,set) ->
                  (sys, one_state_only set))
          )
        in

        let count =
          final
          |> List.fold_left
              ( fun count (_, term_set) ->
                count + (TSet.cardinal term_set) )
              (* Starting at two, true and false are not there yet. *)
              2
        in

        Debug.invgencand "%i candidates" count;

        (* Returning the candidate terms... *)
        final,
        (* ...and candidate term count for stats. *)
        count
    in

    sys_graphs_map [] [ trans_sys ]


  let build_graphs cands =

    let create_graph term_set =
      (* if Flags.only_user_candidates () then *)
      (*   ImplicationGraph.create_degenerate term_set *)
      (* else *)
        ImplicationGraph.create
          (TSet.union true_false_set term_set)
    in

    (* Building the graphs. *)
    List.map (fun (sys,term_set) ->
        (* Creating graph. *)
        (sys, create_graph term_set, TSet.cardinal term_set)
      ) cands
      
end

(* Generates candidate terms for a transition system, and its
   subsystems if the flags require it.
   /!\ The sets do NOT contain true and false /!\ *)
let generate_candidate_terms two_state top_sys trans =
  CandidateTermGen.candidate_terms_of_trans two_state top_sys trans

(* Generates implication graphs for a transition system, and its
   subsystems if the flags require it. *)
let generate_graphs two_state top_sys trans =
  let candidate_terms, count =
    generate_candidate_terms two_state top_sys trans
  in

  (* Returning implication graphs and candidate term count. *)
  CandidateTermGen.build_graphs candidate_terms, count

let mine_term
      synthesis
      mine_init
      mine_trans
      two_state sys terms set =
  set
  |> (if synthesis then
        (* Synthesizing candidates from sys. *)
        CandidateTermGen.StateVarRules.apply (TransSys.state_vars sys)
      else
        identity)
  |> (if mine_init then
        (* Mining init. *)
        TransSys.init_of_bound sys Numeral.zero
        |> CandidateTermGen.set_of_term
      else
        identity)
  |> (if mine_init then
        (* Mining trans. *)
        TransSys.trans_of_bound sys Numeral.zero
        |> CandidateTermGen.set_of_term
      else
        identity)
  |> (* Mining terms. *)
    (fun set ->
     List.fold_left
       (fun set' term ->
        CandidateTermGen.set_of_term term set')
       set
       terms)
  |> (if two_state then
        (* In two state get the complement. *)
        CandidateTermGen.two_state_complement
      else
        (* In one state, one-state-ify. *)
        CandidateTermGen.one_state_only)

(* Creates a graph for a transition system using the specified list of
   invariants. *)
let create_graph trans candidates =
  match
    CandidateTermGen.build_graphs [ (trans, candidates) ]
  with
    | (_, graph, _) :: _ -> graph
    | _ ->
      Event.log L_fatal "no graph was built" ;
      assert false


    
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

