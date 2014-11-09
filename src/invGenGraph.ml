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
open Printf

module TSet = Term.TermSet
module Graph = ImplicationGraph
module LSD = LockStepDriver

let lsd_ref = ref None
let confirmation_lsd_ref = ref None

let print_stats () =

  Event.stat
    [ Stat.misc_stats_title, Stat.misc_stats ;
      Stat.invgen_stats_title, Stat.invgen_stats ;
      Stat.smt_stats_title, Stat.smt_stats ]

(* Cleans up things on exit. *)
let on_exit _ =

  (* Stop all timers. *)
  Stat.invgen_stop_timers () ;
  Stat.smt_stop_timers () ;

  (* Output statistics. *)
  print_stats () ;
  
  (* Destroying lsd if one was created. *)
  ( match !lsd_ref with
    | None -> ()
    | Some lsd -> LSD.delete lsd ) ;
                
  (* Destroying confirmation lsd if one was created. *)
  ( match !confirmation_lsd_ref with
    | None -> ()
    | Some lsd -> LSD.delete lsd )

let confirmation_lsd_do f =
  match !confirmation_lsd_ref with
  | Some lsd -> f lsd | None -> ()

(* Gathers everything related to candidate term generation .*)
module ImplicationGraphs: sig

  val generate:
    TransSys.t -> (TransSys.t * Graph.t * Graph.t) list

end = struct

  let bool_type = Type.t_bool

  (* Returns true when given unit. *)
  let true_of_unit () = true

  (* Returns false when given unit. *)
  let false_of_unit () = false


  (* Rules generating candidate terms from a system without looking at
     the init and trans terms. *)
  module SynthesisRules : sig

    (* Applies rules to a system to synthesize candidate terms without
       looking at the init and trans terms. *)
    val apply : TransSys.t -> TSet.t -> TSet.t

  end = struct

    (* Creates x=n terms where x is an IntRange (low,up) and
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

      | Type.IntRange (low,up) ->

         if Numeral.(low = up) then set
         else
           unroll_range set low up var
           |> TSet.add
                (Term.mk_leq [ Term.mk_num low ; var ])
           |> TSet.add
                (Term.mk_leq [ var ; Term.mk_num up ])

      | _ -> set

    (* Creates x=0, x>=0 and x<=0 for int and real variables. *)
    let arith_zero_eqs svar set =

      match StateVar.type_of_state_var svar |> Type.node_of_type with

      | Type.Int ->

         let var =
           Var.mk_state_var_instance svar Numeral.zero
           |> Term.mk_var
         in

         (* Adding the new equations to the set. *)
         set
         (* |> TSet.add (Term.mk_eq  [ var ; Term.mk_num Numeral.zero ]) *)
         |> TSet.add (Term.mk_geq [ var ; Term.mk_num Numeral.zero ])
         (* |> TSet.add (Term.mk_leq [ var ; Term.mk_num Numeral.zero ]) *)

      | Type.Real ->

         let var =
           Var.mk_state_var_instance svar Numeral.zero
           |> Term.mk_var
         in

         (* Adding the new equations to the set. *)
         set
         (* |> TSet.add (Term.mk_eq  [ var ; Term.mk_dec Decimal.zero ]) *)
         |> TSet.add (Term.mk_geq [ var ; Term.mk_dec Decimal.zero ])
         (* |> TSet.add (Term.mk_leq [ var ; Term.mk_dec Decimal.zero ]) *)

      | _ -> set


    (* Add boolean variables. *)
    let bool_vars svar set =
      match StateVar.type_of_state_var svar |> Type.node_of_type with

      | Type.Bool when svar != TransSys.init_flag_svar ->
         TSet.add
           (Var.mk_state_var_instance svar Numeral.zero |> Term.mk_var)
           set

      | _ -> set


    (* List of rule/activation condition pairs. *)
    let rule_list =
      [ unroll_ranges,  false_of_unit ;
        arith_zero_eqs, false_of_unit ;
        bool_vars, true_of_unit ]


    (* Applies rules to a system to synthesize candidate terms without
       looking at the init and trans terms. *)
    let apply sys set =
      
      TransSys.state_vars sys
      (* For all state variables in trans sys... *)
      |> List.fold_left
           
           ( fun set' svar ->
             rule_list
             (* ...apply all rules... *)
             |> List.fold_left
                  
                  ( fun set'' (rule, condition) ->
                    (* ...if their activation condition applies.*)
                    if condition ()
                    then rule svar set''
                    else set'' )
                  
                  set' )
           
           set
  end


  (* Rules generating candidate terms from a flat term from the eval_t
     of init or trans. *)
  module FlatRules : sig

    (* Applies rules to a flat term from init or trans to generate new
       candidate terms. *)
    val apply : Term.T.flat -> TSet.t -> TSet.t

  end = struct

    (* Adds term to set if the type of term is bool. *)
    let must_be_bool term set =

      (* Constructing term. *)
      let term = Term.construct term in

      if term |> Term.type_of_term == Type.t_bool
      then TSet.add term set
      else set

    (* Term must be of type bool and not be an and to be a candidate
       invariant. *)
    let bool_terms term set = match term with
      | Term.T.App (symb, _) ->
         ( match Symbol.node_of_symbol symb with
           (* If it is an and we don't need it. *)
           | `AND -> set
           | _ -> must_be_bool term set )
      | _ -> must_be_bool term set


    (* If term is an arithmetic equation among {=,ge,le,gt,lt},
       generate the other ones. Keep in mind that the set rules come
       after, so in particular everything will be negated. *)
    let arith_eqs_fanning_rule term set =
      match term with
        
      | Term.T.App (sym,kids) ->

         ( match Symbol.node_of_symbol sym with
         
           | `EQ ->
              
              (* Making sure it's not a bool equality. *)
              ( match List.hd kids
                      |> Term.type_of_term
                      |> Type.node_of_type
                with
                | Type.Int
                | Type.Real ->
                   (* If it's not add terms. *)
                   set
                   |> TSet.add (Term.construct term)
                   |> TSet.add (Term.mk_gt kids)
                   |> TSet.add (Term.mk_lt kids)
                | _ -> set )
               
           | `LEQ -> set
                     |> TSet.add (Term.construct term)
                     |> TSet.add (Term.mk_eq kids)
                     |> TSet.add (Term.mk_geq kids)
               
           | `GEQ -> set
                     |> TSet.add (Term.construct term)
                     |> TSet.add (Term.mk_eq kids)
                     |> TSet.add (Term.mk_leq kids)
               
           | `GT -> set
                    |> TSet.add (Term.construct term)
                    |> TSet.add (Term.mk_eq kids)
                    |> TSet.add (Term.mk_lt kids)
               
           | `LT -> set
                    |> TSet.add (Term.construct term)
                    |> TSet.add (Term.mk_eq kids)
                    |> TSet.add (Term.mk_gt kids)

           | _ -> set )

      | _ -> set


    (* All rules and activation conditions. *)
    let rule_list =
      [ bool_terms, ( fun () -> not (Flags.invgen_atoms_only ())) ;
        arith_eqs_fanning_rule, false_of_unit ]
        
    (* Checks if a flat term mentions at least one variable. *)
    let has_vars flat_term =
      Term.construct flat_term
      |> Term.state_vars_of_term
      |> StateVar.StateVarSet.exists
           ( fun svar -> svar != TransSys.init_flag_svar )


    (* Applies flat rules depending on their activation condition. *)
    let apply flat_term set =

      (* If the term mentions state variables... *)
      if has_vars flat_term then
        rule_list
        (* ...apply rules depending on their activation condition. *)
        |> List.fold_left
             ( fun set' (rule, condition) -> if condition ()
                                             then rule flat_term set'
                                             else set' )
             set

      else set

  end


  (* Rules expanding a set of candidate terms. *)
  module SetRules : sig

    val apply : TSet.t -> TSet.t

  end = struct

    (* If a term only contains variables at -1 (resp. 0), also
     create the same term at 0 (resp. -1). *)
    let offset_rule set =
      TSet.fold
        ( fun term ->

          let set =
            match Term.var_offsets_of_term term with
            | Some offset1, Some offset2
                 when Numeral.(offset1 = offset2) ->
               
               if Numeral.(offset1 = ~- one) then
                 (* Term offset is -1, adding the same term at 0. *)
                 TSet.of_list
                   [ term ; Term.bump_state Numeral.one term ]
                   
               else if Numeral.(offset1 = zero) then
                 (* Term offset is 0, adding the same term at -1. *)
                 TSet.of_list
                   [ term ; Term.bump_state Numeral.(~-one) term ]
                   
               else
                 failwith
                   (sprintf "Unexpected offset %s."
                            (Numeral.string_of_numeral offset1))

            | _ ->
               (* Term is either two-state or no-state, nothing to do
                    either way. *)
               TSet.singleton term
          in

          TSet.union set )
        set
        TSet.empty

    (* For all boolean term, also add its negation. *)
    let negation_rule set =
      TSet.fold
        (fun term ->
         TSet.add (Term.negate_simplify term))
        set set

    (* List of (rule,condition). Rule will be used to generate
       candidate terms iff 'condition ()' evaluates to true. *)
    let rule_list =
      [ negation_rule, true_of_unit ;
        offset_rule, true_of_unit ]

    (* Applies the rules depending on their activation condition. *)
    let apply set =
      List.fold_left
        ( fun set (rule, condition) ->
          if condition () then rule set else set )
        set
        rule_list

  end


      
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
         

  (* Generates a set of candidate terms from the transition system. *)
  let generate trans_sys =

    (* Term set with true and false. *)
    let true_false_set =
      (TSet.of_list [ Term.t_true ; Term.t_false ])
    in

    let flat_to_term = Term.construct in

    (* Builds a set of candidate terms from a term. Basically applies
       flat rules on all subterms. *)
    let set_of_term term set =
      let set_ref = ref set in
      let set_update set' = set_ref := set' in
      
      ( Term.eval_t
          ( fun flat_term _ ->
            
            (* Applying rules and adding to set. *)
            set_update
              (FlatRules.apply flat_term !set_ref) )
          
          term ) ;

      !set_ref
    in

    (* Creates an associative list between systems and their
       implication graph. *)
    let rec all_sys_graphs_maps result = function
        
      | system :: tail ->
         (* Getting the scope of the system. *)
         let scope = TransSys.get_scope system in

         (* Do we know that system already?. *)
         if List.exists
              ( fun (sys,_) ->
                TransSys.get_scope sys = scope )
              result
              
         then
           (* We do, discarding it. *)
           all_sys_graphs_maps result tail

         else
           
           (* We don't, getting init and trans. *)
           let init, trans =
             TransSys.init_of_bound system Numeral.zero,
             (* Getting trans at [-1,0]. *)
             TransSys.trans_of_bound system Numeral.zero
           in

           let candidates =

             true_false_set
               
             (* Synthesizing candidates. *)
             |> SynthesisRules.apply system
                                     
             (* Candidates from init. *)
             |> set_of_term init
                            
             (* Candidates from trans. *)
             |> set_of_term trans
                            
             (* Applying set rules. *)
             |> SetRules.apply
           in

           let sorted_result =
             result
             (* |> TSet.fold *)
             (*      ( fun term map -> *)
             (*        TransSys.instantiate_term_all_levels *)
             (*          system term *)
             (*        |> (function | (top,others) -> top :: others) *)
             (*        |> List.fold_left *)
             (*             ( fun map (sys,terms) -> *)
             (*               insert_sys_terms *)
             (*                 (sys, TSet.of_list terms) map ) *)
             (*             map ) *)
             (*      candidates *)
             |> insert_sys_terms (system, candidates)
           in

           all_sys_graphs_maps
             sorted_result
             (List.concat [ TransSys.get_subsystems system ; tail ])

      | [] ->
         let rec get_last = function
           | head :: [] -> [head]
           | [] -> assert false;
           | _ :: t -> get_last t
         in

         if Flags.invgen_top_only ()
         then get_last result
         else result
    in

    all_sys_graphs_maps [] [ trans_sys ]
    (* Building the graphs. *)
    |> List.map ( fun (sys,term_set) ->

                  (* Building the set of one-state candidates. *)
                  let term_set_one_state =
                    TSet.filter
                      ( fun term ->
                        match Term.var_offsets_of_term term with
                        | (Some low), (Some hi)
                             when Numeral.(low = zero)
                                  && Numeral.(hi = zero) ->
                           true
                        | None, None -> true
                        | _ -> false )
                      term_set
                    |> TSet.union true_false_set
                  in

                  debug invGenControl
                        "System [%s]: %i candidate invariants (%i one-state)."
                        (TransSys.get_scope sys |> String.concat "/")
                        (TSet.cardinal term_set)
                        (TSet.cardinal term_set_one_state)
                  in

                  debug invGenInit
                        "System [%s]:"
                        (TransSys.get_scope sys |> String.concat "/")
                  in

                  let _ =
                    term_set
                    |> TSet.iter
                         (fun candidate ->
                          debug invGenInit
                                "%s" (Term.string_of_term candidate)
                          in ())
                  in

                  debug invGenInit
                        "System [%s], one state:"
                        (TransSys.get_scope sys |> String.concat "/")
                  in

                  let _ =
                    term_set_one_state
                    |> TSet.iter
                         (fun candidate ->
                          debug invGenInit
                                "%s" (Term.string_of_term candidate)
                          in ())
                  in


                  debug invGenInit "" in

                  (* Updating statistics. *)
                  let cand_count =
                    Stat.get Stat.invgen_candidate_term_count
                  in
                  Stat.set (cand_count + (TSet.cardinal term_set))
                           Stat.invgen_candidate_term_count ;

                  (* Creating graph. *)
                  (sys,
                   Graph.create term_set_one_state,
                   Graph.create term_set) )

end

(* Rewrites a graph until the base instance becomes unsat. *)
let rewrite_graph_until_unsat lsd sys graph =

  (* Rewrites a graph until the base instance becomes unsat. Returns
     the final version of the graph. *)
  let rec loop iteration fixed_point graph =

    (* Graph.to_dot *)
    (*   (sprintf "dot/graph-[%s]-%i-%i.dot" *)
    (*            (TransSys.get_scope sys |> String.concat "-") *)
    (*            (LSD.get_k lsd |> Numeral.to_int) *)
    (*            (iteration)) *)
    (*   graph ; *)


    (* Checking if we should terminate. *)
    Event.check_termination () ;
    
    if fixed_point then (
      
      debug invGenControl "  Fixed point reached." in
      graph
        
    ) else (

      (* Getting candidates invariants from equivalence classes and
         implications. *)
      let candidate_invariants =
        Graph.eq_classes graph
        |> List.fold_left
             ( fun list set ->
               (* If there is only one element in the set there is no
                  equality to add. *)
               if TSet.cardinal set <= 1 then list
               else
                 (* Otherwise we choose a representative. *)
                 let rep = TSet.choose set in
                 
                 TSet.fold
                   (* And we build all the equalities. *)
                   (fun term list' ->
                    (Term.mk_eq [rep ; term]) :: list')
                   set
                   list )
             
             ( List.rev_append
                 (Graph.non_trivial_implications graph)
                 (Graph.trivial_implications graph) )
      in
      
      debug invGenControl "Checking base (%i) [%s at %s]."
            iteration
            (TransSys.get_scope sys |> String.concat "/")
            (LSD.get_k lsd |> Numeral.string_of_numeral)
      in

      match LSD.query_base lsd candidate_invariants with
        
      | Some model ->

         debug invGenControl "Sat." in

         (* Building eval function. *)
         let eval term =
           Eval.eval_term
             (TransSys.uf_defs sys)
             model
             term
           |> Eval.bool_of_value
         in

         (* Timing graph rewriting. *)
         Stat.start_timer Stat.invgen_graph_rewriting_time ;

         (* Rewriting graph. *)
         let fixed_point, graph' =
           Graph.rewrite_graph eval graph
         in

         (* Timing graph rewriting. *)
         Stat.record_time Stat.invgen_graph_rewriting_time ;

         loop (iteration + 1) fixed_point graph'

      | None ->
         debug invGenControl "Unsat." in

         (* Returning current graph. *)
         graph
    )
  in

  debug invGenControl
        "Starting graph rewriting for [%s] at k = %i."
        (TransSys.get_scope sys |> String.concat "/")
        (LSD.get_k lsd |> Numeral.to_int)
  in

  loop 1 false graph

(* Removes implications from a set of term for step. CRASHES if not
   applied to implications. *)
let filter_step_implications implications =

  (* Tests if 'rhs' is an or containing 'lhs', or a negated and
     containing the complement of 'lhs'. *)
  let trivial_rhs_or lhs rhs =

    (* Returns true if 'negated' is an or containing the complement of
       'lhs'. Used if 'rhs' is a not. *)
    let negated_and negated =
      if Term.is_node negated
      then
        
        if Term.node_symbol_of_term negated == Symbol.s_and
        then
          (* Term is an and. *)
          Term.node_args_of_term negated
          |> List.mem (Term.negate lhs)
                      
        else false
      else false
    in     
    
    (* Is rhs an application? *)
    if Term.is_node rhs
    then
      
      if Term.node_symbol_of_term rhs == Symbol.s_or
      then
        (* Rhs is an or. *)
        Term.node_args_of_term rhs |> List.mem lhs

      else if Term.node_symbol_of_term rhs == Symbol.s_not
      then
        (* Rhs is a not, need to check if there is an and below. *)
        ( match Term.node_args_of_term rhs with

          (* Well founded not. *)
          | [ negated ] -> negated_and negated

          (* Dunno what that is. *)
          | _ -> false )

      else false
    else false

  in

  (* Tests if 'lhs' is an and containing 'rhs', or a negated or
     containing the complement of 'rhs'. *)
  let trivial_lhs_and lhs rhs =

    (* Returns true if 'negated' is an and containing the complement of
       'rhs'. Used if 'lhs' is a not. *)
    let negated_or negated =
      if Term.is_node negated
      then
        
        if Term.node_symbol_of_term negated == Symbol.s_or
        then
          (* Term is an or. *)
          Term.node_args_of_term negated
          |> List.mem (Term.negate rhs)
                      
        else false
      else false
    in     
    
    (* Is rhs an application? *)
    if Term.is_node lhs
    then
      
      if Term.node_symbol_of_term lhs == Symbol.s_and
      then
        (* Lhs is an and. *)
        Term.node_args_of_term lhs |> List.mem rhs


      else if Term.node_symbol_of_term lhs == Symbol.s_not
      then
        (* Lhs is a not, need to check if there is an or below. *)
        ( match Term.node_args_of_term lhs with

          (* Well founded not. *)
          | [ negated ] -> negated_or negated

          (* Dunno what that is. *)
          | _ -> false )

      else false
    else false

  in

  (* Number of implications removed. *)
  let rm_count = ref 0 in

  (* Function returning false for the implications to prune. *)
  let filter_implication term =
    
    (* Node should be an application. *)
    assert (Term.is_node term) ;
    
    if Term.node_symbol_of_term term == Symbol.s_implies
    then
      (* Term is indeed an implication. *)
      ( match Term.node_args_of_term term with

        (* Term is a well founded implication. *)
        | [ lhs ; rhs ] ->
           if
             (* Checking if rhs is an and containing lhs, or a negated
               or containing the negation of lhs. *)
             (trivial_rhs_or lhs rhs)
             (* Checking if lhs is an or containing lhs, or a negated
               or containing the negation of lhs. *)
             || (trivial_lhs_and lhs rhs)
           then (
             rm_count := !rm_count + 1 ; false
           ) else true

        (* Implication is not well founded, crashing. *)
        | _ -> assert false )
        
    (* Node is not an implication, crashing. *)
    else assert false
  in
  
  let result = List.filter filter_implication implications in

  debug invGenPruning "  Pruned %i step implications." !rm_count in

  result


(* Gets the top level new invariants and adds all intermediary
   invariants into lsd. *)
let get_top_inv_add_invariants lsd sys invs =
  
  invs
    
  (* Instantiating each invariant at all levels. *)
  |> List.map
       (TransSys.instantiate_term_all_levels sys)
       
  |> List.fold_left
       ( fun top ((_,top'), intermediary) ->

         (* Adding top level invariants as new invariants. *)
         LSD.new_invariants lsd top' ;
         confirmation_lsd_do (fun lsd -> LSD.new_invariants lsd top') ;

         (* Adding subsystems invariants as new invariants. *)
         intermediary
         (* Folding intermediary as a list of terms. *)
         |> List.fold_left
              ( fun terms (_,terms') -> List.rev_append terms' terms)
              []
         (* Adding it into lsd. *)
         |> (fun invs ->
             LSD.new_invariants lsd invs ;
             confirmation_lsd_do (fun lsd -> LSD.new_invariants lsd invs)) ;

         (* Appending new top invariants. *)
         List.rev_append top' top )
       []

(* Queries step to find invariants to communicate. *)
let find_invariants lsd invariants sys graph =

  debug invGenControl
        "Check step for [%s] at k = %i."
        (TransSys.get_scope sys |> String.concat "/")
        (LSD.get_k lsd |> Numeral.to_int)
  in

  (* Graph.to_dot *)
  (*   (sprintf "dot/graph-[%s]-%i.dot" *)
  (*            (TransSys.get_scope sys |> String.concat "-") *)
  (*            (LSD.get_k lsd |> Numeral.to_int)) *)
  (*   graph ; *)

  (* Equivalence classes as binary equalities. *)
  let eq_classes =
    Graph.eq_classes graph
    |> List.fold_left
         ( fun list set ->
           match TSet.elements set with
             
           (* No equality to construct. *)
           | [t] -> list
                      
           | t :: tail ->
              (* Building equalities pair-wise. *)
              tail
              |> List.fold_left
                   ( fun (t',list) t'' ->
                     (t'', (Term.mk_eq [t';t'']) :: list) )
                   (t, [])
              (* Only keeping the list of equalities *)
              |> snd
           | [] -> failwith "Graph equivalence class is empty.")
         []
  in

  (* Non trivial equivalence classes between equivalence classes. *)
  let implications =
    Graph.non_trivial_implications graph
    |> filter_step_implications
  in

  (* Candidate invariants. *)
  let candidate_invariants =
    List.rev_append eq_classes implications
  in

  (* New invariants discovered at this step. *)
  let new_invariants =
    match LSD.query_step lsd candidate_invariants with
    (* No unfalsifiable candidate invariants. *)
    | _, [] -> []
    | _, unfalsifiable ->
       unfalsifiable
       (* Removing the invariants we already know. *)
       |> List.filter
            (fun inv -> not (TSet.mem inv invariants))
  in

  (* Communicating new invariants and building the new set of
     invariants. *)
  match new_invariants with
    
  | [] ->
     debug invGenControl "  No new invariants /T_T\\." in

     invariants
      
  | _ ->

     debug invGenControl
           "Confirming invariants."
     in
     
     (* Confirming invariant. *)
     ( match !confirmation_lsd_ref with
       | Some conf_lsd ->
          ( match LSD.query_base
                    conf_lsd new_invariants
            with
            | None -> ()
            | _ -> assert false ) ;
          ( match LSD.query_step
                    conf_lsd new_invariants
            with
            | [],_ ->
               debug invGenControl
                     "Confirmed."
               in
               ()
            | list,_ ->
               printf "Could not confirm invariant(s):\n" ;
               new_invariants
               |> List.iter
                    ( fun t -> Term.string_of_term t |> printf "%s\n" ) ;
             assert false )
       | None -> () ) ;


     let impl_count' =
       new_invariants
       |> List.fold_left
            ( fun sum inv ->
              if (Term.is_node inv)
                 && (Term.node_symbol_of_term inv = Symbol.s_implies)
              then sum + 1
              else sum )
            0
     in
     
     debug invGenControl
           "  %i invariants discovered (%i implications) \\*o*/ [%s]."
           (List.length new_invariants)
           impl_count'
           (TransSys.get_scope sys |> String.concat "/")
     in

     (* Updating statistics. *)
     let inv_count = Stat.get Stat.invgen_invariant_count in
     let impl_count = Stat.get Stat.invgen_implication_count in
     Stat.set
       (inv_count + (List.length new_invariants))
       Stat.invgen_invariant_count ;
     Stat.set
       (impl_count + impl_count') Stat.invgen_implication_count ;
     Stat.update_time Stat.invgen_total_time ;
     
     new_invariants
     |> List.iter
          (fun inv ->
           debug invGenInv "%s" (Term.string_of_term inv) in ()) ;


     let top_level_inv =
       new_invariants
       (* Instantiating new invariants at top level. *)
       |> get_top_inv_add_invariants lsd sys
       (* And-ing them. *)
       |> Term.mk_and
       (* Guarding with init. *)
       |> (fun t ->
           Term.mk_or [ TransSys.init_flag_var Numeral.zero
                        |> Term.mk_var ;
                        t ])
     in

     debug invGenInv
           "%s" (Term.string_of_term top_level_inv)
     in

     top_level_inv
     (* Broadcasting them. *)
     |> Event.invariant ;

     (* Adding the new invariants to the old ones. *)
     new_invariants
     |> List.fold_left
          ( fun set t -> TSet.add t set )
          invariants

let rewrite_graph_find_invariants
      trans_sys lsd invariants (sys,graph) =

  (* Getting new invariants from the framework. *)
  let new_invariants, _, _ =
    (* Receiving messages. *)
    Event.recv ()
    (* Updating transition system. *)
    |> Event.update_trans_sys_tsugi trans_sys
  in

  debug invGenControl "Adding new invariants in LSD." in

  (* Adding new invariants to LSD. *)
  LSD.new_invariants lsd new_invariants ;
  
  (* Rewriting the graph. *)
  let graph' = rewrite_graph_until_unsat lsd sys graph in
  (* At this point base is unsat, discovering invariants. *)
  let invariants' = find_invariants lsd invariants sys graph' in
  (* Returning new mapping and the new invariants. *)
  (sys, graph'), invariants'

(* Generates invariants by splitting an implication graph. *)
let generate_invariants trans_sys lsd =

  (* Associative list from systems to candidate terms. *)
  let sys_graph_map = ImplicationGraphs.generate trans_sys in

  debug invGenInit
        "Graph generation result:"
  in

  sys_graph_map
  |> List.iter
       ( fun (sys,_,_) ->
         debug invGenInit "  %s" (TransSys.get_scope sys
                                  |> String.concat "/") in () ) ;

    
  let invariants_at_0 =
    if Flags.invgen_one_state () then (

      (debug invGenControl
             "Running on one-state invariants."
       in ()) ;
      
      sys_graph_map
      |> List.fold_left
           ( fun invs (sys, graph, _) ->
             let _, invs' =
               rewrite_graph_find_invariants
                 trans_sys lsd invs (sys,graph)
             in
             invs' )
           TSet.empty
           
    ) else TSet.empty
  in

  (* Removing graphs at 0. *)
  let sys_graph_map' =
    sys_graph_map |> List.map (fun (sys, _, graph) -> (sys,graph))
  in

  (* Incrementing k. *)
  LSD.increment lsd ;
  ( match !confirmation_lsd_ref with
    | Some conf_lsd ->
       LSD.increment conf_lsd
    | None -> () ) ;

  (* Updating stats. *)
  Stat.set 1 Stat.invgen_k ;
  Event.progress 1 ;
  Stat.update_time Stat.invgen_total_time ;
  print_stats () ;
  
  
  let rec loop invariants map =

    debug invGenControl
          "Main loop at k = %i."
          (LSD.get_k lsd |> Numeral.to_int)
    in

    (* Generating new invariants and updated map by going through the
       sys/graph map. *)
    let invariants', map' =
      map
      |> List.fold_left
           ( fun (invs, mp) sys_graph ->
             (* Getting updated mapping and invariants. *)
             let mapping, invs' =
               rewrite_graph_find_invariants
                 trans_sys lsd invs sys_graph
             in
             (invs', (mapping :: mp)) )
           (invariants, [])
      (* Reversing the map to keep the ordering by decreasing
         instantiation count. *)
      |> ( fun (invars, rev_map) ->
           invars, List.rev rev_map )
    in

    debug invGenControl "Incrementing k in LSD." in

    (* Incrementing the k. *)
    LSD.increment lsd ;

    (* Incrementing the k in confirmation lsd. *)
    ( match !confirmation_lsd_ref with
      | Some conf_lsd ->
         LSD.increment conf_lsd
      | None -> () ) ;

    (* Updating statistics. *)
    let k_int = LSD.get_k lsd |> Numeral.to_int in
    Stat.set k_int Stat.invgen_k ;
    Event.progress k_int ;
    Stat.update_time Stat.invgen_total_time ;
    print_stats () ;

    (* Output current progress. *)
    Event.log
      L_info
      "INVGEN loop at k =  %i" k_int ;

    (* if Numeral.(one < (LSD.get_k lsd)) then () *)
    (* else loop invariants' map' *)

    loop invariants' map'

  in

  loop invariants_at_0 sys_graph_map' |> ignore

(* Module entry point. *)
let main trans_sys =

  let lsd = LSD.create trans_sys in

  let confirmation_lsd = LSD.create trans_sys in

  (* Updating statistics. *)
  Stat.set 0 Stat.invgen_k ;
  Event.progress 0 ;
  Stat.start_timer Stat.invgen_total_time ;

  lsd_ref := Some lsd ;
  confirmation_lsd_ref := Some confirmation_lsd ;

  generate_invariants trans_sys lsd


                      
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

