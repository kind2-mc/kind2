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
    | Some lsd -> LSD.delete lsd )

(* Rewrites a graph until the base instance becomes unsat. *)
let rewrite_graph_until_unsat lsd sys graph =

  LSD.check_satisfiability lsd ;

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
      
      debug invGenTSControl "  Fixed point reached." in
      assert false
        
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
                     if rep != term then
                       (Term.mk_eq [rep ; term]) :: list'
                     else
                       list')
                   set
                   list )
             
             ( List.rev_append
                 (Graph.non_trivial_implications graph)
                 (Graph.trivial_implications graph) )
      in
      
      debug invGenTSControl "Checking base (%i) [%s at %s]."
            iteration
            (TransSys.get_scope sys |> String.concat "/")
            (LSD.get_k lsd |> Numeral.string_of_numeral)
      in

      match LSD.query_base lsd candidate_invariants with
        
      | Some model ->

         debug invGenTSControl "Sat." in

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
         debug invGenTSControl "Unsat." in
      
         (* Returning current graph. *)
         graph
    )
  in

  debug invGenTSControl
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

  (* Tests if 'lhs' and 'rhs' are arithmetic operators that trivially
     imply each other, such as x<=2 and x<=0. *)
  let trivial_impl_arith lhs rhs =

    (* Returns true if the two input terms are arith constants and the
       first one is greater than or equal to the second one. *)
    let term_geq t1 t2 =
      if (Term.is_numeral t1) && (Term.is_numeral t2)
      then
        (* Comparing numerals. *)
        Numeral.( (Term.numeral_of_term t1) >= (Term.numeral_of_term t2) )
      else if (Term.is_decimal t1) && (Term.is_decimal t2)
      then
        (* Comparing decimals. *)
        Decimal.( (Term.decimal_of_term t1) >= (Term.decimal_of_term t2) )
      else
        (* Uncomparable terms. *)
        false
    in

    (* Are lhs and rhs applications? *)
    if (Term.is_node lhs) && (Term.is_node rhs)
    then

      (* Are rhs and lhs similar applications? *)
      if (Term.node_symbol_of_term lhs) == (Term.node_symbol_of_term rhs)
      then (

        match (Term.node_args_of_term lhs), (Term.node_args_of_term rhs) with

          | [kid1 ; kid2], [kid1' ; kid2'] ->

            (* If lhs and rhs are applications of [symbol], and if
               [kid1] and [kid1'] are the same variables then return
               [operator kid2 kid2']. Else, if [kid2] and [kid2'] are the
               same variables then return [operator kid1'
               kid1]. Otherwise return false. *)
            let compare symbol operator =

              if (Term.node_symbol_of_term lhs) == symbol
              then (

                if
                  (Term.is_free_var kid1) && (Term.is_free_var kid1')
                then

                  ( (Term.free_var_of_term kid1) ==
                      (Term.free_var_of_term kid1') )
                  && ( operator kid2 kid2' )

                else if
                    (Term.is_free_var kid2)
                    && (Term.is_free_var kid2')
                then

                  ( (Term.free_var_of_term kid2) ==
                      (Term.free_var_of_term kid2') )
                  && ( operator kid1' kid1 )

                else

                  false
                    
              ) else false
                
            in


            (* Returns true if
               x>=n  x>=n' and n  >= n'
               n>=x n'>=x  and n' >= n *)
            (compare Symbol.s_geq term_geq)
              
            (* Returns true if
               x>n  x>n'   and n  >= n'
               n>x n'>x    and n' >= n *)
            || (compare Symbol.s_gt term_geq)
              
            (* Returns true if
               x<=n  x<=n' and n  <= n'
               n<=x n'<=x  and n' <= n *)
            || (compare Symbol.s_leq (fun t1 t2 -> term_geq t2 t1))
              
            (* Returns true if
               x<n  x<n'   and n  <= n'
               n<x n'<x    and n' <= n *)
            || (compare Symbol.s_lt (fun t1 t2 -> term_geq t2 t1))


          (* Kid count does not fit the template, returning false. *)
          | _ -> false

      (* [rhs] and [lhs] are not similar applications, returning false. *)
      ) else false

    (* [rhs] and [lhs] are not applications, returning false. *)
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
             (* Checking if lhs and rhs are arith operator and lhs
                trivially implies rhs. *)
             || (trivial_impl_arith lhs rhs)
           then (
             rm_count := !rm_count + 1 ; false
           ) else true

        (* Implication is not well founded, crashing. *)
        | _ -> assert false )
        
    (* Node is not an implication, crashing. *)
    else assert false
  in
  
  let result = List.filter filter_implication implications in

  debug invGenTSControl "  Pruned %i step implications." !rm_count in

  result


(* Gets the top level new invariants and adds all intermediary
   invariants into lsd. *)
let get_top_inv_add_invariants lsd sys invs =

  debug invGenTSInvariants
        "Getting top invariants on"
  in

  invs
  |> List.iter
       ( fun term ->
         debug invGenTSInvariants
               "%s" (Term.string_of_term term)
         in () ) ;
  
  invs
    
  (* Instantiating each invariant at all levels. *)
  |> List.map
       (TransSys.instantiate_term_all_levels sys)
       
  |> List.fold_left
       ( fun top ((_,top'), intermediary) ->

         debug invGenTSInvariants "Adding top level invariants." in

         (* Adding top level invariants as new invariants. *)
         LSD.new_invariants lsd top' ;

         (* Adding subsystems invariants as new invariants. *)
         intermediary
         (* Folding intermediary as a list of terms. *)
         |> List.fold_left
              ( fun terms (_,terms') -> List.rev_append terms' terms)
              []
         (* Adding it into lsd. *)
         |> (fun invs ->
             debug invGenTSInvariants "Adding intermediary invariants." in
             LSD.new_invariants lsd invs) ;

         (* Appending new top invariants. *)
         List.rev_append top' top )
       []

(* Queries step to find invariants to communicate. *)
let find_invariants lsd invariants sys graph =

  debug invGenTSControl
        "Check step for [%s] at k = %i."
        (TransSys.get_scope sys |> String.concat "/")
        (LSD.get_k lsd |> Numeral.to_int)
  in

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
                 if rep != term then
                   (Term.mk_eq [rep ; term]) :: list'
                 else list')
               set
               list )
         
         ( (Graph.non_trivial_implications graph)
           |> filter_step_implications )
  in
    
  (* (\* Equivalence classes as binary equalities. *\) *)
  (* let eq_classes = *)
  (*   Graph.eq_classes graph *)
  (*   |> List.fold_left *)
  (*        ( fun list set -> *)
  (*          match TSet.elements set with *)
             
  (*          (\* No equality to construct. *\) *)
  (*          | [t] -> list *)
                      
  (*          | t :: tail -> *)
  (*             (\* Building equalities pair-wise. *\) *)
  (*             tail *)
  (*             |> List.fold_left *)
  (*                  ( fun (t',list) t'' -> *)
  (*                    (t'', (Term.mk_eq [t';t'']) :: list) ) *)
  (*                  (t, []) *)
  (*             (\* Only keeping the list of equalities *\) *)
  (*             |> snd *)
  (*          | [] -> failwith "Graph equivalence class is empty.") *)
  (*        [] *)
  (* in *)

  (* (\* Non trivial equivalence classes between equivalence classes. *\) *)
  (* let implications = *)
  (*   Graph.non_trivial_implications graph *)
  (*   |> filter_step_implications *)
  (* in *)

  (* (\* Candidate invariants. *\) *)
  (* let candidate_invariants = *)
  (*   List.rev_append eq_classes implications *)
  (* in *)

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
     debug invGenTSControl "  No new invariants /T_T\\." in

     invariants
      
  | _ ->

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
     
     debug invGenTSInv
           "  %i invariants discovered (%i implications) \\*o*/ [%s]."
           (List.length new_invariants)
           impl_count'
           (TransSys.get_scope sys |> String.concat "/")
     in
     debug invGenTSControl
           "  %i invariants discovered (%i implications) \\*o*/ [%s]."
           (List.length new_invariants)
           impl_count'
           (TransSys.get_scope sys |> String.concat "/")
     in
     debug invGenTSInvariants
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
           debug invGenTSInv "%s" (Term.string_of_term inv) in ()) ;


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

     debug invGenTSInv
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

  (* Getting new invariants and updating transition system. *)
  let new_invariants =


    let new_invs, updated_props =
      (* Receiving messages. *)
      Event.recv ()
      (* Updating transition system. *)
      |> Event.update_trans_sys trans_sys
      (* Extracting invariant module/term pairs. *)
    in

    updated_props
    (* Looking for new invariant properties. *)
    |> List.fold_left
         ( fun list (_, (name,status)) ->
           if status = TransSys.PropInvariant
           then
             (* Memorizing new invariant property. *)
             ( TransSys.prop_of_name trans_sys name )
             :: list
           else
             list )
         (* New invariant properties are added to new invariants. *)
         ( List.map snd new_invs )
           
  in

  debug invGenTSControl "Adding new invariants in LSD." in

  (* Adding new invariants to LSD. *)
  LSD.new_invariants lsd new_invariants ;
  
  (* Rewriting the graph. *)
  let graph' = rewrite_graph_until_unsat lsd sys graph in
  
  (* Graph.to_dot *)
  (*   (sprintf "dot/graph-[%s]-%i.dot" *)
  (*            (TransSys.get_scope sys |> String.concat ".") *)
  (*            (LSD.get_k lsd |> Numeral.to_int)) *)
  (*   graph' ; *)

  (* At this point base is unsat, discovering invariants. *)
  let invariants' = find_invariants lsd invariants sys graph' in
  
  (* Returning new mapping and the new invariants. *)
  (sys, graph'), invariants'


                   
(* Generates invariants by splitting an implication graph. *)
let generate_invariants trans_sys lsd =

  (* Associative list from systems to candidate terms. *)
  let sys_graph_map = Graph.generate_graphs_two_state trans_sys in

  (* Incrementing lsd to 1 .*)
  LSD.increment lsd ;

  (* Updating stats. *)
  Stat.set 1 Stat.invgen_k ;
  Event.progress 1 ;
  Stat.update_time Stat.invgen_total_time ;
  print_stats () ;
  
  
  let rec loop invariants map =

    debug invGenTSControl
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

    debug invGenTSControl "Incrementing k in LSD." in

    (* Incrementing the k. *)
    LSD.increment lsd ;

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

  loop TSet.empty sys_graph_map |> ignore

(* Module entry point. *)
let main trans_sys =

  let lsd = LSD.create true trans_sys in

  (* Updating statistics. *)
  Stat.set 0 Stat.invgen_k ;
  Event.progress 0 ;
  Stat.start_timer Stat.invgen_total_time ;

  lsd_ref := Some lsd ;

  generate_invariants trans_sys lsd


                      
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

