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

module TSet = Term.TermSet
module Graph = ImplicationGraph
module CandTerm = InvGenCandTermGen
module LSD = LockStepDriver


(* Input signature of a graph-based invariant generation technique. *)
module type In = sig

  (* Two state mode flag. *)
  val two_state : bool

end

(* Output signature of a graph-based invariant generation technique. *)
module type Out = sig

  (* Invariant generation entry point. *)
  val main : TransSys.t -> unit

  (* Destroys the underlying solver and cleans things up. *)
  val on_exit : TransSys.t option -> unit

end

(* Builds an invariant generation technique from an [In] module. *)
module Make (InModule : In) : Out = struct

  (* Two state mode flag. *)
  let two_state = InModule.two_state

  (* Guards a term with init if in two state mode. *)
  let sanitize_term =
    if two_state then
      ( fun term ->
        Term.mk_or
          [ TransSys.init_flag_var Numeral.zero |> Term.mk_var ;
            term ] )
    else identity
    
  (* Getting the right stats. *)
  let (
    k_stat, inv_stat, impl_stat,
    time_stat, rewrite_stat, candidate_count_stat,
    stop_timers
  ) = (
    if two_state then
      Stat.invgengraph_ts_k,
      Stat.invgengraph_ts_invariant_count,
      Stat.invgengraph_ts_implication_count,
      Stat.invgengraph_ts_total_time,
      Stat.invgengraph_ts_graph_rewriting_time,
      Stat.invgengraph_ts_candidate_term_count,
      Stat.invgengraph_ts_stop_timers
    else
      Stat.invgengraph_os_k,
      Stat.invgengraph_os_invariant_count,
      Stat.invgengraph_os_implication_count,
      Stat.invgengraph_os_total_time,
      Stat.invgengraph_os_graph_rewriting_time,
      Stat.invgengraph_os_candidate_term_count,
      Stat.invgengraph_os_stop_timers
  )

  (* Name of the technique for communication. *)
  let name = if two_state then "INVGENTS" else "INVGENOS"

  (* Prints information about the state of the run. *)
  let communicate_progress () =
    Event.log
      L_info
      "%s @[<v>at k = %i@,\
               %i invariants discovered@,\
               %i of which are implications@,\
               (originally %i candidate terms)@]"
      name
      (Stat.get k_stat)
      (Stat.get inv_stat)
      (Stat.get impl_stat)
      (Stat.get candidate_count_stat)

  (* Prints the statistics. *)
  let print_stats () =
    Event.stat
      [ Stat.misc_stats_title, Stat.misc_stats ;
        (
          if two_state then
            Stat.invgengraph_ts_stats_title, Stat.invgengraph_ts_stats
          else
            Stat.invgengraph_os_stats_title, Stat.invgengraph_os_stats
        ) ;
        Stat.smt_stats_title, Stat.smt_stats ]

  (* Initializes the statistics of the module. *)
  let init_stats () =
    (* Getting the right initial k value. *)
    let init_k = if two_state then 1 else 0 in
    (* Updating statistics. *)
    Stat.set init_k k_stat ;
    (* Notifying framework. *)
    Event.progress init_k ;
    (* Starting timer. *)
    Stat.start_timer time_stat ;
    (* Communicating progress. *)
    communicate_progress ()

  (* Updates the candidate term count stat. *)
  let update_candidate_count_stats count =
    (* Updating statistics. *)
    Stat.set count candidate_count_stat

  (* Updates invariant discovery related stats. *)
  let update_invariant_stats
      sys_name k_int inv_count impl_count
  =
    if inv_count > 0 then (
      (* Updating invariant count. *)
      Stat.set
        (inv_count + Stat.get inv_stat)
        inv_stat ;
      (* Updating implication count. *)
      Stat.set
        (impl_count + Stat.get impl_stat)
        impl_stat ;
      (* Updating time. *)
      Stat.update_time time_stat ;
      (* Printing info if not in top only mode (since
         [update_progress] would be ran right afterwards). *)
      if not (Flags.invgengraph_top_only ()) then
        Event.log
          L_info
          "%s @[<v>%i (%i) invariants discovered@,\
                   at %i for system [%s].@]"
          name
          inv_count
          impl_count
          k_int
          sys_name
    )

  (* Updates progress related stats. *)
  let update_progress_stats k_int =
    (* Updating stats. *)
    Stat.set k_int k_stat ;
    Stat.update_time time_stat ;
    (* Notifying framwork. *)
    Event.progress k_int ;
    (* Explicit output. *)
    communicate_progress ()

  (* Times a rewriting of the graph. *)
  let time_rewrite_update_stats rewrite =
    (* Starting graph rewriting timer. *)
    Stat.start_timer rewrite_stat ;
    (* Rewriting graph. *)
    let result = rewrite () in
    (* Stopping graph rewriting timer. *)
    Stat.record_time rewrite_stat ;
    (* Returning result. *)
    result

  (* Filters candidate invariants from a set of term for step. *)
  let filter_step_candidates invariants to_prune =
      

    (* Tests if [rhs] is an [or] containing [lhs], or a negated and
       containing the complement of [lhs]. *)
    let trivial_rhs_or lhs rhs =

      (* Returns true if [negated] is an or containing the complement
         of [lhs]. Used if [rhs] is a not. *)
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

        ( if Term.node_symbol_of_term rhs == Symbol.s_or
          then
            (* Rhs is an or. *)
            Term.node_args_of_term rhs |> List.mem lhs

          else if Term.node_symbol_of_term rhs == Symbol.s_not
          then
            (* Rhs is a not, need to check if there is an and
               below. *)
            ( match Term.node_args_of_term rhs with

              (* Well founded not. *)
              | [ negated ] -> negated_and negated

              (* Dunno what that is. *)
              | _ -> false )

          else false )
      else false

    in

    (* Tests if [lhs] is an [and] containing [rhs], or a negated or
       containing the complement of [rhs]. *)
    let trivial_lhs_and lhs rhs =

      (* Returns true if [negated] is an and containing the complement
         of [rhs]. Used if [lhs] is a not. *)
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

        ( if Term.node_symbol_of_term lhs == Symbol.s_and
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

          else false )

      else false

    in

    (* Tests if [lhs] and [rhs] are arithmetic operators that
       trivially imply each other, such as [x<=2] and [x<=0]. *)
    let trivial_impl_arith lhs rhs =

      (* Returns true if the two input terms are arith constants and
         the first one is greater than or equal to the second one. *)
      let term_geq t1 t2 =
        if (Term.is_numeral t1) && (Term.is_numeral t2)
        then
          (* Comparing numerals. *)
          Numeral.(
            (Term.numeral_of_term t1) >= (Term.numeral_of_term t2)
          )

        else if (Term.is_decimal t1) && (Term.is_decimal t2)
        then
          (* Comparing decimals. *)
          Decimal.(
            (Term.decimal_of_term t1) >= (Term.decimal_of_term t2)
          )

        else
          (* Uncomparable terms. *)
          false
      in

      (* Are lhs and rhs applications? *)
      if (Term.is_node lhs) && (Term.is_node rhs)
      then

        (* Are rhs and lhs similar applications? *)
        if
          (Term.node_symbol_of_term lhs)
          == (Term.node_symbol_of_term rhs)
        then (

          match
            (Term.node_args_of_term lhs),
            (Term.node_args_of_term rhs)
          with

            | [kid1 ; kid2], [kid1' ; kid2'] ->

              (* If lhs and rhs are applications of [symbol], and if
                 [kid1] and [kid1'] are the same variables then return
                 [operator kid2 kid2']. Else, if [kid2] and [kid2']
                 are the same variables then return [operator kid1'
                 kid1]. Otherwise return false. *)
              let compare symbol operator =

                if (Term.node_symbol_of_term lhs) == symbol
                then

                  ( if
                      (Term.is_free_var kid1)
                      && (Term.is_free_var kid1')
                    then

                      ( (Term.free_var_of_term kid1) ==
                          (Term.free_var_of_term kid1') )
                      && ( operator kid2 kid2' )

                    else if
                        (Term.is_free_var kid2)
                        && (Term.is_free_var kid2')
                    then

                      ( (Term.free_var_of_term kid2)
                        == (Term.free_var_of_term kid2') )
                      && ( operator kid1' kid1 )

                    else false )
                    
                else false

              in


              (* Returns true if
                 [x>=n  x>=n' and n  >= n']
                 [n>=x n'>=x  and n' >= n] *)
              (compare Symbol.s_geq term_geq)

              (* Returns true if
                 [x>n  x>n'   and n  >= n']
                 [n>x n'>x    and n' >= n] *)
              || (compare Symbol.s_gt term_geq)

              (* Returns true if
                 [x<=n  x<=n' and n  <= n']
                 [n<=x n'<=x  and n' <= n] *)
              || (compare
                      Symbol.s_leq (fun t1 t2 -> term_geq t2 t1))

              (* Returns true if
                 [x<n  x<n'   and n  <= n']
                 [n<x n'<x    and n' <= n] *)
              || (compare
                    Symbol.s_lt (fun t1 t2 -> term_geq t2 t1))


            (* Kid count does not fit the template, returning
               false. *)
            | _ -> false

        (* [rhs] and [lhs] are not similar applications, returning
           false. *)
        ) else false

      (* [rhs] and [lhs] are not applications, returning false. *)
      else false

    in

    (* Number of implications removed. *)
    let rm_count = ref 0 in

    (* Function returning false for the implications to prune. *)
    let filter_implication term =

      if TSet.mem term invariants then
        (* This term is an invariant, filtering it. *)
        false
      else (

        (* Node should be an application. *)
        assert (Term.is_node term) ;

        if Term.node_symbol_of_term term == Symbol.s_implies
        then (

          if (Term.vars_of_term term |> Var.VarSet.cardinal) <= 1 then
            false
          else

            (* Term is indeed an implication. *)
            ( match Term.node_args_of_term term with

              (* Term is a well founded implication. *)
              | [ lhs ; rhs ] ->
                if
                  (* Checking if rhs is an and containing lhs, or a
                     negated or containing the negation of lhs. *)
                  (trivial_rhs_or lhs rhs)
                  (* Checking if lhs is an or containing lhs, or a
                     negated or containing the negation of lhs. *)
                  || (trivial_lhs_and lhs rhs)
                (* Checking if lhs and rhs are arith operator and lhs
                   trivially implies rhs. *)
              (* || (trivial_impl_arith lhs rhs) *)
                then
                  ( rm_count := !rm_count + 1 ; false )
                else true

              (* Implication is not well-founded, crashing. *)
              | _ -> assert false )
          
        (* Node is not an implication. *)
        ) else true
      )
    in
  
    List.filter filter_implication to_prune

  (* Rewrites a graph until the base instance of the input lsd becomes
     unsat. *)
  let rewrite_graph_until_base_unsat lsd sys graph =

    (* Rewrites a graph until the base instance becomes unsat. Returns
       the final version of the graph. *)
    let rec loop iteration fixed_point graph =

      (* Making sure the last rewriting actually changed something. *)
      assert (not fixed_point) ;

      (* Getting candidates invariants from equivalence classes and
         implications. *)
      let candidate_invariants =
      
        Graph.eq_classes graph
        (* Iterating over the equivalence classes. *)
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
                      (Term.mk_eq [rep ; term])
                      :: list'
                    else
                      list')
                  set
                  list )

            (* Adding equivalence classes to the non trivial
               implications. *)
            (Graph.non_trivial_implications graph)
      in

      (* Checking if we should terminate before doing anything. *)
      Event.check_termination () ;

      (* Querying base .*)
      match LSD.query_base lsd sys candidate_invariants with

        | Some model ->
          (* LSD instance is sat. *)

          (* Building eval function. *)
          let eval term =
            Eval.eval_term
              (TransSys.uf_defs sys)
              model
              term
            |> Eval.bool_of_value
          in
          
         (* Rewriting graph. *)
          let fixed_point, graph' =
            time_rewrite_update_stats
              (fun () -> Graph.rewrite_graph eval graph)
          in

          (* LSD base instance is not unsat, looping. *)
          loop (iteration + 1) fixed_point graph'

        | None ->
          (* Returning current graph. *)
          graph
    in

    (* Starting graph rewriting process. *)
    loop 1 false graph


  (* Gets the top level new invariants and adds all intermediary
     invariants into lsd. *)
  let get_top_inv_add_invariants lsd sys inv =

    (* Getting top invariants and intermediary ones. *)
    let ((_,top), intermediary) =
      (* Instantiating invariant at all levels. *)
      TransSys.instantiate_term_all_levels sys inv
    in

    (* Adding subsystem invariants as new invariants. *)
    intermediary
    (* Folding intermediary as a list of terms. *)
    |> List.fold_left
        ( fun terms (_,terms') -> List.rev_append terms' terms )
        []
    (* Adding it into lsd. *)
    |> LSD.add_invariants lsd ;

    (* Adding top level invariants as new invariants. *)
    LSD.add_invariants lsd top ;

    (* Returning top level invariants. *)
    (* match intermediary with *)
    (*   | [] -> top *)
    (*   | _ -> [] *)
    top

  (* Queries step to find invariants to communicate. *)
  let find_and_communicate_invariants lsd invariants sys graph =

    (* Getting candidates invariants from equivalence classes and
       implications. *)
    let candidate_invariants =

      Graph.eq_classes graph
      (* Iterating over equivalence classes. *)
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

          (* Adding equivalence classes to non trivial
             implications. *)
          ( Graph.non_trivial_implications graph )
      (* Removing previously discovered invariants and
         uninteresting implications. *)
      |> filter_step_candidates invariants
    in

    match candidate_invariants with

      | [] ->
        (* Nothing to try. *)
        invariants

      | candidates ->

        (* Discovering new invariants. *)
        let new_invariants =
          LSD.query_step lsd sys candidates |> snd
        in

        (* Counting implications for statistics. *)
        new_invariants
        |> List.fold_left
            ( fun sum inv ->
              if
                (Term.is_node inv)
                && (Term.node_symbol_of_term inv = Symbol.s_implies)
              then sum + 1
              else sum )
            0
        (* Updating invariant discovery related statistics. *)
        |> update_invariant_stats
            (TransSys.get_name sys)
            (LSD.get_k lsd |> Numeral.to_int)
            (List.length new_invariants) ;

        (* Updating the set of invariants. *)
        let invariants' =
          List.fold_left
            ( fun inv_set new_invariant ->
              TSet.add new_invariant inv_set )
            invariants
            new_invariants
        in

        if Flags.ind_lazy_invariants () then (
          new_invariants
          |> List.fold_left
              (fun list inv ->
                (* Guarding with init if necessary. *)
                sanitize_term inv
                (* Getting top level invariants, adding it and intermediary
                   ones in LSD. *)
                |> get_top_inv_add_invariants lsd sys
                |> List.rev_append list)
              []
          (* Broadcasting new invariant. *)
          |> List.iter Event.invariant
        ) else (
          match new_invariants with
            | [] -> ()
            | _ ->
              new_invariants
              |> Term.mk_and
              |> sanitize_term
              |> get_top_inv_add_invariants lsd sys
              |> List.iter Event.invariant
        );

        (* Returning updated invariant set. *)
        invariants'


  let rewrite_graph_find_invariants
      trans_sys lsd invariants (sys,graph) =

    (* Getting new invariants from the framework and updating
       transition system. *)
    let new_invariants =
    
      (* Receiving things. *)
      let new_invs, updated_props =
        Event.recv ()
        (* Updating transition system. *)
        |> Event.update_trans_sys trans_sys
      in

      updated_props
      (* Looking for new invariant properties. *)
      |> List.fold_left
          ( fun list (_, (name,status)) ->
            if status = TransSys.PropInvariant
            then
              (* Memorizing new invariant property. *)
              ( TransSys.named_term_of_prop_name trans_sys name )
              :: list
            else
              list )
          (* New invariant properties are added to new invariants. *)
          ( List.map snd new_invs )
    in

    (* Adding new invariants to LSD. *)
    LSD.add_invariants lsd new_invariants ;
  
    (* BASE CASE: rewriting the graph until base is unsat. *)
    let graph' =
      rewrite_graph_until_base_unsat lsd sys graph
    in
 
    (* STEP CASE: checking which properties are k inductive, asserting
       them in lsd, and broadcast. *)
    let invariants' =
      find_and_communicate_invariants lsd invariants sys graph'
    in
  
    (* Returning new mapping and the new invariants. *)
    (sys, graph'), invariants'

  (* Generates invariants by splitting an implication graph. *)
  let generate_invariants trans_sys lsd =

    (* Generating the candidate terms and building the graphs. *)
    let sys_graph_map, candidate_term_count =
      trans_sys |> CandTerm.generate_graphs two_state
    in

    (* Updating stats. *)
    update_candidate_count_stats candidate_term_count ;

    (* Initializing statistics. *)
    init_stats () ;

    (* Looks for invariants for all the systems in the system graph
       map. *)
    let rec loop invariants map =

      (* Generating new invariants and updated map by going through
         the sys/graph map. *)
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
          
        (* Reversing the map to keep the ordering by reversed
           topological order. *)
        |> ( fun (invars, rev_map) ->
          invars, List.rev rev_map )
      in

      (* Incrementing the k. *)
      LSD.increment lsd ;

      (* Updating statistics. *)
      LSD.get_k lsd
      |> Numeral.to_int
      |> update_progress_stats ;

      (* Recursing with updated invariants and sys/graph mapping. *)
      loop invariants' map'

    in

    loop TSet.empty sys_graph_map


  (* Reference to lsd for easy clean up. *)
  let lsd_ref = ref None

  (* Cleans up things on exit. *)
  let on_exit _ =
    (* Stop all timers. *)
    stop_timers () ;
    Stat.smt_stop_timers () ;
    (* Output statistics. *)
    print_stats () ;
    (* Destroying lsd if one was created. *)
    ( match !lsd_ref with
      | None -> ()
      | Some lsd -> LSD.delete lsd )

  (* Module entry point. *)
  let main trans_sys =

    (* Creating lsd instance. *)
    let lsd =
      LSD.create
        two_state
        (Flags.invgengraph_top_only ())
        trans_sys
    in

    (* Memorizing lsd for clean exit. *)
    lsd_ref := Some lsd ;

    (* Generating invariants. *)
    generate_invariants trans_sys lsd

end

(* One state graph-based invariant generation module. *)
module OneState = Make (struct let two_state = false end)

(* Two state graph-based invariant generation module. *)
module TwoState = Make (struct let two_state = true end)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

