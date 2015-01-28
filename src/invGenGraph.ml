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

  (** Invariant generation entry point. *)
  val main : TransSys.t -> unit

  (** Destroys the underlying solver and cleans things up. *)
  val on_exit : TransSys.t option -> unit

  (** Destroys the underlying lsd instance. *)
  val no_more_lsd : unit -> unit

  (** Launches invariant generation with a max [k] and a set of
      candidate terms. More precisely, [run sys ignore maxK
      candidates] will find invariants from set [candidates] by going
      up to [maxK] for [sys] and ignoring any term appearing in
      [ignore]. The result is a pair composed of the invariants
      discovered and the new set of ignored terms. *)
  val run :
    TransSys.t -> Term.TermSet.t -> Numeral.t -> Term.TermSet.t ->
    Term.TermSet.t * Term.TermSet.t

  (** Mines candidate terms from a system.  First bool flag activates
      synthesis, i.e. mining based on the state variables of the
      system. Second (resp. third) bool flag activates init
      (resp. transition) predicate mining. *)
  val mine_system :
    bool -> bool -> bool -> TransSys.t -> Term.TermSet.t

  (** Mines candidate terms from a list of terms, and adds them to the
      input set. *)
  val mine_terms :
    TransSys.t -> Term.t list -> Term.TermSet.t -> Term.TermSet.t

  (** Mines candidate terms from the list of terms. More precisely,
      [mine_terms_run sys ignore maxK candidates set] will mine
      candidate terms from list of terms [candidates], and add them to
      [set].  It then runs goes up to [maxK] for [sys] and ignores any
      term appearing in [ignore]. The result is a pair composed of the
      invariants discovered and the new set of ignored terms. *)
  val mine_terms_run :
    TransSys.t -> Term.TermSet.t -> Numeral.t -> Term.t list -> Term.TermSet.t ->
    Term.TermSet.t * Term.TermSet.t

end

(* Builds an invariant generation technique from an [In] module. *)
module Make (InModule : In) : Out = struct

  (* Two state mode flag. *)
  let two_state = InModule.two_state
    
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

  (* Checks if one state is enabled. *)
  let is_one_state_running () = Flags.enable () |> List.mem `INVGENOS

  (* Guards a term with init if in two state mode. *)
  let sanitize_term =
    if two_state then
      ( fun term ->
        Term.mk_or
          [ TransSys.init_flag_var Numeral.zero |> Term.mk_var ;
            term ] )
    else identity

  (* Lazy function deciding if a term should be kept or not depending
     on the lower bound and upper bound of the offsets of its state
     variables. *)
  let lazy_offset_criterion =
    lazy
      ( if two_state then
          (* In two state, ignore terms only mentioning -1. *)
          (fun candidate ->
           match Term.var_offsets_of_term candidate with
           | _, Some ubound -> Numeral.(ubound = zero)
           | _ -> false)
        else
          (* We are in one state mode, keeping everything. *)
          (fun candidate -> true) )
                                    

  (* Filters candidate invariants from a set of term for step. *)
  let filter_step_candidates invariants ignore =

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

    (* Function returning false for the candidate invariants to prune
       out. *)
    let filter_candidates term =

      if TSet.mem term invariants then
        (* This term is known to be an invariant, pruning it. *)
        false
      else if TSet.mem term ignore then
        false
      else (

        (* Applying offset criterion. *)
        let offset_filter =
          (Lazy.force lazy_offset_criterion) term
        in

        let structural_criterion () =
          if Term.node_symbol_of_term term == Symbol.s_implies then
              (* Term is indeed an implication. *)
              ( match Term.node_args_of_term term with

                (* Term is a well founded implication. *)
                | [ lhs ; rhs ] ->
                   (* Checking if rhs is an and containing lhs, or a
                      negated or containing the negation of lhs. *)
                   (trivial_rhs_or lhs rhs)
                   (* Checking if lhs is an or containing lhs, or a
                      negated or containing the negation of lhs. *)
                   || (trivial_lhs_and lhs rhs)
                   (* Checking if lhs and rhs are arith operator and lhs
                      trivially implies rhs. *)
                   || (trivial_impl_arith lhs rhs)

                (* Implication is not well-founded, crashing. *)
                | _ -> assert false )
          else
            (* Node is not an implication. *)
            true
        in

        offset_filter
      )
    in
  
    List.filter filter_candidates

  (* Rewrites a graph until the base instance of the input lsd becomes
     unsat. *)
  let rewrite_graph_until_base_unsat lsd sys graph =

    (* Rewrites a graph until the base instance becomes unsat. Returns
       the final version of the graph. *)
    let rec loop iteration graph =

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
          loop (iteration + 1) graph'

        | None ->
           (* Returning current graph. *)
           graph, iteration = 1
    in

    (* Starting graph rewriting process. *)
    loop 1 graph


  (* Lifts [invariants] for all the systems calling [sys] and
     communicates them to the framework. *)
  let communicate_invariants top_sys lsd sys = function
    | [] ->
       0
    | invariants ->
       
       (* All intermediary invariants and top level ones. *)
       let ((_, top_invariants), intermediary_invariants) =
         if top_sys == sys then
           (top_sys, List.map sanitize_term invariants), []
         else
           Term.mk_and invariants
           (* Guarding with init if needed. *)
           |> sanitize_term
           (* Instantiating at all levels. *)
           |> TransSys.instantiate_term_all_levels sys
       in

       intermediary_invariants
       |> List.iter
            ( fun (sub_sys, terms') ->
              (* Adding invariants to the lsd. *)
              LSD.add_invariants lsd sub_sys terms' ;
              (* Adding invariants to the transition system. *)
              terms'
              |> List.map
                   (TransSys.add_invariant sub_sys) ;
              (* Broadcasting invariants. *)
              terms'
              |> List.iter
                   (TransSys.get_scope sub_sys
                    |> Event.invariant) ) ;

       let top_scope = TransSys.get_scope top_sys in

       top_invariants
       |> List.iter
            (fun inv ->
             (* Adding top level invariants to transition system. *)
             TransSys.add_invariant top_sys inv ;
             (* Adding top level invariants to LSD. *)
             LSD.add_invariants lsd top_sys [ inv ] ;
             Event.invariant top_scope inv ) ;

       List.length top_invariants

  (* Queries step to find invariants to communicate. *)
  let find_and_communicate_invariants
        top_sys lsd invariants ignore sys graph =

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
      |> filter_step_candidates invariants ignore
    in

    (* Discovering new invariants. *)
    let new_invariants, trivial =
      LSD.increment_and_query_step lsd sys candidate_invariants
    in

    (* (\* Counting implications for statistics. *\) *)
    (* new_invariants *)
    (* |> List.fold_left *)
    (*     ( fun sum inv -> *)
    (*       if *)
    (*         (Term.is_node inv) *)
    (*         && (Term.node_symbol_of_term inv = Symbol.s_implies) *)
    (*       then sum + 1 *)
    (*       else sum ) *)
    (*     0 *)

    (* (\* Updating invariant discovery related statistics. *\) *)
    (* |> update_invariant_stats *)
    (*     (TransSys.get_name sys) *)
    (*     (LSD.get_k lsd |> Numeral.to_int) *)
    (*     (List.length new_invariants) ; *)

    (* Updating the set of invariants. *)
    let invariants' =
      List.fold_left
        ( fun inv_set new_invariant ->
          TSet.add new_invariant inv_set )
        invariants
        new_invariants
    in

    (* Udating the set of ignored candidates. *)
    let ignore' =
      (List.fold_left
         ( fun inv_set new_invariant ->
           TSet.add new_invariant inv_set )
         ignore
         trivial)
    in

    (* Lifting, adding to lsd, and communicating invariants. *)
    let top_count =
      communicate_invariants top_sys lsd sys new_invariants
    in

    ( match new_invariants with
      | [] -> ()
      | _ ->
         Event.log
           L_info
           "%s @[<v>%i invariants discovered (%i total)@ \
            at %i for [%s],@ \
            %i top level invariants generated.@]"
           name
           (List.length new_invariants)
           (TSet.cardinal invariants')
           (LSD.get_k lsd sys |> Numeral.pred |> Numeral.to_int)
           (TransSys.get_scope sys |> String.concat "/")
           top_count ) ;

    (* Returning updated invariant set. *)
    invariants', ignore'

  (* Receives messages, updates transition system, asserts new
     invariants in lsd. *)
  let recv_update_top_sys_lsd top_sys lsd =

    (* Receiving messages. *)
    Event.recv ()

    (* Updating transition system. *)
    |> Event.update_trans_sys_sub top_sys

    (* Handling new invariants and property statuses. *)
    |> ( fun (invariants, properties) ->

         (* Adding new invariants to lsd. *)
         invariants
         |> List.iter
              ( fun (_, (scope,inv)) ->
                LSD.add_invariants
                  lsd
                  (TransSys.subsystem_of_scope top_sys scope)
                  [ inv ] ) ;

         (* Adding valid properties to lsd. *)
         properties
         |> List.iter
              ( function
                | (_, (name,status))
                     when status = TransSys.PropInvariant ->
                   (* Getting term from property name. *)
                   [ TransSys.named_term_of_prop_name top_sys name ]
                   (* Adding it to lsd. *)
                   |> LSD.add_invariants lsd top_sys
                | _ -> () ) ; )

  (* Rewrites the graph until the base instance becomes unsat, then
     extracts invariants from the step instance. Returns the new
     binding, i.e. the updated graph and the new invariants. *)
  let rewrite_graph_find_invariants
        top_sys lsd (sys, graph, invariants, ignore) =

    (* BASE INSTANCE: rewriting the graph until base is unsat. *)
    let graph', unsat_on_first_check =
      rewrite_graph_until_base_unsat lsd sys graph
    in

    (* Receiving things. *)
    recv_update_top_sys_lsd top_sys lsd ;

    (* STEP INSTANCE: checking which properties are k inductive,
       asserting them in lsd, and broadcast. *)
    let invariants', ignore' =
      find_and_communicate_invariants
        top_sys lsd invariants ignore sys graph'
    in
  
    (* Returning new binding and base instance flag. *)
    (sys, graph', invariants', ignore'), unsat_on_first_check

  let lazy_max_successive =
    lazy
      ( (* match *)
        (*   Flags.invgengraph_max_successive () *)
        (* with *)
        (* | n when n > 0 -> *)
        (*    (fun count -> count > n) *)
        (* | _ -> *)
           (fun count -> false) )

  (* Iterates on a [sys], [graph], [invariants] until the base
     instance is unsat on the first check or the upper bound given by
     the flags has been reached. *)
  let iterate_on_binding top_sys lsd (binding, cand_count) =
    let max_successive = Lazy.force lazy_max_successive in

    let rec loop count ((sys,_,invs,_) as binding) =
      let k = LSD.get_k lsd sys in
      debug
        invGen
        "%s @[<v>rewriting [%s]@ \
         lsd at %i, %i invariants discovered@ \
         from %i candidate terms.@]"
        name
        (TransSys.get_scope sys |> String.concat "/")
        (k |> Numeral.to_int)
        (TSet.cardinal invs)
        cand_count in
      (* Getting new binding and base flag. *)
      let binding', base_unsat_on_first_check =
        rewrite_graph_find_invariants top_sys lsd binding
      in
      let k' = LSD.get_k lsd sys in
      if
        base_unsat_on_first_check
        || Flags.invgengraph_max_succ () <= count
      then
        (* Done, returning new binding. *)
        binding', cand_count
      else
        (* Looping. *)
        loop (count + 1) binding'
    in

    loop 1 binding

  (* Generates invariants by splitting an implication graph. *)
  let generate_invariants top_sys lsd =

    (* Generating the candidate terms and building the graphs. Result is a list
       of triplets: system, graph, invariants. *)
    let sys_graph_map, candidate_term_count =
      top_sys
      |> CandTerm.generate_graphs two_state
      |> ( fun (list, count) ->
            list
            |> List.map
                 ( fun (sys,graph,cand_count) ->
                   (* Building triplet. *)
                   (sys, graph, TSet.empty, TSet.empty),
                   cand_count )
            |> (fun list' -> list', count) )
    in

    Event.log
      L_info
      "%s Starting with %i candidate terms total."
      name
      candidate_term_count ;

    (* Updating stats. *)
    update_candidate_count_stats candidate_term_count ;

    (* Initializing statistics. *)
    (* init_stats () ; *)

    (* Looks for invariants for all the systems in the system graph
       map. *)
    let rec loop map =

      (* Going through the map to generate invariants and generate the
         new map for the next iteration. *)
      let map' =
        List.map (iterate_on_binding top_sys lsd) map
      in

      (* Recursing with updated invariants and sys/graph mapping. *)
      loop map'

    in

    loop sys_graph_map


  (* Reference to lsd for easy clean up. *)
  let lsd_ref = ref None

  let no_more_lsd () =
    (* Destroying lsd if one was created. *)
    ( match !lsd_ref with
      | None -> ()
      | Some lsd -> LSD.delete lsd ) ;
    lsd_ref := None

  (* Cleans up things on exit. *)
  let on_exit _ =
    (* Stop all timers. *)
    stop_timers () ;
    Stat.smt_stop_timers () ;
    (* Output statistics. *)
    print_stats () ;
    no_more_lsd ()

  (* Module entry point. *)
  let main trans_sys =

    (* Creating lsd instance. *)
    let lsd =
      LSD.create
        two_state
        false
        trans_sys
    in

    (* Memorizing lsd for clean exit. *)
    lsd_ref := Some lsd ;

    (* Generating invariants. *)
    generate_invariants trans_sys lsd


  (* Launches invariant generation with a max [k] and a set of
     candidate terms. *)
  let run sys ignore maxK candidates =

    let lsd =
      (* Creating lsd instance. *)
      LSD.create
        two_state
        true
        sys
    in

    (* Memorizing lsd for clean exit. *)
    lsd_ref := Some lsd ;

    let rec loop invariants ignore k graph =

      if Numeral.(k > maxK) then

        (* Maximal number of iterations reached, returning
           invariants. *)
        invariants, ignore
        
      else (

        (* Rewriting graph in the base case. *)
        let graph', _ =
          rewrite_graph_until_base_unsat lsd sys graph
        in

        (* Extracting invariants at k. *)
        let invariants', ignore' =
          find_and_communicate_invariants
            sys lsd invariants ignore sys graph'
        in

        (* Looping with new invariants. *)
        loop invariants' ignore' Numeral.(succ k) graph'

      )

    in

    (* Memorizing invariants to return to delete lsd. *)
    let res =
      InvGenCandTermGen.create_graph sys candidates
      |> loop TSet.empty ignore Numeral.zero
    in

    (* Deleting lsd. *)
    no_more_lsd () ;

    res

  (* Mines candidates terms from a system. *)
  let mine_system
        synthesis mine_init mine_trans sys =
    InvGenCandTermGen.mine_term
      synthesis mine_init mine_trans
      two_state sys [] TSet.empty

  (* Mines candidate terms from a list of terms and adds them to the
     set. *)
  let mine_terms sys terms set =
    (* Bumping all terms to 0. *)
    let terms' =
      terms
      |> List.map
           ( fun term ->
             match Term.var_offsets_of_term term with
             | _, Some offset ->
                if Numeral.(offset = zero) then
                  term
                else
                  Term.bump_state Numeral.(- offset) term
             | _ -> term )
    in
    (* Mining terms. *)
    InvGenCandTermGen.mine_term
      false false false two_state sys terms' set

  (* Mines candidate terms from a list of terms, adds them to [set],
     and runs invariant generation up to [maxK]. *)
  let mine_terms_run sys ignore maxK terms set =
    mine_terms sys terms set |> run sys ignore maxK

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

