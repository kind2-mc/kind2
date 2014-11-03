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

let confirmation_lsd_do f =
  match !confirmation_lsd_ref with
  | Some lsd -> f lsd | None -> ()

(* Gathers everything related to candidate term generation .*)
module CandidateTerms: sig

  val generate_implication_graphs:
    TransSys.t list -> (TransSys.t * Graph.t) list

end = struct

  (********** Rules for candidate term generation. ***********)
  

  (* Only keep terms with vars in them. *)
  let must_have_var_rule =
    TSet.filter
      ( fun term ->
        not (Term.vars_of_term term |> Var.VarSet.is_empty)
        &&  (term != ((TransSys.init_flag_var Numeral.zero)
                      |> Term.mk_var))
        &&  (term != ((TransSys.init_flag_var Numeral.(~-one))
                      |> Term.mk_var)) )

  (* Only keep terms which are a var. *)
  let must_be_var =
    TSet.filter Term.is_free_var

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
               failwith "Unexpected offset %i."
                        (Numeral.string_of_numeral offset1)

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
      (fun term -> TSet.add (Term.negate term))
      set set

  (* Returns true when given unit. *)
  let true_of_unit () = true

  (* List of (rule,condition). Rule will be used to generate
       candidate terms iff 'condition ()' evaluates to true. *)
  let rule_list =
    [ must_have_var_rule , true_of_unit ;
      (* must_be_var , true_of_unit ; *)
      offset_rule, true_of_unit ;
      negation_rule, true_of_unit ]

  (* Applies the rules for the condition of which evaluates to true
       on a set of terms. *)
  let apply_rules set =
    List.fold_left
      ( fun set (rule, condition) ->
        if condition () then rule set else set )
      set
      rule_list



  (*************** Lucky candidate terms *************)

  let int_ge_0_lucky sys set =
    TransSys.state_vars sys
    |> List.fold_left
         ( fun set sv ->
           ( match StateVar.type_of_state_var sv
                   |> Type.node_of_type
             with
             | Type.Int ->
                let var =
                  Var.mk_state_var_instance
                    sv Numeral.zero
                  |> Term.mk_var
                in
                
                TSet.add
                  (Term.mk_geq [Term.mk_num Numeral.zero ; var])
                  set
             | _ -> set ) )
         set

  let lucky_list =
    [ int_ge_0_lucky, true_of_unit ]

  let add_lucky sys set =
    List.fold_left
      ( fun set (luck, condition) ->
        if condition () then luck sys set else set )
      set
      lucky_list
      



      
  (* Inserts or updates a sys/terms binding in an associative list
     sorted by topological order.  If sys is already in the list, then
     its terms are updated with the union of the old ones and the new
     ones. If it's not then it is inserted at the right place wrt
     topological order. *)
  let update_sys_graph ((sys,terms) as pair) =

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
  let generate_implication_graphs trans_sys =

    (* Term set with true and false. *)
    let true_false_set =
      (TSet.of_list [ Term.mk_true () ; Term.mk_false () ])
    in

    let flat_to_term = Term.construct in

    let bool_type = Type.mk_bool () in

    (* Builds a set of candidate terms from a term. *)
    let set_of_term sys t =
      ( Term.eval_t
          (* Getting all the subterms of t. *)
          ( fun term ->
            List.fold_left
              TSet.union
              (TSet.singleton (Term.construct term)) )
          t )
      (* Remove non boolean atoms. *)
      |> TSet.filter
           ( fun t -> (Term.type_of_term t) = bool_type )
      |> add_lucky sys
      (* Apply the candidate term generation rules. *)
      |> apply_rules
      (* Adding true and false. *)
      |> TSet.union true_false_set
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

           (* Getting their candidate terms. *)
           let candidates =
             TSet.union (set_of_term system init)
                        (set_of_term system trans)
             |> TSet.union true_false_set
           in

           let sorted_result =
             result
             |> TSet.fold
                  ( fun term map ->
                    TransSys.instantiate_term_all_levels
                      system term
                    |> (function | (top,others) -> top :: others)
                    |> List.fold_left
                         ( fun map (sys,terms) ->
                           update_sys_graph
                             (sys, TSet.of_list terms) map )
                         map )
                  candidates
             |> update_sys_graph (system, candidates)
           in

           all_sys_graphs_maps
             sorted_result
             (List.concat [ TransSys.get_subsystems system ; tail ])

      | [] -> result
    in

    all_sys_graphs_maps [] trans_sys
    (* Building the graphs. *)
    |> List.map ( fun (sys,term_set) ->

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

                  debug invGenInit "" in
                  
                  (sys, Graph.create term_set) )

end

(* Rewrites a graph until the base instance becomes unsat. *)
let rewrite_graph_until_unsat lsd sys graph =

  (* Rewrites a graph until the base instance becomes unsat. Returns
     the final version of the graph. *)
  let rec loop iteration fixed_point graph =
    
    if fixed_point then (
      
      debug invGenControl "  Fixed point reached." in
      graph
        
    ) else (

      (* Getting candidates invariants from equivalence classes and
         implications. *)
      let candidate_invariants =
        let eq_classes =
          Graph.eq_classes graph
          |> List.fold_left
               ( fun list set ->
                 match TSet.elements set with
                 | [t] -> list
                 | l -> (Term.mk_eq l) :: list )
               []
        in
                           
        List.concat [ eq_classes ;
                      Graph.non_trivial_implications graph ;
                      Graph.trivial_implications graph ]
      in

      match LSD.query_base lsd candidate_invariants with
        
      | Some model ->

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
           Graph.rewrite_graph eval graph
         in

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

  (* Graph.to_dot *)
  (*   (sprintf "dot/graph-[%s]-%i.dot" *)
  (*            (TransSys.get_scope sys |> String.concat "-") *)
  (*            (LSD.get_k lsd |> Numeral.to_int)) *)
  (*   graph ; *)

  debug invGenControl
        "Check step for [%s] at k = %i."
        (TransSys.get_scope sys |> String.concat "/")
        (LSD.get_k lsd |> Numeral.to_int)
  in

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
    List.concat [ eq_classes ; implications ]
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


     let impl_count =
       new_invariants
       |> List.fold_left
            ( fun sum inv ->
              if (Term.is_node inv)
                 && (Term.node_symbol_of_term inv = Symbol.s_implies)
              then sum + 1
              else sum )
            0
     in
     
     debug invGen
           "  %i invariants discovered (%i implications) \\*o*/ [%s]."
           (List.length new_invariants)
           impl_count
           (TransSys.get_scope sys |> String.concat "/")
     in
     
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
  let sys_graph_map =
    CandidateTerms.generate_implication_graphs [trans_sys] in

  debug invGenInit
        "Graph generation result:"
  in

  sys_graph_map
  |> List.iter
       ( fun (sys,_) ->
         debug invGenInit "  %s" (TransSys.get_scope sys
                                  |> String.concat "/") in () ) ;
  
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

    (* Incrementing the k. *)
    LSD.increment lsd ;

    (* Incrementing the k in confirmation lsd. *)
    ( match !confirmation_lsd_ref with
      | Some conf_lsd ->
         LSD.increment conf_lsd
      | None -> () ) ;

    (* if Numeral.(one < (LSD.get_k lsd)) then () *)
    (* else loop invariants' map' *)

    loop invariants' map'

  in

  loop TSet.empty sys_graph_map |> ignore

(* Cleans up things on exit. *)
let on_exit _ =
  
  (* Destroying lsd if one was created. *)
  match !lsd_ref with
  | None -> ()
  | Some lsd -> LSD.delete lsd ;
                
  (* Destroying confirmation lsd if one was created. *)
  match !confirmation_lsd_ref with
  | None -> ()
  | Some lsd -> LSD.delete lsd

(* Module entry point. *)
let main trans_sys =

  let lsd = LSD.create trans_sys in

  let confirmation_lsd = LSD.create trans_sys in

  (* Skipping k=0. *)
  LSD.increment lsd ;
  LSD.increment confirmation_lsd ;

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

