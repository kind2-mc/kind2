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

(* Inserts a system / graph pair in a list ordered by decreasing
   instantiation count. *)
let insert_sys_graph list ((sys,_) as pair) =

  let count = TransSys.instantiation_count in
  let sys_count = count sys in

  let rec loop prefix = function
    | ((sys',_) :: _) as l when sys_count >= count sys' ->
       List.rev_append prefix (pair :: l)
    | head :: tail ->
       loop (head :: prefix) tail
    | [] -> List.rev (pair :: prefix)
  in

  loop [] list
       

(* Generates a set of candidate terms from the transition system. *)
let generate_implication_graphs trans_sys =

  let flat_to_term = Term.construct in

  let bool_type = Type.mk_bool () in

  (* If a term only contains variables at -1 (resp. 0), also create
     the same term at 0 (resp. -1). *)
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
  in

  (* For all boolean term, also add its negation. *)
  let negation_rule set =
    TSet.fold
      (fun term -> TSet.add (Term.negate term))
      set
      set
  in

  (* Returns true when given unit. *)
  let true_of_unit () = true in

  (* Term set with true and false. *)
  let true_false_set =
    (TSet.of_list [ Term.mk_true () ; Term.mk_false () ])
  in

  (* List of (rule,condition). Rule will be used to generate candidate
     terms iff 'condition ()' evaluates to true. *)
  let rule_list =
    [ offset_rule  , true_of_unit ;
      negation_rule, true_of_unit ]
  in

  (* Applies the rules for the condition of which evaluates to
     true on a set of terms. *)
  let apply_rules set =
    List.fold_left
      ( fun set (rule, condition) ->
        if condition () then rule set else set )
      set
      rule_list
  in

  (* Builds a set of candidate terms from a term. *)
  let set_of_term t =
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
    (* Apply the candidate term generation rules. *)
    |> apply_rules
    (* Adding true and false. *)
    |> TSet.union true_false_set
  in

  (* Creates an associative list between systems and their implication graph. *)
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
           TSet.union (set_of_term init) (set_of_term trans)
           |> TSet.union true_false_set
         in

         debug invGen "System [%s]:" (scope |> String.concat "/") in
         debug invGen
               "  > %i candidate terms."
               (TSet.cardinal candidates)
         in

         let sorted_result =
           insert_sys_graph
             result
             (system, Graph.create candidates)
         in

         all_sys_graphs_maps
           sorted_result
           (List.concat [ TransSys.get_subsystems system ; tail ])

    | [] -> result
  in

  all_sys_graphs_maps [] trans_sys

(* Rewrites a graph until the base instance becomes unsat. *)
let rewrite_graph_until_unsat lsd sys graph =

  (* Rewrites a graph until the base instance becomes unsat. Returns
     the final version of the graph. *)
  let rec loop iteration fixed_point graph =
    
    if fixed_point then (
      
      debug invGen "  Fixed point reached." in
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
         debug invGen "Unsat." in

         (* Returning current graph. *)
         graph
    )
  in

  debug invGen
        "Starting graph rewriting for [%s] at k = %i."
        (TransSys.get_scope sys |> String.concat "/")
        (LSD.get_k lsd |> Numeral.to_int)
  in

  loop 1 false graph

(* Removes implications from a set of term for step. *)
let filter_step_implications term_set = term_set

(* Queries step to find invariants to communicate. *)
let find_invariants lsd invariants sys graph =

  debug invGen
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
     debug invGen "  No new invariants /T_T\\." in

     invariants
      
  | _ ->
     debug invGen
           "  %i invariants discovered \\*o*/."
           (List.length new_invariants)
    in

    new_invariants
    (* Instantiating new invariants at top level. *)
    |> List.map (TransSys.instantiate_term_top sys)
    |> List.flatten
    (* And-ing them. *)
    |> Term.mk_and
    (* Broadcasting them. *)
    |> Event.invariant ;

    (* Adding the new invariants to the old ones. *)
    new_invariants
    |> List.fold_left
         ( fun set t -> TSet.add t set )
         invariants

let rewrite_graph_find_invariants lsd invariants (sys,graph) =
  (* Rewriting the graph. *)
  let graph' = rewrite_graph_until_unsat lsd sys graph in
  (* At this point base is unsat, discovering invariants. *)
  let invariants' = find_invariants lsd invariants sys graph in
  (* Returning new mapping and the new invariants. *)
  (sys, graph'), invariants'

(* Generates invariants by splitting an implication graph. *)
let generate_invariants trans_sys lsd =

  (* Associative list from systems to candidate terms. *)
  let sys_graph_map = generate_implication_graphs [trans_sys] in

  let rec loop invariants map =

    debug invGen
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
                 lsd invs sys_graph
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

    loop invariants' map'

  in

  loop TSet.empty sys_graph_map |> ignore

(* Cleans up things on exit. *)
let on_exit _ =
  (* Destroying lsd if one was created. *)
  match !lsd_ref with
  | None -> ()
  | Some lsd -> LSD.delete lsd

(* Module entry point. *)
let main trans_sys =

  let lsd = LSD.create trans_sys in

  (* Skipping k=0. *)
  LSD.increment lsd ;

  lsd_ref := Some lsd ;

  generate_invariants trans_sys lsd


                      
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

