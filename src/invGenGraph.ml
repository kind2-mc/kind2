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

let bla = "bla"


(* Generates a set of candidate terms from the transition system. *)
let generate_candidate_terms trans_sys =

  let flat_to_term = Term.construct in

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

  let negation_rule set =
    TSet.fold
      (fun term -> TSet.add (Term.mk_not term))
      set
      set
  in

  let no_two_state_rule =
    TSet.filter
      ( fun term ->
        match Term.var_offsets_of_term term with
        | None, None -> true
        | Some n, _ when Numeral.(n = zero) -> true
        | _ -> false )
  in

  let set_of_term t =
    Term.eval_t
      ( fun term ->
        List.fold_left
          TSet.union
          (TSet.singleton (Term.construct term)
           |> offset_rule) )
      t
    |> no_two_state_rule
  in

  let uf_defs_pairs = TransSys.uf_defs_pairs trans_sys in

  let bool_type = Type.mk_bool () in

  uf_defs_pairs
  |> List.fold_left
       ( fun set ( (_ , (_,init)) , (_ , (_,trans)) ) ->

         (* printf "Init:\n" ; *)
         (* printf "%s\n" (Term.string_of_term init) ; *)
         (* printf "\n" ; *)

         (* printf "Trans:\n" ; *)
         (* printf "%s\n" (Term.string_of_term trans) ; *)
         (* printf "\n" ; *)

         let init_terms = set_of_term init in

         let trans_terms = Term.bump_state Numeral.(~- one) trans
                           |> set_of_term in

         (* TSet.union init_terms *) trans_terms |> TSet.union set )
       (TSet.of_list [ Term.mk_true () ; Term.mk_false () ])
  |> TSet.filter
       ( fun t -> (Term.type_of_term t) = bool_type )
  |> negation_rule

(* Generates invariants by splitting an implication graph. *)
let generate_invariants trans_sys lsd =

  (* Getting the candidate terms. *)
  let candidate_terms = generate_candidate_terms trans_sys in

  printf "\nCandidate terms (%i):\n" (TSet.cardinal candidate_terms) ;
  candidate_terms
  |> TSet.iter (fun t -> printf "  %s\n" (Term.string_of_term t)) ;
  printf "\n" ;
  printf "\n" ;

  (* Creating an implication graph with just one node. *)
  let implication_graph = Graph.create candidate_terms in

  let rec loop fixed_point graph iteration =

    let k = (LSD.get_k lsd) in

    printf "K is %2i, starting iteration %2i.\n"
           Numeral.(to_int k)
           iteration ;

    if (Numeral.to_int k) > 20
    then
      printf "Max k reached.\n"
    else if iteration > 10
    then
      printf "Max number of iterations reached.\n"
    else if fixed_point then
      printf "Fixed point reached.\n"
    else (

      let eq_classes,
          (non_trivial_implications,
           trivial_implications) =
        ( Graph.eq_classes_of graph
          |> List.fold_left
               ( fun list set ->
                 match TSet.elements set with
                 | [t] -> list
                 | l -> (Term.mk_eq l) :: list )
               [] ),
        Graph.implications_of graph
      in

      (* printf "Querying base@%s.\n" (LSD.get_k lsd |> Numeral.string_of_numeral) ; *)
      (* printf "Equivalence classes:\n" ; *)
      (* eq_classes |> List.iter (fun t -> printf "%s\n" (Term.string_of_term t)) ; *)
      (* printf "Implications:\n" ; *)
      (* implications |> List.iter (fun t -> printf "%s\n" (Term.string_of_term t)) ; *)
      (* printf "\n" ; *)
      
      ( match LSD.query_base lsd (List.concat [eq_classes ;
                                               non_trivial_implications ;
                                               trivial_implications]) with
          
        | Some model ->
           (* printf "Sat, got a model.\n" ; *)
           (* model *)
           (* |> List.iter *)
           (*      ( fun (var,t) -> *)
           (*        printf "  %s -> %s\n" *)
           (*               (Var.string_of_var var) *)
           (*               (Term.string_of_term t) ) ; *)
           (* Getting evaluation function. *)
           let eval term =
             Eval.eval_term
               (TransSys.uf_defs trans_sys)
               model
               term
             |> Eval.bool_of_value
           in

           let (fixed_point, graph') = Graph.rewrite_graph eval graph in
           Graph.to_dot (sprintf "dot/graph-%s-%i.dot"
                                 (LSD.get_k lsd |> Numeral.string_of_numeral)
                                 iteration)
                        graph' ;

           loop fixed_point graph' (iteration + 1)
                
        | None ->
           printf "Unsat, checking step.\n" ;
           
           ( match LSD.query_step
                     lsd
                     (List.concat [eq_classes ;
                                   non_trivial_implications]) with

             | _, [] ->
                printf "No invariants discovered, incrementing k.\n"

             | _, unfalsifiable ->
                printf "Invariants discovered {\n" ;
                unfalsifiable
                |> List.iter
                     (fun t -> printf "%s\n" (Term.string_of_term t)) ;
                printf "}\nIncrementing k now.\n"
           ) ;
           
           LSD.increment lsd ;
           loop false graph 0 )
    )
  in

  loop false implication_graph 0 ;

  ()

(* Cleans up things on exit. *)
let on_exit _ =
  (* Destroying lsd if one was created. *)
  match !lsd_ref with
  | None -> ()
  | Some lsd -> LSD.delete lsd

(* Module entry point. *)
let main trans_sys =

  Event.set_module `INVGEN ;

  let lsd = LSD.create trans_sys in

  lsd_ref := Some lsd ;

  generate_invariants trans_sys lsd
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

