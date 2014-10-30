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
      (fun term -> TSet.add (Term.negate term))
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

  let bool_type = Type.mk_bool () in

  let set_of_term t =
    (Term.eval_t
       ( fun term ->
         List.fold_left
           TSet.union
           (TSet.singleton (Term.construct term)) )
       t)
    |> TSet.filter
         ( fun t -> (Term.type_of_term t) = bool_type )
    |> negation_rule
  in

  let uf_defs_pairs = TransSys.uf_defs_pairs trans_sys in

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

(* Generates invariants by splitting an implication graph. *)
let generate_invariants trans_sys lsd =

  (* Getting the candidate terms. *)
  let candidate_terms = generate_candidate_terms trans_sys in

  printf "\n%i candidate terms.\n" (TSet.cardinal candidate_terms) ;
  (* printf "\nCandidate terms (%i) {\n" (TSet.cardinal candidate_terms) ; *)
  (* candidate_terms *)
  (* |> TSet.iter (fun t -> printf "%s\n" (Term.string_of_term t)) ; *)
  (* printf "}\n" ; *)
  (* printf "\n" ; *)

  (* Creating an implication graph with just one node. *)
  let implication_graph = Graph.create candidate_terms in

  let rec loop invariants fixed_point graph iteration =

    let k = (LSD.get_k lsd) in

    (* debug invGen *)
    (*       "K is %2i, starting iteration %2i.\n" *)
    (*       Numeral.(to_int k) iteration *)
    (* in *)

    flush stdout ;
    
    if (Numeral.to_int k) > 200000
    then
      printf "Max k reached.\n"
    else if fixed_point then
      printf "Fixed point reached.\n"
    else (

      let
        (* Equivalence classes as n-ary equalities. *)
        (eq_classes,
         (* Equivalence classes as binary equalities for step. *)
         split_eq_classes) =
        
        ( Graph.eq_classes_of graph
          |> List.fold_left
               ( fun (list,list') set ->
                 match TSet.elements set with
                 | [t] -> (list, list')
                 | (t :: tail) as l ->
                    (* Equivalence class as an n-ary equality. *)
                    (Term.mk_eq l) :: list,
                    (* Equivalence class as binary equalities. *)
                    List.rev_append
                      (List.map
                         (fun t' -> Term.mk_eq [t ; t'])
                         tail )
                      list' )
               ([], []) )
      in

      let
        (* Implications different from (false -> _) and (_ ->
           true). *)
        (non_trivial_implications,
         (* Implications from false and to true: not used in step. *)
         trivial_implications) = Graph.implications_of graph
      in
      
      ( match LSD.query_base lsd (List.concat [eq_classes ;
                                               non_trivial_implications ;
                                               trivial_implications]) with
          
        | Some model ->
           let eval term =
             Eval.eval_term
               (TransSys.uf_defs trans_sys)
               model
               term
             |> Eval.bool_of_value
           in

           (* let t_start = Sys.time () in *)
           let (fixed_point, graph') = Graph.rewrite_graph eval graph in
           (* let rewrite_time = Sys.time () -. t_start in *)
           (* printf "Rewrite time: %f\n" rewrite_time ; *)

           loop invariants fixed_point graph' (iteration + 1)
                
        | None ->
           (* printf "Unsat, checking step.\n" ; *)
           (* if iteration > 0 then *)
           (*   Graph.to_dot (sprintf "dot/graph-%03i-%03i.dot" *)
           (*                         (LSD.get_k lsd |> Numeral.to_int) *)
           (*                         iteration) *)
           (*                graph ; *)

           let new_invariants =
             match LSD.query_step
                     lsd
                     (List.concat [split_eq_classes ;
                                   non_trivial_implications]) with

             | _, [] -> []

             | _, unfalsifiable ->
                unfalsifiable
                |> List.filter
                     (fun inv -> not (TSet.mem inv invariants))
           in

           let invariants' =
             match new_invariants with
             | [] ->
                debug invGen
                      "No invariants discovered at k=%i."
                      (Numeral.to_int k)
                in
                invariants
             | _ ->
                debug invGen
                      "Invariants discovered at k=%i (%i)."
                      (Numeral.to_int k)
                      (List.length new_invariants)
                in
                Event.invariant
                  (Term.mk_and new_invariants) ;
           
                new_invariants
                |> List.fold_left
                     ( fun set t ->
                       TSet.add t set )
                     invariants
           in
           
           LSD.increment lsd ;
           loop invariants' false graph 0 )
    )
  in

  loop TSet.empty false implication_graph 0 ;

  ()

(* Cleans up things on exit. *)
let on_exit _ =
  (* Destroying lsd if one was created. *)
  match !lsd_ref with
  | None -> ()
  | Some lsd -> LSD.delete lsd

(* Module entry point. *)
let main trans_sys =

  ()

  (* printf "\n" ; *)

  (* let scope_to_string = String.concat "/" in *)
  (* let scope_of ts = TransSys.get_scope ts |> scope_to_string in *)
  (* let subs_of ts = TransSys.get_subsystems ts in *)
  (* let string_of_uf uf = UfSymbol.string_of_uf_symbol uf in *)

  (* let rec print_scope_subsys prefix ts = *)
  (*   printf "%-40s" *)
  (*          ( sprintf "%sNode [%s]" *)
  (*                    prefix *)
  (*                    (scope_of ts) ) ; *)
  (*   printf "%-40s" *)
  (*          ( sprintf "| init: [%s]" *)
  (*                    (TransSys.init_uf_symbol ts |> string_of_uf) ); *)
  (*   printf "%-40s\n" *)
  (*          ( sprintf "| trans: [%s]" *)
  (*                    (TransSys.trans_uf_symbol ts |> string_of_uf) ); *)
  (*   subs_of ts *)
  (*   |> List.iter *)
  (*        (print_scope_subsys (sprintf "%s%s" prefix "  ")) *)
  (* in *)

  (* print_scope_subsys "" trans_sys ; *)

  (* printf "\n" ; *)

  
  (* Event.set_module `INVGEN ; *)

  (* let lsd = LSD.create trans_sys in *)

  (* (\* Skipping k=0. *\) *)
  (* LSD.increment lsd ; *)

  (* lsd_ref := Some lsd ; *)

  (* generate_invariants trans_sys lsd *)


                      
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

