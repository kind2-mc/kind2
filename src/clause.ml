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

(* Clause *)
type t = 

  {
    
    (* One activation literal for the positive, unprimed clause *)
    actlit_p0 : Term.t;

    (* One activation literal for the positive, primed clause  *)
    actlit_p1 : Term.t;

    (* One activation literal for each negated unprimed literal in
       clause *)
    actlits_n0 : Term.t list;
    
    (* One activation literal for each negated primed literal in
       clause *)
    actlits_n1 : Term.t list;

    (* Literals in clause, to be treated as disjunction *)
    literals: Term.t list;

    (* Clause before inductive generalization *)
    parent: t option;
      
  } 


(* Compare clauses by their lexicographically comparing their (sorted
   and duplicate-free lists of) literals *)
let compare { literals = l1 } { literals = l2 } =
  compare_lists Term.compare l1 l2

    
(* Clauses are equal if their (sorted and duplicate-free lists of)
   literals are equal *)
let equal { literals = l1 } { literals = l2 } =
  List.length l1 = List.length l2 && List.for_all2 Term.equal l1 l2


(* A trie of clauses *)
module ClauseTrie = Trie.Make (Term.TermMap)
  
  
(* Set of properties *)
type prop_set =

  {

    (* Clause of property set *)
    clause: t;

    (* Named properties *)
    props : (string * Term.t) list
    
  } 

(* ********************************************************************** *)
(* Activation literals                                                    *)
(* ********************************************************************** *)
    
(* Type of activation literal *)
type actlit_type = 
  | Actlit_p0  (* positive unprimed *)
  | Actlit_n0  (* negative unprimed *)
  | Actlit_p1  (* positive primed *)
  | Actlit_n1  (* negative primed *)


(* Get string tag for type of activation literal *)
let tag_of_actlit_type = function 
  | Actlit_p0 -> "p0"
  | Actlit_n0 -> "n0"
  | Actlit_p1 -> "p1"
  | Actlit_n1 -> "n1"

(* Counters for activation literal groups *)
let actlit_counts = ref []
  

(* Number of property sets considered *)
let prop_set_count = ref (- 1)

  
(* Prefix for name of activation literals to avoid name clashes *)
let actlit_prefix = "__pdr"


(* Process term for type of type of activation literal *)
let term_for_actlit_type term = function

  (* Return term unchanged *)
  | Actlit_p0 -> term

  (* Negate term *)
  | Actlit_n0 -> Term.negate term 

  (* Prime term *)
  | Actlit_p1 -> Term.bump_state Numeral.one term

  (* Negate and prime term *)
  | Actlit_n1 -> Term.bump_state Numeral.one term |> Term.negate 

      
(* Create an activation literal of given type for term, and assert
   term guarded with activation literal *)
let create_and_assert_fresh_actlit solver tag term actlit_type = 

  (* Get reference for counter of activation literal group *)
  let actlit_count_ref = 

    try 

      (* Return reference in association list *)
      List.assoc tag !actlit_counts 

    with Not_found ->

      (* Initialize reference *)
      let c = ref (-1) in 

      (* Add reference in association list *)
      actlit_counts := (tag, c) :: !actlit_counts;

      (* Return reference *)
      c

  in

  (* Increment counter for tag *)
  incr actlit_count_ref;

  SMTSolver.trace_comment 
    solver
    (Format.sprintf
       "create_and_assert_fresh_actlit: Assert activation literal %s for %s %d"
       (tag_of_actlit_type actlit_type)
       tag
       !actlit_count_ref);

  (* Name of uninterpreted function symbol primed negative *)
  let uf_symbol_name = 
    Format.asprintf "%s_%s_%d" 
      actlit_prefix
      tag
      !actlit_count_ref
  in

  (* Create uninterpreted constant *)
  let uf_symbol = 
    UfSymbol.mk_uf_symbol uf_symbol_name [] Type.t_bool
  in

  (* Return term of uninterpreted constant *)
  let actlit = Term.mk_uf uf_symbol [] in

  (* Declare symbols in solver *)
  SMTSolver.declare_fun solver uf_symbol;

  Stat.incr Stat.pdr_activation_literals;
  
  (* Prepare term for activation literal type *)
  let term' = term_for_actlit_type term actlit_type in

  (* Assert term in solver instance *)
  SMTSolver.assert_term 
    solver
    (Term.mk_implies [actlit; term']);

  (* Return activation literal *)
  actlit 


(* Create or return activation literal for frame [k] *)
let actlit_and_symbol_of_frame k = 

  (* Name of uninterpreted function symbol *)
  let uf_symbol_name = 
    Format.asprintf "%s_frame_%d" actlit_prefix k
  in

  (* Create or retrieve uninterpreted constant *)
  let uf_symbol = 
    UfSymbol.mk_uf_symbol uf_symbol_name [] Type.t_bool
  in

  (* Return term of uninterpreted constant *)
  let actlit = Term.mk_uf uf_symbol [] in
    
  (* Return uninterpreted constant and term *)
  (uf_symbol, actlit)

let actlit_of_frame k = actlit_and_symbol_of_frame k |> snd

let actlit_symbol_of_frame k = actlit_and_symbol_of_frame k |> fst
        
    
(* ********************************************************************** *)
(* Clauses                                                                *)
(* ********************************************************************** *)
    
    
(* Create three fresh activation literals for a list of literals and
   declare in the given solver instance *)
let clause_of_literals solver parent literals =

  (* Sort and eliminate duplicates *)
  let literals = Term.TermSet.(of_list literals |> elements) in
  
  (* Disjunction of literals *)
  let term = Term.mk_or literals in

  (* Create activation literals for positive clause *)
  let (actlit_p0, actlit_p1) =
    let mk = create_and_assert_fresh_actlit solver "clause" term in
    mk Actlit_p0, mk Actlit_p1
  in

  (* Create activation literals for negated literals in clause *)
  let actlits_n0, actlits_n1 =
    let mk t = 
      List.map 
        (fun l -> 
           create_and_assert_fresh_actlit solver "clause_lit" l t)
        literals
    in
    mk Actlit_n0, mk Actlit_n1
  in

  (* Return clause with activation literals *)
  { actlit_p0; actlits_n0; actlit_p1; actlits_n1; literals; parent }


(* Return disjunction of literals from a clause *)
let term_of_clause { literals } = Term.mk_or literals

(* Return literals from a clause *)
let literals_of_clause { literals } = literals

(* Activation literal for positve, unprimed clause *)
let actlit_p0_of_clause { actlit_p0 } = actlit_p0

(* Activation literal for positve, unprimed clause *)
let actlit_p1_of_clause { actlit_p1 } = actlit_p1

(* Activation literal for negative, unprimed clause *)
let actlits_n0_of_clause { actlits_n0 } = actlits_n0

(* Activation literal for negative, primed clause *)
let actlits_n1_of_clause { actlits_n1 } = actlits_n1

(* Get parent of clause *)
let rec parent_of_clause = function 
  | { parent = None } as clause -> clause 
  | { parent = Some c } -> parent_of_clause c

let length_of_clause { literals } = List.length literals

  
(* ********************************************************************** *)
(* Property sets                                                          *)    
(* ********************************************************************** *)

(* Create three fresh activation literals for a set of properties and
   declare in the given solver instance *)
let prop_set_of_props solver props = 

  (* Increment refercent for property set *)
  incr prop_set_count;

  SMTSolver.trace_comment 
    solver
    (Format.sprintf
       "actlits_of_propset: Assert activation literals for property set %d"
       !prop_set_count);

  (* Conjunction of property terms *)
  let term = List.map snd props |> Term.mk_and in

  (* Unit clause of term *)
  let literals = [term] in

  (* Create activation literals for terms *)
  let (actlit_p0, actlit_n0, actlit_p1, actlit_n1) =
    let mk = create_and_assert_fresh_actlit solver "prop" term in
    (mk Actlit_p0, mk Actlit_n0, mk Actlit_p1, mk Actlit_n1)
  in

  (* Return together with clause with activation literals *)
  { clause = 
      { actlit_p0; 
        actlits_n0 = [actlit_n0]; 
        actlit_p1; 
        actlits_n1 = [actlit_n1]; 
        literals; 
        parent = None } ;
    props }

(* Return conjunction of properties *)
let term_of_prop_set { clause } = term_of_clause clause

(* Return clause for property set *)
let clause_of_prop_set { clause } = clause

let props_of_prop_set { props } = props
  
let actlit_p0_of_prop_set { clause = { actlit_p0 } } = actlit_p0
  
let actlit_p1_of_prop_set { clause = { actlit_p1 } } = actlit_p1

let actlits_n0_of_prop_set { clause = { actlits_n0 } } = actlits_n0

let actlits_n1_of_prop_set { clause = { actlits_n1 } } = actlits_n1
    
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
