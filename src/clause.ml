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

  
(* Generate next unique identifier for clause *)
let next_clause_id =
  let r = ref 0 in
  fun () -> incr r; !r

    
(* Source of a clause *)
type source =
  | PropSet (* Clause is a pseudo clause for property set *)
  | BlockFrontier (* Negation of clause reaches a state outside the property in one step *)
  | BlockRec of t (* Negtion of clause reaches a state outside the
                     negation of the clause to block *)
  | IndGen of t (* Clause is an inductive generalization of the clause *)
  | CopyOf of t (* Clause is a copy of the clause *)

      
(* Clause *)
and t = 

    {

      (* Unique identifier for clause *)
      clause_id : int;
      
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

      (* Source of clause *)
      source: source;
      
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
  
(* Return clause before inductive generalization *)
let rec undo_ind_gen = function

  (* Clause is not an inductive generalization *)
  | { source = PropSet } 
  | { source = BlockFrontier }
  | { source = BlockRec _ } -> None

  (* Return inductive generalization of original clause *)
  | { source = IndGen c } -> Some c

  (* Return clause before inductive generalization *)
  | { source = CopyOf c } -> undo_ind_gen c

        
(* Return disjunction of literals from a clause *)
let term_of_clause { literals } = Term.mk_or literals

(* Return literals from a clause *)
let literals_of_clause { literals } = literals


(* Keep track of the status of each activation literal per solver instance

*)
  
(* For each solver instance a set of clause identifiers whose p0, p1,
   n0 and n1 activation literals have been declared and *)
let solver_actlit_status = IntegerHashtbl.create 7

  
(* Initial value for activation literal status *)
let actlit_status_default = 0

  
(* Initial size of activation literal status array *)
let actlit_array_size = 256 

  
(* Bit values for flags in activation literal status *)
let actlit_p0_bit = 1
let actlit_p1_bit = 2
let actlit_n0_bit = 4
let actlit_n1_bit = 8
let actlit_dead_bit = 16


  
(* Return the status of the activation literals of the clause in the
   solver instance 

   Add a new array for the solver instance on the first call, and
   epxand the array if it does not contain the clause. *)
let get_actlit_status_array solver clause_id =

  (* Identifier of solver instance *)
  let solver_id = SMTSolver.id_of_instance solver in
  
  try

    (* Get array of activation literal status from hash table for
       solver instance *)
    let actlit_status =
      IntegerHashtbl.find solver_actlit_status solver_id
    in

    (* Does array contain an entry for the clause? *)
    if Array.length actlit_status >= clause_id then

      (* Return activation literal status array *)
      actlit_status

    else

      (* Double array size *)
      let actlit_status' =
        Array.make
          (Array.length actlit_status * 2)
          actlit_status_default
      in

      (* Copy entries from previous array *)
      Array.blit
        actlit_status
        0
        actlit_status'
        0
        (Array.length actlit_status);

      (* Replace previous array with grown array *)
      IntegerHashtbl.replace
        solver_actlit_status
        solver_id
        actlit_status';

      (* Return activation literal status array *)
      actlit_status'

  (* Activation literal status array not created for solver instance *)
  with Not_found ->

    (* Initialize activation literal array of minimum size, or larger
       to accommodate clause *)
    let actlit_status =
      Array.make (min clause_id actlit_array_size) actlit_status_default
    in
    
    (* Add activation literal array for solver instance *)
    IntegerHashtbl.add
      solver_actlit_status
      solver_id
      actlit_status;

    (* Return activation literal status array *)
    actlit_status

      
(* Return status of activation literals of clause *)
let get_actlit_status_of_clause solver { clause_id } =
  (get_actlit_status_array solver clause_id).(clause_id)


(* Set status bit in of activation literal status of clause *)
let set_actlit_status_of_clause solver { clause_id } bit =

  (* Get activation literal status array *)
  let actlit_status_array =
    get_actlit_status_array solver clause_id
  in

  (* Set bit in value of array, and set array element to new value *)
  actlit_status_array.(clause_id)
    |> (lor) bit
    |> Array.set actlit_status_array clause_id

  
(* Activation literal for positve, unprimed clause *)
let actlit_p0_of_clause solver ({ actlit_p0; literals } as clause) =

  (* Get status of activation literals of clause *)
  let actlit_status = get_actlit_status_of_clause solver clause in

  (* Activation literals of clause set to false? *)
  if actlit_status land actlit_dead_bit <> 0 then

    raise (Invalid_argument "actlit_of_clause: Clause is dead");
    
  (* Activation literal not defined *)
  if actlit_status land actlit_p0_bit = 0 then
             
    (

      (* Get uninterpreted function symbol from term *)
      let uf_symbol =
        Term.node_symbol_of_term actlit_p0
        |> Symbol.uf_of_symbol
      in
      
      (* Declare symbol in solver *)
      SMTSolver.declare_fun solver uf_symbol;
      
      Stat.incr Stat.pdr_activation_literals;

      (* Assert implication from activation literal *)
      SMTSolver.assert_term
        solver
        (Term.mk_implies [actlit_p0; Term.mk_or literals]);

      (* Mark activation literal as defined *)
      set_actlit_status_of_clause solver clause actlit_p0_bit;
      
    );

  (* Return activation literal *)
  actlit_p0

    
(* Activation literal for positve, unprimed clause *)
let actlit_p1_of_clause { actlit_p1 } = actlit_p1

(* Activation literal for negative, unprimed clause *)
let actlits_n0_of_clause solver ({ actlits_n0; literals } as clause) =

  (* Get status of activation literals of clause *)
  let actlit_status = get_actlit_status_of_clause solver clause in

  (* Activation literals of clause set to false? *)
  if actlit_status land actlit_dead_bit <> 0 then

    raise (Invalid_argument "actlit_of_clause: Clause is dead");
    
  (* Activation literal not defined *)
  if actlit_status land actlit_n0_bit = 0 then
             
    (

      List.iter2
        (fun t l -> 
      
          (* Get uninterpreted function symbol from term *)
          let uf_symbol =
            Term.node_symbol_of_term t
            |> Symbol.uf_of_symbol
          in
      
          (* Declare symbol in solver *)
          SMTSolver.declare_fun solver uf_symbol;
          
          Stat.incr Stat.pdr_activation_literals;

          (* Assert implication from activation literal *)
          SMTSolver.assert_term
            solver
            (Term.mk_implies [t; Term.mk_not l]))

        actlits_n0
        literals;

      (* Mark activation literal as defined *)
      set_actlit_status_of_clause solver clause actlit_n0_bit;
      
    );

  (* Return activation literal *)
  actlits_n0
  

  

(* Activation literal for negative, primed clause *)
let actlits_n1_of_clause { actlits_n1 } = actlits_n1

(* Return number of literals in clause *)
let length_of_clause { literals } = List.length literals

(* Pretty-print the source of a clause *)
let pp_print_source ppf = function
  | PropSet -> Format.fprintf ppf "PropSet"
  | BlockFrontier -> Format.fprintf ppf "BlockFrontier"
  | BlockRec c -> Format.fprintf ppf "BlockRec %a" Term.pp_print_term (actlit_p0_of_clause c)
  | IndGen c -> Format.fprintf ppf "IndGen %a" Term.pp_print_term (actlit_p0_of_clause c)
  | CopyOf c -> Format.fprintf ppf "CopyOf %a" Term.pp_print_term (actlit_p0_of_clause c)

    
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
let mk_clause_of_literals source literals =

  (* Sort and eliminate duplicates *)
  let literals = Term.TermSet.(of_list literals |> elements) in
  
  (* Next unique identifier for clause *)
  let clause_id = next_clause_id () in

  (* Create uninterpreted function symbol *)
  let mk_uf_symbol tag =

    (* Name of uninterpreted function symbol *)
    let uf_symbol_name = 
      Format.asprintf "%s_%d_%s" 
        "__pdr_clause"
        clause_id
        tag
    in

    (* Create uninterpreted function symbol *)
    UfSymbol.mk_uf_symbol uf_symbol_name [] Type.t_bool
      
  in

  (* Create activation literal for positive unprimed clause *)
  let actlit_p0 = mk_uf_symbol "p0" |> (fun uf -> Term.mk_uf uf []) in

  (* Create activation literal for positive primed clause *)
  let actlit_p1 = mk_uf_symbol "p1" |> (fun uf -> Term.mk_uf uf []) in
  
  (* Create activation literals for negated unprimed literal *)
  let actlits_n0 =
    List.mapi
      (fun i _ ->
        mk_uf_symbol
          (Format.asprintf "n0_%d" i)
          |> (fun uf -> Term.mk_uf uf []))
      literals
  in

  (* Create activation literals for negated primed literal *)
  let actlits_n1 =
    List.mapi
      (fun i _ ->
        mk_uf_symbol
          (Format.asprintf "n1_%d" i)
          |> (fun uf -> Term.mk_uf uf []))
      literals
  in

  (* Return clause with activation literals *)
  { clause_id; actlit_p0; actlits_n0; actlit_p1; actlits_n1; literals; source }


(* 

(* Copy clause and all its parents with fresh activation literal *)
let rec copy_clause solver = function

  (* Clause without parent *)
  | { source = BlockFrontier as source; literals; actlit_p0 }
  | { source = BlockRec _ as source; literals; actlit_p0 }
  | { source = PropSet as source; literals; actlit_p0 } ->

    SMTSolver.trace_comment
      solver
      (Format.asprintf
         "Copying clause %a"
         Term.pp_print_term actlit_p0);
    
    (* Copy clause with no parents *)
    mk_clause_of_literals solver source literals 
    
  | { source = CopyOf p; literals; actlit_p0 } 
  | { source = IndGen p; literals; actlit_p0 } ->

    SMTSolver.trace_comment
      solver
      (Format.asprintf
         "Copying clause %a"
         Term.pp_print_term actlit_p0);
    
    (* Copy parent clauses first *)
    let p' = copy_clause solver p in

    (* Copy clause with copied parent *)
    mk_clause_of_literals solver (IndGen p') literals 

*)

let rec copy_clause solver ({ literals; actlit_p0 } as c) =
  mk_clause_of_literals (CopyOf c) literals 
      
  
(* ********************************************************************** *)
(* Property sets                                                          *)    
(* ********************************************************************** *)

(* Create three fresh activation literals for a set of properties and
   declare in the given solver instance *)
let prop_set_of_props props = 

  (* Increment reference for property set *)
  incr prop_set_count;

  (* Conjunction of property terms *)
  let term = List.map snd props |> Term.mk_and in

  (* Unit clause of term *)
  let literals = [term] in

  (* Create pseudo clause for propert set *)
  let clause = mk_clause_of_literals PropSet literals in
  
  (* Return together with clause with activation literals *)
  { clause; props }

    
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
