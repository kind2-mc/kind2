(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

exception UnsupportedFeature of string

(* The model of variables, which IC3 generalizes into cubes: a model with
   arrays too large to read is not supported, and IC3 stops *)
let get_var_values solver bounds vars =
  try
    SMTSolver.get_var_values
      ~array_limit:(`Raise SMTSolver.max_array_elements) solver bounds vars
  with SMTSolver.Too_many_array_elements ->
    raise (UnsupportedFeature (Format.sprintf
      "IC3 stops: a model of the system has arrays of more than %d \
       elements, too many to read" SMTSolver.max_array_elements))

module C = Clause

(* Frame is a trie of clauses *)
module F = Clause.ClauseTrie

(* Check to make sure invariants of IC3 hold *)
let debug_assert = true

(* ********************************************************************** *)
(* Solver instances and cleanup                                           *)
(* ********************************************************************** *)

(* Per-engine state, domain-local: the IC3 engine of each analysis runs
   in its own domain and must not share these with other engines. Each
   accessor returns the domain-local reference. *)

(* Interpolation instance if created *)
let ref_interpolator =
  let key = Domain.DLS.new_key (fun () -> ref None) in
  fun () -> Domain.DLS.get key

let max_unrolling =
  let key = Domain.DLS.new_key (fun () -> ref 0) in
  fun () -> Domain.DLS.get key

(* Formatter to output inductive clauses to *)
let ppf_inductive_assertions =
  let key = Domain.DLS.new_key (fun () -> ref Format.std_formatter) in
  fun () -> Domain.DLS.get key

  
(* Output statistics *)
let print_stats () = 

  KEvent.stat
    ([Stat.misc_stats_title, Stat.misc_stats] @
     (if Flags.IC3QE.abstr () = `IA then 
        [Stat.ic3_stats_title, Stat.ic3_stats;
         Stat.ic3ia_stats_title, Stat.ic3ia_stats]
      else 
        [Stat.ic3_stats_title, Stat.ic3_stats]) @
     [Stat.smt_stats_title, Stat.smt_stats])


(* Cleanup before exit *)
let on_exit _ = 

  (* Stop all timers *)
  Stat.ic3_stop_timers ();
  Stat.smt_stop_timers ();

  (* Output statistics *)
  print_stats () ;

  (* Delete solvers in quantifier elimination*)
  QE.on_exit ()


(* ********************************************************************** *)
(* Exception raised in proof process                                      *)
(* ********************************************************************** *)


(* All remaining properties are valid *)
exception Success of int * Term.t

(* Counterexample trace for some property *)
exception Counterexample of C.t list 

(* Property disproved by other module *)
exception Disproved of string

(* Restart for other reason *)
(* exception Restart *)



(* ********************************************************************** *)
(* Utility functions                                                      *)
(* ********************************************************************** *)

(* Receive and handle events 

   Assert new invariants received and terminate on message *)
let handle_events
    solver
    input_sys 
    aparam 
    trans_sys
    props =

  (* Receive queued messages 

     Side effect: Terminate when ControlMessage TERM is received.*)
  let messages = KEvent.recv () in

  (* Update transition system from messages *)
  let new_invs, _ = 
    KEvent.update_trans_sys input_sys aparam trans_sys messages 
  in

  (* Upper bound's exclusive. *)
  Unroller.assert_new_invs_to solver Numeral.(succ one) new_invs ;

  (* Restart if one of the properties to prove has been disproved *)
  List.iter
    (fun (p, _) -> match TransSys.get_prop_status trans_sys p with 
       | Property.PropFalse _ -> raise (Disproved p)
       | _ -> ())
    props


(* Compute the frame sizes of a delta-encoded list of frames *)
let frame_sizes frames = 

  let rec aux accum = function 

    (* All frames added up, return accumulator *)
    | [] -> accum

    (* Take first frame *)
    | f :: tl -> 

      match accum with 

        (* No previous frame: take size of frame *)
        | [] -> aux [F.cardinal f] tl

        (* Add size of frame to size of previous frame *)
        | h :: _ -> aux (((F.cardinal f) + h) :: accum) tl

  in

  (* Start with empty accumulator *)
  aux [] frames


(* Compute the frame sizes of a delta-encoded list of frames in a
   blocking trace *)
let frame_sizes_block frames trace = 

  (* Frames with frames from trace *)
  let frames' = List.rev_append (List.map snd trace) frames in

  frame_sizes frames'

    
(* ************************************************************************ *)
(* Soundness check                                                          *)
(* ************************************************************************ *)

(* Check if for two successive frames R_i-1 & T |= R_i *)
let rec check_frames' solver prop_set accum = function

  | [] -> true

  | (r_i : C.t F.t) :: tl ->

    (* Check if all successors of frame are in the next frame *)
    let is_rel_ind () = 

      SMTSolver.trace_comment 
        solver
        (Format.sprintf 
           "check_frames: Does R_%d & T |= R_%d hold?"
           (List.length tl)
           (List.length tl |> succ));

      (* Activation literal for conjunction of clauses *)
      let actlit_n1 = 
        C.create_and_assert_fresh_actlit 
          solver
          "check_frames" 
          (List.map
             C.term_of_clause
             ((C.clause_of_prop_set prop_set) :: (F.values r_i) @ accum)
              |> Term.mk_and)
          C.Actlit_n1
      in

      if
        
        (* Check P[x] & R_i-1[x] & T[x,x'] |= R_i[x'] & P[x'] *)
        SMTSolver.check_sat_assuming_tf
          solver
          
          ((* Clauses of R_i are on rhs of entailment *)
            actlit_n1 ::

              (match tl with 

                (* Preceding frame is not R_0 *)
                | r_pred_i :: _ -> 

                  C.actlit_p0_of_prop_set solver prop_set :: 
                    
                    List.map (C.actlit_p0_of_clause solver) accum @ 

                    (* Clauses of R_i are in R_i-1, assert on lhs of entailment *)     
                    List.map (C.actlit_p0_of_clause solver) (F.values r_i) @ 

                    (* Assert clauses of R_i-1 on lhs of entailment *)
                    List.map (C.actlit_p0_of_clause solver) (F.values r_pred_i)

                (* Preceding frame is R_0, assert initial state only *)
                | [] -> [C.actlit_of_frame 0]))

      then

        (* Fail if entailment does not hold *)
        false

      else
        
        (

          (* Deactivate activation literal *)
          Term.mk_not actlit_n1 |> SMTSolver.assert_term solver;
          Stat.incr Stat.ic3_stale_activation_literals;
          
          (* Check preceding frames if entailment holds *)
          check_frames' solver prop_set ((F.values r_i) @ accum) tl

        )

    in

    (* Check if all clauses in frame are initial *)
    let rec is_initial = function 

      (* Check if first clause is initial *)
      | c :: ctl -> 

        SMTSolver.trace_comment 
          solver
          (Format.sprintf 
             "check_frames: Does I |= C for C in R_%d hold?"
             (List.length tl |> succ));

        if
          
          (* Check if clause is initial *)
          SMTSolver.check_sat_assuming_tf 
            solver

            (* Check I |= C *)
            ((C.actlit_of_frame 0) :: C.actlits_n0_of_clause solver c)

        then
          
          (* If sat: Clause is not initial *)
          false

        else
          
          (* If unsat: continue with next clause *)
          is_initial ctl
            
      (* All clauses are initial, now check if frame successors of
         frame are in the next frame *)
      | [] -> is_rel_ind ()

    in

    SMTSolver.trace_comment 
      solver
      (Format.sprintf 
         "check_frames: Does R_%d |= P hold?"
         (List.length tl |> succ));

    SMTSolver.check_sat_assuming
      solver
      (fun _ -> ())
      (fun _ -> ())

      (* Check R_i |= P *)
      (C.actlits_n0_of_prop_set solver prop_set @
         List.map (C.actlit_p0_of_clause solver) ((F.values r_i) @ accum));
          
      (* Property may or may not be implied by frame, keep on
         checking *)
      is_initial (F.values r_i)




let check_frames solver prop_set clauses frames =

  SMTSolver.trace_comment
    solver
    (Format.asprintf
       "@[<v>check_frames: frames k to 1@,%a@]"
       (pp_print_list
          (fun ppf r_i -> 
            Format.fprintf ppf
              "@,Frame:@,%a"
              (pp_print_list
                 (fun ppf c ->
                   Format.fprintf ppf
                     "%d"
                     (C.id_of_clause c))
                 "@,")
              (F.values r_i))
          "@,")
       frames);
  
  check_frames' solver prop_set clauses frames 


(*let order_terms terms term_tbl =

  List.sort 
    (fun t1 t2 -> 
       let v1 = 
         try Term.TermHashtbl.find term_tbl t1 with Not_found -> 0 
       in
       let v2 = 
         try Term.TermHashtbl.find term_tbl t2 with Not_found -> 0 
       in
       v1 - v2)
    terms


let incr_binding term term_tbl =

  let v = 

    try

      Term.TermHashtbl.find term_tbl term

    with Not_found -> 

      0 

  in

  Term.TermHashtbl.add term_tbl term (v+1)*)


(* ************************************************************************ *)
(* Utility functions for subsumption                                        *)
(* ************************************************************************ *)

(* Return the number of subsumed clauses and increment statistics 

   Pipe the result of Trie.S.subsume through this function. *)
let count_subsumed solver (c, f) =

  (* Number of subsumed clauses *)
  let num = List.length c in

  (* Only if at least one clause subsumed *)
  if num > 0 then
  
    (SMTSolver.trace_comment
       solver
       (Format.sprintf
          "@[<v>Backward subsumed %d clauses in R_k@]" num);

     (* Increment statistics *)
     Stat.incr ~by:num Stat.ic3_back_subsumed);

  (* Return result unchanged *)
  (c, f)
    
    

(* Deactivate activation literals of subsumed clauses *)
let deactivate_subsumed solver (subsumed, frame') =

  (* Deactivate activation literals for each subsumed clause *)
  List.iter
    (fun (_, c) -> C.deactivate_clause solver c)
    subsumed;
  
  (subsumed, frame')

(* ************************************************************************ *)
(* Inductive generalization                                                 *)
(* ************************************************************************ *)
    
(* Inductively generalize [clause] relative to [frame]

   Assuming that [clause] is relatively inductive to [frame] and
   initial, find a smaller subclause of [clause] that is still
   relatively inductive to [frame] and initial. *)
let ind_generalize solver prop_set frame clause literals =

  (* Linearly traverse the list of literals in the clause, and remove
     a literal the clause without the literal remains relatively
     inductive and initial

     [kept] are the literals that cannot be removed. 

  *)
  let rec linear_search kept = function

    (* All literals considered, return literals that had to be kept *)
    | [] ->

      (* Could we drop literals? *)
      if List.length kept = C.length_of_clause clause then 

        (* Return clause unchanged *)
        clause

      else

        (

          SMTSolver.trace_comment solver
            (Format.sprintf 
               "ind_generalize: Dropped %d literals from clause."
               (C.length_of_clause clause - List.length kept));

          (* Deactivate activation literal of parent clause *)
          C.deactivate_clause solver clause;
          
          (* New clause with generalized clause as parent *)
          let clause' = C.mk_clause_of_literals (C.IndGen clause) kept in
          
          SMTSolver.trace_comment solver
            (Format.asprintf 
               "@[<hv>New clause from inductive generalization of #%d:@ #%d @[<hv 1>{%a}@]@]"
               (C.id_of_clause clause)
               (C.id_of_clause clause')
               (pp_print_list Term.pp_print_term ";@ ")
               (C.literals_of_clause clause'));
          
          clause'
            
        )

    (* Do not try to generalize to the empty clause, this should not
       be possible in a sound transition system *)
    | l :: [] when kept = [] -> linear_search [l] []

    | l :: tl ->

      (* Clause without current literal *)
      let clause' = kept @ tl |> Term.mk_or in

      (* Actiation literal for clause *)
      let clause'_actlit_p0, clause'_actlit_n0, clause'_actlit_n1 = 
        let mk = C.create_and_assert_fresh_actlit solver "ind_gen" clause' in 
        mk C.Actlit_p0, mk C.Actlit_n0, mk C.Actlit_n1
      in

      (* Keep literal and try with following literals *)
      let keep_literal () =

        (* Deactivate activation literal *)
        Term.mk_not clause'_actlit_p0 |> SMTSolver.assert_term solver;
        Term.mk_not clause'_actlit_n0 |> SMTSolver.assert_term solver;
        Term.mk_not clause'_actlit_n1 |> SMTSolver.assert_term solver;
        Stat.incr ~by:3 Stat.ic3_stale_activation_literals;
        
        linear_search (l :: kept) tl

      in

      (* Drop literal and try with following literals *)
      let drop_literal () =

        (* Deactivate activation literal *)
        Term.mk_not clause'_actlit_p0 |> SMTSolver.assert_term solver;
        Term.mk_not clause'_actlit_n0 |> SMTSolver.assert_term solver;
        Term.mk_not clause'_actlit_n1 |> SMTSolver.assert_term solver;
        Stat.incr ~by:3 Stat.ic3_stale_activation_literals;
        
        linear_search kept tl

      in

      (* Clause without literal is initial *)
      let is_initial () = 

        SMTSolver.trace_comment solver
          "ind_generalize: Checking if clause without literal is \
           relatively inductive.";

        if 
          
          SMTSolver.check_sat_assuming_tf 
            solver
            
            (* Check P[x] & R[x] & C[x] & T[x,x'] |= C[x'] *)
            (C.actlit_p0_of_prop_set solver prop_set ::
               clause'_actlit_p0 ::
               clause'_actlit_n1 ::
               frame)

        then
          
          (* If sat: Clause without literal is not relatively inductive *)
          keep_literal ()

        else
          
          (* If unsat: Clause without literal is relatively inductive *)
          drop_literal ()

      in

      SMTSolver.trace_comment solver
        "ind_generalize: Checking if clause without literal is initial.";

      if
        
        SMTSolver.check_sat_assuming_tf 
          solver

          (* Check I |= C *)
          ([clause'_actlit_n0; C.actlit_of_frame 0])

      then
        
        (* If sat: Clause without literal is not initial *)
        keep_literal ()

      else
        
        (* If unsat: Clause without literal is initial *)
        is_initial ()


  in

  linear_search [] literals

(*


      let kept_woc = C.remove c kept in

  let block_term = C.to_term kept_woc in
  let primed_term = Term.mk_and (List.map (fun t -> Term.mk_not (Term.bump_state Numeral.one t)) (C.elements kept_woc)) in

  let init = SMTSolver.check_sat_term solver_init [Term.mk_not block_term] in
  let (cons, model) = SMTSolver.check_sat_term_model solver_frames [(Term.mk_and [block_term;primed_term])] in

  (* If, by removing the literal c, the blocking clause then
       either a. becomes reachable in the inital state or b. satisfies
       consecution then we need to keep it *)
  if cons || init then 

    (debug ic3
           "@[<v>%a@]"
           (pp_print_list 
              (fun ppf (v, t) -> 
               Format.fprintf ppf 
                              "(%a %a)"
                              Var.pp_print_var v
                              Term.pp_print_term t)
              "@,")
           model
     in

     linear_search kept discarded cs)

  else (

    debug ic3 "Removing literal: %a" Term.pp_print_term c in

    incr_binding c term_tbl;

    Stat.incr Stat.ic3_literals_removed;

    linear_search kept_woc (c :: discarded) cs

  )
  | [] ->  kept, C.of_literals discarded
                                    

                                    
    in

    let binary_search kept clause =
      
      let discarded = ref [] in
      
      let rec binary_search kept clause =
        let block_term = C.to_term (C.of_literals kept) in
        let primed_term = Term.mk_and (List.map (fun t -> Term.bump_state Numeral.one (Term.mk_not t)) kept) in
        
        let init = SMTSolver.check_sat_term solver_init [Term.mk_not block_term] in
        let cons = SMTSolver.check_sat_term solver_frames [(Term.mk_and [block_term;primed_term])] in
        
        if not (cons || init) then (
          discarded := !discarded @ (Array.to_list clause);
          []
        )
        else if Array.length clause < 2 then
          Array.to_list clause
        else
          let m = (Array.length clause) / 2 in
          let t1 = Array.sub clause 0 (m/2) in
          let t2 = Array.sub clause ((m/2)+1) m in
          let m2 = binary_search (kept @ (Array.to_list t1)) t2 in
          let m1 = binary_search (kept @ m2) t1 in      
          m1 @ m2
      in
      
      (C.of_literals (binary_search kept clause)), (C.of_literals !discarded)

    in


    
    let block_term = C.to_term clause in
    let primed_term = Term.mk_and (List.map (fun t -> Term.mk_not (Term.bump_state Numeral.one t)) (C.elements clause)) in

    let init = SMTSolver.check_sat_term solver_init [Term.mk_not block_term] in
    let (cons,model) = SMTSolver.check_sat_term_model solver_frames [(Term.mk_and [block_term;primed_term])] in

    (debug ic3
           "@[<v>%a@]"
           (pp_print_list 
              (fun ppf (v, t) -> 
               Format.fprintf ppf 
                              "(%a %a)"
                              Var.pp_print_var v
                              Term.pp_print_term t)
              "@,")
           model
     in

     assert (not cons));
    
    let k,d = match Flags.IC3.inductively_generalize() with
      | 1 -> linear_search clause [] (C.elements clause)
      | 2 -> linear_search clause [] (order_terms (C.elements clause) term_tbl)
      | 3 -> binary_search [] (Array.of_list (C.elements clause))
      | _ -> clause , C.empty
    in



    debug ic3
          "@[<v>Reduced blocking clause to@,@[<v>%a@]"
          (pp_print_list Term.pp_print_term "@,") 
          (C.elements k)
    in

    k,d

*)


(* ************************************************************************ *)
(* Extrapolation from a two-state counterexample                            *)
(* ************************************************************************ *)

(* ************************************************************************ *)
(* Abstraction of function symbols in the generalization                    *)
(* ************************************************************************ *)

(* The function symbols of the system that quantifier elimination does not
   reason about: those of abstract functions (imported functions, functions
   abstracted by their contracts, ...) and of recursive functions defined at
   the SMT level. Empty if the system has none. *)
let abstracted_ufs =
  let key = Domain.DLS.new_key (fun () -> ref UfSymbol.UfSymbolSet.empty) in
  fun () -> Domain.DLS.get key

let set_abstracted_ufs trans_sys =
  abstracted_ufs () :=
    TransSys.fold_subsystems ~include_top:true
      (fun acc ts ->
        let acc =
          List.fold_left (fun acc uf -> UfSymbol.UfSymbolSet.add uf acc)
            acc (TransSys.get_function_symbols ts)
        in
        List.fold_left
          (List.fold_left (fun acc (uf, _, _) -> UfSymbol.UfSymbolSet.add uf acc))
          acc (TransSys.get_rec_fun_defs ts))
      UfSymbol.UfSymbolSet.empty trans_sys

(* The term has a quantifier, which the generalization does not eliminate *)
exception Quantified_term

(* The generalization abstracts the system over application variables: a
   state variable [a] for each shape of application [f(t)] of an abstracted
   symbol, with [a' = f(t')] after each transition, [a = f(t)] in the
   initial states, and the congruence of the application variables of a
   symbol, [t = u => a = b] for [a = f(t)] and [b = f(u)], in both states.
   The abstract system is the system with the applications as function
   outputs, which Kind 2 gives a state variable each: the quantifier
   elimination sees variables only, and the cubes, clauses and frames are
   over the variables of the system and the application variables. The
   checks of IC3QE keep the symbols, so a proof holds of the system, and a
   counterexample of the abstraction is checked on the system (see
   [cex_of_trace]).

   A shape is an application over the variables at offset zero, or at
   offsets zero and one, as [f(x + y')], for an application over the two
   states, whose variable is defined after a transition only. A shape
   without variables, the output of a function without inputs or over
   constants, has a constant variable. *)
type app_var =
{
  shape : Term.t ;
  var : StateVar.t ;
  (* The offsets of the variables of the shape *)
  offsets : [ `None | `Zero | `Mixed ] ;
}

(* The scope of the variables IC3QE adds, which no system has: with the
   identifier of the analysis, as the variables of an analysis outlive it
   (the certificates and invariants of other analyses may mention them), and
   a variable of another analysis with the same name may have another type *)
let ic3qe_scope uid = [ "__ic3qe" ; "a" ^ string_of_int uid ]

let is_ic3qe_var sv =
  match StateVar.scope_of_state_var sv with
  | "__ic3qe" :: _ -> true
  | _ -> false

(* Whether a term is over the variables of the system alone, without those
   IC3QE adds, which the other engines do not know *)
let system_term term =
  not (StateVar.StateVarSet.exists is_ic3qe_var (Term.state_vars_of_term term))

(* The abstraction: the scope of the variables IC3QE adds; the application
   variables, those declared in the solver of IC3QE and those not yet; the
   instances of the variables declared; the bounds of the array variables
   of the system, where those of the variables IC3QE adds are recorded; the
   definitions of the application variables after a transition, with the
   applications; the constraints over the variables IC3QE adds, over
   offsets zero and one, and those on the initial state; and the history of the refinements (see
   [refine]): for each delay [d], the variable that says the history is [d]
   steps long, and for each application variable and delay the variables of
   the arguments and of the value of the application [d] steps earlier; the
   lemmas added; the number of refinements done, and of variables created *)
type abstraction =
{
  scope : string list ;
  mutable app_vars : app_var list ;
  mutable declared : app_var list ;
  mutable pending : app_var list ;
  mutable vars : Var.t list ;
  bounds : (LustreExpr.expr LustreExpr.bound_or_fixed list) StateVar.StateVarHashtbl.t ;
  mutable definitions : Term.t list ;
  mutable constraints : Term.t list ;
  mutable init_constraints : Term.t list ;
  mutable valid : (int * StateVar.t) list ;
  mutable cells : ((StateVar.t * int) * (StateVar.t list * StateVar.t)) list ;
  mutable lemmas : (StateVar.t * StateVar.t * int) list ;
  mutable refinements : int ;
  mutable counter : int ;
}

let empty_abstraction scope bounds =
  { scope ; app_vars = [] ; declared = [] ; pending = [] ; vars = [] ; bounds ;
    definitions = [] ; constraints = [] ; init_constraints = [] ;
    valid = [] ; cells = [] ; lemmas = [] ; refinements = 0 ; counter = 0 }

let abstraction_key =
  Domain.DLS.new_key (fun () ->
    empty_abstraction (ic3qe_scope 0) (StateVar.StateVarHashtbl.create 1))

let abstraction () = Domain.DLS.get abstraction_key

(* Start the abstraction of an analysis *)
let reset_abstraction aparam trans_sys =
  Domain.DLS.set abstraction_key
    (empty_abstraction
       (ic3qe_scope (Analysis.info_of_param aparam).Analysis.uid)
       (TransSys.get_state_var_bounds trans_sys))

(* A fresh variable of IC3QE *)
let mk_ic3qe_var ?(is_const = false) name ty =
  let a = abstraction () in
  a.counter <- a.counter + 1 ;
  StateVar.mk_state_var ~is_input:false ~is_const ~for_inv_gen:false
    (Format.sprintf "%s_%d" name a.counter) a.scope ty

let at0 sv = Term.mk_var (Var.mk_state_var_instance sv Numeral.zero)
let at1 sv = Term.mk_var (Var.mk_state_var_instance sv Numeral.one)

let symbol_of_shape shape =
  match Term.destruct shape with
  | Term.T.App (s, _) | Term.T.Const s -> s
  | _ -> assert false

let args_of_shape shape =
  match Term.destruct shape with
  | Term.T.App (_, args) -> args
  | _ -> []

(* The instances of an application variable: the constant, or at offsets
   zero and one, or at offset one only for a shape over the two states *)
let instances_of_app_var av =
  match av.offsets with
  | `None -> [ Var.mk_const_state_var av.var ]
  | `Zero ->
    [ Var.mk_state_var_instance av.var Numeral.zero ;
      Var.mk_state_var_instance av.var Numeral.one ]
  | `Mixed -> [ Var.mk_state_var_instance av.var Numeral.one ]

(* The instance of an application variable at an offset, with its shape
   there; for a shape over the two states, the offset of the later one *)
let app_var_at av k =
  match av.offsets with
  | `None -> Term.mk_var (Var.mk_const_state_var av.var), av.shape
  | `Zero ->
    Term.mk_var (Var.mk_state_var_instance av.var k), Term.bump_state k av.shape
  | `Mixed ->
    Term.mk_var (Var.mk_state_var_instance av.var k),
    Term.bump_state (Numeral.pred k) av.shape

(* The application variable of an application, created if it is new. The
   application is over the variables of the system and application
   variables, for the applications in its arguments. *)
let app_var_of_application app =
  let a = abstraction () in
  (* An application over the variable of a shape over the two states is
     over the two states too, as that variable has an instance at offset
     one only *)
  let over_mixed =
    StateVar.StateVarSet.exists (fun sv ->
      List.exists (fun av ->
        av.offsets = `Mixed && StateVar.equal_state_vars av.var sv) a.app_vars)
      (Term.state_vars_of_term app)
  in
  let offsets, shape =
    match Term.var_offsets_of_term app with
    | None, None -> `None, app
    | Some lo, Some hi when Numeral.equal lo hi && not over_mixed ->
      `Zero, Term.bump_state (Numeral.neg lo) app
    | Some _, Some hi -> `Mixed, Term.bump_state (Numeral.sub Numeral.one hi) app
    | _ -> assert false
  in
  match List.find_opt (fun av -> Term.equal av.shape shape) a.app_vars with
  | Some av -> av
  | None ->
    let av =
      { shape ; offsets ;
        var =
          mk_ic3qe_var ~is_const:(offsets = `None) "app"
            (Term.type_of_term shape) }
    in
    a.app_vars <- a.app_vars @ [ av ] ;
    a.pending <- a.pending @ [ av ] ;
    av

(* The term with the predicates of [uf_defs] inlined and each application of
   an abstracted symbol replaced by its application variable, at the offset
   of the application. Raises [Quantified_term] if the term or a predicate
   it applies has a quantifier. *)
let abstract_ufs uf_defs term =
  let abstracted = !(abstracted_ufs ()) in
  let memo = Term.TermHashtbl.create 17 in
  let app_var uf args =
    let app = Term.mk_uf uf args in
    let av = app_var_of_application app in
    let k =
      match snd (Term.var_offsets_of_term app) with
      | Some k -> k
      | None -> Numeral.zero
    in
    fst (app_var_at av k)
  in
  let rec abstract term =
    match Term.TermHashtbl.find_opt memo term with
    | Some t -> t
    | None ->
      if Term.has_quantifier term then raise Quantified_term ;
      let t =
        Term.eval_t ~fail_on_quantifiers:true (fun flat args ->
          match flat with
          | Term.T.Var v -> Term.mk_var v
          (* An application without arguments, such as the output of a
             function without inputs, is a constant *)
          | Term.T.Const s -> (
            match Symbol.node_of_symbol s with
            | `UF uf when UfSymbol.UfSymbolSet.mem uf abstracted -> app_var uf []
            | _ -> Term.mk_const s)
          | Term.T.App (s, _) -> (
            match Symbol.node_of_symbol s with
            | `UF uf when List.mem_assq uf uf_defs ->
              let vars, def = List.assq uf uf_defs in
              abstract (Term.apply_subst (List.combine vars args) def)
            | `UF uf when UfSymbol.UfSymbolSet.mem uf abstracted ->
              app_var uf args
            | _ -> Term.mk_app s args))
          term
      in
      Term.TermHashtbl.add memo term t ;
      t
  in
  abstract term

(* The clauses of a conjunction that are over the variables of the system.
   A clause over the variables IC3QE adds is left out: no system has them,
   and with the applications in place of the application variables the
   clause would have applications of the symbols, which the evaluation of
   a term in a model does not interpret. *)
let system_clauses term =
  let clauses =
    match Term.destruct term with
    | Term.T.App (s, args) when Symbol.node_of_symbol s = `AND -> args
    | _ -> [ term ]
  in
  List.filter system_term clauses

(* Declare variables IC3QE adds: in its solver, and in the solver of the
   quantifier elimination *)
let declare_ic3qe_vars solver vars =
  let a = abstraction () in
  a.vars <- a.vars @ vars ;
  (* The values of an array variable are read with its bounds, which a
     variable IC3QE adds does not have: it is unbounded, and has no value in
     the models *)
  List.iter (fun v ->
    let ty = Var.type_of_var v in
    if Type.is_array ty then
      StateVar.StateVarHashtbl.replace a.bounds
        (Var.state_var_of_state_var_instance v)
        (List.map (fun _ -> LustreExpr.Unbound None)
           (Type.all_index_types_of_array ty))) vars ;
  Var.declare_all_vars (SMTSolver.declare_fun solver) vars ;
  QE.declare_vars vars

(* Add a constraint of the abstraction: to the solver of IC3QE, and to the
   constraints the generalization sees, which are over the variables IC3QE
   adds and those of the system, without the symbols *)
let add_constraint solver c =
  let a = abstraction () in
  a.constraints <- c :: a.constraints ;
  SMTSolver.assert_term solver c

(* Add the definition of an application variable after a transition, with
   the application: to the solver of IC3QE, and to the definitions, which
   the generalization does not see (the definition is trivial once the
   application is abstracted) *)
let add_definition solver c =
  let a = abstraction () in
  a.definitions <- c :: a.definitions ;
  SMTSolver.assert_term solver c

(* Add a constraint on the initial state *)
let add_init_constraint solver c =
  let a = abstraction () in
  a.init_constraints <- c :: a.init_constraints ;
  SMTSolver.assert_term solver (Term.mk_implies [ C.actlit_of_frame 0 ; c ])

(* The congruence of two application variables of a symbol at an offset:
   equal arguments give equal values *)
let congruence av bv k =
  let a, sa = app_var_at av k and b, sb = app_var_at bv k in
  Term.mk_implies
    [ Term.mk_and
        (List.map2 (fun x y -> Term.mk_eq [ x ; y ])
           (args_of_shape sa) (args_of_shape sb)) ;
      Term.mk_eq [ a ; b ] ]

(* Declare the application variables not declared yet in the solver of
   IC3QE, with their constraints: their definition, after a transition and
   in the initial state, and their congruence with the application
   variables of the symbol declared before *)
let declare_pending solver =
  let a = abstraction () in
  let pending = a.pending in
  a.pending <- [] ;
  List.iter (fun av ->
    declare_ic3qe_vars solver (instances_of_app_var av) ;
    let def k = let v, s = app_var_at av k in Term.mk_eq [ v ; s ] in
    (match av.offsets with
     | `None -> add_definition solver (def Numeral.zero)
     | `Zero ->
       add_definition solver (def Numeral.one) ;
       add_init_constraint solver (def Numeral.zero)
     | `Mixed -> add_definition solver (def Numeral.one)) ;
    List.iter (fun bv ->
      if symbol_of_shape bv.shape == symbol_of_shape av.shape then (
        add_constraint solver (congruence av bv Numeral.one) ;
        (* At offset zero too, unless the variables are constant, or one
           is defined after a transition only *)
        match av.offsets, bv.offsets with
        | `Mixed, _ | _, `Mixed | `None, `None -> ()
        | _ -> add_constraint solver (congruence av bv Numeral.zero))
    ) a.declared ;
    a.declared <- a.declared @ [ av ]
  ) pending

(* Create the application variables of the fixed terms of the system: the
   initial state, the global constraints, the transition relation and the
   properties, and declare them *)
let abstract_system solver trans_sys =
  if not (UfSymbol.UfSymbolSet.is_empty !(abstracted_ufs ())) then (
    let props =
      List.map snd (TransSys.props_list_of_bound trans_sys Numeral.zero)
    in
    let fixed =
      TransSys.init_of_bound None trans_sys Numeral.zero
      :: TransSys.global_constraints trans_sys
      @ TransSys.trans_of_bound None trans_sys Numeral.one
        :: props @ List.map (Term.bump_state Numeral.one) props
    in
    (match abstract_ufs (TransSys.uf_defs trans_sys) (Term.mk_and fixed) with
     | _ -> ()
     | exception Quantified_term -> ()) ;
    declare_pending solver)


(* ************************************************************************ *)
(* Refinement of the abstraction with history variables                     *)
(* ************************************************************************ *)

(* The abstraction keeps the congruence of the applications of one state
   and the next only: a counterexample of the abstract system may interpret
   a symbol differently at different steps, as [f(a)] at step [i] and
   [f(a)] at step [j > i] with different values. Such a counterexample is
   spurious, and the abstraction is refined so that it is not found again:
   history variables record the arguments and the value of the application
   [d = j - i] steps earlier, and the congruence of the two applications
   becomes a constraint over one transition, [ha = t => hv = a] for [a =
   f(t)], which the solver and the generalization see. The variables and
   the constraints are added to the solver of IC3QE as they are needed, by
   the spurious counterexamples; the frames stay valid, as the constraints
   only restrict the transitions, and IC3QE restarts with the same
   properties. *)

(* The variables IC3QE adds that are declared: the application variables
   and the history variables, at offsets zero and one, or constant *)
let ic3qe_vars () = (abstraction ()).vars

(* The variables of the models IC3QE reads: those of the system at offsets
   zero and one, and those IC3QE adds *)
let cti_vars trans_sys =
  TransSys.vars_of_bounds trans_sys Numeral.zero Numeral.one @ ic3qe_vars ()

(* The variable that says the history is [d] steps long, created with those
   of the delays below if it does not exist yet: false in the initial
   state, true after one transition, and then that of the delay below *)
let rec history_valid solver d =
  let a = abstraction () in
  match List.assoc_opt d a.valid with
  | Some v -> v
  | None ->
    let below = if d = 1 then None else Some (history_valid solver (d - 1)) in
    let v = mk_ic3qe_var "valid" Type.t_bool in
    a.valid <- (d, v) :: a.valid ;
    declare_ic3qe_vars solver
      [ Var.mk_state_var_instance v Numeral.zero ;
        Var.mk_state_var_instance v Numeral.one ] ;
    add_init_constraint solver (Term.mk_not (at0 v)) ;
    add_constraint solver
      (Term.mk_eq
         [ at1 v ; match below with None -> Term.t_true | Some v' -> at0 v' ]) ;
    v

(* The variables of the arguments and of the value of an application
   variable [d] steps earlier, created with their constraints if they do
   not exist yet, with those of the delays below *)
let rec history_cell solver av d =
  let a = abstraction () in
  match List.assoc_opt (av.var, d) a.cells with
  | Some cell -> cell
  | None ->
    ignore (history_valid solver d) ;
    let args = args_of_shape av.shape in
    let ha =
      List.map (fun t -> mk_ic3qe_var "arg" (Term.type_of_term t)) args
    in
    let hv = mk_ic3qe_var "value" (Term.type_of_term av.shape) in
    declare_ic3qe_vars solver
      (List.concat_map (fun sv ->
         [ Var.mk_state_var_instance sv Numeral.zero ;
           Var.mk_state_var_instance sv Numeral.one ]) (hv :: ha)) ;
    (* After a transition, the arguments and the value one step earlier are
       those in the state the transition is from, and [d] steps earlier
       those [d - 1] steps earlier in that state *)
    (if d = 1 then (
       List.iter2 (fun sv t -> add_constraint solver (Term.mk_eq [ at1 sv ; t ]))
         ha args ;
       add_constraint solver
         (Term.mk_eq [ at1 hv ; fst (app_var_at av Numeral.zero) ]))
     else (
       let ha', hv' = history_cell solver av (d - 1) in
       List.iter2 (fun sv sv' -> add_constraint solver (Term.mk_eq [ at1 sv ; at0 sv' ]))
         ha ha' ;
       add_constraint solver (Term.mk_eq [ at1 hv ; at0 hv' ]))) ;
    a.cells <- ((av.var, d), (ha, hv)) :: a.cells ;
    ha, hv

(* Add the lemma of the congruence of an application [av] and an
   application [bv] of the symbol [d] steps later: if the history is [d]
   steps long and the arguments then were those now, the value then is the
   value now. At offsets one and zero. Returns false if the lemma was added
   before. *)
let add_lemma solver av bv d =
  let a = abstraction () in
  if List.exists (fun (x, y, d') -> x == av.var && y == bv.var && d = d') a.lemmas
  then false
  else (
    a.lemmas <- (av.var, bv.var, d) :: a.lemmas ;
    let ha, hv = history_cell solver av d in
    let valid_d = history_valid solver d in
    let b, sb = app_var_at bv Numeral.one in
    let lemma =
      Term.mk_implies
        [ Term.mk_and
            (at1 valid_d
             :: List.map2 (fun sv t -> Term.mk_eq [ at1 sv ; t ]) ha (args_of_shape sb)) ;
          Term.mk_eq [ at1 hv ; b ] ]
    in
    add_constraint solver lemma ;
    add_constraint solver (Term.bump_state (Numeral.of_int (-1)) lemma) ;
    true)

(* With the symbols abstracted (see [app_var]), the states of a trace of
   blocking clauses are found together, in one unrolling of the system with
   the symbols: an initial state, then a state in the cube of each clause,
   each a successor of the one before, with the constraints of the
   abstraction. A path is a counterexample, [`Real].

   Without one, the trace is spurious, and its conflicts are returned. The
   abstract system is unrolled the same way, and has a model, as the trace
   is one of the abstraction. Two application variables of a symbol at
   different steps whose arguments are equal in the model, with different
   values, are a conflict, [(av, bv, d)]: the earlier and the later
   application variable, [d] steps apart. *)
let cex_of_trace trans_sys trace =
  let cubes =
    List.map (fun c -> C.copy_clause c |> C.term_of_clause |> Term.negate) trace
  in
  let n = List.length cubes in
  let num = Numeral.of_int in
  let a = abstraction () in
  let uf_defs = TransSys.uf_defs trans_sys in
  (* The variables IC3QE adds, at the offsets of the unrolling *)
  let ic3qe_instances =
    List.concat_map (fun av ->
      match av.offsets with
      | `None -> [ Var.mk_const_state_var av.var ]
      | `Zero -> List.init (n + 1) (fun k -> Var.mk_state_var_instance av.var (num k))
      | `Mixed -> List.init n (fun k -> Var.mk_state_var_instance av.var (num (k + 1))))
      a.declared
    @ List.concat_map (fun sv ->
        List.init (n + 1) (fun k -> Var.mk_state_var_instance sv (num k)))
        (List.map snd a.valid
         @ List.concat_map (fun (_, (args, v)) -> v :: args) a.cells)
  in
  let with_solver f =
    let solver =
      SMTSolver.create_instance ~produce_models:true
        (TransSys.get_logic trans_sys) (Flags.Smt.solver ())
    in
    TransSys.define_and_declare_of_bounds trans_sys
      (SMTSolver.define_fun solver)
      ~define_rec:(SMTSolver.define_funs_rec solver)
      (SMTSolver.declare_fun solver)
      (SMTSolver.declare_sort solver)
      Numeral.zero (num n) ;
    Var.declare_all_vars (SMTSolver.declare_fun solver) ic3qe_instances ;
    Fun.protect ~finally:(fun () -> SMTSolver.delete_instance solver)
      (fun () -> f solver)
  in
  (* The terms of each transition of the unrolling, with the initial state
     in the first one *)
  let transitions =
    List.mapi (fun i cube ->
      let k = i + 1 in
      let transition =
        TransSys.global_constraints trans_sys
        @ TransSys.trans_of_bound None trans_sys (num k)
          :: Term.bump_state (num k) cube
          :: List.map (Term.bump_state (num (k - 1)))
               (a.definitions @ a.constraints)
      in
      if k = 1 then
        TransSys.init_of_bound None trans_sys Numeral.zero
        :: a.init_constraints @ transition
      else transition
    ) cubes
  in
  let path =
    with_solver (fun solver ->
      List.iter (fun t -> SMTSolver.assert_term solver (Term.mk_and t)) transitions ;
      if SMTSolver.check_sat solver then
        Some
          (get_var_values solver (TransSys.get_state_var_bounds trans_sys)
             (TransSys.vars_of_bounds trans_sys Numeral.zero (num n))
           |> fun m ->
             Model.path_from_model (TransSys.state_vars trans_sys) m (num n)
             |> Model.path_to_list)
      else None)
  in
  match path with
  | Some path -> `Real path
  | None ->
    with_solver (fun solver ->
      List.iter (fun t ->
        let t' =
          try abstract_ufs uf_defs (Term.mk_and t)
          with Quantified_term ->
            raise (UnsupportedFeature
              "Shutting down IC3QE: Cannot generalize quantified terms.")
        in
        SMTSolver.assert_term solver t') transitions ;
      (* The application variables at each step, with their arguments *)
      let instances =
        List.concat_map (fun av ->
          if av.offsets <> `Zero then []
          else
            List.init (n + 1) (fun k ->
              let v, shape = app_var_at av (num k) in
              k, av, v, args_of_shape shape)) a.declared
      in
      if instances = [] || not (SMTSolver.check_sat solver) then `Conflicts []
      else
        let values =
          SMTSolver.get_term_values solver
            (List.concat_map (fun (_, _, v, args) -> v :: args) instances
             |> List.sort_uniq Term.compare)
        in
        let value_of t = snd (List.find (fun (t', _) -> Term.equal t t') values) in
        let instances =
          List.map (fun (k, av, v, args) -> k, av, value_of v, List.map value_of args)
            instances
        in
        List.concat_map (fun (ki, avi, vi, ai) ->
          List.filter_map (fun (kj, avj, vj, aj) ->
            if ki < kj && symbol_of_shape avi.shape == symbol_of_shape avj.shape
               && List.equal Term.equal ai aj && not (Term.equal vi vj)
            then Some (avi, avj, kj - ki) else None
          ) instances
        ) instances
        |> List.sort_uniq (fun (x, y, d) (x', y', d') ->
             match StateVar.compare_state_vars x.var x'.var with
             | 0 -> (
               match StateVar.compare_state_vars y.var y'.var with
               | 0 -> compare d d'
               | c -> c)
             | c -> c)
        |> fun conflicts -> `Conflicts conflicts)

(* The longest history a refinement creates *)
let max_history = 64

(* Refine the abstraction for the conflicts of a spurious counterexample:
   add their lemmas. Returns false if no lemma was added, or the
   refinements are over the limit of --ic3qe_uf_refinements. *)
let refine solver conflicts =
  let a = abstraction () in
  if a.refinements >= Flags.IC3QE.uf_refinements () then false
  else
    let added =
      conflicts
      |> List.filter (fun (_, _, d) -> d <= max_history)
      |> List.map (fun (av, bv, d) -> add_lemma solver av bv d)
      |> List.exists Fun.id
    in
    if added then (
      a.refinements <- a.refinements + 1 ;
      KEvent.log L_info
        "IC3QE: spurious counterexample, refining the abstraction of the \
         function symbols with history variables (%d of %d refinements)"
        a.refinements (Flags.IC3QE.uf_refinements ()) ;
      true)
    else false


(* Given a model and two formulas f and g return a conjunction of
   literals such that

   (1) x = s |= B[x]
   (2) B[x] |= exists x' (F[x] & T[x,x'] & G[x'])

   If the system has abstracted function symbols (see [abstracted_ufs]),
   the term is that of the abstract system (see [app_var]): the
   applications of the symbols are replaced by their application
   variables, with the constraints of the abstraction, and B is over the
   unprimed variables of the system and the application variables, without
   the symbols. (2) then holds of the abstract system: a counterexample
   built from the cubes is checked on the system with the symbols (see
   [cex_of_trace]). *)
let extrapolate solver trans_sys state f g =

  (* Construct term to be generalized with the transition relation and
     the invariants *)
  let term =
    Term.mk_and
      ((TransSys.global_constraints trans_sys) @
      [f;
       TransSys.trans_of_bound None trans_sys Numeral.one;
(*
       TransSys.invars_of_bound trans_sys ~one_state_only:true Numeral.zero;
       TransSys.invars_of_bound trans_sys Numeral.one;
*)
       Term.bump_state Numeral.one g])
  in

  let term =
    if UfSymbol.UfSymbolSet.is_empty !(abstracted_ufs ()) then term
    else
      let term' =
        try abstract_ufs (TransSys.uf_defs trans_sys) term
        with Quantified_term ->
          raise (UnsupportedFeature
            "Shutting down IC3QE: Cannot generalize quantified terms.")
      in
      (* The constraints of the abstraction, over the variables IC3QE adds,
         with those of the application variables the term may have added *)
      declare_pending solver ;
      Term.mk_and (term' :: (abstraction ()).constraints)
  in

  (* Get primed variables in the transition system *)
  let primed_vars =
    Var.VarSet.elements
      (Term.vars_at_offset_of_term (Numeral.one) term)
  in

  Stat.start_timer Stat.ic3_generalize_time;

  (* Generalize term by quantifying over and eliminating primed
     variables *)
  let gen_term =
    try
      QE.generalize
        trans_sys
        (TransSys.uf_defs trans_sys)
        state
        primed_vars
        term
    with
    | QE.QuantifiedTermFound _ ->
        let err = "Shutting down IC3QE: Cannot generalize quantified terms." in
        raise (UnsupportedFeature err)
  in

  Stat.record_time Stat.ic3_generalize_time;

  (* Return generalized term *)
  gen_term


(* ************************************************************************ *)
(* Block unreachable generalized counterexamples to induction               *)
(* ************************************************************************ *)

(* Add cube to block in future frames *)
let add_to_block_tl solver block_clause block_trace = function

  (* Last frame has no successors *)
  | [] -> [] 

  (* Add cube as proof obligation in next frame *)
  | (block_clauses, r_succ_i) :: block_clauses_tl -> 

    (* (block_clauses @ [C.copy_clause solver block_clause, block_trace], r_succ_i) :: block_clauses_tl *)

    let block_clause' =
      C.copy_clause_block_prop block_clause
    in

    SMTSolver.trace_comment solver
      (Format.asprintf 
         "@[<hv>Copied clause #%d for blocking at depth %d:@ #%d @[<hv 1>{%a}@]@]"
         (C.id_of_clause block_clause)
         (List.length block_clauses_tl)
         (C.id_of_clause block_clause')
         (pp_print_list Term.pp_print_term ";@ ")
         (C.literals_of_clause block_clause'));
          
    ((block_clause', block_trace) :: block_clauses, r_succ_i) :: block_clauses_tl
    (* (block_clauses @ [block_clause', block_trace], r_succ_i) :: block_clauses_tl *)


(* ************************************************************************ *)
(* Implicit abstraction                                                     *)
(* ************************************************************************ *)

(* Interpolation Group ids for MathSAT *)
let ig_newid =
  let r = ref 0 in
  fun () -> incr r; Format.sprintf "g%d" !r

let abstr_simulate trace trans_sys raise_cex =

  Stat.incr (Stat.ic3ia_num_simulations);

  let intrpo =
    match !(ref_interpolator ()) with
      | Some s ->
        
        if (List.length trace) > !(max_unrolling ()) then (
          
          TransSys.declare_vars_of_bounds
            trans_sys
            (SMTSolver.declare_fun s)
            (Numeral.of_int (!(max_unrolling ()) + 1))
            (Numeral.of_int (List.length trace));

          max_unrolling () := List.length trace;
        );
        s

      | None ->

        let solver =
          SMTSolver.create_instance
            ~produce_interpolants:true
            (TransSys.get_logic trans_sys)
            (Flags.Smt.get_itp_solver ())
        in   

        TransSys.define_and_declare_of_bounds
          trans_sys
          (SMTSolver.define_fun solver)
          ~define_rec:(SMTSolver.define_funs_rec solver)
          (SMTSolver.declare_fun solver)
          (SMTSolver.declare_sort solver)
          (Numeral.zero)
          (Numeral.of_int (List.length trace));

        ref_interpolator () := Some solver;
        max_unrolling () := List.length trace;
        solver

  in                             

  let interpolizers =
    List.mapi
      (fun i cex ->
         [(TransSys.trans_of_bound (Some (SMTSolver.declare_fun intrpo))
             trans_sys (Numeral.of_int (i+1)));
          (Term.bump_state (Numeral.of_int (i+1)) cex)]
      )
      trace
  in

  let interpolizers =
    (Term.mk_and ((TransSys.global_constraints trans_sys) @
                  (TransSys.init_of_bound
                     (Some (SMTSolver.declare_fun intrpo))
                     trans_sys Numeral.zero)
                  :: List.hd interpolizers))
    ::
    (List.map Term.mk_and (List.tl interpolizers))
  in


  SMTSolver.push intrpo;  

  (* Compute the interpolants *)

  let names =
    match Flags.Smt.itp_solver () with
    | `MathSAT_SMTLIB -> (
      List.map
        (fun t ->
          let id = ig_newid () in
          SMTSolver.assert_term intrpo (Term.set_inter_group t id) ;
          SMTExpr.ArgString id
        )
        interpolizers
    )
    | `Bitwuzla_SMTLIB
    | `OpenSMT_SMTLIB
    | `SMTInterpol_SMTLIB -> (
      List.map
        (fun t ->
         SMTExpr.ArgString
           (SMTSolver.assert_named_term_wr
              intrpo
              t))
      interpolizers
    )
    | _ -> failwith ("Interpolating solver not found or unsupported")
  in
  Stat.start_timer Stat.ic3ia_interpolation_time;

  if SMTSolver.check_sat 
      intrpo
  then
    raise_cex ()
  else
    let interpolants = 
      SMTSolver.get_interpolants
        intrpo
        names
    in


    SMTSolver.pop
      intrpo;

    Stat.record_time Stat.ic3ia_interpolation_time;                               

    let rec add = function
      | x :: xs , y :: ys -> x + y :: add (xs , ys)
      | xs , [] -> xs
      | [] , ys -> ys
    in
    let refinements = Stat.get_int_list (Stat.ic3ia_refinements) in
    let refinements_end = Stat.get_int_list (Stat.ic3ia_refinements_end) in
    let refinement_indexes = 
      List.map
        (fun i -> if Term.equal i Term.t_false then 0 else 1)
        interpolants 
    in

    Stat.set_int_list
      (add (refinements, refinement_indexes))
      Stat.ic3ia_refinements;

    Stat.set_int_list
      ((add (List.rev refinements_end, refinement_indexes)) |> List.rev)
      Stat.ic3ia_refinements_end;


    let interpolants =
      List.mapi
        (fun i t -> Term.bump_state (Numeral.of_int (~-(i+1))) t)
        interpolants
      |> 
      List.filter
        (fun t -> not (t == Term.t_false || t == Term.t_true))
      |>
      List.fold_left
        (fun acc interp -> Term.TermSet.union (Term.get_atoms interp) acc)
        Term.TermSet.empty
    in

    interpolants


(* Block sets of bad states in frames

   The last two arguments [frames] and [trace] are lists of frames and
   cubes to block. 

   [frames] is the list of frames below the current frame in
   descencing order, with R_i-1 at the head and R_1 last. 

   [trace] is the list of frames above the current frame in ascending
   order with R_i at the head and R_k last. Each frame is paired with
   a list of cubes that are to be shown unreachable in that frame.

*)
let rec block solver input_sys aparam trans_sys prop_set term_tbl predicates = 

  function 

    (* Nothing to block in frames above, current frame is R_k *)
    | [] -> 

      (function 

        (* k > 0, we must have at least one frame *)
        | [] ->  raise (Invalid_argument "block")

        (* Head of frames is the last frame *)
        | r_k :: frames_tl as frames -> 

          (* Receive and assert new invariants *)
          handle_events
            solver
            input_sys
            aparam
            trans_sys
            (C.props_of_prop_set prop_set);

          SMTSolver.trace_comment 
            solver
            (Format.sprintf 
               "block: Check if all successors of frontier R_%d are safe."
               (List.length frames));

          match
            
            (* Check P[x] & R_k[x] & T[x,x'] |= P[x']

               R_k does not imply P[x] yet *)
            SMTSolver.check_sat_assuming_ab 
              solver 
              (fun _ -> 
                
                (* Get counterexample as a pair of states from satisfiable
                   query 
                   
                   Don't use SMTSolver.get_model, because it is
                   expensive due to the many activation literals *)
                get_var_values
                  solver
                  (TransSys.get_state_var_bounds trans_sys)
                  (cti_vars trans_sys))

              (fun _ -> ())

              (C.actlit_p0_of_prop_set solver prop_set :: 
                 C.actlits_n1_of_prop_set solver prop_set @
                 List.map (C.actlit_p0_of_clause solver) (F.values r_k))

          (* If sat: we have a state in R_k that has a successor
             outside the property *)
          with

            | SMTSolver.Sat cti ->

              (
                
                (* Extrapolate from counterexample to a cube in R_k *)
                let cti_gen = 

                  (* Abstraction used? *)
                  match Flags.IC3QE.abstr () with

                    (* No abstraction *)
                    | `None ->

                      (* Compute preimage with quantifier elimination

                         P[x] & R_k[x] & T[x,x'] & ~P[x'] is sat

                         R_k does not imply P[x] yet *)
                      extrapolate 
                        solver
                        trans_sys 
                        cti 
                        (C.term_of_prop_set prop_set :: 
                           List.map C.term_of_clause (F.values r_k)
                            |> Term.mk_and)
                        (C.term_of_prop_set prop_set |> Term.negate) 

                    (* Implicit abstraction *)
                    | `IA ->

                      (* Evaluate all predicates on CTI *)
                      List.map 

                        (fun p ->

                          match

                            (* Evaluate predicate *)
                            Eval.eval_term
                              (TransSys.uf_defs trans_sys)
                              cti
                              p
                              
                          with

                            (* Predicate evaluates to true, use positively *)
                            | Eval.ValBool true -> p

                            (* Predicate evaluates to true, use negatively *)
                            | Eval.ValBool false -> Term.negate p

                            (* Predicate must evaluate to either true or
                               false, we cannot have a partial model *)
                            | _ -> assert false)
                        
                        predicates
                        
                in

                (* Create a clause with activation literals from
                   generalized counterexample *)
                let clause =
                  try
                    C.mk_clause_of_literals
                      C.BlockFrontier
                      (List.map Term.negate cti_gen)
                  with Invalid_argument _ as e -> (
                    if List.exists (fun t -> Term.has_quantifier t) cti_gen then (
                      raise (UnsupportedFeature
                        "Shutting down IC3QE: QE failed during generalization step.")
                    )
                    else
                      raise e
                  )
                in

                SMTSolver.trace_comment solver
                  (Format.asprintf 
                     "@[<hv>New clause at frontier:@ #%d @[<hv 1>{%a}@]@]"
                     (C.id_of_clause clause)
                     (pp_print_list Term.pp_print_term ";@ ")
                     (C.literals_of_clause clause));

                (* Recursively block cube by showing that clause is
                   relatively inductive *)
                block 
                  solver
                  input_sys 
                  aparam
                  trans_sys 
                  prop_set
                  ()
                  predicates
                  [([clause, [C.clause_of_prop_set prop_set]], r_k)] 
                  frames_tl

              )
                
            (* If unsat: Frames are safe, cannot get outside property
               in one step in all frames up to R_k *)
            | SMTSolver.Unsat () ->

              (
                
                SMTSolver.trace_comment 
                  solver
                  (Format.sprintf 
                     "block: All successors of R_%d are safe."
                     (List.length frames));
                
                (* Return frames *)
                frames, predicates
                  
              )
                
      )

    (* No more cubes to block in R_i *)
    | ([], r_i) :: block_tl -> 

      (function frames ->

        SMTSolver.trace_comment 
          solver
          (Format.sprintf 
             "block: All counterexamples blocked in R_%d"
             (succ (List.length frames)));

        (* Return to counterexamples to block in R_i+1 *)
        block 
          solver
          input_sys 
          aparam 
          trans_sys
          prop_set
          term_tbl
          predicates
          block_tl
          (r_i :: frames))


    (* Take the first cube to be blocked in current frame *)
    | (((block_clause_orig, block_trace) :: block_clauses_tl), r_i) 
      :: block_tl as trace -> 

      (function frames -> 

        (* Combine clauses from higher frames to get the actual
           clauses of the delta-encoded frame R_i-1

           Get clauses in R_i..R_k from [trace], R_i-1 is first frame
           in [frames]. *)
        let clauses_r_pred_i, actlits_p0_r_pred_i = 

          (* May be empty *)
          match frames with

            (* Special case: R_0 = I *)
            | [] -> ([], [C.actlit_of_frame 0])

            | r_pred_i :: _ -> 

              List.fold_left

                (* Join lists of clauses *)
                (fun (ac, al) (_, r) ->
                  (F.values r) @ ac,
                  List.map (C.actlit_p0_of_clause solver) (F.values r) @ al)

                (C.clause_of_prop_set prop_set :: (F.values r_pred_i), 
                 C.actlit_p0_of_prop_set solver prop_set :: 
                   List.map (C.actlit_p0_of_clause solver) (F.values r_pred_i))

                trace

        in

        (* Inductively generalize clauses propagated for blocking to
           this frame *)
        let block_clause, trace = match C.source_of_clause block_clause_orig with 

          (* Clause was propagates for blocking *)
          | C.CopyBlockProp _ -> 

            let block_clause = 

              Stat.time_fun Stat.ic3_ind_gen_time
                (fun () -> 
                  ind_generalize 
                    solver
                    prop_set
                    actlits_p0_r_pred_i
                    block_clause_orig
                    (C.literals_of_clause block_clause_orig))
            in

            block_clause, 

            (* Need to modify trace to add generalized clause *)
            (((block_clause, block_trace) :: block_clauses_tl), r_i) 
            :: block_tl

          (* Clause is an actual blocking clause *)
          | _ -> block_clause_orig, trace

        in

        (* Receive and assert new invariants *)
        handle_events 
          solver
          input_sys
          aparam
          trans_sys
          (C.props_of_prop_set prop_set);

        SMTSolver.trace_comment 
          solver
          (Format.sprintf 
             "block: Is blocking clause relative inductive to R_%d?"
             (List.length frames));

        (match
            
            (* Check P[x] & R_i-1[x] & C[x] & T[x,x'] |= C[x'] *)
            SMTSolver.check_sat_assuming_ab 
              solver

              (* Get counterexample from satisfiable query *)
              (fun _ ->

                match frames with

                  (* Need no model when in initial frame *)
                  | [] -> Model.create 0

                  (* Get model in all other frames *)
                  | _ ->
                    get_var_values
                      solver
                      (TransSys.get_state_var_bounds trans_sys)
                      (cti_vars trans_sys))

              (* Get unsat core from unsatisfiable query *)
              (fun _ -> SMTSolver.get_unsat_core_lits solver)

              (C.actlit_p0_of_clause solver block_clause :: 
                 C.actlits_n1_of_clause solver block_clause @
                 actlits_p0_r_pred_i)
              
         with
             
           (* If unsat: clause is relative inductive and bad state is
              not reachable *)
           | SMTSolver.Unsat core_actlits_trans ->
             
             SMTSolver.trace_comment 
               solver
               "block: Check I |= C to get unsat core.";
             
             (* Activation literals in unsat core of I |= C *)
             let core_actlits_init = 
               SMTSolver.check_sat_assuming
                 solver
                 
                 (* Must be unsat *)
                 (fun _ -> 
                   
                   KEvent.log L_info "Query is satisfiable, waiting for BMC";
                   
                   (* This should only happen when we are faster than
                      BMC, who has not yet discovered at one-step
                      violation of a property. We wait for messages *)
                   let rec wait () = 
                     handle_events 
                       solver
                       input_sys
                       aparam 
                       trans_sys
                       (C.props_of_prop_set prop_set);
                     KEvent.wait_for_message ();
                     wait ()
                   in
                   ignore (wait ()); 
                   
                   (* We won't return from waiting *)
                   assert false)
                 
                 (* Get literals in unsat core *)
                 (fun _ -> SMTSolver.get_unsat_core_lits solver)
                 
                 (* Check I |= C *)
                 ((C.actlit_of_frame 0) :: C.actlits_n0_of_clause solver block_clause)
                 
             in
             
             (* Reduce clause to unsat core of R & T |= C *)
             let block_clause_literals_core_n1 = 
               
               List.fold_left2 
                 
                 (fun a t l ->
                   
                   if 

                     (* Keep clause literal [l] if activation literals
                        [t] is in unsat core *)
                     List.exists (Term.equal t) core_actlits_trans

                   then

                     l :: a

                   else

                     a)

                 (* Start with empty clause *)
                 []

                 (* Fold over clause literals and their activation literals *)
                 (C.actlits_n1_of_clause solver block_clause)
                 (C.literals_of_clause block_clause)

             in

             (* Reduce clause to unsat core of I |= C *)
             let block_clause_literals_core = 

               List.fold_left2 

                 (fun a t l ->

                   if 

                     (* Keep clause literal [l] if activation literal [t]
                        is in unsat core *)
                     List.exists (Term.equal t) core_actlits_init

                   then

                     (* Drop clause literal [l] if it is in accumulator
                        to prevent duplicates *)
                     if List.exists (Term.equal l) a then a else l :: a

                   else

                     a)

                 (* Start with literal in core of consecution query *)
                 block_clause_literals_core_n1

                 (* Fold over clause literals and their activation literals *)
                 (C.actlits_n0_of_clause solver block_clause)
                 (C.literals_of_clause block_clause)

             in

             SMTSolver.trace_comment
               solver
               (Format.asprintf
                  "@[<hv>block: Reduced clause@ %a@ with unsat core to@ %a@]"
                  Term.pp_print_term (C.term_of_clause block_clause)
                  Term.pp_print_term (Term.mk_or block_clause_literals_core));

             (* Inductively generalize clause *)
             let block_clause_gen =
               Stat.time_fun Stat.ic3_ind_gen_time
                 (fun () -> 
                   ind_generalize 
                     solver
                     prop_set
                     actlits_p0_r_pred_i
                     block_clause
                     block_clause_literals_core)
             in

             SMTSolver.trace_comment
               solver
               (Format.asprintf
                  "@[<hv>block: Reduced clause@ %a@ with ind. gen. to@ %a@]"
                  Term.pp_print_term (Term.mk_or block_clause_literals_core)
                  Term.pp_print_term (C.term_of_clause block_clause_gen));

             (* Add blocking clause to all frames up to where it has to
                be blocked *)
             let r_i', frames', block_tl' =

               (* Literals of clause as key for trie *)
               let block_clause_gen_literals = C.literals_of_clause block_clause_gen in

               (try

                  (* Adding a clause may fail if it a prefix of a clause
                     in the trie, or if a clause in the trie is a
                     prefix of this clause *)
                  F.add block_clause_gen_literals block_clause_gen r_i

                with Invalid_argument _ ->

                  (SMTSolver.trace_comment
                     solver
                     (Format.asprintf
                        "@[<v>Clause@ @[<hv>{%a@}@]@ subsumes a clause in frame, \
                      must do subsumption before adding@ @[<hv>%a@]@]"
                        (pp_print_list Term.pp_print_term ";@ ")
                        block_clause_gen_literals
                        (pp_print_list
                           (fun ppf (k, c) ->
                             Format.fprintf ppf
                               "@[<hv 1>{%a}@ =@ %a"
                               (pp_print_list Term.pp_print_term ";@ ") k
                               Term.pp_print_term (C.term_of_clause c))
                           ",@ ")
                        (F.bindings r_i));

                   (* The new blocking clause is not subsumed, because
                      otherwise we would not get the counterexample *)
                   (* if F.is_subsumed r_i block_clause_gen_literals then r_i else *)

                   (* Subsume in this frame and add *)
                   F.subsume r_i block_clause_gen_literals

                      (* Count number of subsumed clauses *)
                      |> count_subsumed solver

                      (* Deactivate activation literals of subsumed clauses *)
                      |> deactivate_subsumed solver

                      |> snd

                      (* Add clause to frame after subsumption *)
                      |> F.add block_clause_gen_literals block_clause_gen)),

               frames,

               (* Add cube to block to next higher frame if flag is set *)
               if Flags.IC3QE.block_in_future () then

                 add_to_block_tl
                   solver
                   block_clause_orig
                   block_trace
                   block_tl

               else

                 block_tl

             in

             (* Combine clauses from higher frames to get the actual
                clauses of the delta-encoded frame R_i-1

                Get clauses in R_i..R_k from [trace], R_i-1 is first frame
                in [frames]. *)
             let clauses_r_succ_i, _ (* actlits_p0_r_succ_i *) = 
               List.fold_left
                 (fun (ac, al) (_, r) ->
                   (F.values r) @ ac,
                   List.map (C.actlit_p0_of_clause solver) (F.values r) @ al)
                 ([], [])
                 ((block_clauses_tl, r_i') :: block_tl') 
             in

             (* DEBUG *)
             if debug_assert then
               assert
                 (check_frames solver prop_set clauses_r_succ_i (r_i' :: frames'));

             (* Update frame size statistics *)
             Stat.set_int_list
               (frame_sizes_block frames' trace) 
               Stat.ic3_frame_sizes; 

             (* TODO: If clause was propagated from preceding frame,
                remove from there *)

             (* Add clause to frame and continue with next clauses in
                this frame *)
             block 
               solver
               input_sys 
               aparam
               trans_sys 
               prop_set
               term_tbl
               predicates
               (if

                   (* Block in higher frames first? *)
                   true &&

                     (* Only if not in the highest frame *)
                     (match block_tl' with
                       | [] -> false
                       | _ -> true) 

                then

                   (* Remove all clauses to block and go to the next
                      higher frame *)
                   (([], r_i') :: block_tl')

                else

                   (* Block clauses in this frame first *)
                   ((block_clauses_tl, r_i') :: block_tl'))

               frames'

           (* If sat: bad state is reachable *)
           | SMTSolver.Sat cti ->
             
             (* Are there frames below R_i? *)
             match frames with 
                 
               (* Bad state is reachable from R_0, we have found a
                  counterexample path *)
               | [] ->

                 SMTSolver.trace_comment
                   solver
                   (Format.asprintf
                      "@[<hv>~P reachable from I:@ @[<hv>%a@]@]"
                      (pp_print_list
                         (fun ppf c ->
                           Format.fprintf ppf
                             "%d"
                             (C.id_of_clause c))
                         ",@ ")
                      (block_clause :: block_trace));


                 let raise_cex () = 
                   raise (Counterexample (block_clause :: block_trace))
                 in

                 (match Flags.IC3QE.abstr () with
                   | `None ->
                     raise_cex ()

                   | `IA ->
                     SMTSolver.trace_comment 
                       solver
                       (Format.sprintf
                          "block: generating interpolants."
                       );

                     let cex_trace =
                       List.map
                         (fun bcl -> Term.mk_and (List.map Term.negate (Clause.literals_of_clause bcl)))
                         (block_clause :: block_trace)
                     in

                     let interpolants = abstr_simulate cex_trace trans_sys raise_cex in

                     let new_interpolants =
                      Term.TermSet.(diff interpolants (of_list predicates))
                      |> Term.TermSet.elements
                     in

                     List.iteri
                       (fun _ t ->
                         SMTSolver.assert_term
                           solver
                           (Term.mk_eq
                              [t;
                               Term.bump_state (Numeral.of_int 2) t]);

                         SMTSolver.assert_term
                           solver
                           (Term.mk_eq
                              [Term.bump_state (Numeral.one) t;
                               Term.bump_state (Numeral.of_int 3) t]);
                       )
                       new_interpolants;


                     block
                       solver
                       input_sys 
                       aparam
                       trans_sys
                       prop_set
                       term_tbl
                       (new_interpolants @ predicates)
                       []
                       (List.rev (List.map (fun (_,s) -> s) trace))

                 )

               (* i > 1 and bad state is reachable from R_i-1 *)
               | r_pred_i :: frames_tl -> 

                 (* Generalize the counterexample to a list of literals

                    R_i-1[x] & C[x] & T[x,x'] & ~C[x'] is sat *)
                 let cti_gen =
                   match Flags.IC3QE.abstr () with
                     | `None ->

                       extrapolate 
                         solver
                         trans_sys 
                         cti
                         ((C.term_of_clause block_clause ::
                             List.map C.term_of_clause clauses_r_pred_i) 
                             |> Term.mk_and)
                         (C.term_of_clause block_clause |> Term.negate)

                     | `IA ->
                       List.map 
                         (fun p ->match  Eval.eval_term
                             (TransSys.uf_defs trans_sys)
                             cti
                             p
                           with

                             | Eval.ValBool true -> p

                             | Eval.ValBool false -> Term.negate p

                             | _ -> raise (Invalid_argument "abstract cex evaluation")

                         )
                         predicates
                 in

                 (* Create a clause with activation literals from generalized
                    counterexample *)
                 let block_clause' = 
                   C.mk_clause_of_literals
                     (C.BlockRec block_clause)
                     (List.map Term.negate cti_gen) 
                 in

                 SMTSolver.trace_comment solver
                   (Format.asprintf 
                      "@[<hv>New clause at depth %d to block #%d:@ #%d @[<hv 1>{%a}@]@]"
                      (List.length trace)
                      (C.id_of_clause block_clause)
                      (C.id_of_clause block_clause')
                      (pp_print_list Term.pp_print_term ";@ ")
                      (C.literals_of_clause block_clause'));


                 block 
                   solver
                   input_sys 
                   aparam 
                   trans_sys 
                   prop_set
                   term_tbl
                   predicates
                   (([block_clause', (block_clause :: block_trace)], 
                     r_pred_i) :: trace) 
                   frames_tl

        )

      )


(* ************************************************************************ *)
(* Forward propagation                                                      *)
(* ************************************************************************ *)

(* Split list of clauses into those that are inductive and those that
   are not *)
let rec partition_inductive
    solver
    trans_sys
    frame
    not_inductive
    maybe_inductive = 

  (* Use activation literals of clauses on lhs *)
  let actlits_p0 = 
    List.map (C.actlit_p0_of_clause solver) (frame @ maybe_inductive) 
  in

  (* Conjunction of clauses *)
  let clauses = Term.mk_and (List.map C.term_of_clause maybe_inductive) in

  (* Assert p0 => ~(C_1' & ... & C_n') *)
  let actlit_n1 = 
    C.create_and_assert_fresh_actlit solver "is_ind" clauses C.Actlit_n1
  in

  SMTSolver.trace_comment
    solver
    "Checking for inductiveness of clauses";
  
  match 
    
    (* Are all clauses inductive? 
       
       Check R & C_1 & ... & C_n & T |= C_1' & ... & C_n'
    *)
    SMTSolver.check_sat_assuming_ab 
      solver

      (* Get model for failed entailment check *)
      (fun solver ->
        get_var_values
          solver
          (TransSys.get_state_var_bounds trans_sys)
          (cti_vars trans_sys))
      
      (fun _ -> ())
      
      (actlit_n1 :: actlits_p0)
      
  with

    (* Some candidate clauses are not inductive: filter out the ones
       that could still be *)
    | SMTSolver.Sat model -> 
      
      (* Separate not inductive terms from potentially inductive terms 
         
         C_1 & ... & C_n & T & ~ (C_1' & ... & C_n') is satisfiable,
         partition C_1', ..., C_n' by their model value, false terms are
         certainly not inductive, true terms can be inductive. *)
      let maybe_inductive', not_inductive_new = 
        List.partition 
          (function c -> 
            C.term_of_clause c
            |> Term.bump_state Numeral.one
            |> Eval.eval_term [] model
            |> Eval.bool_of_value)
          maybe_inductive
      in

      (* Clauses found to be not inductive *)
      let not_inductive' = not_inductive @ not_inductive_new in

      (* Deactivate activation literal *)
      Term.mk_not actlit_n1 |> SMTSolver.assert_term solver;
      Stat.incr Stat.ic3_stale_activation_literals;

      (* No clauses are inductive? *)
      if maybe_inductive = [] then (not_inductive', []) else
        
        (* Continue checking if remaining clauses are inductive *)
        partition_inductive 
          solver
          trans_sys 
          frame
          not_inductive'
          maybe_inductive'

    (* All candidate clause are inductive: return clauses show not to be
       inductive and inductive clauses *)
    | SMTSolver.Unsat () ->
      
    (* Deactivate activation literal *)
      Term.mk_not actlit_n1 |> SMTSolver.assert_term solver;
      Stat.incr Stat.ic3_stale_activation_literals;

      not_inductive, maybe_inductive


      
(* Split list of clauses into clauses that can be propagated relative
   to the frame and those that cannot be *)
let partition_fwd_prop
    solver
    trans_sys
    prop_set
    frame
    clauses = 

  (* Use activation literals of clauses on lhs *)
  let actlits_p0 =
    List.map (C.actlit_p0_of_clause solver) (frame @ clauses) 
  in

  (* Check until we find a set of clauses that can be propagated
     together *)
  let rec partition_fwd_prop' keep maybe_prop = 

    SMTSolver.trace_comment
      solver
      "partition_fwd_prop: Checking for forward propagation of clause set";

    (* Assert n1 => ~(C_1' & ... & C_n') *)
    let actlit_n1 = 
      C.create_and_assert_fresh_actlit 
        solver
        "fwd_prop" 
        (List.map C.term_of_clause maybe_prop |> Term.mk_and) 
        C.Actlit_n1
    in

    match
    
      (* Can all clauses be propagated? 
         
         Check P[x] & R[x] & T[x,x'] |= C_1[x'] & ... & C_n[x']
      *)
      SMTSolver.check_sat_assuming_ab 
        solver

        (* Get model for failed entailment check *)
        (fun solver ->
          get_var_values
            solver
            (TransSys.get_state_var_bounds trans_sys)
            (cti_vars trans_sys))

        (fun _ -> ())

        (C.actlit_p0_of_prop_set solver prop_set :: actlit_n1 :: actlits_p0)

    with
        
      (* Some candidate clauses cannot be propagated: filter out the ones
         that could still be *)
      | SMTSolver.Sat model -> 

        (* Separate not propagateable terms from potentially propagateable
           terms
           
           C_1 & ... & C_n & T & ~ (C_1' & ... & C_n') is satisfiable,
           partition C_1', ..., C_n' by their model value, false terms are
           certainly not propagateable, true terms might be propagated. *)
        let maybe_prop', keep_new = 
          List.partition 
            (function c -> 
              C.term_of_clause c
              |> Term.bump_state Numeral.one
              |> Eval.eval_term [] model
              |> Eval.bool_of_value)
            maybe_prop
        in
        
        (* Clauses found not propagateable *)
        let keep' = keep @ keep_new in

        (* Deactivate activation literal *)
        Term.mk_not actlit_n1 |> SMTSolver.assert_term solver;
        Stat.incr Stat.ic3_stale_activation_literals;
        
        (* No clauses can be propagated? *)
        if maybe_prop' = [] then (keep', []) else
          
          (* Continue checking if remaining clauses are inductive *)
          partition_fwd_prop' 
            keep'
            maybe_prop'
            
      (* All clause can be forward propagated: return clauses to keep and
         clauses to propagate *)
      | SMTSolver.Unsat () ->

        (* Deactivate activation literal *)
        Term.mk_not actlit_n1 |> SMTSolver.assert_term solver;
        Stat.incr Stat.ic3_stale_activation_literals;
        
        keep, maybe_prop


            
            
  in

            
  (* Check if all clauses can be propagated *)
  partition_fwd_prop' [] clauses

    
(* Forward propagate clauses in all frames *)
let fwd_propagate solver input_sys aparam trans_sys prop_set frames =

  let subsume_and_add a c =

    SMTSolver.trace_comment
      solver
      (Format.asprintf
         "@[<v>subsume_and_add: clause %d@]"
         (C.id_of_clause c));

    (* Forward propagated clause to add to frame *)
    let c' =

      if 

        (* Inductive generalization after forward propagation? *)
        Flags.IC3QE.fwd_prop_ind_gen () ||

        (* Inductively generalize forward propagated clause that was
           not generalized *)
        (match C.source_of_clause c with
          | C.CopyFwdProp _ -> true
          | _ -> false)

      then


        (Stat.time_fun Stat.ic3_ind_gen_time
           (fun () -> 
              ind_generalize 
                solver
                prop_set
                (F.values a |> List.map (C.actlit_p0_of_clause solver))
                c
                (C.literals_of_clause c)))

      else

        (* Propagate clause as it is *)
        c

    in

    (* Literals of clause as key for trie *)
    let l = C.literals_of_clause c' in

    (* Subsumption after forward propagation? *)
    if Flags.IC3QE.fwd_prop_subsume () then

      (* Is clause subsumed in frame? *)
      if F.is_subsumed a l then

        (

          SMTSolver.trace_comment
            solver
            (Format.asprintf
               "@[<v>Clause is subsumed in frame@,%a@]"
               (pp_print_list Term.pp_print_term "@,")
               (F.values a |> List.map (C.actlit_p0_of_clause solver)));

          (* Deactivate activation literals of subsumed clause *)
          C.deactivate_clause solver c';

          (* Increment statistics *)
          Stat.incr Stat.ic3_fwd_subsumed;

          (* Drop clause from frame *)
          a)

      else

        (* Subsume in frame with clause *)
        F.subsume a l

        (* Increment statistics *)
        |> count_subsumed solver

        (* Deactivate activation literals of subsumed clauses *)
        |> deactivate_subsumed solver

        (* Continue with frame after subsumption *)
        |> snd

        (* Add clause to frame  *)
        |> F.add l c'

    else

      (* Adding a clause may fail if it a prefix of a clause in the
         trie, or if a clause in the trie is a prefix of this
         clause *)
      try F.add l c' a with Invalid_argument _ ->

        SMTSolver.trace_comment
          solver
          (Format.asprintf
             "@[<v>Failed to add clause to trie, checking subsumption@]");

        (* Is clause subsumed in frame? *)
        if F.is_subsumed a l then
          (C.deactivate_clause solver c';
           SMTSolver.trace_comment
             solver
             (Format.asprintf
                "@[<v>Clause is subsumed in frame@,%a@]"
                (pp_print_list Term.pp_print_term "@,")
                (F.values a |> List.map (C.actlit_p0_of_clause solver)));
           Stat.incr Stat.ic3_fwd_subsumed;
           a)
        else
          F.subsume a l
          |> count_subsumed solver
          |> deactivate_subsumed solver
          |> snd
          |> F.add l c'

  in

  let rec fwd_propagate' solver input_sys aparam trans_sys prop frames =

    function 

      (* After the last frame *)
      | [] -> 

        (* Receive and assert new invariants *)
        handle_events 
          solver
          input_sys
          aparam
          trans_sys
          (C.props_of_prop_set prop_set);

        (* Check inductiveness of blocking clauses? *)
        if Flags.IC3QE.check_inductive () && prop <> [] then 

          (

            SMTSolver.trace_comment
              solver
              "fwd_propagate: Checking for inductiveness of clauses \
               in last frame.";

            (* Split clauses to be propagated into the new frame into
               inductive and non-inductive clauses *)
            let non_inductive_clauses, inductive_clauses =
              partition_inductive
                solver
                trans_sys
                []
                []
                prop
            in

            (* Some clauses found inductive *)
            if inductive_clauses <> [] then 

              (

                let empty_prop_set = C.prop_set_of_props [] in

                let inductive_clauses_gen = 
                  List.map
                    (fun c ->
                       (Stat.time_fun Stat.ic3_ind_gen_time
                          (fun () -> 
                             ind_generalize 
                               solver
                               empty_prop_set
                               []
                               c
                               (C.literals_of_clause c))))
                    inductive_clauses
                in

                (* Convert clauses to terms *)
                let inductive_clause_terms =
                  List.map C.term_of_clause inductive_clauses_gen
                in

                (* The invariants for the system: the clauses over its
                   variables; those over the variables IC3QE adds (see
                   [system_clauses]) are kept to IC3QE *)
                let inductive_terms =
                  List.filter system_term inductive_clause_terms
                in

                (* Broadcast inductive clauses as invariants *)
                List.iter (
                  fun i ->
                    (* Certificate 1 inductive *)
                    let cert = (1, i) in
                    KEvent.invariant
                      (TransSys.scope_of_trans_sys trans_sys) i cert false
                ) inductive_terms ;

                (* Increment statistics *)
                Stat.incr 
                  ~by:(List.length inductive_clauses) 
                  Stat.ic3_inductive_blocking_clauses;

                (* Add inductive blocking clauses as invariants *)
                List.iter (
                  fun i ->
                    (* Certificate 1 inductive *)
                    let cert = (1, i) in
                    TransSys.add_invariant trans_sys i cert false |> ignore
                ) inductive_terms ;

                SMTSolver.trace_comment
                  solver
                  "fwd_propagate: Asserting new invariants.";

                (* Add invariants to solver instance, as clauses: the
                   frames they leave rely on them *)
                List.iter 
                  (function t -> 
                    SMTSolver.assert_term solver t;
                    Term.bump_state Numeral.one t |> SMTSolver.assert_term solver) 
                  inductive_clause_terms

              );

            (* Add a new frame with the non-inductive clauses *)
            let frames' =
              (List.fold_left
                 subsume_and_add
                 F.empty
                 non_inductive_clauses)
              :: frames
            in

            (* DEBUG *)
            if debug_assert then
              assert (check_frames solver prop_set [] frames');

            frames'

          )

        else

          (

            (* Add a new frame with clauses to propagate *)
            let frames' =
              (List.fold_left
                 subsume_and_add
                 F.empty
                 prop)
              :: frames
            in
            
            (* DEBUG *)
            if debug_assert then
              assert (check_frames solver prop_set [] frames');
            
            frames')

      (* Frames in ascending order *)
      | frame :: frames_tl -> 

        (* Receive and assert new invariants *)
        handle_events 
          solver
          input_sys
          aparam
          trans_sys
          (C.props_of_prop_set prop_set);

        SMTSolver.trace_comment
          solver
          (Format.sprintf 
             "fwd_propagate: Checking forward propagation of clauses \
              in frame %d."
             (succ (List.length frames)));

        (* Clauses from frames up to R_k are contained in this and all
           preceding frames up to R_1 *)
        let frames_tl_full = 
          List.fold_left (fun a f -> ((F.values f) @ a)) [] frames_tl
        in

        (* Add propagated clauses to frame with subsumption *)
        let frame' =
          List.fold_left subsume_and_add frame prop
        in
        
        (* DEBUG *)
        if debug_assert then
          assert
            (check_frames'
               solver
               prop_set
               frames_tl_full
               (frame' :: frames));
        
        (* Separate clauses that propagate from clauses to keep in
           this frame *)
        let keep, fwd = 
          partition_fwd_prop
            solver
            trans_sys
            prop_set
            frames_tl_full
            (F.values frame')
        in

        (* Update statistics *)
        Stat.incr 
          ~by:(List.length fwd) 
          Stat.ic3_fwd_propagated;

        (* DEBUG *)
        if debug_assert then
          assert
            (check_frames'
               solver
               prop_set
               (frames_tl_full @ fwd)
               ((List.fold_left
                   (fun a c -> 
                     F.add (C.literals_of_clause c) c a) frame' keep) :: frames));

        (* All clauses propagate? *)
        if keep = [] then 

          (

            Stat.set (List.length frames |> succ) Stat.ic3_fwd_fixpoint;
            
            (* Extract inductive invariant *)
            let ind_inv = 
              (List.fold_left 
                 (fun a c -> List.map C.term_of_clause (F.values c) @ a) 
                 (List.map C.term_of_clause fwd)
                 (frames_tl))
              |> Term.mk_and
            in

            (* Activation literals for inductive invariant *)
            let ind_inv_p0, ind_inv_n0, ind_inv_n1 = 

              let mk = 
                C.create_and_assert_fresh_actlit
                  solver
                  "ind_inv"
                  ind_inv
              in

              mk C.Actlit_p0, mk C.Actlit_n0, mk C.Actlit_n1

            in

            (* DEBUG

               Check if inductive invariant is initial *)
            if debug_assert then
              assert
                (not
                   (SMTSolver.check_sat_assuming_tf
                      solver
                      [C.actlit_of_frame 0; ind_inv_n0]));

            (* DEBUG

               Check if inductive invariant is inductive *)
            if debug_assert then
              assert
                (not
                   (SMTSolver.check_sat_assuming_tf
                      solver
                      [C.actlit_p0_of_prop_set solver prop_set;
                       ind_inv_p0;
                       ind_inv_n1])); 

            (* Fixpoint found, this frame is equal to the next *)
            raise (Success (List.length frames, ind_inv))

          )

        else

          (

            let fwd' = 

              (* Try propagating clauses before generalization? *)
              if Flags.IC3QE.fwd_prop_non_gen () then

                (
                  
                  SMTSolver.trace_comment
                    solver
                    (Format.sprintf 
                       "fwd_propagate: Checking forward propagation of clauses \
                      before generalization in frame %d."
                       (succ (List.length frames)));

                  let keep_before_gen =
                    List.fold_left
                      (fun a c ->
                        match C.undo_ind_gen c with
                          | None -> a
                          | Some p ->

                            let p' = C.copy_clause_fwd_prop p in

                            SMTSolver.trace_comment solver
                              (Format.asprintf 
                                 "@[<hv>Copied clause #%d in forward propagation:@ \
                                        #%d @[<hv 1>{%a}@]@]"
                                 (C.id_of_clause p)
                                 (C.id_of_clause p')
                                 (pp_print_list Term.pp_print_term ";@ ")
                                 (C.literals_of_clause p'));
                            
                            p' :: a)
                      []
                      keep
                  in
                  
                  (* Take parent clauses of not propagating clauses and
                     try to propagate *)
                  let keep', fwd' = 
                    partition_fwd_prop
                      solver
                      trans_sys
                      prop_set
                      (frames_tl_full @ keep @ fwd)
                      keep_before_gen
                  in

                  (* Deactivate activation literals of not propagating
                     clauses *)
                  List.iter (C.deactivate_clause solver) keep';
                  
                  (* Update statistics *)
                  Stat.incr ~by:(List.length fwd') Stat.ic3_fwd_gen_propagated;

                  (* Keep clauses as before, in addition propagate
                     non-generalized clauses *)
                  (fwd @ fwd')

                )
                  
              else
                
                (* Propagate clauses as before *)
                fwd 
                  
            in

            (* Propagate clauses in next frame *)
            fwd_propagate' 
              solver
              input_sys 
              aparam 
              trans_sys
              fwd'
              ((List.fold_left subsume_and_add F.empty keep)
               :: frames)
              frames_tl

          )

  in

  (* Forward propagate all clauses and add a new frame *)
  fwd_propagate'
    solver
    input_sys 
    aparam
    trans_sys
    []
    []
    (List.rev frames)

             
(*
   TODO: After a restart we want to propagate all used blocking
   clauses into R_1. *)
let rec ic3 solver input_sys aparam trans_sys prop_set frames predicates =

  (* Must have checked for 0 and 1 step counterexamples, either by
     delegating to BMC or before this point *)
  let bmc_checks_passed prop_set =

    (* Every property is either invariant or at least 1-true *)
    List.for_all 
      (fun (p, _) -> match TransSys.get_prop_status trans_sys p with
         | Property.PropInvariant _ -> true
         | Property.PropKTrue k when k >= 1 -> true
         | _ -> false)
      (C.props_of_prop_set prop_set)

  in

  (* Current k is length of trace *)
  let ic3_k = succ (List.length frames) in

  KEvent.log L_info "IC3QE main loop at k=%d" ic3_k;

  KEvent.progress ic3_k;

  Stat.set ic3_k Stat.ic3_k;

  Stat.start_timer Stat.ic3_fwd_prop_time;

  let frames' =

    try 

      (* Forward propagate clauses in all frames *)
      fwd_propagate
        solver
        input_sys
        aparam 
        trans_sys
        prop_set
        frames

    (* Fixed point reached *)
    with Success (ic3_k, ind_inv) -> 

      if 

        (* No 0- or 1-step countexample? *)
        bmc_checks_passed prop_set 

      then

        (* Property is proved *)
        raise (Success (ic3_k, ind_inv)) 

      else

        (* Wait until BMC process has passed k=1 *)
        let rec wait_for_bmc () = 

          KEvent.log L_info "Waiting for BMC to pass k=1";

          (* Receive messages and update transition system *)
          handle_events 
            solver
            input_sys
            aparam 
            trans_sys
            (C.props_of_prop_set prop_set);

          (* No 0- or 1-step countexample? *)
          if bmc_checks_passed prop_set then

            (* Raise exception again *)
            raise (Success (ic3_k, ind_inv))

          else

            (

              (* Wait for the next message *)
              KEvent.wait_for_message ();

              (* Wait *)
              wait_for_bmc ()

            )

        in

        (* Wait until BMC has passed k=1 *)
        wait_for_bmc ()

  in

  Stat.record_time Stat.ic3_fwd_prop_time;

  Stat.set_int_list (frame_sizes frames') Stat.ic3_frame_sizes;

  Stat.start_timer Stat.ic3_strengthen_time;

  (* Recursively block counterexamples in frontier frame *)
  let frames'' , predicates = 
    block
      solver
      input_sys
      aparam 
      trans_sys
      prop_set
      ()
      predicates 
      []
      frames' 
  in

  Stat.record_time Stat.ic3_strengthen_time;

  Stat.set_int_list (frame_sizes frames'') Stat.ic3_frame_sizes;

  Stat.update_time Stat.ic3_total_time; 

  (* Output statistics *)
  if output_on_level L_debug then print_stats ();

  (* No reachable state violates the property, continue with next k *)
  ic3 solver input_sys aparam trans_sys prop_set frames'' predicates

(* Most elements of an array value that a state of a counterexample path
   is constrained to element by element, as in kmoxi's expansion of an
   equality with a constant array *)
let max_path_array_elements = 1 lsl 8

(* The constraint that the state variable instance [v] has the value [t]:
   for an array, the equations of its elements if there are few enough,
   since some solvers do not take an equation with a constant array.
   Otherwise, only Z3 and MathSAT do: cvc5 exits on it, Yices 2 does not
   know the syntax, and Bitwuzla answers unknown. *)
let path_value_eqs v t =
  let ty = Var.type_of_var v in
  if not (Type.is_array ty) then [Term.mk_eq [Term.mk_var v; t]]
  else
    match
      TermLib.array_value_eqs max_path_array_elements ty (Term.mk_var v) t
    with
    | Some eqs -> eqs
    | None ->
      match Flags.Smt.solver () with
      | `Z3_SMTLIB | `MathSAT_SMTLIB -> [Term.mk_eq [Term.mk_var v; t]]
      | _ ->
        raise (UnsupportedFeature (Format.sprintf
          "IC3QE stops: a counterexample of the system has an array of \
           more than %d elements, or with an index type that is not \
           finite, whose value only Z3 and MathSAT take back"
          max_path_array_elements))

(* Get a values for the state variables at offset [i], add values to
   path, and return an equational constraint at offset zero for values
   from the model *)
let add_to_path model path state_vars i = 

  (* Turn variable instances to state variables and sort list *)
  let model_i, state_eqs =

    List.fold_left
      (fun (m, eq) sv -> 

         let v = Var.mk_state_var_instance sv i in

         let t = 

           match Var.VarHashtbl.find model v with 

             | Model.Term t -> t
               
             | exception Not_found -> 

               TermLib.default_of_type 
                 (StateVar.type_of_state_var sv)
                                         
             (* An array read element by element, as the solver gives some
                values, or without the theory of arrays *)
             | Model.Map _ ->
               raise (UnsupportedFeature
                 "IC3QE stops: a counterexample of the system has an array \
                  whose value is not a constant array with stores")

             (* A state variable is not a function *)
             | Model.Lambda _ -> assert false

         in

         (* Create equations *)
         ((sv, Model.Term t) :: m),
         path_value_eqs
           (Var.set_offset_of_state_var_instance v Numeral.zero) t
         @ eq)

      ([], [])
      state_vars

  in
  
  (* Join values of model at current instant to result *)
  let path' = 
    list_join
      StateVar.equal_state_vars
      (List.sort
         (fun (sv1, _) (sv2, _) -> StateVar.compare_state_vars sv1 sv2)
         model_i)
      path
  in

  (* Conjunction of equations to constrain previous state to be equal
     to unprimed state in model *)
  let state = Term.mk_and state_eqs in
  
  (* Return path with state added and constraint for state *)
  (path', state)


(* Whether the system has a state variable of an array type *)
let has_arrays trans_sys =
  List.exists
    (fun sv -> Type.is_array (StateVar.type_of_state_var sv))
    (TransSys.state_vars trans_sys)

(* No concrete path is found along a sequence of blocking clauses. Each
   state of a blocking clause should have a successor in the next one, but
   the solver may find none, or answer unknown, with arrays: IC3 stops
   rather than fails then. Without arrays, the trace must have a path. *)
let no_cex_path trans_sys =
  if has_arrays trans_sys then
    raise (UnsupportedFeature
      "IC3QE stops: no concrete counterexample is found along the trace \
       of blocking clauses")
  else
    assert false

(* Extract a concrete counterexample from a sequence of blocking
   clauses *)
let extract_cex_path solver trans_sys trace = 

  SMTSolver.trace_comment
    solver
    "extract_cex_path: extracting concrete counterexample trace.";

  (* Need to copy clauses, may have been subsumed meanwhile *)
  let trace = List.map C.copy_clause trace in

  (* Find a state in the head of the sequence of blocking clauses and
     add to the path. Use the activation literal [pre_state] to
     constrain the previous state to the one in the path. *)
  let rec extract_cex_path' path pre_state = function

    | [] -> 

      (* Return trace in order *)
      List.map 
        (fun (sv, vl) -> (sv, List.rev vl))
        path

    (* Take first blocking clause *)
    | r_i :: tl -> 

      match 
        
        (* Find a state in the blocking clause, starting from the
           given state *)
        SMTSolver.check_sat_assuming_ab
          solver
          
          (fun solver -> 

            (* Add primed state to path, get equational constraint for
               state *)
            let path', state = 
              add_to_path
                (* SMTSolver.get_model solver *)
                (get_var_values
                   solver
                   (TransSys.get_state_var_bounds trans_sys)
                   (cti_vars trans_sys))
                path
                (TransSys.state_vars trans_sys)
                Numeral.one
            in

            path', state)

          (fun _ -> ())

          (* Assume previous state and blocking clause *)
          (pre_state :: C.actlits_n1_of_clause solver r_i)

      with
          
        (* Recurse to continue path out of succeeding blocking
           clause *)
        | SMTSolver.Sat (path', state) -> 
          
            (* Activation literal for state *)
          let actlit_p0_state =
            C.create_and_assert_fresh_actlit
              solver
              "cex_path"
              state
              C.Actlit_p0
          in
          
          extract_cex_path' path' actlit_p0_state tl

        | SMTSolver.Unsat _ -> no_cex_path trans_sys
          
  in

  (* Start path from initial state into first blocking clause, get
     activation literal for state in R_1 *)
  let init_path, state_init = 
    match trace with 

      (* Must have at least one state *)
      | [] -> assert false

      (* First blocking clause is successor of initial state *)
      | r_1 :: _ -> 

        match
          
          (* Find an initial state with the first blocking clause as
             successor *)
          SMTSolver.check_sat_assuming_ab
            solver

            (fun solver ->
              
              (* Add unprimed state to empty path, get equational
                 constraint for state *)
              add_to_path
                (* SMTSolver.get_model solver *)
                (get_var_values
                   solver
                   (TransSys.get_state_var_bounds trans_sys)
                   (cti_vars trans_sys))
                []
                (TransSys.state_vars trans_sys)
                Numeral.zero)

            (fun _ -> ())
            
            (* Assume initial state and blocking clause *)
            ((C.actlit_of_frame 0) ::
                C.actlits_n1_of_clause solver r_1)

        with

          | SMTSolver.Sat r -> r 
            
          | SMTSolver.Unsat _ -> no_cex_path trans_sys

  in

  (* Activation literal for state *)
  let actlit_p0_state_init =
    C.create_and_assert_fresh_actlit
      solver
      "cex_path"
      state_init
      C.Actlit_p0
  in

  (* Extract concrete counterexample starting in a state leading to
     the first blocking clause *)
  extract_cex_path' init_path actlit_p0_state_init trace


(* 

   TODO: Return the maximal R for which P & R & T |= P holds, where R
   contains the blocking clauses before a restart. Therefore we know
   that I |= R. *)
(* let add_to_r1 clauses = [] *)


(* Helper function for restarts *)
let rec restart_loop solver input_sys aparam trans_sys props predicates = 

  (* Exit if no properties left to prove *)
  if props = [] then () else

    (* Properties to prove after restart *)
    let props' = 

      try 

        (* Reset statistics about frames on restart *)
        Stat.set_int_list [] Stat.ic3_frame_sizes;

        (* Get activation literals for current property set *)
        let prop_set =
          C.prop_set_of_props props
        in

        (* Run IC3 procedure *)
        ic3
          solver 
          input_sys
          aparam 
          trans_sys 
          prop_set
          []
          predicates

      with 

        (* All propertes are valid *)
        | Success (_, ind_inv) -> 

          (

            (* Certificate = 1-inductive invariant in conjunction of the
               properties: the clauses over the variables of the system
               (see [system_clauses]) *)
            let cert =
              1, Term.mk_and (system_clauses ind_inv @ List.map snd props)
            in
            
            (* Send out valid properties *)
            List.iter
              (fun (p, _) -> 
                 KEvent.prop_status
                   (Property.PropInvariant cert)
                   input_sys
                   aparam
                   trans_sys
                   p) 
              props;

            (* No more properties remaining *)
            []

          )

        (* Some property is invalid *)
        | Counterexample trace -> 

          (

            (* Extract counterexample from sequence of blocking
               clauses *)
            (* The counterexample: extracted state by state, or, with
               function symbols abstracted in the generalization, found in
               one unrolling with the symbols, as the states a trace gives
               one by one may interpret a symbol differently at different
               steps (see [cex_of_trace]) *)
            let cex =
              if UfSymbol.UfSymbolSet.is_empty !(abstracted_ufs ()) then
                `Real
                  (try
                     extract_cex_path
                       solver
                       trans_sys
                       trace
                   with SMTSolver.Unknown when has_arrays trans_sys ->
                     no_cex_path trans_sys)
              else
                try cex_of_trace trans_sys trace
                with SMTSolver.Unknown when has_arrays trans_sys ->
                  no_cex_path trans_sys
            in
            match cex with
            | `Conflicts conflicts ->
              (* A spurious counterexample: refine the abstraction and run
                 IC3QE again on all the properties, or stop *)
              if refine solver conflicts then props
              else
                raise (UnsupportedFeature
                  "IC3QE stops: the counterexample found is spurious, as it \
                   interprets a function symbol differently at different steps")
            | `Real cex_path ->
(*
            debug ic3
                "@[<v>Counterexample:@,@[<hv>%a@]@]"
                (KEvent.pp_print_path_pt trans_sys false) cex_path
            in
*)
            (* Check which properties are disproved *)
            let props', props_false =

              List.fold_left
                (fun (props', props_false) (p, t) -> 

                   if 

                     (* Property is false along path? *)
                     Model.exists_on_path
                       (fun m -> 
                          match 
                            Eval.eval_term
                              (TransSys.uf_defs trans_sys)
                              m
                              t
                          with 
                            | Eval.ValBool false -> true
                            | _ -> false)
                       (Model.path_of_list cex_path)

                   then

                     (KEvent.prop_status 
                        (Property.PropFalse cex_path) 
                        input_sys
                        aparam 
                        trans_sys 
                        p;

                      KEvent.log
                        L_info 
                        "Property %s disproved by IC3QE"
                        p;

                      (props', p :: props_false))

                   else

                     (KEvent.log
                        L_info 
                        "Property %s not disproved by IC3QE"
                        p;

                      ((p, t) :: props', props_false)))

                ([], [])
                props
            in
(*
            debug ic3
                "Disproved %a, continuing with %a"
                (pp_print_list
                   (fun ppf n -> Format.fprintf ppf "%s" n)
                   "@ ")
                props_false
                (pp_print_list
                   (fun ppf (n, _) -> Format.fprintf ppf "%s" n)
                   "@ ")
                props'
            in
*)
            assert (not (props_false = []));

            props'

          )

        | Disproved _ -> 

          KEvent.log
            L_info 
            "Some properties are disproved";

          (* Check which properties are disproved *)
          let props' =

            List.fold_left
              (fun accum (p, t) -> 

                 (* Property is disproved? *)
                 if TransSys.is_disproved trans_sys p then

                   (KEvent.log
                      L_info 
                      "Removing disproved property %s"
                      p;

                    (* Remove property disproved property from
                         properties to prove *)
                    accum)

                 else 

                   (* Keep property *)
                   (p, t) :: accum)

              []
              props
          in

          props'

        (* Formuala is not in linear integer arithmetic *)
        | Presburger.Not_in_LIA -> 

          (
            let qe_solver_is_available =
              match Flags.Smt.qe_solver () with
              | `detect -> false
              | _ -> true
            in

            if (not qe_solver_is_available) then
              raise (UnsupportedFeature
              "Shutting down IC3QE: Z3 or cvc5 is required for inputs with reals or machine integers.");

            KEvent.log
              L_info
              "Problem contains real or machine integer valued variables, \
               switching off approximate QE";

            Flags.QE.set_qe_method `Impl;

            props

          )

        (* Restart for other reason *)
        (* | Restart -> props *)

    in

    if not (props' = []) then 

      (              

        KEvent.log
          L_info 
          "@[<h>Restarting IC3QE with properties @[<h>%a@]@]"
          (pp_print_list
             (fun ppf (n, _) -> Format.fprintf ppf "%s" n)
             "@ ")
          props';

        Stat.incr Stat.ic3_restarts);

    (* Restart with remaining properties *)
    restart_loop solver input_sys aparam trans_sys props' predicates
    
   
(* Check if the property is valid in the initial state and in the
   successor of the initial state, raise exception [Counterexample] if
   not *)
let bmc_checks solver input_sys aparam trans_sys props bound =

  (* Activation literal for frame, is symbol has been declared *)
  let actlit_R0 = C.actlit_of_frame 0 in

  (* Entailment does not hold: split properties in not falsified and
     falsifiable properties *)
  let not_entailed props k _ = 

    (* Get model for all variables of transition system *)
    let model =
      (* SMTSolver.get_model solver *)
      get_var_values
        solver
        (TransSys.get_state_var_bounds trans_sys)
        (cti_vars trans_sys)
    in

    (* Extract counterexample from solver *)
    let cex =
      Model.path_from_model
        (TransSys.state_vars trans_sys)
        model
        k 
    in

    (* Evaluate term in model *)
    let eval term =
      Eval.eval_term (TransSys.uf_defs trans_sys) model term
      |> Eval.bool_of_value 
    in

    (* Split properties *)
    let not_falsified, falsifiable =
      List.partition
        (fun (_, term) -> Term.bump_state k term |> eval )
        props
    in

    (* Return not falsified and falsifiable properties with
       counterexample *)
    (not_falsified, Some (cex, falsifiable))

  in

  (* Entailment does hold: return all properties as not falsified and
     none as falsifiable *)
  let all_entailed props _ = (props, None) in

  (* Check I |= P for given list of properties *)
  let rec bmc_check check_primed = function 

    (* Terminate if all properties falsifiable *)
    | [] -> [] 

    (* Some properties left to check *)
    | props -> 

      (* Create activation literals and assert formulas for property
         set *)
      let prop_set =
        C.prop_set_of_props props
      in 

      (* Check satsifiability of I & ~P for all not falsified
         properties P, and partition into not falsified and
         falsifiable *)
      SMTSolver.trace_comment 
        solver
        (Format.sprintf
           "bmc_checks: Check for %s-step counterexample"
           (if check_primed then "one" else "zero"));

      let props', props_falsifiable = 
        SMTSolver.check_sat_assuming
          solver
          (not_entailed
             props
             (if check_primed then Numeral.one else Numeral.zero))
          (all_entailed props)
          (if check_primed then
             (actlit_R0 :: 
              (C.actlit_p0_of_prop_set solver prop_set :: 
               C.actlits_n1_of_prop_set solver prop_set))
           else
             (actlit_R0 :: C.actlits_n0_of_prop_set solver prop_set))
      in

      (* Some properties falsified? *)
      match props_falsifiable with

        (* Some properties falsifiable *)
        | Some (cex, falsifiable) -> 

          (* Broadcast properties as falsified with counterexample *)
          List.iter
            (fun (s, _) ->
               KEvent.prop_status
                 (Property.PropFalse (Model.path_to_list cex))
                 input_sys
                 aparam 
                 trans_sys
                 s)
            falsifiable;

          SMTSolver.assert_term
            solver
            (Term.mk_not (C.actlit_p0_of_prop_set solver prop_set));

          (* Check remaining properties *)
          bmc_check check_primed props'

        (* No properties falsifiable *)
        | None -> 

          (* Broadcast properties as 0-true or 1-true *)
          List.iter 
            (fun (s, _) -> 
               KEvent.prop_status
                 (Property.PropKTrue
                    (if check_primed then 1 else 0))
                 input_sys
                 aparam 
                 trans_sys
                 s)
            props';

          (*
          SMTSolver.assert_term
            solver
            (Term.mk_not (C.actlit_p0_of_prop_set prop_set));
          *)

          (* Return properties not falsified *)
          props'

  in

  (* Check if properties hold in the initial state and filter out
     those that don't *)
  let props' = bmc_check false props in

  (* Assert transition relation unguarded

     T[x,x'] *)
  SMTSolver.trace_comment solver "main: Assert unguarded transition relation";
  SMTSolver.assert_term
    solver

    (TransSys.trans_of_bound (Some (SMTSolver.declare_fun solver))
       trans_sys (Numeral.of_int bound));

  (* Check if properties hold in the successor of the initial state
     and filter out those that don't *)
  let props'' = bmc_check true props' in

  (* Return 0-true and 1-true properties *)
  props'' 
  

(* Entry point

     If BMC is not running in parallel, check for zero and one step
     counterexamples.

     Run IC3 main loop and catch [Success] and [Counterexample]
     exceptions.

*)
let main_ic3 input_sys aparam trans_sys =

  (* IC3 solving starts now *)
  Stat.start_timer Stat.ic3_total_time;

  (* Determine logic for the SMT solver: add LIA for some clauses of IC3 *)
  let logic = TransSys.get_logic trans_sys
    (*let open TermLib.FeatureSet in
    match TransSys.get_logic trans_sys with
    | `Inferred fs when mem BV fs ->
        raise
          (UnsupportedFeature
             "Shutting down IC3QE: The current implementation does not support BV \
              problems.")
    | `Inferred fs when not (subset fs (of_list [ Q; UF; A ])) ->
        `Inferred
          (TermLib.FeatureSet.add TermLib.IA
             (TermLib.FeatureSet.add TermLib.LA fs))
    | l -> l*)
  in

  (* Create new solver instance *)
  let solver =
    SMTSolver.create_instance
      ~produce_models:true
      ~produce_unsat_assumptions:true
      logic
      (Flags.Smt.solver ())
  in


  let bound =
    match Flags.IC3QE.abstr () with
      | `None -> 1
      | `IA -> 3
  in

  (* Declare uninterpreted function symbols *)
  SMTSolver.trace_comment
    solver
    "main: Declare state variables and define predicates";

  (* Declare uninterpreted function symbols *)
  TransSys.define_and_declare_of_bounds
    trans_sys
    (SMTSolver.define_fun solver)
    ~define_rec:(SMTSolver.define_funs_rec solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.zero (Numeral.of_int bound);

  (* Get invariants of transition system *)
  let invars_1 =
    TransSys.invars_of_bound trans_sys Numeral.one
  in

  (* Get invariants for current state *)
  let invars_0 =
    TransSys.invars_of_bound
      trans_sys
      ~one_state_only:true
      Numeral.zero
  in

  TransSys.assert_global_constraints trans_sys (SMTSolver.assert_term solver) ;

  (* Assert invariants for current state if not empty *)
  if invars_0 <> [] then

    (SMTSolver.trace_comment solver "main: Assert invariants";
     List.iter (SMTSolver.assert_term solver) invars_0;
     List.iter (SMTSolver.assert_term solver) invars_1);

  (* Create activation literal for frame R_0 *)
  let actconst_r0, actlit_r0 =
    C.actlit_symbol_of_frame 0, C.actlit_of_frame 0
  in

  (* Declare symbol in solver *)
  SMTSolver.declare_fun solver actconst_r0;

  Stat.incr Stat.ic3_activation_literals;

  (* Assert initial state constraint guarded with activation literal

     a_R0 => I[x] *)
  SMTSolver.trace_comment solver "main: Assert guarded initial state";
  SMTSolver.assert_term
    solver
    (Term.mk_implies
       [actlit_r0;
        (TransSys.init_of_bound (Some (SMTSolver.declare_fun solver))
           trans_sys Numeral.zero)]);

  (* Declare the application variables of the abstraction of the function
     symbols, with their constraints *)
  abstract_system solver trans_sys ;

  (* Print inductive assertions to file? *)
  (match Flags.IC3QE.print_to_file () with

    (* Keep default formatter *)
    | None -> ()

    (* Output to given file *)
    | Some f ->

      (* Output channel on file *)
      let oc =
        try open_out f with
          | Sys_error _ ->
            failwith "Could not open file for inductive assertions"
      in

      (* Create formatter and store in reference *)
      ppf_inductive_assertions () := Format.formatter_of_out_channel oc);

  (* Properties to prove from the transition system *)
  let trans_sys_props =
    TransSys.props_list_of_bound trans_sys Numeral.zero
  in
  let predicates =

    match Flags.IC3QE.abstr () with

      | `IA ->

        let init = TransSys.init_of_bound None trans_sys Numeral.zero in
        List.fold_left
          (fun acc (_,t) -> Term.TermSet.add t acc)
          (init |> Term.get_atoms |> Term.TermSet.add init)
          trans_sys_props
        |> Term.TermSet.elements

      | `None ->

        []

  in


  List.iter
    (fun p ->
       SMTSolver.assert_term
         solver
         (Term.mk_eq
            [p;
             Term.bump_state (Numeral.of_int 2) p]);

       SMTSolver.assert_term
         solver
         (Term.mk_eq
            [Term.bump_state Numeral.one p;
             Term.bump_state (Numeral.of_int 3) p]);

    )
    predicates;


  (* Check for zero and one step counterexamples and continue with
     remaining properties *)
  let props' =

    (* Is BMC running in parallel? *)
    if List.mem `BMC (Flags.enabled ()) && not debug_assert then (

      (* When transition relation comes from a contract, it may be unsatisfiable.
         If check for zero counterexample is delegated to BMC, it is safe to assert
         transition relation here. Otherwise, we assert it after check for zero cex
         in bmc_checks
      *)

      (* Assert transition relation unguarded

         T[x,x'] *)
      SMTSolver.trace_comment solver "main: Assert unguarded transition relation";
      SMTSolver.assert_term
        solver

        (TransSys.trans_of_bound (Some (SMTSolver.declare_fun solver))
           trans_sys (Numeral.of_int bound));

      (KEvent.log L_info
         "Delegating check for zero and one step counterexamples \
          to BMC process.";

       trans_sys_props)

    )
    else

      (* BMC is not running, must check here *)
      bmc_checks
        solver
        input_sys
        aparam 
        trans_sys
        trans_sys_props
        bound

  in

  (* Run and restart on disproved properties *)
  restart_loop
    solver
    input_sys
    aparam
    trans_sys
    props'
    predicates


let main input_sys aparam trans_sys =

  (match Flags.Smt.solver () with
  | `Yices2_SMTLIB -> (
    (let open TermLib in
     let open TermLib.FeatureSet in
     match TransSys.get_logic trans_sys with
     | `Inferred l when mem NA l ->

       raise (UnsupportedFeature
         "Shutting down IC3QE: Yices 2 does not support unsat-cores with non-linear models.")

     | _ -> ()
    )
  )
  | _ -> () );

  (* Note: IC3 does not assert the functional congruence instances that
     enforce determinism of (abstracted) functions with container-typed
     arguments (see [TransSys.fn_congruence_instances]); without them, the
     counterexamples it finds for such systems may be spurious with respect
     to the intended (deterministic) semantics. This check is the only guard:
     a system with congruence groups always includes a function symbol,
     which IC3QE otherwise accepts, abstracting its applications in the
     generalization (see [extrapolate]). To support
     these systems, the instances for bounds 0 and 1 would have to be
     asserted alongside the transition relation in the frame solvers, and
     clause generalization would have to account for the difference witness
     functions the instances contain. *)
  if TransSys.has_fn_congruence_groups trans_sys then
    raise (UnsupportedFeature
      "Shutting down IC3: system requires functional congruence instances \
       for functions with container-typed arguments.")
  ;

  match Flags.IC3QE.abstr () with
  | `IA -> main_ic3 input_sys aparam trans_sys
  | `None -> (
    (* The applications of the function symbols are abstracted over
       application variables (see [app_var]) *)
    reset_abstraction aparam trans_sys ;
    set_abstracted_ufs trans_sys ;
    if not (UfSymbol.UfSymbolSet.is_empty !(abstracted_ufs ())) then
      KEvent.log L_info
        "IC3QE: system includes function symbols, abstracted over \
         application variables; spurious counterexamples refine the \
         abstraction with history variables." ;
    main_ic3 input_sys aparam trans_sys
  )


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End:
*)
