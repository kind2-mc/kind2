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

module Num = Numeral
module Dec = Decimal
module SVar = StateVar
module Set = Term.TermSet
module Sys = TransSys

type svar = SVar.t
type set = Set.t
type flat = Term.T.flat
type sys = Sys.t


(* |===| Module signatures for functor. *)


(** Signature of a module for state variable selection rules. *)
module type RulesSig = sig
  (** Information produced by state variable rules. *)
  type svar_info
  (** Information produced by flat rules. *)
  type flat_info
  (** Applies the state variable rules. *)
  val svar_rules : bool -> svar list -> set -> set * svar_info
  (** Applies post svar treatment rules. *)
  val post_svars : bool -> (set * svar_info) -> set * flat_info
  (** Applies the flat term rules. *)
  val flat_rules : bool -> flat -> (set * flat_info) -> set * flat_info
  (** Applies postprocessing rules. *)
  val post_rules : bool -> svar_info -> flat_info -> set -> set
end


(* |===| Helper functions for one/two-state and mining. *)


(* Bumps a term. *)
let bump = Term.bump_state

(* Numeral zero. *)
let zero = Num.zero
(* Numeral one. *)
let one = Num.one
(* Numeral minus one. *)
let m_one = Num.( ~- one )


(* If all vars in the input term have offset 0 (-1), adds input term bumped at
-1 (0) to input set. Otherwise set is unchanged. *)
let state_complement term set =
  match Term.var_offsets_of_term term with
  | Some lo, Some hi when Num.( lo = zero ) && Num.( hi = zero ) ->
    (* Term is one state @0, adding -1 version. *)
    Set.add (Term.bump_state m_one term) set
  | Some lo, Some hi when Num.( lo = m_one ) && Num.( hi = m_one ) ->
    (* Term is one state @-1, adding 0 version. *)
    Set.add (Term.bump_state one term) set
  (* Otherwise return set unchanged. *)
  | _ -> set

(* Applies [state_complement] to the elements of a set. *)
let state_complement_set set = Set.fold state_complement set set

(* Only adds input term if it is one-state. Adds its version @0.
For example, a one-state term @-1 will be bumped at 0 before it's added.
Otherwise set is unchanged. *)
let one_state_ify term set =
  match Term.var_offsets_of_term term with
  | Some lo, Some hi when Num.(lo = hi) ->
    let bump_k = Num.( zero - lo ) in
    Set.add (bump bump_k term) set
  | Some _, Some _ -> set
  (* Otherwise return set unchanged. *)
  | _ -> set

(* Applies [one_state_ify] to the elements of a set. *)
let one_state_ify_set set = Set.fold one_state_ify set Set.empty

(* The last element of a list. *)
let rec get_last = function
| head :: [] -> [head]
| [] -> raise Not_found
| _ :: t -> get_last t

(* Applies something to all flat subterms of a term.

Adds to the input set. *)
let flat_apply term work set =
  let set_ref = ref set in
  let memorize set' = set_ref := set' in
  Term.eval_t (
    fun flat_term _ -> work flat_term !set_ref |> memorize
  ) term ;
  !set_ref

(* Checks if [sub_sys] is a subsystem of [sys]. *)
let is_sub sub_sys sys = Sys.get_subsystems sys |> List.mem sub_sys

(* Inserts or updates a sys/terms bindig in an associative list sorted by
topological arder. If [sys] is already in the list, then its terms are updated
with the union of the old ones and the new ones. If it's not then [sys, terms]
is inserted at the right place w.r.t. topological order. *)
let insert_sys_terms ( (sys, terms) as pair ) =
  let rec loop prefix = function
    | (sys', terms') :: tail when sys == sys' ->
      (* System's already in the list. *)
      (sys, Set.union terms terms') :: tail |> List.rev_append prefix
    | ((sys', _) :: _) as tail when is_sub sys sys' ->
      (* Next system has [sys] as a sub-system, inserting here. *)
      pair :: tail |> List.rev_append prefix
    | head :: tail ->
      (* Skipping this one. *)
      loop (head :: prefix) tail
    | [] ->
      (* Could not find [sys], adding it at the end. *)
      pair :: prefix |> List.rev
  in
  loop []

(* Turns a flat term into a term. *)
let to_term = Term.construct

(* Reconstructs a flat term and adds it to a set. *)
let to_term_add flat set = Set.add (to_term flat) set

(* Node type of a term. *)
let type_of term = Term.type_of_term term |> Type.node_of_type


(* The name of a transition system. *)
let name_of_sys sys =
  TransSys.scope_of_trans_sys sys |> String.concat "/"



(* |===| Functor stuff. *)


(** Module generating candidate terms for invariant generation. *)
module type CandGen = sig
  (** Generates sets of candidate terms from a transition system, and its
  subsystems if the first flag is true. Second flag is for two-state. *)
  val mine : bool -> bool -> sys -> (sys * set) list
end


(** Functor creating a candidate generation module from state var and flat
term rules. *)
module MakeCandGen (Rules: RulesSig) : CandGen = struct

  (* Mining function. *)
  let mine top_only two_state top_sys =
    let svar_rules = Rules.svar_rules two_state in
    let flat_rules = Rules.flat_rules two_state in
    let post_svars = Rules.post_svars two_state in
    let post_rules = Rules.post_rules two_state in

    (* Association list between systems and their candidate terms. *)
    let rec mk_sys_map result = function
      | sys :: tail ->
        let scope = Sys.scope_of_trans_sys sys in

        if List.mem_assoc sys result then
          (* We already know the system, discarding it. *)
          mk_sys_map result tail

        else (

          (* We don't know this system. *)
          let init, trans =
            Sys.init_of_bound sys zero, Sys.trans_of_bound sys zero
          in
          (* Format.printf
            "candidates (%d):@   @[<v>%a@]@.@."
            (Set.cardinal candidates)
            (pp_print_list
              Term.pp_print_term
              "@ "
            ) (Set.elements candidates) ; *)
          let candidates =
            let user_candidates =
              TransSys.get_unknown_candidates sys |> Set.of_list
            in
            
            if Flags.Certif.only_user_candidates () then user_candidates else (
              let candidates, svar_info =
                Set.empty |> svar_rules (Sys.state_vars sys)
              in
              let candidates, flat_info =
                post_svars (candidates, svar_info)
                |> flat_apply init flat_rules
                |> (
                  if Flags.Invgen.mine_trans ()
                  then flat_apply trans flat_rules else identity
                )
              in
              post_rules svar_info flat_info candidates
              |> Set.union user_candidates
            )
          in
          (* Format.printf
            "candidates (%d):@   @[<v>%a@]@.@."
            (Set.cardinal candidates)
            (pp_print_list
              Term.pp_print_term
              "@ "
            ) (Set.elements candidates) ; *)
          (* Adding two-state complement if needed. *)
          let candidates = state_complement_set candidates in
            (* if two_state then state_complement_set candidates
            else one_state_ify_set candidates
          in *)
          (* Format.printf
            "candidates (%d, %b):@   @[<v>%a@]@.@."
            (Set.cardinal candidates)
            two_state
            (pp_print_list
              Term.pp_print_term
              "@ "
            ) (Set.elements candidates) ; *)

          (* Lifting sub-candidates. *)
          let result =
            result |> (
              if Flags.Invgen.lift_candidates () then
                Set.fold (
                  fun term map ->
                    Sys.instantiate_term_all_levels
                      top_sys TransSys.trans_base scope term
                    |> fun (top, others) -> top :: others
                    |> List.fold_left (
                      fun map (sys, terms) ->
                        insert_sys_terms
                          (sys, Set.of_list terms) map
                    ) map
                ) candidates
              else identity
            )
            |> insert_sys_terms (sys, candidates)
          in

          mk_sys_map result (
            List.concat [ Sys.get_subsystems sys ; tail ]
          )

        )

      | [] ->
        (if Flags.Invgen.top_only () then get_last result else result)
        |> (
          if two_state then identity else List.map (
            fun (sys, set) ->
              let res = one_state_ify_set set in
              (* if not two_state then (
                Format.printf
                  "candidates %s (%d, %b):@   @[<v>%a@]@.@."
                  (name_of_sys sys)
                  (Set.cardinal res)
                  two_state
                  (pp_print_list
                    Term.pp_print_term
                    "@ "
                  ) (Set.elements res)
              ) ; *)
              sys, res
          )
        )
    in

    mk_sys_map [] [ top_sys ]

end



(* |===| Helpers for term inspection. *)


(* Returns true if the term mentions at least one non-constant variable. *)
let mentions_var term = Term.vars_of_term term |> Var.VarSet.exists (
  fun var -> not (Var.is_const_state_var var)
)


(* Returns true if the term is a variable or a constant. *)
let rec is_var_or_const term = match Term.destruct term with
| Term.T.Attr (kid, _) -> is_var_or_const kid
| Term.T.Var var -> (
  Var.is_state_var_instance var
) && (
  Var.state_var_of_state_var_instance var
  |> SVar.for_inv_gen
)
| Term.T.Const _ -> true
| _ -> false


(* Returns true if the term is a variable. *)
let rec is_var term = match Term.destruct term with
| Term.T.Attr (kid, _) -> is_var kid
| Term.T.Var var -> (
  Var.is_state_var_instance var
) && (
  Var.state_var_of_state_var_instance var
  |> SVar.for_inv_gen
)
| _ -> false


(* Returns true if the term is a constant. *)
let rec is_const term = match Term.destruct term with
| Term.T.Attr (kid, _) -> is_const kid
| Term.T.Const _ -> true
| _ -> false


(* |===| Bool mining. *)


(* Rules for bool candidate term generation from state variables. *)
module BoolRules = struct
  (* Adds svars of type bool to the input set. *)
  let bool_rule svar set =
    let var =
      Var.mk_state_var_instance svar zero |> Term.mk_var
    in
    Set.add var set |> Set.add (Term.mk_not var)

  (* If [svar] is an [IntRange(lo, hi)], adds to the input set the constraints
  [svar = n], for [n] in [[lo, hi]].

  NB: original version added [lo <= svar] and [svar <= hi] too. *)
  let range_rule lo hi svar =
    let var = Var.mk_state_var_instance svar zero |> Term.mk_var in
    let rec loop lo set =
      if Num.(lo > hi) then set else loop (Num.succ lo) (
        Set.add (Term.mk_eq [var ; Term.mk_num lo]) set
      )
    in
    loop lo

  (* Adds [svar >= 0] for an int [svar] to the input set. *)
  let int_rule svar set =
    let var = Var.mk_state_var_instance svar zero |> Term.mk_var in
    Set.add (Term.mk_geq [var ; Term.mk_num zero]) set
    |> Set.add (Term.mk_eq [var ; Term.mk_num zero])

  (* Adds [svar >= 0] for a real [svar] to the input set. *)
  let real_rule svar set =
    let var = Var.mk_state_var_instance svar zero |> Term.mk_var in
    Set.add (Term.mk_geq [var ; Term.mk_dec Dec.zero]) set
    |> Set.add (Term.mk_eq [var ; Term.mk_dec Dec.zero])



  let all_subterms = false
  let only_depth_one = true

  (* Adds term to input set if term is not [NOT]. *)
  let bool_term_rule flat set = match flat with
  | _ when all_subterms -> to_term_add flat set
  | Term.T.App (sym, kids) ->
    if (not only_depth_one) || List.for_all is_var_or_const kids then (
      match Symbol.node_of_symbol sym with
      | `OR
      | `XOR
      | `IMPLIES
      | `AND
      | `ITE
      | `IS_INT
      | `DISTINCT -> to_term_add flat set
      | _ -> set
    ) else set
  | _ -> set

  (* If term is an arithmetic atom [lhs <op> rhs], add [lhs >= rhs] and
  [lhs <= rhs]. *)
  let arith_op_synth flat set = match flat with
  | Term.T.App (sym, ((kid1 :: kid2 :: []) as kids)) when (
    ( (is_var kid1) && (is_const kid2) ) ||
    ( (is_var kid2) && (is_const kid1) ) (* ||
    ( (is_var kid1) && (is_var kid2) ) *)
  ) -> (
    let add_ineqs () =
      Set.add (Term.mk_geq kids) set
      |> Set.add (Term.mk_leq kids)
    in
    match Symbol.node_of_symbol sym with
    | `LEQ | `GEQ -> add_ineqs ()
    | `GT | `LT -> add_ineqs () |> Set.add (to_term flat)
    | `EQ -> (
      (* Making sure it's an arith equality. *)
      match type_of kid1 with
      | Type.Int | Type.Real -> add_ineqs ()
      | _ -> set
    )
    | _ -> set
  )
  | _ -> set

  type svar_info = ()

  let svar_rules two_state svars set = (
    svars |> List.fold_left (
      fun set svar ->
        if SVar.for_inv_gen svar |> not then set else (
          match SVar.type_of_state_var svar |> Type.node_of_type with
          | Type.Bool -> bool_rule svar set
          | Type.IntRange (lo, hi) -> range_rule lo hi svar set
          | Type.Int -> int_rule svar set
          | Type.Real -> real_rule svar set
          | _ -> set
        )
    ) set,
    ()
  )

  type flat_info = ()

  let post_svars two_state (set, _) = set, ()

  let flat_rules two_state flat (set, _) =
    (* match to_term flat |> type_of with
    | Type.Bool -> arith_op_synth flat set, () (* |> bool_term_rule flat *)
    | _ -> set, () *)
    set, ()

  let post_rules two_state _  _ set =
    (* Set.fold (
      fun term set -> Set.add (Term.negate_simplify term) set
    ) set set
    |> *)
    Set.add Term.t_true set

end



(* |===| Miners. *)


(** Bool candidate term miner. *)
module Bool = MakeCandGen (BoolRules)
















module CandidateTermGen = struct

  (* Short name for sets of terms. *)
  module Set = Term.TermSet


  (* Bool type. *)
  let bool_type = Type.t_bool

  (* Constructs a term. *)
  let flat_to_term = Term.construct



  (* Aggregates state var rules. *)
  module StateVarRules : sig

    (* Applies the state var rules. *)
    val apply: StateVar.t list -> Set.t -> Set.t

  end = struct

    (* If svar is an IntRang(low,up) and low < up, generates terms low <= x, x
     <= up, and x=n where x is an IntRange (low,up) (n\in[low,up]). *)
    let rec unroll_ranges svar set =
      
      (* Creates the terms for an intrange. *)
      let rec unroll_range set low up var =
        if Numeral.(low > up)
        then set
        else
          unroll_range
            (Set.add (Term.mk_eq [var ; Term.mk_num low]) set)
            (Numeral.succ low)
            up
            var
      in

      let var =
        Var.mk_state_var_instance svar Numeral.zero
        |> Term.mk_var
      in

      match StateVar.type_of_state_var svar |> Type.node_of_type with

      | Type.IntRange (low,up) when not Numeral.(low = up) ->
         
         unroll_range set low up var
         |> Set.add
              (Term.mk_leq [ Term.mk_num low ; var ])
         |> Set.add
              (Term.mk_leq [ var ; Term.mk_num up ])

      | _ -> set

               
    (* Generates x>=0 for int and real variables. *)
    let arith_zero_eqs svar set =

      match StateVar.type_of_state_var svar |> Type.node_of_type with

      | Type.Int ->

         (* Variable at 0. *)
         let var =
           Var.mk_state_var_instance svar Numeral.zero
           |> Term.mk_var
         in

         Set.add
           (Term.mk_geq [ var ; Term.mk_num Numeral.zero ])
           set

      | Type.Real ->

         (* Variable at 0. *)
         let var =
           Var.mk_state_var_instance svar Numeral.zero
           |> Term.mk_var
         in

         Set.add
           (Term.mk_geq [ var ; Term.mk_dec Decimal.zero ])
           set

      | _ -> set


    (* Add boolean variables and their negation. *)
    let bool_vars svar set =
      match StateVar.type_of_state_var svar |> Type.node_of_type with

      | Type.Bool ->

         (* Variable at 0. *)
         let var =
           Var.mk_state_var_instance svar Numeral.zero
           |> Term.mk_var
         in
         
         set
         (* Adding variable. *)
         |> Set.add var
         (* Adding negation of the variable. *)
         |> Set.add (Term.mk_not var)

      | _ -> set



    let rule_list =
      [ unroll_ranges, true_of_unit ;
        arith_zero_eqs, true_of_unit ;
        bool_vars, true_of_unit ]

    let apply svars set =
      svars
      (* To all svars... *)
      |> List.fold_left
           ( fun set' svar ->
             if StateVar.for_inv_gen svar
             then
               rule_list
               (* ...apply all rules... *)
               |> List.fold_left
                    ( fun set'' (rule,condition) ->
                      (* ...if their condition is true. *)
                      if condition ()
                      then rule svar set''
                      else set'' )
                    set'
             else set')
           set

  end


  (* Aggregate rules on flat terms. *)
  module FlatTermsRules : sig

    (* Applies the state var rules. *)
    val apply: Term.T.flat -> Set.t -> Set.t

  end = struct

    (* Adds term to set if term has type bool. *)
    let must_be_bool term set =
      if Term.type_of_term term == bool_type
      then Set.add term set
      else set

    (* Returns true if the term mentions at least a non-constant
       variable. *)
    let has_var term =
      Term.vars_of_term term
      |> Var.VarSet.exists
           ( fun var -> not (Var.is_const_state_var var) )

    let rec is_var_or_const term =
      match Term.destruct term with
      | Term.T.App (_,_) -> false
      | Term.T.Attr (kid,_) -> is_var_or_const kid
      | _ -> true

    let rec is_const term =
      match Term.destruct term with
      | Term.T.App (_,_) -> false
      | Term.T.Var _ -> false
      | Term.T.Attr (kid,_) -> is_const kid
      | _ -> true

    let rec is_var term =
      match Term.destruct term with
      | Term.T.App (_,_) -> false
      | Term.T.Const _ -> false
      | Term.T.Attr (kid,_) -> is_var kid
      | _ -> true

    (* Adds term to set if term is bool and is not [AND|NOT]. *)
    let bool_terms flat set = match flat with

      | Term.T.App (sym, kids) ->

         (* if ( (is_var kid1) && (is_const kid2) ) *)
         (*   || ( (is_var kid2) && (is_const kid1) ) then *)
         if List.for_all is_var_or_const kids then
           
           ( match Symbol.node_of_symbol sym with

             | `GT
             | `LT
             | `OR
             | `XOR
             | `DISTINCT
(*
             | `BVULT
*)
             | `IS_INT ->
                Set.add (flat_to_term flat) set

             | _ -> set )

         else set

      | _ -> set


    (* If term is an arithmetic atom "lhs op rhs" add "lhs >= rhs" and
       "lhs <= rhs". *)
    let arith_atoms flat set = match flat with

      | Term.T.App (sym, ((kid1 :: kid2 :: []) as kids)) ->

        (* The inequality has to be a 'small' one. Either var op
           const, const op var, orr var op var. *)
        if ( (is_var kid1) && (is_const kid2) )
           || ( (is_var kid2) && (is_const kid1) )
           (*|| ( (is_var kid1) && (is_var kid2) )*)
        then

          ( match Symbol.node_of_symbol sym with

            | `EQ ->

                (* Making sure it's an arith equality. *)
              ( match
                  kid1 |> Term.type_of_term |> Type.node_of_type
                with

                  | Type.Int
                  | Type.Real ->
                     (* It is, adding >= and <=. *)
                    set
                    (* |> Set.add (flat_to_term term) *)
                    |> Set.add (Term.mk_geq kids)
                    |> Set.add (Term.mk_leq kids)
                  | _ -> set )

            | `LEQ -> set
              |> Set.add (Term.mk_geq kids)
              |> Set.add (Term.mk_leq kids)

            | `GEQ -> set
              |> Set.add (Term.mk_geq kids)
              |> Set.add (Term.mk_leq kids)

            | `GT  -> set
              |> Set.add (flat_to_term flat)
              |> Set.add (Term.mk_geq kids)
              |> Set.add (Term.mk_leq kids)

            | `LT  -> set
              |> Set.add (flat_to_term flat)
              |> Set.add (Term.mk_geq kids)
              |> Set.add (Term.mk_leq kids)

            | _ -> set )

        else set
             
      | _ -> set


    (* List of rules over flat terms and their activation
       condition. *)
    let rule_list =
      [ bool_terms, false_of_unit ;
        arith_atoms, true_of_unit ]

    let apply flat set =
      
      rule_list
      (* Apply all rules... *)
      |> List.fold_left
           ( fun set' (rule, condition) ->
             (* If their condition is true. *)
             if condition ()
             then rule flat set'
             else set' )
           set

  end

  (* The numeral -1. *)
  let minus_one_num = Numeral.(~- one)

  (* Inserts or updates a sys/terms binding in an associative list
     sorted by topological order.  If sys is already in the list, then
     its terms are updated with the union of the old ones and the new
     ones. If it's not then it is inserted at the right place wrt
     topological order. *)
  let insert_sys_terms ((sys,terms) as pair) =

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
           ( (sys, Set.union terms terms') :: tail )
           
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


  (* If all vars in term have offset 0, adds term bumped at -1 to set. *)
  let add_offset_complement term set =
    match Term.var_offsets_of_term term with
    | Some(low), Some(up) when Numeral.(low = zero)
                               && Numeral.(up = zero) ->
       (* Term is one state @0, adding -1 version. *)
       Set.add
         (Term.bump_state minus_one_num term)
         set
         
    | Some(low), Some(up) when Numeral.(low = minus_one_num)
                               && Numeral.(up = minus_one_num) ->
       (* Term is one state @-1, adding 0 version. *)
       Set.add
         (Term.bump_state Numeral.one term)
         set
         
    | _ -> set


  (* If term is one state @0, adds term to set. If term is one state
     @-1, bumps the term to 0 and adds it to set. If term is two states,
     it is dismissed. *)
  let one_statify term set =
    match Term.var_offsets_of_term term with
    | Some(low), Some(up) when Numeral.(low = zero)
                               && Numeral.(up = zero) ->
       (* Term is one state @0, adding it. *)
       Set.add term set
         
    | Some(low), Some(up) when Numeral.(low = minus_one_num)
                               && Numeral.(up = minus_one_num) ->
       (* Term is one state @-1, adding 0 version. *)
       Set.add
         (Term.bump_state Numeral.one term)
         set

    | _ -> set

  (* Term set with true and false. *)
  let true_false_set = Set.of_list [ Term.t_true ; Term.t_false ]

  (* Adds the -1 (resp. 0) version of terms mentioning only variables
     of offset 0 (resp. -1). *)
  let two_state_complement set =
    Set.fold add_offset_complement set set

  (* Removes all two state candidate terms from a set of terms. *)
  let one_state_only set =
    Set.fold one_statify set true_false_set

  (* Builds a set of candidate terms from a term. Basically applies
       flat rules on all subterms. *)
  let set_of_term term set =
    let set_ref = ref set in
    (* Updates the set reference. *)
    let set_update set' = set_ref := set' in
    
    ( Term.eval_t
        ( fun flat_term _ ->
          (* Applying rules and updating set reference. *)
          set_update
            (FlatTermsRules.apply flat_term !set_ref) )
        
        term ) ;

    !set_ref

  (* Generates sets of candidate terms from a transition system, and
     its subsystems if the flags require it. *)
  let candidate_terms_of_trans two_state top_sys trans_sys =
    
    let rec get_last = function
      | head :: [] -> [head]
      | [] ->
        Event.log L_fatal "can't get last" ;
        assert false ;
      | _ :: t -> get_last t
    in

    (* Creates an associative list between systems and their
       implication graph. Even when running in top system only, we
       need to look at the subsystems and instantiate their candidate
       terms. *)
    let rec sys_graphs_map result = function

      | system :: tail ->
         (* Getting the scope of the system. *)
         let scope = TransSys.scope_of_trans_sys system in

         (* Do we know that system already?. *)
         if List.exists
              ( fun (sys,_) ->
                TransSys.scope_of_trans_sys sys = scope )
              result
              
         then
           (* We do, discarding it. *)
           sys_graphs_map result tail

         else (

           Debug.invgencand "Looking at [%s]."
                 (TransSys.scope_of_trans_sys system |> String.concat "/");
           
           (* We don't, getting init and trans. *)
           let init, trans =
             TransSys.init_of_bound system Numeral.zero,
             (* Getting trans at [-1,0]. *)
             TransSys.trans_of_bound system Numeral.zero
           in

           Debug.invgencand "Generating candidates.";

           let user_candidates =
             if two_state then Set.empty
             else Set.of_list (TransSys.get_unknown_candidates system) in
  
           let candidates' =

             if Flags.Certif.only_user_candidates () then user_candidates
             else
               user_candidates

               (* Synthesizing candidates. *)
               |> StateVarRules.apply (TransSys.state_vars system)

               (* Candidates from init. *)
               |> set_of_term init

               (* Candidates from trans. *)
               (* |> if Flags.Invgen.mine_trans ()
               then set_of_term trans else identity *)
           in

           let candidates =
             (* Adding two state complement if
                required. One-state-ification will take place at the
                very end to avoid missing candidate terms through
                instantiation. *)
             if two_state then two_state_complement candidates'
             else candidates'
           in

           let sorted_result =
             result
             |> ( if Flags.Invgen.lift_candidates () then
                    Set.fold
                      ( fun term map ->
                        TransSys.instantiate_term_all_levels
                          top_sys TransSys.trans_base scope term
                          |> (function | (top,others) -> top :: others)
                          |> List.fold_left
                              ( fun map (sys,terms) ->
                                insert_sys_terms
                                  (sys, Set.of_list terms) map )
                              map )
                      candidates
                  else identity )
             |> insert_sys_terms (system, candidates)
           in

           sys_graphs_map
             sorted_result
             (List.concat [ TransSys.get_subsystems system ; tail ])
         )

      | [] ->

        let final =
          (* Only getting to system if required. *)
          ( if Flags.Invgen.top_only ()
            then get_last result else result )
          |> (
            (* One state-ing everything if required. *)
            if two_state then
              identity
            else
              List.map
                (fun (sys,set) ->
                  (sys, one_state_only set))
          )
        in

        let count =
          final
          |> List.fold_left
              ( fun count (_, term_set) ->
                count + (Set.cardinal term_set) )
              (* Starting at two, true and false are not there yet. *)
              2
        in

        Debug.invgencand "%i candidates" count;

        (* Returning the candidate terms... *)
        final,
        (* ...and candidate term count for stats. *)
        count
    in

    sys_graphs_map [] [ trans_sys ]
      
end

let mine_term synthesis two_state sys terms set =
  set |> (
    if synthesis then
      (* Synthesizing candidates from sys. *)
      CandidateTermGen.StateVarRules.apply (TransSys.state_vars sys)
    else
      identity
  )
  |> (
    (* Mining init. *)
    TransSys.init_of_bound sys Numeral.zero
    |> CandidateTermGen.set_of_term
  )
  |> (
    if Flags.Invgen.mine_trans () then
      (* Mining trans. *)
      TransSys.trans_of_bound sys Numeral.zero
      |> CandidateTermGen.set_of_term
    else
      identity
  )
  |> (
    (* Mining terms. *)
    fun set ->
      List.fold_left (
        fun set' term -> CandidateTermGen.set_of_term term set'
      ) set terms
  )
  |> (
    if two_state then
      (* In two state get the complement. *)
      CandidateTermGen.two_state_complement
    else
      (* In one state, one-state-ify. *)
      CandidateTermGen.one_state_only
  )


    
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

