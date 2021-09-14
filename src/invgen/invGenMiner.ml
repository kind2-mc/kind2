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

[@@@ocaml.warning "-27"]

open Lib

module Num = Numeral
module Dec = Decimal
module SVar = StateVar
module Set = Term.TermSet
module Sys = TransSys

type svar = SVar.t
(* type svs = SVS.t *)
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

  (** Complimentary set of candidates. *)
  val comp_set : sys -> set

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
  (* Otherwise no offset (constant), add to set. *)
  | _ -> Set.add term set

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
  (try
    Term.eval_t ~fail_on_quantifiers:false (
      fun flat_term _ -> work flat_term !set_ref |> memorize
    ) term ;
   with Invalid_argument _ ->
     KEvent.log L_warn
       "Cannot mine invariants in quantified terms"
  );
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

let type_of_svar svar = SVar.type_of_state_var svar |> Type.node_of_type

(*
(* The name of a transition system. *)
let name_of_sys sys =
  TransSys.scope_of_trans_sys sys |> String.concat "/"
*)


(* |===| Functor stuff. *)


(** Module generating candidate terms for invariant generation. *)
module type CandGen = sig
  (** Generates sets of candidate terms from a transition system, and its
  subsystems if the first flag is false. Second flag is for two-state. *)
  val mine : bool -> bool -> sys -> (sys * set) list
end

(* TODO: Make the graph-based approach for invariant generation work when
   terms include divisions. Currently, a Division_by_zero exception may
   raise during graph stabilization if a model assigns zero to a divisor.
*)
let filter_terms_with_unsupported_symbols candidates =
  let rec includes_unsupported_symbol term =
    match Term.destruct term with
    (* | Term.T.Attr (t, _) -> includes_unsupported_symbol t *)
    | Term.T.App (s, l) -> (
      match Symbol.node_of_symbol s with
      | `UF _
      | `DIV
      | `INTDIV -> true
      | _ -> List.exists includes_unsupported_symbol l
    )
    | _ -> false
  in
  Set.filter (fun t -> includes_unsupported_symbol t |> not) candidates

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
            Sys.init_of_bound None sys zero, Sys.trans_of_bound None sys zero
          in
          (* Format.printf
            "candidates (%d):@   @[<v>%a@]@.@."
            (Set.cardinal candidates)
            (pp_print_list
              Term.pp_print_term
              "@ "
            ) (Set.elements candidates) ; *)
          let candidates =
            let candidates = Rules.comp_set sys in
            
            if Flags.Certif.only_user_candidates () then candidates else (
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
              |> Set.union candidates
            )
          in
          (* Format.printf
            "candidates (%d):@   @[<v>%a@]@.@."
            (Set.cardinal candidates)
            (pp_print_list
              Term.pp_print_term
              "@ "
            ) (Set.elements candidates) ; *)
          let candidates = filter_terms_with_unsupported_symbols candidates in
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
                      top_sys TransSys.trans_base scope term two_state
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
        (if top_only then get_last result else result)
        |> (
          if two_state then identity else List.map (
            fun (sys, set) ->
              let res = one_state_ify_set set in
              (* Format.printf
                "candidates %s (%d, %b):@   @[<v>%a@]@.@."
                (name_of_sys sys)
                (Set.cardinal res)
                two_state
                (pp_print_list
                  Term.pp_print_term
                  "@ "
                ) (Set.elements res) ; *)
              sys, res
          )
        )
    in

    mk_sys_map [] [ top_sys ]

end



(* |===| Helpers for term inspection. *)

(* Returns true if the term is a variable or a constant. *)
let is_var_or_const term = match Term.destruct term with
(* | Term.T.Attr (kid, _) -> is_var_or_const kid *)
| Term.T.Var var -> (
  Var.is_state_var_instance var
) && (
  Var.state_var_of_state_var_instance var
  |> SVar.for_inv_gen
)
| Term.T.Const _ -> true
| _ -> false


(* Returns true if the term is a variable. *)
let is_var term = match Term.destruct term with
(* | Term.T.Attr (kid, _) -> is_var kid *)
| Term.T.Var var -> (
  Var.is_state_var_instance var
) && (
  Var.state_var_of_state_var_instance var
  |> SVar.for_inv_gen
)
| _ -> false


(* Returns true if the term is a constant. *)
let is_const term = match Term.destruct term with
(* | Term.T.Attr (kid, _) -> is_const kid *)
| Term.T.Const _ -> true
| _ -> false


let var_of svar = Var.mk_state_var_instance svar zero |> Term.mk_var


(* |===| Bool mining. *)


(* Rules for bool candidate term generation from state variables. *)
module BoolRules = struct

  (* Adds svars of type bool to the input set. *)
  let bool_rule svar set =
    let var = var_of svar in
    Set.add var set |> Set.add (Term.mk_not var)

  (* add equalities with all constructors *)
  let enum_rule lo hi svar =
    let var = var_of svar in
    let rec loop lo set =
      if Num.(lo > hi) then set else loop (Num.succ lo) (
        Set.add (Term.mk_eq [var ; Term.mk_num lo]) set
      )
    in
    loop lo

  (* If [svar] is an [IntRange(lo, hi)], adds to the input set the constraints
  [svar = n], for [n] in [[lo, hi]].

  NB: original version added [lo <= svar] and [svar <= hi] too. *)
  let range_rule lo hi svar = enum_rule lo hi svar
  
  (* Adds [svar >= 0] and [svar == 0] for an int [svar] to the input set. *)
  let int_rule svar set =
    let var = var_of svar in
    Set.add (Term.mk_geq [var ; Term.mk_num zero]) set
    |>
      if Flags.Invgen.all_out () then
        Set.add (Term.mk_eq [var ; Term.mk_num zero])
      else identity

  (* Adds [svar >= 0] for a real [svar] to the input set. *)
  let real_rule svar set =
    let var = var_of svar in
    Set.add (Term.mk_geq [var ; Term.mk_dec Dec.zero]) set
    |>
      if Flags.Invgen.all_out () then
        Set.add (Term.mk_eq [var ; Term.mk_dec Dec.zero])
      else identity



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
      set
      |> Set.add (Term.mk_geq kids)
      |> Set.add (Term.mk_leq kids)
      (* |> Set.add (Term.mk_eq  kids) *)
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

  let comp_set sys = TransSys.get_unknown_candidates sys |> Set.of_list

  type svar_info = unit

  let svar_rules two_state svars set = (
    svars |> List.fold_left (
      fun set svar ->
        if SVar.for_inv_gen svar |> not then set else (
          match type_of_svar svar with
          | Type.Bool -> bool_rule svar set
          | Type.IntRange (lo, hi, Type.Range) -> range_rule lo hi svar set
          | Type.IntRange (lo, hi, Type.Enum) -> enum_rule lo hi svar set
          | Type.Int -> int_rule svar set
          | Type.Real -> real_rule svar set
          | _ -> set
        )
    ) set,
    ()
  )

  type flat_info = unit

  let post_svars two_state (set, _) = set, ()

  let flat_rules two_state flat (set, _) =
    match to_term flat |> type_of with
    | Type.Bool -> (
      arith_op_synth flat set
      |>
        if Flags.Invgen.all_out () then
          bool_term_rule flat
        else identity
    ), ()
    | _ -> set, ()

  let post_rules two_state _  _ set =
    (
      if Flags.Invgen.all_out () then
        Set.fold (
          fun term set -> Set.add (Term.negate_simplify term) set
        ) set set
      else set
    )
    |> Set.add Term.t_true

end


(** Bool candidate term miner. *)
module Bool = MakeCandGen (BoolRules)




let empty_model = Model.of_list []

let eval term =
  Eval.eval_term [] empty_model term
  |> Eval.term_of_value

let generic_octagons mk_plus mk_minus oct3 f =
  let rec octagons_3 terms tail' set = match tail' with
    | term :: tail ->
    (*   Format.printf "  oct 3 %a (%d)@."
        fmt_term term
        (List.length tail) ; *)
      List.map (fun term' -> [ term' ; term ]) terms
      |> List.fold_left (
        fun set terms ->
          Set.add (mk_plus terms |> f) set
          |> Set.add (mk_minus terms |> f)
      ) set
      |> octagons_3 terms tail
    | [] -> set
  in
  let rec octagons_2_3 term terms set = match terms with
    | term' :: tail ->
     (*  Format.printf "  oct 2 %a (%d)@."
        fmt_term term'
        (List.length tail) ; *)
      let oterms =
        let pair = [ term ; term' ] in
        [
          mk_plus pair |> f ;
          mk_minus pair |> f ;
          (* pair |> List.rev |> mk_minus |> f *)
        ]
      in
      oterms
      |> List.fold_left (
        fun set term -> Set.add term set
      ) set
      |> (if oct3 then octagons_3 oterms tail else identity)
      |> octagons_2_3 term tail
    | [] -> set
  in
  let rec loop terms set = match terms with
    | term :: tail ->
      (* Format.printf "loop %a (%d)@."
        fmt_term term
        (List.length tail) ; *)
      (* Adding current term. *)
      Set.add term set
      (* Forming octagons. *)
      |> octagons_2_3 term tail
      (* Looping. *)
      |> loop tail
    | [] -> set
  in
  loop

let octagons = generic_octagons Term.mk_plus Term.mk_minus

let octagons_bv = generic_octagons Term.mk_bvadd Term.mk_bvsub

(** Integer rules. *)
module IntRules = struct
  let comp_set _ = Set.empty

  (* We'll extract the state var to create octagons. *)
  type svar_info = unit

  let svar_rules two_state svars set =
    (* Format.printf "svars: @[<v>%a@]@.@."
      (pp_print_list
        (fun fmt svar ->
          Format.fprintf fmt "%a (%a)"
            fmt_svar svar
            Type.pp_print_type_node (type_of_svar svar)
        ) "@ "
      ) svars ; *)
    let svars, set =
      svars |> List.fold_left (
        fun (svars, set) svar ->
        match type_of_svar svar with
        | Type.Int ->
          if SVar.for_inv_gen svar then
            (var_of svar) :: svars, set
          else svars, set
        | Type.IntRange (lo, hi, Type.Range) ->
          svars,
          Set.add (Term.mk_num lo) set |> Set.add (Term.mk_num hi)
        | _ -> svars, set
      ) ([], set)
    in
    (* Format.printf "loop: @[<v>%a@]@.@."
      (pp_print_list
        (fun fmt term ->
          Format.fprintf fmt "%a (%a)"
            fmt_term term
            Type.pp_print_type_node (type_of term)
        ) "@ "
      ) svars ; *)
    let set =
      octagons (Flags.Invgen.all_out ()) identity svars set
    in
    (* Format.printf "set: @[<v>%a@]@.@."
      (pp_print_list fmt_term "@ ")
      (Set.elements set) ; *)
    set, ()

  (* We're gonna use the flat info to store the constants found in the flat
  terms. *)
  type flat_info = set

  let post_svars _ (set, _) = (set, Set.empty)

  let flat_rules two_state flat (set, constants) =
    let term = to_term flat in
    match type_of term with
    | Type.Int
    | Type.IntRange _ -> (
      match flat with
      | Term.T.App (_, kids) ->
        if (
          Flags.Invgen.all_out ()
        ) || (
          kids |> List.for_all is_var_or_const
        ) then Set.add term set, constants else set, constants
      | Term.T.Const sym -> (
        match Symbol.node_of_symbol sym with
        | `NUMERAL _ -> Set.add term set, Set.add term constants
        | _ -> failwith "Constant of type int is not a numeral."
      )
      (* | Term.T.Attr (term, _) ->
        flat_rules two_state (Term.destruct term) (set, constants)*)
      | Term.T.Var _ ->
        Set.add term set, constants
    )
    | _ -> set, constants

  let post_rules _ _ constants set =
    let zero, one = Term.mk_num zero, Term.mk_num one in
    let set =
      Set.add zero set
      |> Set.add one
      |> octagons true eval (
        Set.add one constants |> Set.elements
      )
    in
    let set =
      Set.fold (
        fun term set -> Set.add (Term.mk_minus_simplify term) set
      ) set set
    in
    (* Format.printf "set: @[<v>%a@]@.@."
      (pp_print_list fmt_term "@ ")
      (Set.elements set) ; *)
    set


end


(** Int candidate term miner. *)
module Int = MakeCandGen (IntRules)


module type MachineIntegerSig = sig
  val length: int
  val is_type: Type.t -> bool
  val is_symbol: Symbol.t -> bool
end

(** Machine integer rules. *)
module MachineIntegerRules(M: MachineIntegerSig) = struct
  let comp_set _ = Set.empty

  (* We'll extract the state var to create octagons. *)
  type svar_info = unit

  let svar_rules two_state svars set =
    (* Format.printf "svars: @[<v>%a@]@.@."
      (pp_print_list
        (fun fmt svar ->
          Format.fprintf fmt "%a (%a)"
            fmt_svar svar
            Type.pp_print_type_node (type_of_svar svar)
        ) "@ "
      ) svars ; *)
    let svars, set =
      svars |> List.fold_left (
        fun (svars, set) svar ->
        if M.is_type (SVar.type_of_state_var svar) then
          if SVar.for_inv_gen svar then
            (var_of svar) :: svars, set
          else svars, set
        else svars, set
      ) ([], set)
    in
    (* Format.printf "loop: @[<v>%a@]@.@."
      (pp_print_list
        (fun fmt term ->
          Format.fprintf fmt "%a (%a)"
            fmt_term term
            Type.pp_print_type_node (type_of term)
        ) "@ "
      ) svars ; *)
    let set =
      octagons_bv (Flags.Invgen.all_out ()) identity svars set
    in
    (* Format.printf "set: @[<v>%a@]@.@."
      (pp_print_list fmt_term "@ ")
      (Set.elements set) ; *)
    set, ()

  (* We're gonna use the flat info to store the constants found in the flat
  terms. *)
  type flat_info = set

  let post_svars _ (set, _) = (set, Set.empty)

  let flat_rules two_state flat (set, constants) =
    let term = to_term flat in
    if M.is_type (Term.type_of_term term) then
      match flat with
      | Term.T.App (_, kids) ->
        if (
          Flags.Invgen.all_out ()
        ) || (
          kids |> List.for_all is_var_or_const
        ) then Set.add term set, constants else set, constants
      | Term.T.Const sym -> (
        if M.is_symbol sym then
          Set.add term set, Set.add term constants
        else
          failwith "Type of constant and term does not match"
      )
      (* | Term.T.Attr (term, _) ->
        flat_rules two_state (Term.destruct term) (set, constants)*)
      | Term.T.Var _ ->
        Set.add term set, constants
    else set, constants

  let post_rules _ _ constants set =
    let zero = Term.mk_bv (Bitvector.zero M.length) in
    let one = Term.mk_bv (Bitvector.one M.length) in
    let set =
      Set.add zero set
      |> Set.add one
      |> octagons_bv true eval(
        Set.add one constants |> Set.elements
      )
    in
    let set =
      Set.fold (
        fun term set -> Set.add (Term.mk_bvneg_simplify term) set
      ) set set
    in
    (* Format.printf "set: @[<v>%a@]@.@."
      (pp_print_list fmt_term "@ ")
      (Set.elements set) ; *)
    set


end

module Int8M : MachineIntegerSig = struct
  let length = 8
  let is_type = Type.is_int8
  let is_symbol = Symbol.is_bv8
end

module Int16M : MachineIntegerSig = struct
  let length = 16
  let is_type = Type.is_int16
  let is_symbol = Symbol.is_bv16
end

module Int32M : MachineIntegerSig = struct
  let length = 32
  let is_type = Type.is_int32
  let is_symbol = Symbol.is_bv32
end

module Int64M : MachineIntegerSig = struct
  let length = 64
  let is_type = Type.is_int64
  let is_symbol = Symbol.is_bv64
end

module UInt8M : MachineIntegerSig = struct
  let length = 8
  let is_type = Type.is_uint8
  let is_symbol = Symbol.is_ubv8
end

module UInt16M : MachineIntegerSig = struct
  let length = 16
  let is_type = Type.is_uint16
  let is_symbol = Symbol.is_ubv16
end

module UInt32M : MachineIntegerSig = struct
  let length = 32
  let is_type = Type.is_uint32
  let is_symbol = Symbol.is_ubv32
end

module UInt64M : MachineIntegerSig = struct
  let length = 64
  let is_type = Type.is_uint64
  let is_symbol = Symbol.is_ubv64
end

(** Int8 candidate term miner. *)
module Int8 = MakeCandGen (MachineIntegerRules(Int8M))

(** Int16 candidate term miner. *)
module Int16 = MakeCandGen (MachineIntegerRules(Int16M))

(** Int32 candidate term miner. *)
module Int32 = MakeCandGen (MachineIntegerRules(Int32M))

(** Int64 candidate term miner. *)
module Int64 = MakeCandGen (MachineIntegerRules(Int64M))

(** UInt8 candidate term miner. *)
module UInt8 = MakeCandGen (MachineIntegerRules(UInt8M))

(** UInt16 candidate term miner. *)
module UInt16 = MakeCandGen (MachineIntegerRules(UInt16M))

(** UInt32 candidate term miner. *)
module UInt32 = MakeCandGen (MachineIntegerRules(UInt32M))

(** UInt64 candidate term miner. *)
module UInt64 = MakeCandGen (MachineIntegerRules(UInt64M))

(** Real rules. *)
module RealRules = struct
  let comp_set _ = Set.empty

  (* We'll extract the state var to create octagons. *)
  type svar_info = unit

  let svar_rules two_state svars set =
    (* Format.printf "svars: @[<v>%a@]@.@."
      (pp_print_list
        (fun fmt svar ->
          Format.fprintf fmt "%a (%a)"
            fmt_svar svar
            Type.pp_print_type_node (type_of_svar svar)
        ) "@ "
      ) svars ; *)
    let svars, set =
      svars |> List.fold_left (
        fun (svars, set) svar ->
        match type_of_svar svar with
        | Type.Real ->
          if SVar.for_inv_gen svar then
            (var_of svar) :: svars, set
          else svars, set
        | _ -> svars, set
      ) ([], set)
    in
    (* Format.printf "loop: @[<v>%a@]@.@."
      (pp_print_list
        (fun fmt term ->
          Format.fprintf fmt "%a (%a)"
            fmt_term term
            Type.pp_print_type_node (type_of term)
        ) "@ "
      ) svars ; *)
    let set =
      octagons (Flags.Invgen.all_out ()) identity svars set
    in
    (* Format.printf "set: @[<v>%a@]@.@."
      (pp_print_list fmt_term "@ ")
      (Set.elements set) ; *)
    set, ()

  (* We're gonna use the flat info to store the constants found in the flat
  terms. *)
  type flat_info = set

  let post_svars _ (set, _) = (set, Set.empty)

  let flat_rules two_state flat (set, constants) =
    let term = to_term flat in
    match type_of term with
    | Type.Real -> (
      match flat with
      | Term.T.App (_, kids) ->
        if (
          Flags.Invgen.all_out ()
        ) || (
          kids |> List.for_all is_var_or_const
        ) then Set.add term set, constants else set, constants
      | Term.T.Const sym -> (
        match Symbol.node_of_symbol sym with
        | `DECIMAL _ -> Set.add term set, Set.add term constants
        | _ -> failwith "Constant of type real is not a decimal."
      )
      (*| Term.T.Attr (term, _) ->
        flat_rules two_state (Term.destruct term) (set, constants)*)
      | Term.T.Var _ ->
        Set.add term set, constants
    )
    | _ -> set, constants

  let post_rules _ _ constants set =
    let zero, one = Term.mk_dec Decimal.zero, Term.mk_dec Decimal.one in
    let set =
      Set.add zero set
      |> Set.add one
      |> octagons true eval (
        Set.add one constants |> Set.elements
      )
    in
    let set =
      Set.fold (
        fun term set -> Set.add (Term.mk_minus_simplify term) set
      ) set set
    in
    (* Format.printf "set: @[<v>%a@]@.@."
      (pp_print_list fmt_term "@ ")
      (Set.elements set) ; *)
    set


end


(** Real candidate term miner. *)
module Real = MakeCandGen (RealRules)














(*
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

