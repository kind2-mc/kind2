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

module Sys = TransSys
module Num = Numeral
module Set = Term.TermSet
module Map = Term.TermHashtbl
module N = LustreNode
module SVar = StateVar
module SVM = SVar.StateVarMap
module SVS = SVar.StateVarSet
module VSet = Var.VarSet
module Tree = Term.T


let sys_name sys =
  Sys.scope_of_trans_sys sys |> Scope.to_string

let fmt_lus_var fmt var =
  let fst, lst =
    if Num.( (Var.offset_of_state_var_instance var) = ~- one)
    then "(pre ", ")" else "", ""
  in
  Format.fprintf fmt "%s%s%s"
    fst
    (SVar.name_of_state_var (Var.state_var_of_state_var_instance var))
    lst

(* Continuation type for the term-to-lustre printer.
Used to specify what should happen after the next step. *)
type continue =
| T of Term.t (* Next step is to print a term. *)
| S of string (* Next step is to print a string. *)


(* [wrap_with_sep e s [t1 ; ... ; tn]] creates the list
[[Ss ; T t1 ; S s ; ... ; S s ; tn ; e]]. *)
let wrap_with_sep ending sep kids =
  let ending = [ S ending ] in
  let rec loop kids lst = match kids with
    | [] -> List.rev_append lst ending
    | [kid] -> (S sep) :: (T kid) :: ending |> List.rev_append lst
    | kid :: kids -> (T kid) :: (S sep) :: lst |> loop kids
  in
  loop kids []

let rec fmt_lus_down next fmt term = match Term.destruct term with
| Term.T.App (sym, kid :: kids) -> (
  let node = Symbol.node_of_symbol sym in
  match node with
  (* Unary. *)
  | `NOT ->
    Format.fprintf fmt "(not " ;
    assert (kids = []) ;
    fmt_lus_down ([ S ")" ] :: next) fmt kid
  (* Binary. *)
  | `EQ
  | `MOD
  | `LEQ
  | `LT
  | `GEQ
  | `GT
  | `IMPLIES -> (
    match kids with
    | [rhs] ->
      let op =
        match node with
        | `EQ -> " = "
        | `MOD -> " % "
        | `LEQ -> " <= "
        | `LT -> " < "
        | `GEQ -> " >= "
        | `GT -> " > "
        | `IMPLIES -> " => "
        | _ -> failwith "unreachable"
      in
      Format.fprintf fmt "(" ;
      fmt_lus_down (
        [ S op ; T rhs ; S ")" ] :: next
      ) fmt kid
    | [] -> failwith "implication of one kid"
    | _ ->
      Format.sprintf "implication of %d kids" ((List.length kids) + 1)
      |> failwith
  )
  (* Ternary. *)
  | `ITE -> (
    let i, t, e = match kids with
      | [ t ; e ] -> kid, t, e
      | _ -> failwith "illegal ite"
    in
    Format.fprintf fmt "( if " ;
    fmt_lus_down (
      [ S " then " ; T t ; S " else " ; T e ; S " )" ] :: next
    ) fmt kid
  )
  (* N-ary. *)
  | `MINUS when kids = [] ->
    Format.fprintf fmt "- " ;
    fmt_lus_down next fmt kid
  | `MINUS
  | `PLUS
  | `TIMES
  | `DIV
  | `OR
  | `XOR
  | `AND ->
    let op =
      match node with
      | `MINUS -> " - "
      | `PLUS -> " + "
      | `TIMES -> " * "
      | `DIV -> " / "
      | `OR -> " or "
      | `XOR -> " xor "
      | `AND -> " and "
      | _ -> failwith "unreachable"
    in
    Format.fprintf fmt "(" ;
    fmt_lus_down (
      (wrap_with_sep ")" op kids) :: next
    ) fmt kid
  | `DISTINCT
  | `INTDIV
  | `ABS
  | _ ->
    Format.asprintf "unsupported symbol %a" Symbol.pp_print_symbol sym
    |> failwith
  (*
  | `TO_REAL
  | `TO_INT
  | `IS_INT
  (* Illegal. *)
  | `NUMERAL of Numeral.t
  | `DECIMAL of Decimal.t
  | `TRUE
  | `FALSE -> Format.fprintf fmt "illegal" *)
)
| Term.T.App (sym, []) -> failwith "application with no kids"
| Term.T.Var var ->
  fmt_lus_var fmt var ;
  fmt_lus_up fmt next
| Term.T.Const sym ->
  ( match Symbol.node_of_symbol sym with
    | `NUMERAL n -> Format.fprintf fmt "%a" Numeral.pp_print_numeral n
    | `DECIMAL d ->
      Format.fprintf fmt "%a" Decimal.pp_print_decimal_as_lus_real d
    | `TRUE -> Format.fprintf fmt "true"
    | `FALSE -> Format.fprintf fmt "false"
    | _ -> Format.asprintf "Const %a" Symbol.pp_print_symbol sym |> failwith
  ) ;
  fmt_lus_up fmt next
| Term.T.Attr (kid,_) -> fmt_lus_down [] fmt kid

(* Goes up a continuation. Prints the strings it finds and calls
[fmt_lus_down] on terms. *)
and fmt_lus_up fmt = function
| (next :: nexts) :: tail -> (
  let tail = nexts :: tail in
  match next with
  | S str ->
    Format.fprintf fmt "%s" str ;
    fmt_lus_up fmt tail
  | T term ->
    fmt_lus_down tail fmt term
)
| [] :: tail -> fmt_lus_up fmt tail
| [] -> ()

let fmt_lus fmt term =
  let fst, lst =
    match Term.var_offsets_of_term term with
    | (Some lo, Some hi) when Num.(lo < zero) -> "true -> ( ", " )"
    | _ -> "",""
  in
  Format.fprintf fmt "%s%a%s" fst (fmt_lus_down []) term lst

let fmt_lus_mode fmt (req, enss) =
  let fst, lst =
    match Term.var_offsets_of_term req with
    | (Some lo, Some hi) when Num.(lo < zero) -> "true -> ( ", " )"
    | _ -> (
      if enss |> List.exists (
        fun t ->
          match Term.var_offsets_of_term t with
          | (Some lo, Some hi) when Num.(lo < zero) -> true
          | _ -> false
      ) then "true -> ( ", " )" else "", ""
    )
  in
  Format.fprintf fmt "require %s%a%s ;@ %a"
    fst (fmt_lus_down []) req lst
    (pp_print_list
      (fun fmt ens ->
        Format.fprintf fmt "ensure %s%a%s ;" fst (fmt_lus_down []) ens lst)
      "@ "
    ) enss


let fmt_contract fmt (node, assumes, guarantees, modes) =
  Format.fprintf fmt "%a@ let@   @[<v>"
    N.pp_print_node_signature node ;

  ( match assumes with
    | [] -> ()
    | _ ->
      Format.fprintf fmt "@ \
        --| Assumptions.@ \
        --| NB: assumptions usually come from assertions in the original@ \
        --|     lustre system. You should remove them and use the assumptions@ \
        --|     below instead. The behavior will be the same, except that now@ \
        --|     callers will need to prove they respect these assumptions.@ \
        --|     That is, unlike assertions, assumptions ARE SAFE.@ \
        %a@ \
      "
        (pp_print_list
          (fun fmt ass -> Format.fprintf fmt "assume %a ;" fmt_lus ass)
          "@ "
        ) assumes
  ) ;

  ( match guarantees with
    | [] -> ()
    | _ ->
      Format.fprintf fmt "@ --| Guarantees.@ %a@ "
        (pp_print_list
          (fun fmt ass -> Format.fprintf fmt "guarantee %a ;" fmt_lus ass)
          "@ "
        ) guarantees
  ) ;

  ( match modes with
    | [] -> ()
    | _ ->
      Format.fprintf fmt "@ --| Modes.@ " ;
      modes |> List.fold_left (
        fun cnt mode ->
          Format.fprintf fmt "\
            @[<v>\
              mode mode_%d (@   \
                @[<v>%a@]@ \
              ) ;@ \
            @]"
            cnt
            fmt_lus_mode mode ;
          cnt + 1
      ) 0
      |> ignore
  ) ;

  Format.fprintf fmt "@]@ tel"



let generate_contracts in_sys sys param get_node path =

  let max_depth = Flags.Contracts.contract_gen_depth () |> Num.of_int in

  Event.log_uncond "\
    @{<b>Generating contracts@}@   \
    @[<v>\
      for system %s@ \
      using two state (boolean) invariant generation to depth %a@ \
      to file \"%s\"\
    @]"
    (sys_name sys)
    Num.pp_print_numeral max_depth
    path ;

  Event.log_uncond "Running invariant generation..." ;

  let result =
    InvGen.BoolInvGen.main
      (Some max_depth) (Flags.modular () |> not) false true
      in_sys param sys
  in

  Event.log_uncond "Done." ;

  Event.log_uncond "Generating contracts." ;

  let out_channel = open_out path in
  let fmt = Format.formatter_of_out_channel out_channel in

  Format.fprintf fmt
    "(*@[<v>@ \
      The contracts below were generated automatically by the Kind 2@ \
      model-checker.@ \
      @ http://kind2-mc.github.io/kind2/\
    @]@ *)@.@.@.@." ;

  let rec loop = function
    | [] -> ()
    | (sys, non_trivial, trivial) :: tail ->
      let scope = Sys.scope_of_trans_sys sys in

      let node = get_node scope in
      let svar_source_map = node.N.state_var_source_map in
      let source_of svar = SVM.find svar svar_source_map in
      let filter_eligible terms =
        Set.elements terms |> List.filter (
          fun t ->
            Term.state_vars_of_term t
            |> SVS.for_all (
              fun svar ->
                try (
                  match source_of svar with
                  | N.Input | N.Output -> true
                  | _ -> false
                ) with Not_found -> false
            )
        )
      in
      let mentions_curr_output term =
        Term.vars_of_term term
        |> VSet.exists (
          fun var ->
            try (
              match
                Var.state_var_of_state_var_instance var |> source_of
              with
              | N.Output ->
                Var.offset_of_state_var_instance var == Numeral.zero
              | _ -> false
            ) with _ -> false
        )
      in

(*       let mentions_outputs_only =
        List.filter (
          fun t ->
            Term.state_vars_of_term t
            |> SVS.for_all (
              fun svar ->
                try (
                  match source_of svar with
                  N.Output -> true
                  | _ -> false
                ) with Not_found -> false
            )
        )
      in *)

      let is_pure_pre term =
        match Term.var_offsets_of_term term with
        | (Some _, Some hi) -> Num.(hi < zero)
        | _ -> false
      in

      let non_trivial, trivial =
        filter_eligible non_trivial,
        filter_eligible trivial
      in

      Event.log_uncond
        "  @[<v>\
          Working on system %s:@   \
          @[<v>\
                trivial: @[<v>%a@]@ \
            non_trivial: @[<v>%a@]\
          @]
        @]"
        (sys_name sys)
        (pp_print_list Term.pp_print_term "@ ") trivial
        (pp_print_list Term.pp_print_term "@ ") non_trivial ;

      let mk_not term =
        match Term.destruct term with
        | Tree.App (sym, [sub_term])
        when Symbol.node_of_symbol sym = `NOT -> sub_term

        | Tree.App (sym, sub_terms)
        when Symbol.node_of_symbol sym = `GEQ -> Term.mk_lt sub_terms
        | Tree.App (sym, sub_terms)
        when Symbol.node_of_symbol sym = `GT -> Term.mk_leq sub_terms
        | Tree.App (sym, sub_terms)
        when Symbol.node_of_symbol sym = `LT -> Term.mk_geq sub_terms
        | Tree.App (sym, sub_terms)
        when Symbol.node_of_symbol sym = `LEQ -> Term.mk_gt sub_terms

        | _ -> Term.mk_not term
      in

      let split terms =
        let modes = Map.create 107 in
        let insert_mode req ens =
          (try Map.find modes req with Not_found -> Set.empty)
          |> Set.add ens
          |> Map.replace modes req
        in
        let rec loop assumptions guarantees = function
          | term :: tail -> (
            let reboot term =
              term :: tail
              |> List.rev_append (Set.elements assumptions)
              |> List.rev_append (Set.elements guarantees)
              |> loop Set.empty Set.empty
            in

            match Term.destruct term with

            | Tree.App (sym, [lft ; rgt])
            when Symbol.node_of_symbol sym = `IMPLIES -> (
              let assumptions, guarantees =
                match mentions_curr_output lft, mentions_curr_output rgt with
                | (true, true) ->
                  (* Not a mode, current outputs appear left and right. *)
                  assumptions, Set.add term guarantees
                | (false, true) ->
                  (* Mode: [lft] does not mention the outputs and is the
                  require. *)
                  insert_mode lft rgt ;
                  assumptions, guarantees
                | (true, false) ->
                  (* Mode: [rgt] does not mention the outputs and is the
                  require. *)
                  insert_mode (mk_not rgt) (mk_not lft) ;
                  assumptions, guarantees
                | (false, false) ->
                  (* No output mentioned at all, it's an assumption. *)
                  Set.add term assumptions, guarantees
              in
              loop assumptions guarantees tail
            )

            | Tree.App (sym, [lft ; rgt])
            when Symbol.node_of_symbol sym = `EQ && lft == Term.t_true ->
              reboot rgt

            | Tree.App (sym, [lft ; rgt])
            when Symbol.node_of_symbol sym = `EQ && rgt == Term.t_true ->
              reboot lft

            | Tree.App (sym, [lft ; rgt])
            when Symbol.node_of_symbol sym = `EQ && rgt == Term.t_false ->
              reboot (mk_not lft)

            | Tree.App (sym, [lft ; rgt])
            when Symbol.node_of_symbol sym = `EQ && lft == Term.t_false ->
              reboot (mk_not rgt)

            | Tree.App (sym, [lft ; rgt])
            when Symbol.node_of_symbol sym = `EQ && (
              Set.mem lft guarantees || List.mem lft tail
            ) ->
              reboot rgt

            | Tree.App (sym, [lft ; rgt])
            when Symbol.node_of_symbol sym = `EQ && (
              Set.mem rgt guarantees || List.mem rgt tail
            ) ->
              reboot lft

            | _ ->
              let assumptions, guarantees =
                if mentions_curr_output term then
                  (* Guarantee. *)
                  assumptions, Set.add term guarantees
                else 
                  (* if mentions_outputs_only term *)
                  (* Assumption. *)
                  Set.add term assumptions, guarantees
              in
              loop assumptions guarantees tail
          )
          | [] -> Set.elements assumptions, Set.elements guarantees
        in
        let assumptions, guarantees = loop Set.empty Set.empty terms in
        let should_keep term =
          (* If all vars at [-1] and version bumped at [0] is known,
          discard. *)
          not (
            is_pure_pre term && (
              let at_0 = Term.bump_state Numeral.one term in
              List.mem at_0 assumptions ||
              List.mem at_0 guarantees
            )
          )
        in

        assumptions |> List.filter should_keep,
        guarantees |> List.filter should_keep,
        Map.fold (
          fun req enss acc -> (req, Set.elements enss) :: acc
        ) modes []
      in

      let assumptions, guarantees, modes =
        ( if Flags.Contracts.contract_gen_fine_grain () then
            List.rev_append non_trivial trivial
          else non_trivial )
        |> split
      in

      Format.fprintf fmt
        "@[<v>\
          (* \
          @[<v>\
          Contract for node [%s].@ @ \
          @ \
          Do make sure you include this file using an `include` statement.\
          @]@ *)@ \
        contract %s_spec %a@]@.@."
        (sys_name sys)
        (sys_name sys)
        fmt_contract (node, assumptions, guarantees, modes) ;

      loop tail
  in

  loop result ;
  

  close_out out_channel ;

  Event.log_uncond "Done generating contracts."


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)