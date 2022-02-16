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

module Set = Term.TermSet

module Sys = TransSys
module Num = Numeral


(** Exception thrown when a domain is asked to build a trivial implication. *)
exception TrivialRelation


(** Signature of the modules describing an order relation over some domain. *)
module type Domain = sig
  (** Short string description of the domain, used in the logging prefix. *)
  val name : string

  (** Type of the values of the candidate terms. *)
  type t

  (** Value formatter. *)
  val fmt : Format.formatter -> t -> unit

  (** Equality over the domain. *)
  val eq : t -> t -> bool

  (** Ordering relation. *)
  val cmp : t -> t -> bool

  (** Creates the term corresponding to the equality of two terms. *)
  val mk_eq : Term.t -> Term.t -> Term.t
  (** Creates the term corresponding to the ordering of two terms. *)

  val mk_cmp : Term.t -> Term.t -> Term.t

  (** Evaluates a term. *)
  val eval : Sys.t -> Model.t -> Term.t -> t

  (** Mines a transition system for candidate terms. *)
  val mine : bool -> bool -> Analysis.param -> Sys.t -> (
    Sys.t * Set.t
  ) list

  (** Representative of the first equivalence class.
  [False] for bool, a random term in the set for arith. *)
  val first_rep_of : Set.t -> Term.t * Set.t

  (** Returns true iff the input term is bottom. *)
  val is_bot: Term.t -> bool

  (** Returns true iff the input term is top. *)
  val is_top: Term.t -> bool

  (** Returns true iff the one state invgen technique for this domain is
  running. *)
  val is_os_running: unit -> bool
end


(** Boolean domain with implication. *)
module Bool: Domain = struct
  (* Evaluates a term to a boolean. *)
  let eval_bool sys model term =
    Eval.eval_term (Sys.uf_defs sys) model term
    |> Eval.bool_of_value

  let name = "Bool"
  type t = bool
  let fmt = Format.pp_print_bool
  let eq lhs rhs = lhs = rhs
  let cmp lhs rhs = rhs || not lhs
  let mk_eq rep term =
    if rep == Term.t_true then term else (
      if rep == Term.t_false then Term.negate term else
      Term.mk_eq [ rep ; term ]
    )
  let mk_cmp lhs rhs =
    if lhs != Term.t_false && rhs != Term.t_true then
      Term.mk_implies [ lhs ; rhs ]
    else raise TrivialRelation
  let eval = eval_bool
  let first_rep_of terms = Term.t_false, terms
  let mine top_only two_state param top_sys =
    InvGenMiner.Bool.mine top_only two_state top_sys
    |> List.filter (
      fun (sys, _) ->
        (sys == top_sys) || (
          (not top_only) && (
            TransSys.scope_of_trans_sys sys
            |> Analysis.param_scope_is_abstract param
            |> not
          )
        )
    )
  let is_bot term = term = Term.t_false
  let is_top term = term = Term.t_true
  let is_os_running () = (
    Flags.enabled () |> List.mem `INVGENOS
  )
end


(** Integer domain with less than or equal to. *)
module Int: Domain = struct
  (* Evaluates a term to a numeral. *)
  let eval_int sys model term =
    Eval.eval_term (Sys.uf_defs sys) model term
    |> Eval.num_of_value

  let name = "Int"
  type t = Num.t
  let fmt = Num.pp_print_numeral
  let eq = Num.equal
  let cmp = Num.leq
  let mk_eq rep term = Term.mk_eq [ rep ; term ]
  let mk_cmp lhs rhs = Term.mk_leq [ lhs ; rhs ]
  let eval = eval_int
  let mine top_only two_state param top_sys =
    InvGenMiner.Int.mine top_only two_state top_sys
    |> List.filter (
      fun (sys, _) ->
        (sys == top_sys) || (
          (not top_only) && (
            TransSys.scope_of_trans_sys sys
            |> Analysis.param_scope_is_abstract param
            |> not
          )
        )
    )
  let first_rep_of terms =
    let rep = Set.choose terms in
    rep, Set.remove rep terms
  let is_bot _ = false
  let is_top _ = false
  let is_os_running () = (
    Flags.enabled () |> List.mem `INVGENINTOS
  )
end

module type MachineIntegerParam = sig
  val name: string
  val fmt: Format.formatter -> Bitvector.t -> unit
  val cmp: Bitvector.t -> Bitvector.t -> bool
  val mk_cmp: Term.t list -> Term.t
  val eval: Sys.t -> Model.t -> Term.t -> Bitvector.t
  val mine: bool -> bool -> Sys.t -> (Sys.t * Set.t) list
end

module type MachineIntegerMiner = sig
  val name: string
  val mine: bool -> bool -> Sys.t -> (Sys.t * Set.t) list
end

module MakeSigned(M: MachineIntegerMiner) : MachineIntegerParam = struct
  let name = M.name
  let fmt = Bitvector.pp_print_signed_machine_integer
  let cmp = Bitvector.lte
  let mk_cmp = Term.mk_bvsle
  let eval sys model term =
    Eval.eval_term (Sys.uf_defs sys) model term
    |> Eval.ubv_of_value
  let mine = M.mine
end

module MakeUnsigned(M: MachineIntegerMiner) : MachineIntegerParam = struct
  let name = M.name
  let fmt = Bitvector.pp_print_unsigned_machine_integer
  let cmp = Bitvector.ulte
  let mk_cmp = Term.mk_bvule
  let eval sys model term =
    Eval.eval_term (Sys.uf_defs sys) model term
    |> Eval.ubv_of_value
  let mine = M.mine
end

(** Machine integer domain with less than or equal to. *)
module MakeMachineInteger(M: MachineIntegerParam): Domain = struct
  (* Evaluates a term to a bitvector. *)
  let name = M.name
  type t = Bitvector.t
  let fmt = M.fmt
  let eq = Bitvector.equal
  let cmp = M.cmp
  let mk_eq rep term = Term.mk_eq [ rep ; term ]
  let mk_cmp lhs rhs = M.mk_cmp [ lhs ; rhs ]
  let eval = M.eval
  let mine top_only two_state param top_sys =
    M.mine top_only two_state top_sys
    |> List.filter (
      fun (sys, _) ->
        (sys == top_sys) || (
          (not top_only) && (
            TransSys.scope_of_trans_sys sys
            |> Analysis.param_scope_is_abstract param
            |> not
          )
        )
    )
  let first_rep_of terms =
    let rep = Set.choose terms in
    rep, Set.remove rep terms
  let is_bot _ = false
  let is_top _ = false
  let is_os_running () = (
    Flags.enabled () |> List.mem `INVGENMACHOS
  )
end

module Int8Miner: MachineIntegerMiner = struct
  let name = "Int8"
  let mine = InvGenMiner.Int8.mine
end

module Int16Miner: MachineIntegerMiner = struct
  let name = "Int16"
  let mine = InvGenMiner.Int16.mine
end

module Int32Miner: MachineIntegerMiner = struct
  let name = "Int32"
  let mine = InvGenMiner.Int32.mine
end

module Int64Miner: MachineIntegerMiner = struct
  let name = "Int64"
  let mine = InvGenMiner.Int64.mine
end

module Int8: Domain = MakeMachineInteger(MakeSigned(Int8Miner))
module Int16: Domain = MakeMachineInteger(MakeSigned(Int16Miner))
module Int32: Domain = MakeMachineInteger(MakeSigned(Int32Miner))
module Int64: Domain = MakeMachineInteger(MakeSigned(Int64Miner))

module UInt8Miner: MachineIntegerMiner = struct
  let name = "UInt8"
  let mine = InvGenMiner.UInt8.mine
end

module UInt16Miner: MachineIntegerMiner = struct
  let name = "UInt16"
  let mine = InvGenMiner.UInt16.mine
end

module UInt32Miner: MachineIntegerMiner = struct
  let name = "UInt32"
  let mine = InvGenMiner.UInt32.mine
end

module UInt64Miner: MachineIntegerMiner = struct
  let name = "UInt64"
  let mine = InvGenMiner.UInt64.mine
end

module UInt8: Domain = MakeMachineInteger(MakeUnsigned(UInt8Miner))
module UInt16: Domain = MakeMachineInteger(MakeUnsigned(UInt16Miner))
module UInt32: Domain = MakeMachineInteger(MakeUnsigned(UInt32Miner))
module UInt64: Domain = MakeMachineInteger(MakeUnsigned(UInt64Miner))

(** Real domain with less than or equal to. *)
module Real: Domain = struct
  (* Evaluates a term to a decimal. *)
  let eval_real sys model term =
    Eval.eval_term (Sys.uf_defs sys) model term
    |> Eval.dec_of_value

  let name = "Real"
  type t = Decimal.t
  let fmt = Decimal.pp_print_decimal
  let eq = Decimal.equal
  let cmp = Decimal.leq
  let mk_eq rep term = Term.mk_eq [ rep ; term ]
  let mk_cmp lhs rhs = Term.mk_leq [ lhs ; rhs ]
  let eval = eval_real
  let mine top_only two_state param top_sys =
    InvGenMiner.Real.mine top_only two_state top_sys
    |> List.filter (
      fun (sys, _) ->
        (sys == top_sys) || (
          (not top_only) && (
            TransSys.scope_of_trans_sys sys
            |> Analysis.param_scope_is_abstract param
            |> not
          )
        )
    )
  let first_rep_of terms =
    let rep = Set.choose terms in
    rep, Set.remove rep terms
  let is_bot _ = false
  let is_top _ = false
  let is_os_running () = (
    Flags.enabled () |> List.mem `INVGENREALOS
  )
end


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
