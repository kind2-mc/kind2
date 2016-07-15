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
  val mine : bool -> Analysis.param -> bool -> Sys.t -> (
    Sys.t * Term.TermSet.t
  ) list
  (** Returns true iff the input term is bottom. *)
  val is_bot: Term.t -> bool
  (** Returns true iff the input term is top. *)
  val is_top: Term.t -> bool
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
      if rep == Term.t_true then Term.mk_not term else
      Term.mk_eq [ rep ; term ]
    )
  let mk_cmp lhs rhs =
    if lhs != Term.t_false && rhs != Term.t_true then
      Term.mk_implies [ lhs ; rhs ]
    else raise TrivialRelation
  let eval = eval_bool
  let mine top_only param two_state sys =
    Sys.fold_subsystems
      ~include_top:true
      (fun acc sub_sys ->
        let shall_add =
          (sub_sys == sys) || (
            (not top_only) && (
              TransSys.scope_of_trans_sys sub_sys
              |> Analysis.param_scope_is_abstract param
              |> not
            )
          )
        in
        if shall_add then
          (
            sub_sys,
            InvGenMiner.mine_term
              true (* Synthesis. *)
              two_state (* Two step.  *)
              sub_sys
              []
              Term.TermSet.empty
          ) :: acc
        else acc
      )
      []
      sys
    (* InvGenCandTermGen.generate_candidate_terms
      (Flags.Invgen.two_state ()) sys sys
    |> fst *)
  let is_bot term = term = Term.t_false
  let is_top term = term = Term.t_true
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
  let mine _ _ _ _ =
    failwith "integer candidate term mining is unimplemented"
  let is_bot _ = false
  let is_top _ = false
end


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
  let mine _ _ _ _ =
    failwith "real candidate term mining is unimplemented"
  let is_bot _ = false
  let is_top _ = false
end


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)