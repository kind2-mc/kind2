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
open Format
  
(*

type invariants = Term.t list

type property = (string * Term.t)
type properties = property list
type cex = (property list * Model.path)
type cexs = cex list

*)

(* ********************************************************************** *)
(* Properties of transition systems                                       *)
(* ********************************************************************** *)

(* Return the default value of the type *)
let default_of_type t =

  match Type.node_of_type t with

    (* Booleans are false by default *)
    | Type.Bool -> Term.t_false

    (* Integers are zero by default *)
    | Type.Int -> Term.mk_num Numeral.zero

    (* Fixed-width integers are zero by default *)
    | Type.UBV i ->
      begin match i with
      | 8 -> Term.mk_ubv (Bitvector.repeat_bit false 8)
      | 16 -> Term.mk_ubv (Bitvector.repeat_bit false 16)
      | 32 -> Term.mk_ubv (Bitvector.repeat_bit false 32)
      | 64 -> Term.mk_ubv (Bitvector.repeat_bit false 64)
      | _ -> raise (Invalid_argument "default_of_type: BV size not allowed")
      end
    | Type.BV i ->
      begin match i with
      | 8 -> Term.mk_bv (Bitvector.repeat_bit false 8)
      | 16 -> Term.mk_bv (Bitvector.repeat_bit false 16)
      | 32 -> Term.mk_bv (Bitvector.repeat_bit false 32)
      | 64 -> Term.mk_bv (Bitvector.repeat_bit false 64)
      | _ -> raise (Invalid_argument "default_of_type: BV size not allowed")
      end

    (* Integer range values are their lower bound by default *)
    | Type.IntRange (l, _, _) -> Term.mk_num l

    (* Reals are zero by default *)
    | Type.Real -> Term.mk_dec Decimal.zero

    (* No defaults *)
    | Type.Abstr _
    | Type.Array _ -> invalid_arg "default_of_type"



(*******************)
(* Logic fragments *)
(*******************)


(* A feature of a logic fragment for terms *)
type feature =
  | Q  (* Quantifiers *)
  | UF (* Equality over uninterpreted functions *)
  | A  (* Arrays *)
  | IA (* Integer arithmetic *)
  | RA (* Real arithmetic *)
  | LA (* Linear arithmetic *)
  | NA (* Non-linear arithmetic *)
  | BV (* Bit vectors*)


(* Set of features *)
module FeatureSet = Set.Make (struct
    type t = feature
    let compare = Stdlib.compare
  end)


(* Logic fragments for terms *)
type features = FeatureSet.t

(* Try to remove top level quantifief by instantiating with fresh symbols *)
let remove_top_level_quantifier t =
  match Term.T.node_of_t t with
  | Term.T.Forall lam | Term.T.Exists lam ->
    Term.T.sorts_of_lambda lam
    |> List.map (fun t ->
        (UfSymbol.mk_fresh_uf_symbol [] t
         |> Term.mk_uf) @@ [] )
    |> Term.T.instantiate lam
  | _ -> t

(* find the smallest encompassing logic of a sort *)
let rec logic_of_sort ty =
  let open Type in
  let open FeatureSet in
  match node_of_type ty with
  | Bool | Abstr _ -> empty
    
  | Int | IntRange _ -> singleton IA
  
  | UBV _ | BV _ -> singleton BV
                          
  | Real -> singleton RA
              
  | Array (ta, tr) ->
    union (logic_of_sort ta) (logic_of_sort tr)
    |> add UF
    |> add A


let s_abs = Symbol.mk_symbol `ABS
let s_intdiv = Symbol.mk_symbol `INTDIV

(* check if there is at most one term that is not a numeral or decimal *)
let at_most_one_non_num l =
  let rec aux found = function
  | [] -> true
  | t :: l when Term.is_numeral t || Term.is_decimal t ->
    aux found l
  | t :: l ->
    if found then raise Exit
    else aux true l
  in

  try aux false l with Exit -> false
      
(* perform union of a list of logics *)
let sup_logics =
  let open FeatureSet in
  List.fold_left union empty

(* the logic of a flat term given the logics of its subterms *)
let logic_of_flat fun_symbols t acc =
  let open Term.T in
  let open FeatureSet in
  match t with

  | Attr _ -> sup_logics acc
  
  | Var v -> Var.type_of_var v |> logic_of_sort |> union @@ sup_logics acc

  | Const s | App (s, []) ->
    if Symbol.is_uf s then
      Symbol.uf_of_symbol s
      |> UfSymbol.res_type_of_uf_symbol
      |> logic_of_sort
      |> union @@ sup_logics acc
    else if Symbol.is_numeral s then add IA (sup_logics acc)
    else if Symbol.is_decimal s then add RA (sup_logics acc)
    else if Symbol.is_bitvector s then add BV (sup_logics acc)
    else if Symbol.is_ubitvector s then add BV (sup_logics acc)
    else sup_logics acc

  | App (s, _) when Symbol.(s == s_plus || s == s_minus) ->
    add LA (sup_logics acc)

  | App (s, l) when s == Symbol.s_times && at_most_one_non_num l ->
    add LA (sup_logics acc)

  | App (s, n :: l) when Symbol.(s == s_div || s == s_intdiv || s == s_mod) &&
     List.for_all (fun t -> Term.is_numeral t || Term.is_decimal t) l ->
     add LA (sup_logics acc)

  | App (s, [n]) when Symbol.(s == s_abs) &&
     (Term.is_numeral n || Term.is_decimal n) ->
     add LA (sup_logics acc)

  | App (s, _) when Symbol.(s == s_div || s == s_times || s == s_abs ||
                            s == s_intdiv || s == s_mod) ->
    add NA (sup_logics acc)

  | App (s, _) when Symbol.(s == s_lt || s == s_gt ||
                            s == s_leq || s == s_geq) ->
    add LA (sup_logics acc)

  | App (s, _) when Symbol.(is_select s || s == s_store) ->

    let l = sup_logics acc |> add A in
    if Symbol.is_uf s then add UF l else l

  | App (s, _) when Symbol.is_uf s ->

    if List.mem (Symbol.uf_of_symbol s) fun_symbols then sup_logics acc
    else add UF (sup_logics acc)

  | App (s, _) when Symbol.(s == s_to_int || s == s_to_real || is_divisible s) ->
    sup_logics acc |> add LA |> add IA |> add RA

  | App (s, _) when Symbol.(is_to_uint8 s || is_to_uint16 s || is_to_uint32 s || is_to_uint64 s ||
                            is_to_int8 s || is_to_int16 s || is_to_int32 s || is_to_int64 s) ->
    add BV (sup_logics acc)

  | App _ -> sup_logics acc

  

let check_add_Q t l =
  if Term.has_quantifier t then
    FeatureSet.add Q l
  else l
                                                        
(* Returns the logic fragment used by a term *)
let logic_of_term fun_symbols t =
  t
  |> Term.map (fun _ -> remove_top_level_quantifier)
  |> Term.eval_t ~fail_on_quantifiers:false (logic_of_flat fun_symbols)
  |> check_add_Q t



module L = FeatureSet


let pp_print_features fmt l =
  if not (L.mem Q l) then fprintf fmt "QF_"
  else if L.cardinal l = 1 then fprintf fmt "UF";
  if L.is_empty l then fprintf fmt "UF";
  if L.mem A l && Flags.Arrays.smt () then fprintf fmt "A";
  if L.mem UF l then fprintf fmt "UF";
  if L.mem BV l then fprintf fmt "BV";
  if L.mem NA l then fprintf fmt "N"
  else if L.mem LA l || L.mem IA l || L.mem RA l then fprintf fmt "L";
  if L.mem IA l then fprintf fmt "I";
  if L.mem RA l then fprintf fmt "R";
  if L.mem IA l || L.mem RA l then fprintf fmt "A"


let string_of_features l = asprintf "%a" pp_print_features l


type logic = [ `None | `Inferred of features | `SMTLogic of string ]

let pp_print_logic fmt = function
  | `None -> pp_print_string fmt "ALL"
  | `Inferred l ->
      if
        L.mem BV l
        && not (L.is_empty (L.inter l (L.of_list [ IA; RA; LA; NA ])))
      then pp_print_string fmt "ALL"
      else pp_print_features fmt l
  | `SMTLogic s -> pp_print_string fmt (if s = "" then "ALL" else s)


let string_of_logic = function
  | `None -> "ALL"
  | `Inferred l ->
      if
        L.mem BV l
        && not (L.is_empty (L.inter l (L.of_list [ IA; RA; LA; NA ])))
      then "ALL"
      else string_of_features l
  | `SMTLogic s -> if s = "" then "ALL" else s


let logic_allow_arrays = function
  | `None | `SMTLogic _ -> true
  | `Inferred l -> L.mem A l


module Signals = struct

  type handler = | Ignore | Exn | Timeout

  let pp_print_handler fmt = function
    | Ignore -> Format.fprintf fmt "ignore"
    | Exn -> Format.fprintf fmt "raise exception"
    | Timeout -> Format.fprintf fmt "raise timeout"

  type t = {
    (* Signals. *)
    mutable sigalrm: handler ;
    mutable sigint:  handler ;
    mutable sigquit: handler ;
    mutable sigterm: handler ;
    mutable sigpipe: handler ;

    (* Timeout value. *)
    mutable timeout: float option ;

    (* Raise [Break] on ctrl+c. *)
    mutable break: bool ;
  }

  let signals = {
      sigalrm = Ignore ;
      sigint  = Ignore ;
      sigterm = Ignore ;
      sigquit = Ignore ;
      sigpipe = Ignore ;
      timeout = None   ;
      break   = false  ;
  }

  let pp_print_signals fmt () =
    Format.fprintf
      fmt
      "Signals: @[<v>\
       sigalrm | %a@ \
       sigint  | %a@ \
       sigquit | %a@ \
       sigterm | %a@ \
       timeout | %a@ \
       break   | %b@]"
      pp_print_handler signals.sigalrm
      pp_print_handler signals.sigint
      pp_print_handler signals.sigquit
      pp_print_handler signals.sigterm
      (pp_print_option Format.pp_print_float)
      signals.timeout
      signals.break

  let catch_break b =
    if signals.break = b then ()
    else (
      signals.break <- b ;
      Sys.catch_break b
    )

  (* Sets the handler to ignore for some signal. *)
  let ignore_sig s =
    Sys.set_signal s Sys.Signal_ignore

  (* Sets the handler for sigalrm to ignore. *)
  let ignore_sigalrm () =
    if signals.sigalrm = Ignore then ()
    else (
      signals.sigalrm <- Ignore ;
      ignore_sig Sys.sigalrm
    )

  (* Runs something while ignoring [sigalrm]. *)
  let ignoring_sigalrm f =
    let old = signals.sigalrm in
    ignore_sigalrm () ;
    let res =
      try f () with e ->
        signals.sigalrm <- old ;
        raise e
    in
    signals.sigalrm <- old ;
    res

  (* Sets the handler for sigint to ignore. *)
  let ignore_sigint () =
    if signals.sigint = Ignore then ()
    else (
      signals.sigint <- Ignore ;
      ignore_sig Sys.sigint
    )

  (* Sets the handler for sigquit to ignore. *)
  let ignore_sigquit () =
    if signals.sigquit = Ignore then ()
    else (
      signals.sigquit <- Ignore ;
      ignore_sig Sys.sigquit
    )

  (* Sets the handler for sigterm to ignore. *)
  let ignore_sigterm () =
    if signals.sigterm = Ignore then ()
    else (
      signals.sigterm <- Ignore ;
      ignore_sig Sys.sigterm
    )

  (* Sets the handler for sigpipeu to ignore. *)
  let ignore_sigpipe () =
    if signals.sigpipe = Ignore then ()
    else (
      signals.sigpipe <- Ignore ;
      ignore_sig Sys.sigpipe
    )

  (* Ignore all signals. *)
  let ignore_all_sigs () =
    ignore_sigalrm () ;
    ignore_sigint () ;
    ignore_sigquit () ;
    ignore_sigterm () ;
    ignore_sigpipe () ;
    catch_break false

  (* Sets a handler for a signal. *)
  let set_sig s f =
    Sys.set_signal s ( Sys.Signal_handle f )


  (* Sets a handler for sigalrm. *)
  let set_sigalrm_timeout () =
    signals.sigalrm <- Timeout ;
    set_sig Sys.sigalrm (fun _ -> raise TimeoutWall)


  (* Sets a handler for sigalrm. *)
  let set_sigalrm_exn () =
    signals.sigalrm <- Exn ;
    set_sig Sys.sigalrm exception_on_signal

  (* Sets a handler for sigint. *)
  let set_sigint () =
    signals.sigint <- Exn ;
    set_sig Sys.sigint exception_on_signal

  (* Sets a handler for sigquit. *)
  let set_sigquit () =
    signals.sigquit <- Exn ;
    set_sig Sys.sigquit exception_on_signal

  (* Sets a handler for sigterm. *)
  let set_sigterm () =
    signals.sigterm <- Exn ;
    set_sig Sys.sigterm exception_on_signal

  (* Sets a handler for sigpipe. *)
  let set_sigpipe () =
    signals.sigpipe <- Exn ;
    set_sig Sys.sigpipe exception_on_signal


  (* Sets a timeout. *)
  let set_timeout_value ?(interval = 0.) value =
    set_sigalrm_timeout () ;
    (* Set timer. *)
    Unix.setitimer
      Unix.ITIMER_REAL
      { Unix.it_interval = interval ;
        Unix.it_value = value }
    |> ignore

  (* Sets a timeout. *)
  let set_timeout value =
    signals.timeout <- Some(value) ;
    set_timeout_value value

  (* Deactivates timeout. *)
  let unset_timeout () =
    set_timeout_value 0. ;
    signals.timeout <- None ;
    set_sigalrm_exn ()

  (* Sets a timeout based on the flag value and the total time elapsed this
  far. *)
  let set_sigalrm_timeout_from_flag () =
    match Flags.timeout_wall () with
    | timeout when timeout > 0. ->
      let elapsed = Stat.get_float Stat.total_time in
      if timeout < elapsed then raise TimeoutWall
      else timeout -. elapsed |> set_timeout
    | _ ->
      unset_timeout ()

  end


(* Add quantifiers to logic *)
let add_quantifiers = function
  | `None -> `None
  | `Inferred l -> `Inferred (FeatureSet.add Q l)
  | `SMTLogic s as l ->
    try
      let s =
        if String.sub s 0 3 = "QF_" then
          String.sub s 3 (String.length s - 3)
        else s in
      `SMTLogic s
    with Invalid_argument _ -> l


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  

