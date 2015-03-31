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

(* Source of a property *)
type prop_source =

  (* Property is from an annotation *)
  | PropAnnot of position

  (* Property is part of a contract *)
  | Contract of position * string

  (* Property was generated, for example, from a subrange
     constraint *)
  | Generated of StateVar.t list

  (* Property is a requirement of a subnode. The list of state
     variables are the guarantees proving the requirement yields. *)
  | Requirement of position * string list * StateVar.t list

  (* Property is a mode contract implication. *)
  (* | ModeContract of position * string *)

  (* Property is a global contract. *)
  (* | GlobalContract of position * string *)

  (* Property is an instance of a property in a called node

     Reference the instantiated property by the [scope] of the
     subsystem and the name of the property *)
  | Instantiated of string list * string 


let pp_print_prop_source ppf = function
  | PropAnnot pos ->
     Format.fprintf
       ppf "%a" pp_print_position pos
  | Contract (pos, name) ->
     Format.fprintf
       ppf "contract %s at %a" name pp_print_position pos
  | Requirement (pos, scope, _) ->
     Format.fprintf
       ppf
       "requirement of %s for call at %a"
       (String.concat "." scope)
       pp_print_position pos
  | Generated _ ->
     Format.fprintf ppf "subrange constraint"
  | Instantiated (scope,_) ->
     Format.fprintf
       ppf
       "instantiated from %s"
              (String.concat "." scope)

(* Return the default value of the type *)
let default_of_type t = 

  match Type.node_of_type t with

    (* Booleans are false by default *)
    | Type.Bool -> Term.t_false

    (* Integers are zero by default *)
    | Type.Int -> Term.mk_num Numeral.zero

    (* Integer range values are their lower bound by default *)
    | Type.IntRange (l, _) -> Term.mk_num l

    (* Reals are zero by default *)
    | Type.Real -> Term.mk_dec Decimal.zero

    (* No defaults for scalars and arrays *)
    | Type.Scalar _
    | Type.Array _ -> invalid_arg "default_of_type"



(*******************)
(* Logic fragments *)
(*******************)


(* A feature of a logic fragment for terms *)
type feature =
  | Q  (* Quantifiers *)
  | UF (* Equality over uninterpreted functions *)
  | IA (* Integer arithmetic *)
  | RA (* Real arithmetic *)
  | LA (* Linear arithmetic *)
  | NA (* Non-linear arithmetic *)


(* Set of features *)
module FeatureSet = Set.Make (struct
    type t = feature
    let compare = Pervasives.compare
  end)


(* Logic fragments for terms *)
type features = FeatureSet.t

(* Try to remove top level quantifief by instantiating with fresh symbols *)
let remove_top_level_quantifier removed t =
  match Term.T.node_of_t t with
  | Term.T.Forall lam | Term.T.Exists lam ->
    let t' =
      Term.T.sorts_of_lambda lam
      |> List.map (fun t ->
          (UfSymbol.mk_fresh_uf_symbol [] t
           |> Term.mk_uf) @@ [] )
      |> Term.T.instantiate lam
    in
    removed := true;
    t'
  | _ -> t

(* find the smallest encompassing logic of a sort *)
let rec logic_of_sort ty =
  let open Type in
  let open FeatureSet in
  match node_of_type ty with
  | Bool -> empty
    
  | Int | IntRange _ -> singleton IA
                          
  | Real -> singleton RA
              
  | Array (ta, tr) -> add UF (union (logic_of_sort ta) (logic_of_sort tr))
      
  | Scalar _ -> empty


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
let logic_of_flat t acc =
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
    else sup_logics acc

  | App (s, _) when Symbol.(s == s_plus || s == s_minus) ->
    add LA (sup_logics acc)

  | App (s, l) when s == Symbol.s_times && at_most_one_non_num l ->
    add LA (sup_logics acc)

  | App (s, [n; d]) when Symbol.(s == s_div || s == s_intdiv) &&
    (Term.is_numeral d || Term.is_decimal d) ->
    add LA (sup_logics acc)

  | App (s, l) when Symbol.(s == s_div || s == s_times || s == s_abs
                            || s == s_intdiv || s == s_mod) ->
    add NA (sup_logics acc)

  | App (s, l) when Symbol.(s == s_lt || s == s_gt ||
                            s == s_leq || s == s_geq) ->
    add LA (sup_logics acc)

  | App _ -> sup_logics acc

  

(* Returns the logic fragment used by a term *)
let logic_of_term t =
  let removed_q = ref false in
  t
  |> Term.map (fun _ -> remove_top_level_quantifier removed_q)
  |> Term.eval_t logic_of_flat
  |> (if !removed_q then FeatureSet.add Q else Lib.identity)



module L = FeatureSet


let pp_print_features fmt l =
  if not (L.mem Q l) then fprintf fmt "QF_";
  if L.is_empty l then fprintf fmt "SAT";
  if L.mem UF l then fprintf fmt "UF";
  if L.mem NA l then fprintf fmt "N"
  else if L.mem LA l then fprintf fmt "L";
  if L.mem IA l then fprintf fmt "I";
  if L.mem RA l then fprintf fmt "R"; 
  if L.mem IA l || L.mem RA l then fprintf fmt "A"


let string_of_features l = asprintf "%a" pp_print_features l


type logic = [ `None | `Inferred of features | `SMTLogic of string ]

let pp_print_logic fmt = function
  | `None -> ()
  | `Inferred l -> pp_print_features fmt l
  | `SMTLogic s -> pp_print_string fmt s


let string_of_logic = function
  | `None -> ""
  | `Inferred l -> string_of_features l
  | `SMTLogic s -> s




module Signals: sig

  (** Pretty printer for signal info. *)
  val pp_print_signals: Format.formatter -> unit -> unit

  (** Sets the handler for sigalrm to ignore. *)
  val ignore_sigalrm: unit -> unit
  (** Sets the handler for sigint to ignore. *)
  val ignore_sigint: unit -> unit
  (** Sets the handler for sigquit to ignore. *)
  val ignore_sigquit: unit -> unit
  (** Sets the handler for sigterm to ignore. *)
  val ignore_sigterm: unit -> unit

  (** Sets the handler for sigalrm to [exception_on_signal] or raise
      [TimeoutWall] depending on the flags. *)
  val set_sigalrm: unit -> unit
  (** Sets an exception handler for sigint. *)
  val set_sigint: unit -> unit
  (** Sets an exception handler for sigquit. *)
  val set_sigquit: unit -> unit
  (** Sets an exception handler for sigterm. *)
  val set_sigterm: unit -> unit

  (** Sets a timeout. *)
  val set_timeout: float -> unit
  (** Sets a timeout from the timeout flag. *)
  val set_timeout_from_flag: unit -> unit
  (** Deactivates timeout. *)
  val unset_timeout: unit -> unit

  (** Raise exception on ctrl+c if true. *)
  val catch_break: bool -> unit

end = struct

  type handler = | Ignore | Exn | Timeout

  let pp_print_handler fmt = function
    | Ignore ->
       Format.fprintf
         fmt
         "ignore"
    | Exn ->
       Format.fprintf
         fmt
         "raise exception"
    | Timeout ->
       Format.fprintf
         fmt
         "raise timeout"

  type t = {
      (* Signals. *)
      mutable sigalrm: handler ;
      mutable sigint:  handler ;
      mutable sigquit: handler ;
      mutable sigterm: handler ;

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

  (* Ignore all signals. *)
  let ignore_all_sigs () =
    ignore_sigalrm () ;
    ignore_sigint () ;
    ignore_sigquit () ;
    ignore_sigterm () ;
    catch_break false

  (* Sets a handler for a signal. *)
  let set_sig s f =
    Sys.set_signal s ( Sys.Signal_handle f )


  (* Sets a handler for sigalrm. *)
  let set_sigalrm () =
    (* If there is a timeout, then raise [TimeoutWall]. Otherwise use
       usual exeption thing. *)
    let behavior, handler =
      if Flags.timeout_wall () >  0. then
	      (fun _ -> raise TimeoutWall), Timeout
      else
	      exception_on_signal, Exn
    in

    (* Only changing if necessary. *)
    if signals.sigalrm = handler then ()
    else (
      signals.sigalrm <- handler ;
      set_sig Sys.sigalrm behavior
    )

  (* Sets a handler for sigint. *)
  let set_sigint () =
    if signals.sigint = Exn then ()
    else (
      signals.sigint <- Exn ;
      set_sig Sys.sigint exception_on_signal
    )

  (* Sets a handler for sigquit. *)
  let set_sigquit () =
    if signals.sigquit = Exn then ()
    else (
      signals.sigquit <- Exn ;
      set_sig Sys.sigquit exception_on_signal
    )

  (* Sets a handler for sigterm. *)
  let set_sigterm () =
    if signals.sigterm = Exn then ()
    else (
      signals.sigterm <- Exn ;
      set_sig Sys.sigterm exception_on_signal
    )


  (* Sets a timeout. *)
  let set_timeout_value ?(interval = 0.) value =
    set_sigalrm () ;
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

  (* Sets a timeout based on the flag value. *)
  let set_timeout_from_flag () =
    if Flags.timeout_wall () > 0.
    then (
      Format.printf "Setting timeout (%f).@.@." (Flags.timeout_wall ()) ;
      Flags.timeout_wall () |> set_timeout
    ) else ()

  (* Deactivates timeout. *)
  let unset_timeout () =
    if signals.timeout = None then ()
    else (
      signals.timeout <- None ;
      set_timeout_value 0.
    )

  end

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  

