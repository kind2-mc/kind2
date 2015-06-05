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

(* Source of a property *)
type prop_source =

  (* Property is from an annotation *)
  | PropAnnot of position

  (* Property is part of a contract *)
  | Contract of position

  (* Property was generated, for example, from a subrange
     constraint *)
  | Generated of StateVar.t list

  (* Property is an instance of a property in a called node

     Reference the instantiated property by the [scope] of the
     subsystem and the name of the property *)
  | Instantiated of string list * string

  (* Property is only a candidate invariant here to help prove other
     properties *)
  | Candidate


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
  

