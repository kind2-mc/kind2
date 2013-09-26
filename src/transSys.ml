(*
This file is part of the Kind verifier

* Copyright (c) 2007-2013 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

open Lib

(* The transition system *)
type t = 
    { 

      (* INIT: constraints on system variables 

	 A list of formulas over system variables, no previous state
	 variables occur here *)
      mutable init : Term.t list;         

      (* CONSTR: global state constraints 

	 A list of formulas describing invariants of the system *)
      mutable constr : Term.t list;   

      (* TRANS: guarded transitions

	 A list of guarded rules: pairs of terms and assignments to
	 system variables, where assignments are pairs of terms *)
      mutable trans : (Term.t * (StateVar.t * Term.t) list) list;   

      (* PROP: a list of named properties to be verified *)
      mutable props : (string * Term.t) list;

      (* Invariants and properties proved to be valid *)
      mutable invars : Term.t list;

      (* Properties proved to be invalid *)
      mutable props_valid : (string * Term.t) list;

      (* Properties proved to be invalid *)
      mutable props_invalid : (string * Term.t) list;

    }


(* Pretty-print the variable declarations *)
let pp_print_var ppf v =
  Format.fprintf
    ppf
    "@[<hv 1>%a@ %a@]"
    StateVar.pp_print_state_var v
    Type.pp_print_type (StateVar.type_of_state_var v)


(* Pretty-print an assignments of a terms to a variable *)
let pp_print_assign ppf (var, term) = 

  Format.fprintf 
    ppf
    "@[<hv>%a :=@ %a@]"
    StateVar.pp_print_state_var var
    Term.pp_print_term term
    

(* Pretty-print guarded transition rule *)
let pp_print_trans_rule ppf (guard, assign) = 

  Format.fprintf 
    ppf
    "@[<v>%a ==> @ %a@]"
    Term.pp_print_term guard
    (pp_print_list pp_print_assign "") assign


(* Pretty-print a property *)
let pp_print_prop ppf (name, term) = 

  Format.fprintf
    ppf
    "@[<hv 1>(\"%s\"@ %a)@]"
    name
    Term.pp_print_term term


(* Pretty-print a transition system *)
let pp_print_trans_sys 
    ppf 
    { init = i; constr = c; trans = g; invars = n; props = p  } =

  (* Collect declared state variables in a list 

     We want to avoid printing spurious separators at the end of the
     list of variables, hence we need to know the last element and
     cannot use {!StateVar.iter} *)
  let v = StateVar.fold (fun v a -> v :: a) [] in

  Format.fprintf 
    ppf
    "@[<v>@[<hv 2>(vars@ (@[<v>%a@]))@]@ \
          @[<hv 2>(init@ (@[<v>%a@]))@]@ \
          @[<hv 2>(trans@ (@[<v>%a@]))@]@ \
          @[<hv 2>(rules@ (@[<v>%a@]))@]@ \
          @[<hv 2>(invar@ (@[<v>%a@]))@]@ \
          @[<hv 2>(props@ (@[<v>%a@]))@]@."
    (pp_print_list pp_print_var "@ ") v
    (pp_print_list Term.pp_print_term "@ ") i
    (pp_print_list Term.pp_print_term "@ ") c
    (pp_print_list pp_print_trans_rule "@ ") g 
    (pp_print_list Term.pp_print_term "@ ") n 
    (pp_print_list pp_print_prop "@ ") p


(* Determine the required logic for the SMT solver 

   TODO: Fix this to QF_UFLIA for now, dynamically determine later *)
let get_logic _ = `QF_UFLIA

(* Add to offset of state variable instances *)
let bump_state i term = 

  let i' = numeral_of_int i in

  (* Bump offset of state variables *)
  Term.T.map
    (function _ -> function 
       | t when Term.is_free_var t -> 
         Term.mk_var 
           (Var.bump_offset_of_state_var_instance i' 
              (Term.free_var_of_term t))
       | _ as t -> t)
    term


(* Instantiate the initial state constraint to the bound *)
let init_of_bound i z = 

  (* Create conjunction of initial state formulas *)
  let init_0 = Term.mk_and z.init in 

  (* Bump bound if greater than zero *)
  if i = 0 then init_0 else bump_state i init_0 


(* Instantiate the transition relation constraint to the bound *)
let constr_of_bound i z = 

  (* Create conjunction of initial state formulas *)
  let constr_1 = Term.mk_and z.constr in 

  (* Bump bound if greater than zero *)
  if i = 1 then constr_1 else bump_state (i - 1) constr_1 


(* Instantiate the properties to the bound *)
let props_of_bound i z = 

  (* Create conjunction of initial state formulas *)
  let props_0 = Term.mk_and (List.map snd z.props) in 

  (* Bump bound if greater than zero *)
  if i = 0 then props_0 else bump_state i props_0 


(* Instantiate the valid properties to the bound *)
let invars_of_bound i z = 

  (* Create conjunction of initial state formulas *)
  let invars_0 = Term.mk_and z.invars in 

  (* Bump bound if greater than zero *)
  if i = 0 then invars_0 else bump_state i invars_0 


(* Get all state variables at a given offset in the term *)
let vars_at_offset_of_term i term = 

  let i' = numeral_of_int i in

  (* Collect all variables in a set *)
  let var_set = 
    Term.eval_t
      (function 
        | Term.T.Var v when Var.offset_of_state_var_instance v = i' -> 
          (function [] -> Var.VarSet.singleton v | _ -> assert false)
        | Term.T.Var _ 
        | Term.T.Const _ -> 
          (function [] -> Var.VarSet.empty | _ -> assert false)
        | Term.T.App _ -> List.fold_left Var.VarSet.union Var.VarSet.empty)
      term
  in

  (* Return elements of a set as list *)
  Var.VarSet.elements var_set


(* Get all variables of a term *)
let vars_of_term term = 

  (* Collect all variables in a set *)
  let var_set = 
    Term.eval_t
      (function 
        | Term.T.Var v -> 
          (function [] -> Var.VarSet.singleton v | _ -> assert false)
        | Term.T.Const _ -> 
          (function [] -> Var.VarSet.empty | _ -> assert false)
        | Term.T.App _ -> List.fold_left Var.VarSet.union Var.VarSet.empty)
      term
  in

  (* Return elements of a set as list *)
  Var.VarSet.elements var_set


(* Collect all state variables in a set *)
let state_vars_of_term term  = 

  Term.eval_t
    (function 
      | Term.T.Var v -> 
        (function 
          | [] -> 
            StateVar.StateVarSet.singleton 
              (Var.state_var_of_state_var_instance v)
          | _ -> assert false)
      | Term.T.Const _ -> 
        (function [] -> StateVar.StateVarSet.empty | _ -> assert false)
      | Term.T.App _ -> 
        List.fold_left 
          StateVar.StateVarSet.union 
          StateVar.StateVarSet.empty)
    term
  

(* Get all state variables of a transition system *)
let state_vars_of_sys z = 

  (* List of sets of state variables in all terms *)
  let state_var_sets = 
    (List.map state_vars_of_term z.init) @
      (List.map state_vars_of_term z.constr) @
      (List.map (function (_, t) -> state_vars_of_term t) z.props)
  in

  (* Return elements of a set as list *)
  StateVar.StateVarSet.elements
    (List.fold_left 
       StateVar.StateVarSet.union
       StateVar.StateVarSet.empty
       state_var_sets)
  
  
(* Return unprimed and primed variables

   We return all declared state variables regardless of those used in
   the transition system. *)
let vars z = 

  StateVar.fold
    (fun sv a -> 
       Var.mk_state_var_instance sv (Lib.numeral_of_int 0) ::
         Var.mk_state_var_instance sv (Lib.numeral_of_int 1) ::
         a)
    []


(* Return state variables

   We return all declared state variables regardless of those used in
   the transition system. *)
let state_vars z = 

  StateVar.fold
    (fun sv a -> if not (StateVar.is_definition sv) then sv :: a else a)
    []


(* Return constraints for types like integer ranges *)
let invars_of_types () = 
  
  StateVar.fold 
    (fun v a -> match Type.node_of_type (StateVar.type_of_state_var v) with
       | Type.IntRange (l, u) -> 
         Term.mk_leq 
           [Term.mk_num l; 
            Term.mk_var (Var.mk_state_var_instance v (numeral_of_int 0)); 
            Term.mk_num u] :: 
           a
       | _ -> a)
    []


(* Add a list of invariants to a transition system *)
let add_invariant ({ invars } as t) new_invar =
  t.invars <- new_invar :: invars


(* Pretty-print a list of properties with either the word "property"
   or "properties" before *)
let pp_print_property_list ppf = 

  (* Pretty-print a list of properties separated by commas *)
  let rec pp_print_property_list' ppf = function 

    | [] -> ()

    | p :: tl -> 

      Format.fprintf ppf 
        "%s%t" 
        p 
        (function ppf -> if not (tl = []) then 
            Format.fprintf ppf ",@ %a" pp_print_property_list' tl)

  in

  function 

    | [] -> 
      raise 
        (Invalid_argument "pp_print_property_list: empty list of properties")

    | [_] as p -> 

      Format.fprintf ppf 
        "property %a" 
        pp_print_property_list' p

    | p -> 

      Format.fprintf ppf 
        "properties %a" 
        pp_print_property_list' p


(* Output a message that module m has proved the given list of
   properties *)
let log_property_valid m = function 

  | [] ->

    raise 
      (Invalid_argument "log_property_valid: empty list of properties")

  | p -> ()

(*
    Event.log m Event.L_info
      "@[<hov>Success: %a proved in %s@]@."
      pp_print_property_list 
      p
      m
*)

(* Output a message that module m has disproved the given list of
   properties *)
let log_property_invalid m = function 

  | [] ->

    raise 
      (Invalid_argument "log_property_valid: empty list of properties")

  | p -> ()

(*
    Event.log 
      0 
      "@[<hov>Failure: %a disproved in %s@]@."
      pp_print_property_list 
      p
      m
*)

(*
(* Output a counterexample *)
let log_counterexample = function

  | [] ->

    (function _ -> 
      raise 
        (Invalid_argument "log_property_valid: empty list of properties"))

  | p -> 

    Event.log 
      0 
      "@[<hov>Counterexample for %a@]@;%a@."
      pp_print_property_list 
      p
*)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
