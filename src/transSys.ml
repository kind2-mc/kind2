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


type prop_status =

  (* Status of property is unknown *)
  | Unknown

  (* Property is true up to k-th step *)
  | KTrue of int

  (* Property is invariant *)
  | Invariant 

  (* Property is false at some step *)
  | False

  (* Property is false at k-th step *)
  | KFalse of int 


type t = 

  {

    (* Definitions of uninterpreted function symbols *)
    uf_defs : (UfSymbol.t * (Var.t list * Term.t)) list;

    (* State variables of top node *)
    state_vars : StateVar.t list;

    (* Initial state constraint *)
    init : Term.t;

    (* Transition relation *)
    trans : Term.t;

    (* Propertes to prove invariant *)
    props : (string * Term.t) list; 

    (* Invariants *)
    mutable invars : Term.t list;

    (* Status of property *)
    mutable prop_status : (string * prop_status) list;

    (* Properties proved to be valid *)
    mutable props_valid : (string * Term.t) list;

    (* Properties proved to be invalid *)
    mutable props_invalid : (string * Term.t) list;
    
  }


let pp_print_state_var ppf state_var = 

  Format.fprintf ppf
    "@[<hv 1>(%a %a)@]" 
    StateVar.pp_print_state_var state_var
    Type.pp_print_type (StateVar.type_of_state_var state_var)

  
let pp_print_var ppf var = 

  Format.fprintf ppf
    "@[<hv 1>(%a %a)@]" 
    Var.pp_print_var var
    Type.pp_print_type (Var.type_of_var var)
  

let pp_print_uf_def ppf (uf_symbol, (vars, term)) =

  Format.fprintf 
    ppf   
    "@[<hv 1>(%a@ @[<hv 1>(%a)@]@ %a)@]"
    UfSymbol.pp_print_uf_symbol uf_symbol
    (pp_print_list pp_print_var "@ ") vars
    Term.pp_print_term term


let pp_print_prop ppf (prop_name, prop_term) = 

  Format.fprintf 
    ppf
    "@[<hv 1>(%s@ %a)@]"
    prop_name
    Term.pp_print_term prop_term


let pp_print_trans_sys 
    ppf
    { uf_defs; 
      state_vars; 
      init; 
      trans; 
      props; 
      invars; 
      props_valid; 
      props_invalid }= 

  Format.fprintf 
    ppf
    "@[<v>@[<hv 2>(state-vars@ (@[<v>%a@]))@]@,\
          @[<hv 2>(fun-defs@ (@[<v>%a@]))@]@,\
          @[<hv 2>(init@ (@[<v>%a@]))@]@,\
          @[<hv 2>(trans@ (@[<v>%a@]))@]@,\
          @[<hv 2>(props@ (@[<v>%a@]))@]@,\
          @[<hv 2>(invar@ (@[<v>%a@]))@]@,\
          @[<hv 2>(props-valid@ (@[<v>%a@]))@]@,\
          @[<hv 2>(props-invalid@ (@[<v>%a@]))@]@."
    (pp_print_list pp_print_state_var "@ ") state_vars
    (pp_print_list pp_print_uf_def "@ ") uf_defs
    Term.pp_print_term init 
    Term.pp_print_term trans
    (pp_print_list pp_print_prop "@ ") props
    (pp_print_list Term.pp_print_term "@ ") invars
    (pp_print_list pp_print_prop "@ ") props_valid
    (pp_print_list pp_print_prop "@ ") props_invalid


(* Create a transition system *)
let mk_trans_sys uf_defs state_vars init trans props = 

  (* Create constraints for integer ranges *)
  let invars_of_types = 
    
    List.fold_left 
      (fun accum state_var -> 

         (* Type of state variable *)
         match StateVar.type_of_state_var state_var with
           
           (* Type is a bounded integer *)
           | sv_type when Type.is_int_range sv_type -> 
             
             (* Get lower and upper bounds *)
             let l, u = Type.bounds_of_int_range sv_type in

             (* Add equation l <= v[0] <= u to invariants *)
             Term.mk_leq 
               [Term.mk_num l; 
                Term.mk_var
                  (Var.mk_state_var_instance state_var Numeral.zero); 
                Term.mk_num u] :: 
             accum
           | _ -> accum)
      []
      state_vars
  in

  { uf_defs = uf_defs;
    state_vars = state_vars;
    init = init;
    trans = trans;
    props = props;
    prop_status = List.map (fun (n, _) -> (n, Unknown)) props;
    invars = invars_of_types;
    props_valid = [];
    props_invalid = [] }


(* Determine the required logic for the SMT solver 

   TODO: Fix this to QF_UFLIA for now, dynamically determine later *)
let get_logic _ = ((Flags.smtlogic ()) :> SMTExpr.logic)


(* Return the state variables of the transition system *)
let state_vars t = t.state_vars


(* Return the variables of the transition system between given instants *)
let rec vars_of_bounds' trans_sys lbound ubound accum = 

  (* Return when upper bound below lower bound *)
  if Numeral.(ubound < lbound) then accum else

    (* Add state variables at upper bound instant  *)
    let accum' = 
      List.fold_left
        (fun accum sv -> 
           Var.mk_state_var_instance sv ubound :: accum)
        accum
        trans_sys.state_vars
    in

    (* Recurse to next lower bound *)
    vars_of_bounds' trans_sys lbound (Numeral.pred ubound) accum'

let vars_of_bounds trans_sys lbound ubound = 
  vars_of_bounds' trans_sys lbound ubound []



(* Instantiate the initial state constraint to the bound *)
let init_of_bound i t = 

  (* Bump bound if greater than zero *)
  if Numeral.(i = zero) then t.init else Term.bump_state i t.init


(* Instantiate the transition relation to the bound *)
let trans_of_bound i t = 

  (* Bump bound if greater than zero *)
  if Numeral.(i = one) then 
    t.trans 
  else 
    Term.bump_state (Numeral.(i - one)) t.trans


(* Instantiate the initial state constraint to the bound *)
let invars_of_bound i t = 

  (* Create conjunction of property terms *)
  let invars_0 = Term.mk_and (t.invars @ (List.map snd t.props_valid)) in 

  (* Bump bound if greater than zero *)
  if Numeral.(i = zero) then invars_0 else Term.bump_state i invars_0


(* Instantiate terms in association list to the bound *)
let named_terms_list_of_bound i l = 

  (* Create list of property terms *)
  let props_0 = List.map snd l in 

  (* Bump bound if greater than zero *)
  if
    Numeral.(i = zero)
  then
    props_0
  else
    List.map (Term.bump_state i) props_0


(* Instantiate all properties to the bound *)
let props_list_of_bound i t = 
  named_terms_list_of_bound i t.props


(* Instantiate valid properties to the bound *)
let props_valid_list_of_bound i t = 
  named_terms_list_of_bound i t.props_valid


(* Instantiate all properties to the bound *)
let props_of_bound i t = 
  Term.mk_and (props_list_of_bound i t)


(* Instantiate valid properties to the bound *)
let props_valid_of_bound i t = 
  Term.mk_and (props_valid_list_of_bound i t)


(* Add an invariant to the transition system *)
let add_invariant t invar = t.invars <- invar :: t.invars

(* Add a valid property to the transition system *)
let add_valid_prop t prop = t.props_valid <- prop :: t.props_valid

(* Add an invalid property to the transition system *)
let add_invalid_prop t prop = t.props_invalid <- prop :: t.props_invalid


(* Mark property as invariant *)
let prop_invariant t prop =

  t.prop_status <- 
    
    List.map 

      (fun (n, s) -> match s with

         (* Mark property as invariant if it was unknown, k-true or
            invariant *)
         | Unknown
         | KTrue _
         | Invariant -> (n, Invariant) 

         (* Fail if property was false or k-false *)
         | False 
         | KFalse _ -> raise (Invalid_argument "prop_invariant")) 

      t.prop_status


(* Mark property as false *)
let prop_false t prop =

  t.prop_status <- 
    
    List.map 

      (fun (n, s) -> match s with

         (* Mark property as false if it was unknown or l-true *)
         | Unknown
         | KTrue _ -> (n, False)

         (* Fail if property was invariant *)
         | Invariant ->
           raise (Invalid_argument "prop_false")

         (* Mark property as false if it was false or l-false *)
         | False
         | KFalse _ ->  (n, False))

      t.prop_status


(* Mark property as k-false *)
let prop_kfalse t k prop =

  t.prop_status <- 
    
    List.map 

      (fun (n, s) -> match s with

         (* Mark property as k-false if it was unknown, l-true for l <
            k or invariant *)
         | Unknown -> (n, KFalse k)

         (* Fail if property was invariant *)
         | Invariant -> 
           raise (Invalid_argument "prop_kfalse")

         (* Fail if property was l-true for l >= k *)
         | KTrue l when l >= k -> 
           raise (Invalid_argument "prop_kfalse")

         (* Mark property as k-false if it was l-true for l < k *)
         | KTrue _ -> (n, KFalse k)

         (* Keep if property was false *)
         | False -> (n, s)

         (* Keep if property was l-false for l <= k *)
         | KFalse l when l <= k -> (n, s)

         (* Mark property as k-false *)
         | KFalse _ -> (n, KFalse k))

      t.prop_status


(* Mark property as k-true *)
let prop_ktrue t k prop =

  t.prop_status <- 
    
    List.map 

      (fun (n, s) -> match s with

         (* Mark as k-true if it was unknown *)
         | Unknown -> (n, KTrue k)

         (* Keep if it was l-true for l > k *)
         | KTrue l when l > k -> (n, s)

         (* Mark as k-true if it was l-true for l <= k *)
         | KTrue _ -> (n, KTrue k)

         (* Keep if it was invariant *)
         | Invariant -> (n, s)

         (* Keep if it was false for unknown l *)
         | False -> (n, False)

         (* Keep if property was l-false for l > k *)
         | KFalse l when l > k -> (n, s)

         (* Fail if property was l-false for l <= k *)
         | KFalse _ -> 
           raise (Invalid_argument "prop_kfalse"))

      t.prop_status





(* Return true if all properties are either valid or invalid *)
let all_props_proved trans_sys =

  List.for_all
    (fun p -> 
      List.mem p trans_sys.props_valid 
      || List.mem p trans_sys.props_invalid) 
    trans_sys.props 
      

(* Return declarations for uninterpreted symbols *)
let uf_symbols_of_trans_sys { state_vars } = 
  List.map StateVar.uf_symbol_of_state_var state_vars


(* Apply [f] to all uninterpreted function symbols of the transition
   system *)
let iter_state_var_declarations { state_vars } f = 
  List.iter (fun sv -> f (StateVar.uf_symbol_of_state_var sv)) state_vars
  
(* Apply [f] to all function definitions of the transition system *)
let iter_uf_definitions { uf_defs } f = 
  List.iter (fun (u, (v, t)) -> f u v t) uf_defs
  


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
