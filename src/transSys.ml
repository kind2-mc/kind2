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

type input  =
  (* A node list representation of a Lustre program, where nodes not connected
     to the main node have been culled out. *)
  | LustreInput of LustreNode.t list

type t = 

  {

    (* Definitions of uninterpreted function symbols for initial state
       constraint *)
    uf_defs_init : (UfSymbol.t * (Var.t list * Term.t)) list;

    (* Definitions of uninterpreted function symbols for transition
       relation *)
    uf_defs_trans : (UfSymbol.t * (Var.t list * Term.t)) list;

    (* State variables of top node *)
    state_vars : StateVar.t list;

    (* Initial state constraint *)
    init : Term.t;

    (* Transition relation *)
    trans : Term.t;

    (* Propertes to prove invariant *)
    props : (string * Term.t) list; 

    (* The input which produced this system. *)
    input : input;

    (* Invariants *)
    mutable invars : Term.t list;

    (* Status of property *)
    mutable prop_status : (string * prop_status) list;
    
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

let pp_print_prop_status ppf (p, s) =
  Format.fprintf ppf "@[<hv 2>(%s %a)@]" p pp_print_prop_status s

let pp_print_trans_sys 
    ppf
    { uf_defs_init; 
      uf_defs_trans; 
      state_vars; 
      init; 
      trans; 
      props;
      invars;
      prop_status }= 

  Format.fprintf 
    ppf
    "@[<v>@[<hv 2>(state-vars@ (@[<v>%a@]))@]@,\
          @[<hv 2>(init-defs@ (@[<v>%a@]))@]@,\
          @[<hv 2>(trans-defs@ (@[<v>%a@]))@]@,\
          @[<hv 2>(init@ (@[<v>%a@]))@]@,\
          @[<hv 2>(trans@ (@[<v>%a@]))@]@,\
          @[<hv 2>(props@ (@[<v>%a@]))@]@,\
          @[<hv 2>(invar@ (@[<v>%a@]))@]@,\
          @[<hv 2>(status@ (@[<v>%a@]))@]@."
    (pp_print_list pp_print_state_var "@ ") state_vars
    (pp_print_list pp_print_uf_def "@ ") uf_defs_init
    (pp_print_list pp_print_uf_def "@ ") uf_defs_trans
    Term.pp_print_term init 
    Term.pp_print_term trans
    (pp_print_list pp_print_prop "@ ") props
    (pp_print_list Term.pp_print_term "@ ") invars
    (pp_print_list pp_print_prop_status "@ ") prop_status


(* Create a transition system *)
let mk_trans_sys uf_defs_init uf_defs_trans state_vars init trans props input = 

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

  { uf_defs_init = uf_defs_init;
    uf_defs_trans = uf_defs_trans;
    state_vars = List.sort StateVar.compare_state_vars state_vars;
    init = init;
    trans = trans;
    props = props;
    input = input;
    prop_status = List.map (fun (n, _) -> (n, PropUnknown)) props;
    invars = invars_of_types }


(* Determine the required logic for the SMT solver 

   TODO: Fix this to QF_UFLIA for now, dynamically determine later *)
let get_logic _ = ((Flags.smtlogic ()) :> SMTExpr.logic)


(* Return the state variables of the transition system *)
let state_vars t = t.state_vars

(* Return the input used to create the transition system *)
let get_input t = t.input

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
let init_of_bound t i = 

  (* Bump bound if greater than zero *)
  if Numeral.(i = zero) then t.init else Term.bump_state i t.init


(* Instantiate the transition relation to the bound *)
let trans_of_bound t i = 

  (* Bump bound if greater than zero *)
  if Numeral.(i = one) then 
    t.trans 
  else 
    Term.bump_state (Numeral.(i - one)) t.trans


(* Instantiate the initial state constraint to the bound *)
let invars_of_bound t i = 

  (* Create conjunction of property terms *)
  let invars_0 = Term.mk_and t.invars in 

  (* Bump bound if greater than zero *)
  if Numeral.(i = zero) then invars_0 else Term.bump_state i invars_0


(* Instantiate terms in association list to the bound *)
let named_terms_list_of_bound l i = 

  (* Bump bound if greater than zero *)
  if
    Numeral.(i = zero)
  then
    l
  else
    List.map (fun (n, t) -> (n, Term.bump_state i t)) l


(* Instantiate all properties to the bound *)
let props_list_of_bound t i = 
  named_terms_list_of_bound t.props i


(* Instantiate all properties to the bound *)
let props_of_bound t i = 
  Term.mk_and (List.map snd (props_list_of_bound t i))


(* Add an invariant to the transition system *)
let add_invariant t invar = t.invars <- invar :: t.invars


(* Return current status of all properties *)
let prop_status_all trans_sys = trans_sys.prop_status


(* Return current status of property *)
let prop_status trans_sys p = 

  try 

    List.assoc p trans_sys.prop_status

  with Not_found -> PropUnknown


(* Mark property as invariant *)
let prop_invariant t prop =

  t.prop_status <- 
    
    List.map 

      (fun (n, s) -> if n = prop then 

          match s with
            
            (* Mark property as invariant if it was unknown, k-true or
               invariant *)
            | PropUnknown
            | PropKTrue _
            | PropInvariant -> (n, PropInvariant) 
                               
            (* Fail if property was false or k-false *)
            | PropFalse 
            | PropKFalse _ -> raise (Failure "prop_invariant") 

        else (n, s))

      t.prop_status


(* Mark property as false *)
let prop_false t prop =

  t.prop_status <- 

    List.map 

      (fun (n, s) -> if n = prop then 

          match s with

            (* Mark property as false if it was unknown or l-true *)
            | PropUnknown
            | PropKTrue _ -> (n, PropFalse)

            (* Fail if property was invariant *)
            | PropInvariant ->
              raise (Failure "prop_false")

            (* Mark property as false if it was false or l-false *)
            | PropFalse
            | PropKFalse _ ->  (n, PropFalse) 

        else (n, s))

      t.prop_status


(* Mark property as k-false *)
let prop_kfalse t k prop =

  t.prop_status <- 

    List.map 

      (fun (n, s) -> if n = prop then 

          match s with

            (* Mark property as k-false if it was unknown, l-true for l <
               k or invariant *)
            | PropUnknown -> (n, PropKFalse k)

            (* Fail if property was invariant *)
            | PropInvariant -> 
              raise (Failure "prop_kfalse")

            (* Fail if property was l-true for l >= k *)
            | PropKTrue l when l >= k -> 
              raise (Failure "prop_kfalse")

            (* Mark property as k-false if it was l-true for l < k *)
            | PropKTrue _ -> (n, PropKFalse k)

            (* Keep if property was false *)
            | PropFalse -> (n, s)

            (* Keep if property was l-false for l <= k *)
            | PropKFalse l when l <= k -> (n, s)

            (* Mark property as k-false *)
            | PropKFalse _ -> (n, PropKFalse k) 

        else (n, s))

      t.prop_status


(* Mark property as k-true *)
let prop_ktrue t k prop =

  t.prop_status <- 

    List.map 

      (fun (n, s) -> if n = prop then 

          match s with

            (* Mark as k-true if it was unknown *)
            | PropUnknown -> (n, PropKTrue k)

            (* Keep if it was l-true for l > k *)
            | PropKTrue l when l > k -> (n, s)

            (* Mark as k-true if it was l-true for l <= k *)
            | PropKTrue _ -> (n, PropKTrue k)

            (* Keep if it was invariant *)
            | PropInvariant -> (n, s)

            (* Keep if it was false for unknown l *)
            | PropFalse -> (n, PropFalse)

            (* Keep if property was l-false for l > k *)
            | PropKFalse l when l > k -> (n, s)

            (* Fail if property was l-false for l <= k *)
            | PropKFalse _ -> 
              raise (Failure "prop_kfalse") 

        else (n, s))

      t.prop_status


(* Update transition system from event list *)
let update_from_events trans_sys events = 

  (* Tail-recursive iteration *)
  let rec update_from_events' trans_sys invars prop_status cex = function 

    (* No more events, return new invariants and changed property status *)
    | [] -> (invars, prop_status, cex)

    (* Invariant discovered *)
    | (m, Event.Invariant t) :: tl -> 

      (* Property status if received invariant is a property *)
      let tl' =
        List.fold_left

          (fun accum (p, t') -> 

             (* Invariant is equal to property term? *)
             if Term.equal t t' then

               (* Inject property status event *)
               ((m, Event.PropStatus (p, PropInvariant)) :: accum)

             else

               accum)

          tl
          trans_sys.props

      in
      
      (* Add invariant to transtion system *)
      add_invariant trans_sys t;

      (* Continue with invariant added to accumulator *)
      update_from_events'
        trans_sys
        ((m, t) :: invars)
        prop_status
        cex 
        tl'

    (* Property found unknown *)
    | (_, Event.PropStatus (p, PropUnknown)) :: tl -> 

      (* Continue without changes *)
      update_from_events' trans_sys invars prop_status cex tl

    (* Property found true for k steps *)
    | (m, Event.PropStatus (p, (PropKTrue k as s))) :: tl -> 

      (* Change property status in transition system *)
      prop_ktrue trans_sys k p;

      (* Continue with propert status added to accumulator *)
      update_from_events'
        trans_sys
        invars
        ((m, (p, s)) :: prop_status) 
        cex
        tl

    (* Property found invariant *)
    | (m, Event.PropStatus (p, (PropInvariant as s))) :: tl -> 

      (* Change property status in transition system *)
      prop_invariant trans_sys p;

      (try 

         (* Add proved property as invariant *)
        add_invariant 
          trans_sys 
          (List.assoc p trans_sys.props)

       (* Skip if named property not found *)
       with Not_found -> ());

      (* Continue with propert status added to accumulator *)
      update_from_events'
        trans_sys 
        invars
        ((m, (p, s)) :: prop_status)
        cex
        tl

    (* Property found false *)
    | (m, Event.PropStatus (p, (PropFalse as s))) :: tl -> 

      (* Change property status in transition system *)
      prop_false trans_sys p;

      (* Continue with propert status added to accumulator *)
      update_from_events' 
        trans_sys
        invars
        ((m, (p, s)) :: prop_status) 
        cex
        tl

    (* Property found false after k steps *)
    | (m, Event.PropStatus (p, (PropKFalse k as s))) :: tl ->

      (* Change property status in transition system *)
      prop_kfalse trans_sys k p;

      (* Continue with propert status added to accumulator *)
      update_from_events' 
        trans_sys
        invars
        ((m, (p, s)) :: prop_status) 
        cex
        tl
        
    (* Counterexample for some properties *)
    | (m, Event.Counterexample (p, c)) :: tl -> 

      (* Skip and continue *)
      update_from_events' 
        trans_sys
        invars
        prop_status
        ((m, (p, c)) :: cex) 
        tl

  in

  update_from_events' trans_sys [] [] [] events


(* Return true if the property is proved invariant *)
let is_proved trans_sys prop = 

  try 

    (match List.assoc prop trans_sys.prop_status with
      | PropInvariant -> true
      | _ -> false)
        
  with Not_found -> false


(* Return true if the property is proved not invariant *)
let is_disproved trans_sys prop = 

  try 

    (match List.assoc prop trans_sys.prop_status with
      | PropKFalse _
      | PropFalse -> true
      | _ -> false)
        
  with Not_found -> false



(* Return true if all properties are either valid or invalid *)
let all_props_proved trans_sys =

  List.for_all
    (fun (p, _) -> 
       try 
         (match List.assoc p trans_sys.prop_status with
           | PropUnknown
           | PropKTrue _ -> false
           | PropInvariant
           | PropFalse 
           | PropKFalse _ -> true)
       with Not_found -> false)
    trans_sys.props 
      

(* Return declarations for uninterpreted symbols *)
let uf_symbols_of_trans_sys { state_vars } = 
  List.map StateVar.uf_symbol_of_state_var state_vars

let uf_defs_init { uf_defs_init } = uf_defs_init

let uf_defs_trans { uf_defs_trans } = uf_defs_trans

let uf_defs { uf_defs_init; uf_defs_trans } = uf_defs_init @ uf_defs_trans

(* Apply [f] to all uninterpreted function symbols of the transition
   system *)
let iter_state_var_declarations { state_vars } f = 
  List.iter (fun sv -> f (StateVar.uf_symbol_of_state_var sv)) state_vars
  
(* Apply [f] to all function definitions of the transition system *)
let iter_uf_definitions { uf_defs_init; uf_defs_trans } f = 
  List.iter (fun (u, (v, t)) -> f u v t) uf_defs_init;
  List.iter (fun (u, (v, t)) -> f u v t) uf_defs_trans
  

(* Extract a path in the transition system, return an association list
   of state variables to a list of their values *)
let path_from_model trans_sys get_model k =

  let rec path_from_model' accum state_vars = function 

    (* Terminate after the base instant *)
    | i when Numeral.(i < zero) -> accum

    | i -> 

      (* Get a model for the variables at instant [i] *)
      let model =
        get_model
          (List.map (fun sv -> Var.mk_state_var_instance sv i) state_vars)
      in

      (* Turn variable instances to state variables and sort list 

         TODO: It is not necessary to sort the list, if the SMT solver
         returns the list in the order it was input. *)
      let model' =
        List.sort
          (fun (sv1, _) (sv2, _) -> StateVar.compare_state_vars sv1 sv2)
          (List.map
             (fun (v, t) -> (Var.state_var_of_state_var_instance v, t))
             model)
      in

      (* Join values of model at current instant to result *)
      let accum' = 
        list_join
          StateVar.equal_state_vars
          model'
          accum
      in

      (* Recurse for remaining instants  *)
      path_from_model'
        accum'
        state_vars
        (Numeral.pred i)

  in

  path_from_model'
    (List.map (fun sv -> (sv, [])) (state_vars trans_sys))
    (state_vars trans_sys)
    k



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
