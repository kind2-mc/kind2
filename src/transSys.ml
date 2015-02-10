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

type source = 
  | Lustre of LustreNode.t list 
  | Native


type pred_def = (UfSymbol.t * (Var.t list * Term.t)) 

(* Current status of a property *)
type prop_status =

  (* Status of property is unknown *)
  | PropUnknown

  (* Property is true for at least k steps *)
  | PropKTrue of int

  (* Property is true in all reachable states *)
  | PropInvariant 

  (* Property is false at some step *)
  | PropFalse of (StateVar.t * Term.t list) list


(* A property of a transition system *)
type property = 

  { 

    (* Identifier for the property *)
    prop_name : string;

    (* Source of the property *)
    prop_source : TermLib.prop_source;

    (* Term with variables at offsets [prop_base] and [prop_base - 1] *)
    prop_term : Term.t;

    (* Current status *)
    mutable prop_status : prop_status 

  }

(* A contract of a transition system. *)
type contract =
    { (* Name of the contract. *)
      name : string ;
      (* Property corresponding to this contract, at [trans_init]. *)
      prop : Term.t ;
      (* Source of the contract. *)
      source : TermLib.contract_source ;
      (* Requirements of the contract. *)
      requires : Term.t list ;
      (* Ensures of the contract. *)
      ensures: Term.t list ;
      (* Current status. *)
      mutable status : prop_status }


(* Return the length of the counterexample *)
let length_of_cex = function 

  (* Empty counterexample has length zero *)
  | [] -> 0

  (* Length of counterexample from first state variable *)
  | (_, l) :: _ -> List.length l


let pp_print_prop_status_pt ppf = function 
  | PropUnknown -> Format.fprintf ppf "unknown"
  | PropKTrue k -> Format.fprintf ppf "true-for %d" k
  | PropInvariant -> Format.fprintf ppf "invariant"
  | PropFalse [] -> Format.fprintf ppf "false"
  | PropFalse cex -> Format.fprintf ppf "false-at %d" (length_of_cex cex)


(* Property status is known? *)
let prop_status_known = function 

  (* Property may become invariant or false *)
  | PropUnknown
  | PropKTrue _ -> false

  (* Property is invariant or false *)
  | PropInvariant
  | PropFalse _ -> true


(* Offset of state variables in initial state constraint *)
let init_base = Numeral.zero

(* Offset of primed state variables in transition relation *)
let trans_base = Numeral.one

(* Offset of primed state variables in properties and invariants *)
let prop_base = Numeral.zero


type t = {
  
  (* Scope of state variables *)
  scope: string list;

  (* Init and trans pairs of this system and its subsystems in
     topological order. *)
  uf_defs: (pred_def * pred_def) list ;

  (* State variables of top node *)
  state_vars: StateVar.t list ;

  (* Initial predicate of the system. *)
  init: pred_def ;

  (* Transition predicate of the system. *)
  trans: pred_def ;

  (* The direct subsystems of this system. *)
  subsystems: t list ;

  (* The length of the longest branch of the call graph underneath
     this system. *)
  max_depth : Numeral.t ;

  (* Properties of the transition system to prove invariant *)
  properties : property list;

  (* The contracts of this system. *)
  contracts : contract list ;

  (* The source which produced this system. *)
  source: source ;

  (* Invariants *)
  mutable invars: Term.t list;

  (* Systems instantiating this system, and for each instantiation a
     map from state variables of this system to the state variables of
     the instantiating system as well as a function to guard Boolean
     terms. *)
  mutable callers : 
    (t * (((StateVar.t * StateVar.t) list * (Term.t -> Term.t)) list)) list;

}

(* The init flag of a system. *)
let init_flag_of_trans_sys { scope } =
  StateVar.mk_init_flag scope
  |> Var.mk_state_var_instance

(* The depth input of a system. *)
let depth_input_of_trans_sys { scope } =
  StateVar.mk_depth_input scope
  |> Var.mk_const_state_var

(* The max depth input of a system. *)
let max_depth_input_of_trans_sys { scope } =
  StateVar.mk_max_depth_input scope
  |> Var.mk_const_state_var
           

(* Return the predicate for the initial state constraint *)
let init_uf_symbol { init = (s, _) } = s

(* Return the predicate for the transition relation *)
let trans_uf_symbol { trans = (s, _) } = s

(* Return the variables in the initial state constraint *)
let init_vars { init = (_, (v, _)) } = v

(* Return the variables in the transition relation *)
let trans_vars { trans = (_, (v, _)) } = v

(* Return the definition of the initial state constraint *)
let init_term { init = (_, (_, t)) } = t

(* Return the definition of the transition relation *)
let trans_term { trans = (_, (_, t)) } = t


(* Add entry for new system instantiation to the transition system *)
let add_caller callee caller c = 
 
  (* Fold over the association list and add to the existing entry, or
     to the end *)
  let rec add_caller' accum = function
    | [] ->  (caller, [c]) :: accum
    | (caller', c') :: tl when 
        caller'.scope = caller.scope -> (caller', (c :: c')) :: accum
    | h :: tl -> add_caller' (h :: accum) tl 
  in

  callee.callers <- add_caller' [] callee.callers

(* Instantiates some terms from a subsystem to a system calling
   it. System [subsys] is the subsystem [terms] comes from, [sys] is
   the system [terms] will be instantiated to. *)
let instantiate_terms_for_sys { callers } terms sys =
  try
    (* Looking for [sys] in the callers. *)
    List.assq sys callers
    (* Iterating on the list of maps and lift functions. *)
    |> List.map
         (fun (map, lift_fun) ->
          terms
          (* Applying lift function. *)
          |> List.map
               (fun t ->
                (* Substituting variables. *)
                Term.substitute_variables map t
                (* Applying lift function. *)
                |> lift_fun))
  with
  | Not_found -> []


(* Instantiates a term for all systems instantiating the input
   system. *)
let instantiate_term { callers } term =

  callers
  |> List.map
       ( fun (sys, maps) ->

         (* let print_map = *)
         (*   (\* Turns a map from state vars to terms into a string. *\) *)
         (*   let string_of_map map = *)
         (*     map *)
         (*     |> List.map *)
         (*          ( fun (v,t) -> *)
         (*            Printf.sprintf "(%s -> %s)" *)
         (*                           (StateVar.string_of_state_var v) *)
         (*                           (StateVar.string_of_state_var t) ) *)
         (*     |> String.concat ", " *)
         (*   in *)
           
         (*   List.map *)
         (*     (fun map -> *)
         (*      Printf.printf "  Mapping to [%s]:\n" *)
         (*                    (String.concat "/" sys.scope) ; *)
         (*      Printf.printf "  > %s\n\n" (string_of_map map) ) *)
         (* in *)
         
         (* Building one new term per instantiation mapping for
            sys. *)
         let terms =
           maps
           |> List.map
               (* For each map of this over-system, substitute the
                  variables of term according to map. *)
               ( fun (map,f) ->
                 Term.substitute_variables map term |> f )
         in

         sys, terms )

(* Inserts a system / terms pair in an associative list from systems
   to terms.  Updates the biding by the old terms and the new ones if
   it's already there, adds a new biding otherwise. *)
let insert_in_sys_term_map assoc_list ((sys,terms) as pair) =

  let rec loop prefix = function
      
    | (sys',terms') :: tail when sys == sys' ->
       (* Updating the binding and returning. *)
       List.rev_append
         prefix
         ( (sys, List.rev_append terms terms') :: tail )

    (* Looping. *)
    | head :: tail -> loop (head :: prefix) tail

    (* 'sys' was not there, adding the biding. *)
    | [] -> pair :: assoc_list
  in

  loop [] assoc_list


(* Returns true iff the input system has no parent systems. *)
let is_top { callers } = callers = []


(* Instantiates a term for the top system by going up the system
   hierarchy, for all instantiations of the input system. Returns the
   top system and the corresponding terms, paired with the
   intermediary systems and terms. Note that the input system term of
   the function will be in the result, either as intermediary or top
   level. *)
let instantiate_term_all_levels t term =

  let rec loop at_top intermediary = function
    | (sys, (term :: term_tail)) :: tail ->

      debug transSys "[loop] sys: %s" (sys.scope |> String.concat "/") in

       (* Instantiating this term upward. *)
       let at_top', intermediary', recursive' =
         instantiate_term sys term
         |> List.fold_left
              ( fun (at_top'', intermediary'', recursive'')
                    ((sys',_) as pair) ->

                      debug transSys "[loop] inst sys: %s" (sys'.scope |> String.concat "/") in

                if is_top sys' then
                  (* Top system, no need to recurse on these terms. *)
                  insert_in_sys_term_map at_top'' pair,
                  intermediary'',
                  recursive''
                else
                  (* Not the top system, need to memorize the terms
                     for the result and for recursion. *)
                  at_top'',
                  insert_in_sys_term_map intermediary'' pair,
                  insert_in_sys_term_map recursive'' pair )

              (at_top, intermediary, ((sys,term_tail) :: tail))
       in

       (* Making sure there at most one top system. *)
       assert (List.length at_top' <= 1) ;

       loop at_top' intermediary' recursive'

    (* No more terms for this system, looping. *)
    | (sys, []) :: tail -> loop at_top intermediary tail

    (* No more terms to instantiate. *)
    | [] ->
       ( match at_top with
         (* There should be exactly one top level system. *)
         | head :: [] ->
            (head, intermediary)
         | _ ->
            assert false )
  in


  if is_top t
  then (
    debug transSys "Instantiate: system is already top." in
    (* If the system is already the top one, there is no instantiating
       to do. *)
    (t, [term]), []
  ) else (
    debug transSys "Instantiate: system is not top." in
    loop [] [t, [term]] [t, [term]]
)


(* Instantiates a term for the top system by going up the system
   hierarchy, for all instantiations of the input system. *)
let instantiate_term_top t term =

  let rec loop at_top = function
      
    | (sys, ((term :: term_tail) as list)) :: tail ->
       
       (* Instantiating this term upward. *)
       ( match instantiate_term sys term with
           
         | [] ->
            (* Nothing, so sys is the top node. *)
            loop (List.rev_append list at_top)
                 tail

         | list' ->
            (* Sys is not the top node. *)
            loop at_top
                 (List.rev_append
                    (* Looping on the new (sys,terms) pairs... *)
                    list'
                    (* ...and the (sys,terms) pairs we haven't looked
                       at yet. *)
                    ((sys, term_tail)
                     :: tail)) )
         
    | (sys, []) :: tail -> loop at_top tail
                                
    | [] ->
       ( match at_top with
         (* If at_top is empty, 't' is already the top system. *)
         | [] -> [term]
         | list -> list )
  in

  loop [] (instantiate_term t term)

(* Number of times this system is instantiated in other systems. *)
let instantiation_count { callers } =
  callers
  |> List.fold_left
       ( fun sum (sys,maps) ->
         sum + (List.length maps) )
       0


(* Returns the contracts of a system. *)
let get_contracts { contracts } =
  contracts
  |> List.map
       ( fun { name ; source ; requires ; ensures ; status } ->
         name, source, requires, ensures, status )

(* For a system, returns [Some true] if all contracts are invariants,
   [Some false] if at least one of the contracts is falsified, and
   [None] otherwise --i.e. some contracts are unknown / k-true. *)
let verifies_contracts { contracts } =
  contracts
  |> List.fold_left
       ( fun bool_opt ->
         function
         | { status = PropInvariant } -> bool_opt
         | { status = PropFalse(_) } -> Some false
         | _ -> None )
       (Some true)

(* Returns the contracts of a system as a list of implications. *)
let get_contracts_implications { contracts } =
  contracts
  |> List.map
       ( fun { name ; requires ; ensures } ->
         (name,
          (* Building the implication between the requires and the
             ensures. *)
          Term.mk_implies
            [ Term.mk_and requires ;
              Term.mk_and ensures ]) )

let rec abstracted_subsystems_of_depth'
          result
          continuation
          (prefix,depth)
          ({subsystems ; max_depth ; contracts ; scope}) =
  (* if depth > Numeral.(to_int max_depth) then *)

  (*   (\* Name of the system. *\) *)
  (*   let name = *)
  (*     String.concat "-" scope *)
  (*   in *)

  (*   Format.printf *)
  (*     "Depth > max_depth for %s (%s,%d).\n" *)
  (*     name prefix depth ; *)

  (*   (\* Nothing will be abstracted in this branch. *\) *)
  (*   continue result continuation (prefix,depth) [] *)

  (* else ( *)

    (* Name of the system. *)
    let name =
      String.concat "-" scope
    in

    (* Format.printf *)
    (*   "Looking at %s (%s,%d).\n" *)
    (*   name prefix depth ; *)

    (* Prefix update function. *)
    let prefix' sep =
      if prefix = "" then name
      else
        [ prefix ; name ] |> String.concat sep
    in

    (* Does this node have contracts? *)
    ( match contracts with
      | [] ->
         (* Format.printf *)
         (*   "No contracts.\n" ; *)
         (* System does not change the abstraction depth since it has
            no contracts. *)
         continue
           result
           continuation
           (* Separating prefix by ["./"] to indicate the system has
              no contracts and does not modify abstraction depth. *)
           (prefix' "./", depth)
           subsystems
      | _ ->
         (* Is this subsystem abstracted away? *)
         if depth > 0 then (
           (* Format.printf *)
           (*   "Not abstracting.\n" ; *)
           (* It's not, continuing with subsystems. *)
           continue
             result
             continuation
             (prefix' ".", depth - 1)
             subsystems
         ) else (
           (* Format.printf *)
           (*   "Abstracting.\n" ; *)
           (* Subsystem is abstracted away, continuing. *)
           continue
             ((prefix' ".") :: result)
             continuation
             (prefix,depth)
             [] ) )

and continue result continuation ((prefix,depth) as info) = function
  | [] ->
     (* No subsystem provided, looking at continuation. *)

     ( match continuation with

       | [] ->
          (* Continuation is empty, we're done. *)
          result

       | (_, _, []) :: continuation_tail ->
          (* Head of the continuation contains no subsystems,
             looping. *)
          continue result continuation_tail info []

       | (prefix, depth, sys :: sys_tail) :: continuation_tail ->
          (* A subsystem is in the continuation, let's check it out. *)
          abstracted_subsystems_of_depth'
            result
            ((prefix,depth,sys_tail) :: continuation_tail)
            (prefix,depth)
            sys )

  | subsystem :: sub_tail ->
     (* There is a subsystem to handle. *)
     abstracted_subsystems_of_depth'
       result
       (* Adding the tail of subsystems to the continuation. *)
       ((prefix,depth,sub_tail) :: continuation)
       info
       subsystem

(* [abstracted_subsystems_of_depth sys depth] returns the subsystems
   of [sys] abstracted when the abstraction depth is [depth]. *)
let abstracted_subsystems_of_depth sys depth =

  abstracted_subsystems_of_depth'
    []
    []
    ("", if sys.contracts = [] then depth else depth + 1)
    sys


(* Returns the subsystems of a system. *)
let get_subsystems { subsystems } = subsystems

(* Return the input used to create the transition system *)
let get_scope t = t.scope

(* Name of the system. *)
let get_name t = t.scope |> String.concat "/"

(* Returns all the subsystems of a transition system, including that
   system, by reverse topological order. *)
let get_all_subsystems sys =

  let insert_subsystem ({ subsystems } as sys) list =
    let rec loop rev_prefix = function
      | sys' :: _
           when sys == sys' ->
         (* [sys] is already in the list, nothing to do. *)
         list
      | ({ subsystems = subsystems' } as sys') :: tail ->
         if List.memq sys subsystems' then
           (* [sys] is a subsystem of [sys'], inserting here. *)
           sys :: sys' :: tail |> List.rev_append rev_prefix
         else
           (* No relation between [sys] and [sys'], looping. *)
           loop (sys' :: rev_prefix) tail
      | [] -> sys :: rev_prefix |> List.rev
    in
    loop [] list
  in

  let rec iterate_over_subsystems ({subsystems} as sys) continuation result =
    insert_subsystem sys result
    |> continue subsystems continuation

  and continue subsystems continuation result =

    match subsystems with
    | [] ->

       (* No subsystems, let's look at the continuation. *)
       ( match continuation with
         | [] ->
            (* Nothing to continue with, returning result. *)
            result

         | [] :: continuation_tail ->
            (* Head of the continuation is empty, looping on its
               tail. *)
            continue
              [] continuation_tail result

         | (sys :: continuation_head) :: continuation_tail ->
            (* Found one system to insert in the result. *)
            iterate_over_subsystems
              sys (continuation_head :: continuation_tail) result )

    | sub_sys :: sub_sys_tail ->
       (* There are some subsystems to insert, looping on the head and
          adding the rest to the continuation. *)
       iterate_over_subsystems
         sub_sys (sub_sys_tail :: continuation) result
  in
 
  iterate_over_subsystems sys [] []

let pp_print_state_var ppf state_var = 

  Format.fprintf ppf
    "@[<hv 1>(%a@ %a%t%t%t)@]" 
    StateVar.pp_print_state_var state_var
    Type.pp_print_type (StateVar.type_of_state_var state_var)
    (function ppf -> 
      if StateVar.is_const state_var then Format.fprintf ppf "@ :const")
    (function ppf -> 
      if StateVar.is_input state_var then Format.fprintf ppf "@ :input")
    (function ppf -> 
      if StateVar.for_inv_gen state_var then Format.fprintf ppf "@ :for-inv-gen")
  
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

let pp_print_uf_defs 
    ppf
    ((init_uf_symbol, (init_vars, init_term)), 
     (trans_uf_symbol, (trans_vars, trans_term))) = 

  Format.fprintf ppf
    "@[<hv 2>(define-pred-init@ %a@ @[<hv 2>(%a)@]@ %a)@]@,\
     @[<hv 2>(define-pred-trans@ %a@ @[<hv 2>(%a)@]@ %a)@]"
    UfSymbol.pp_print_uf_symbol init_uf_symbol
    (pp_print_list pp_print_var "@ ") init_vars
    Term.pp_print_term init_term
    UfSymbol.pp_print_uf_symbol trans_uf_symbol
    (pp_print_list pp_print_var "@ ") trans_vars
    Term.pp_print_term trans_term


let pp_print_prop_source ppf = function 
  | TermLib.PropAnnot _ -> Format.fprintf ppf ":user"
  | TermLib.Contract _ -> Format.fprintf ppf ":contract"
  | TermLib.SubRequirement _ -> Format.fprintf ppf ":requirement"
  | TermLib.Generated p -> Format.fprintf ppf ":generated"
  | TermLib.Instantiated _ -> Format.fprintf ppf ":subsystem"

let pp_print_contract_source ppf = function 
  | TermLib.ContractAnnot _ -> Format.fprintf ppf ":user"

let pp_print_property ppf { prop_name; prop_source; prop_term; prop_status } = 

  Format.fprintf 
    ppf
    "@[<hv 1>(%s@ %a@ %a@ %a)@]"
    prop_name
    Term.pp_print_term prop_term
    pp_print_prop_source prop_source
    pp_print_prop_status_pt prop_status

let pp_print_caller ppf (m, t) = 

  Format.fprintf ppf 
    "@[<hv 1>(%a)@,%a@]"
    (pp_print_list 
       (fun ppf (s, t) ->
          Format.fprintf ppf
            "@[<hv 1>(@[<hv>%a@]@ @[<hv>%a@])@]"
            StateVar.pp_print_state_var s
            StateVar.pp_print_state_var t)
       "@ ")
    m
    Term.pp_print_term (t Term.t_true)



let pp_print_callers ppf (t, c) = 
  
  Format.fprintf ppf
    "@[<hv 1>(%a@ %a)@]"
    (pp_print_list Format.pp_print_string ".") t.scope
    (pp_print_list pp_print_caller "@ ") c

let pp_print_contract
      ppf { name ; source ; requires ; ensures ; status } =
  Format.fprintf
    ppf
    "@[<hv 2>%s %a (%a)@ @[<v>requires: @[<hv 2>%a@]@ ensures:  @[<hv 2>%a@]@]@]"
    name
    pp_print_contract_source source
    pp_print_prop_status_pt status
    (pp_print_list Term.pp_print_term "@ ") requires
    (pp_print_list Term.pp_print_term "@ ") ensures


let pp_print_trans_sys 
    ppf
    ({ uf_defs;
       state_vars;
       properties;
       contracts;
       invars;
       source;
       max_depth;
       callers } as trans_sys) = 

  Format.fprintf 
    ppf
    "@[<v>@[<hv 2>(state-vars@ (@[<v>%a@]))@]@,\
          %a@,\
          @[<hv 2>(init@ (@[<v>%a@]))@]@,\
          @[<hv 2>(trans@ (@[<v>%a@]))@]@,\
          @[<hv 2>(props@ (@[<v>%a@]))@]@,\
          @[<hv 2>(contracts@ (@[<v>%a@]))@]@,\
          @[<hv 2>(invar@ (@[<v>%a@]))@]@,\
          @[<hv 2>(source@ (@[<v>%a@]))@]@,\
          @[<hv 2>(max depth@ %a)@]@,\
          @[<hv 2>(callers@ (@[<v>%a@]))@]@."
    (pp_print_list pp_print_state_var "@ ") state_vars
    (pp_print_list pp_print_uf_defs "@ ") (uf_defs)
    Term.pp_print_term (init_term trans_sys)
    Term.pp_print_term (trans_term trans_sys)
    (pp_print_list pp_print_property "@ ") properties
    (pp_print_list pp_print_contract "@ ") contracts
    (pp_print_list Term.pp_print_term "@ ") invars
    (pp_print_list (fun ppf { LustreNode.name } -> LustreIdent.pp_print_ident false ppf name) "@ ") (match source with Lustre l -> l | _ -> [])
    Numeral.pp_print_numeral max_depth
    (pp_print_list pp_print_callers "@,") callers


(* Determine the required logic for the SMT solver 

   TODO: Fix this to QF_UFLIA for now, dynamically determine later *)
let get_logic _ = ((Flags.smtlogic ()) :> Term.logic)


(* Return the state variables of the transition system *)
let state_vars t = t.state_vars

(* Return the input used to create the transition system *)
let get_source t = t.source

(* Returns the max depth of a transition system. *)
let get_max_depth t = t.max_depth

(* Create a transition system *)
let mk_trans_sys
      scope state_vars init trans
      subsystems props contracts source =

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

  (* Goes through the subsystems and constructs the list of
     uf_defs. *)
  let rec get_uf_defs result = function
    | { uf_defs } :: tail ->

       (* Removing uf_defs of the subsystem from the result to ensure
          topological order. *)
       let result' =
         result
         |> List.filter
              ( fun pair ->
                not (List.mem pair uf_defs) )
       in

       get_uf_defs
         (* Adding uf_defs of the subsystem to the result. *)
         (List.concat [ uf_defs ; result' ])
         tail

    | [] -> result
  in

  let max_depth =
    let rec loop max_so_far = function
      | [] ->
         (* No more subsystems, returning max depth. *)
         max_so_far
      | { max_depth } :: tail ->
         (* Keeping the max of the max_depth, looping. *)
         loop Numeral.(max (succ max_depth) max_so_far) tail
    in
    loop Numeral.zero subsystems
  in

  let contracts =
    contracts
    |> List.map
         (fun (name, source, reqs, ens) ->
          { name = name ;
            prop =
              Term.mk_implies
                [ Term.mk_and reqs ;
                  Term.mk_and ens ] ;
            source = source ;
            requires = reqs ;
            ensures = ens ;
            status = PropUnknown })
  in

  let system = 
    { scope = scope;
      uf_defs = get_uf_defs [ (init, trans) ] subsystems ;
      state_vars =
        state_vars |> List.sort StateVar.compare_state_vars ;
      init = init ;
      trans = trans ;
      properties =
        props
        |> List.map
             (fun (n, s, t) -> 
              { prop_name = n;
                prop_source = s; 
                prop_term = t; 
                prop_status = PropUnknown }) ;
      contracts = contracts ;
      subsystems = subsystems ;
      max_depth = max_depth ;
      source = source ;
      invars = invars_of_types ;
      callers = []; }
  in

  debug transSys "Done creating system:@ " in
  debug transSys "%a" pp_print_trans_sys system in

  system

(* Return the variables of the transition system between given instants *)
let rec vars_of_bounds' state_vars lbound ubound accum =

  (* Return when upper bound below lower bound *)
  if Numeral.(ubound < lbound)
  then accum
  else
    state_vars

    |> List.rev
    (* Add state variables at upper bound instant  *)
    |> List.fold_left
         ( fun accum sv -> 
           Var.mk_state_var_instance sv ubound :: accum )
         accum

    (* Recurse to next lower bound *)
    |> vars_of_bounds' state_vars lbound Numeral.(pred ubound)

(* Returns the variables of the transition system between two
   bounds. *)
let vars_of_bounds
      trans_sys lbound ubound =
  vars_of_bounds' trans_sys.state_vars lbound ubound []


(* Declares variables of the transition system between two offsets. *)
let declare_vars_of_bounds
      t declare lbound ubound =
  (* Declaring non-constant variables. *)
  vars_of_bounds t lbound ubound
  |> Var.declare_vars declare


(* Instantiate the initial state constraint to the bound *)
let init_of_bound t i = 

  let init_term =
    init_term t
  in

  (* Bump bound if greater than zero *)
  if Numeral.(i = zero)
  then init_term
  else Term.bump_state i init_term


(* Instantiate the transition relation to the bound. *)
let trans_of_bound t i = 

  let trans_term = trans_term t in

  (* Bump bound if greater than zero *)
  if Numeral.(i = one)
  then trans_term 
  else Term.bump_state (Numeral.(i - one)) trans_term

(* Builds a call to the transition relation function linking state [k]
   and [k']. *)
let trans_fun_of { uf_defs } k k' =
  match List.rev uf_defs with
    (* uf_defs are in topological order, so the last one is the top one. *)
    | (_, (trans_uf, (vars,_))) :: _ ->
      let trans_base_pre = Numeral.( pred trans_base ) in

      let rec bump_as_needed res = function
        | var :: tail ->
          let bumped_term =
            if Var.is_const_state_var var then Term.mk_var var
            else (
              let offset = Var.offset_of_state_var_instance var in
              if Numeral.( offset = trans_base ) then
                (* Unprimed state variable, bumping to k'. *)
                Var.bump_offset_of_state_var_instance
                  Numeral.( k' - offset ) var
                  |> Term.mk_var
              else if Numeral. (offset = trans_base_pre ) then
                (* Primed state variable, bumping to k. *)
                Var.bump_offset_of_state_var_instance
                  Numeral.( k - offset ) var
                  |> Term.mk_var
              else
                (* This cannot happen. *)
                assert false
            )
          in
          bump_as_needed (bumped_term :: res) tail
        | [] -> List.rev res
      in
      
      Term.mk_uf trans_uf (bump_as_needed [] vars)
        
    | _ -> assert false

  (* debug transSys "@[<v>%a@]" *)
  (*   (Lib.pp_print_list StateVar.pp_print_state_var "@,") t.state_vars in *)

  (* (\* Variables at [k]. *\) *)
  (* let vars_at_k' = vars_of_bounds t k' k' in *)

  (* debug transSys "@[<v>%a@]" *)
  (*   (Lib.pp_print_list Var.pp_print_var "@,") vars_at_k' in *)

  (* (\* Variables at [k'] appended to [vars_at_k], as terms. *\) *)
  (* let all_vars = *)
  (*   vars_of_bounds' t k k vars_at_k' *)
  (*   |> List.map Term.mk_var *)
  (* in *)

  (* debug transSys "@[<v>%a@]" *)
  (*   (Lib.pp_print_list Term.pp_print_term "@,") all_vars in *)

  (* (\* Building the uf application. *\) *)
  (* Term.mk_uf (trans_uf_symbol t) all_vars *)


(* Instantiate the initial state constraint to the bound *)
let invars_of_bound t i = 

  (* Create conjunction of property terms *)
  let invars_0 = Term.mk_and t.invars in 

  (* Bump bound if greater than zero *)
  if Numeral.(i = zero) then invars_0 else Term.bump_state i invars_0

(* Constrains the top level depth and max depth inputs. *)
let depth_inputs_constraint sys max_depth =

  (* Building the constraint on the depth input and the max depth
     input for input system. *)
  Term.mk_and

    [ (* Depth input constraint. *)
      Term.mk_eq
        [ (* Getting depth input var. *)
          depth_input_of_trans_sys sys
          (* Creating corresponding term. *)
          |> Term.mk_var ;

          (* Value for depth input is always zero. *)
          Numeral.zero |> Term.mk_num ] ;

      (* Max depth input constraint. *)
      Term.mk_eq
        [ (* Getting max depth input var. *)
          max_depth_input_of_trans_sys sys
          (* Creating corresponding term. *)
          |> Term.mk_var ;
          
          let _ =
            (* Making sure value for max depth input is legal. *)
            assert Numeral.(max_depth <= sys.max_depth)
          in
          (* Using specified value. *)
          max_depth |> Term.mk_num ] ]

(* Creates the constraints setting the depth input constant to a
   value. *)
let abstraction_depth_input_constraint sys value =
  Term.mk_eq
    [ depth_input_of_trans_sys sys |> Term.mk_var ;
      Term.mk_num value ]

(* The invariants of a transition system. *)
let get_invars { invars } = invars


(* Instantiate terms in association list to the bound *)
let named_terms_list_of_bound l i = 

  (* Bump bound if greater than zero *)
  if
    Numeral.(i = zero)
  then
    List.map 
      (fun { prop_name; prop_term } -> 
         (prop_name, prop_term)) 
      l
  else
    List.map 
      (fun { prop_name; prop_term } -> 
         (prop_name, Term.bump_state i prop_term)) 
      l
      

(* Instantiate all properties to the bound *)
let props_list_of_bound t i = 
  named_terms_list_of_bound t.properties i


(* Instantiate all properties to the bound *)
let props_of_bound t i = 
  Term.mk_and (List.map snd (props_list_of_bound t i))

(* Get property by name *)
let property_of_name t name =

  List.find
    (fun { prop_name } -> prop_name = name )
    t.properties

(* Get property by name *)
let named_term_of_prop_name t name =

  (property_of_name t name).prop_term

(* Finds the subsystem of [t] corresponding to [scope]. *)
let subsystem_of_scope t scope =

  (* Goes through [t] and its subsystems looking for [scope], stopping
     at the first occurence. Fails if [scope] cannot be found. *)
  let rec loop subs_left t =
    (* Is [t] the right system? *)
    if t.scope = scope then t
    else
    (* Its not, checking if it has any subsystems. *)
    ( match t.subsystems with
      | [] ->
        (* It does not, checking the other subsystems. *)
        (match subs_left with
          | [] ->
            (* Could not find [scope], failing. *)
            raise
              (Invalid_argument
                (Printf.sprintf
                  "Unexpected scope [%s]."
                  (String.concat "/" scope)))
          | sub :: subs ->
            (* Looping on remaining systems. *)
            loop subs sub)
      | sub :: subs ->
        (* System has subsystems, looping. *)
        loop (List.rev_append subs subs_left) sub )
  in

  (* Looking for the right subsystem in t *)
  loop [] t

(* Add an invariant to the transition system *)
let add_scoped_invariant t scope invar =
  (* Finding the right system. *)
  let sys = subsystem_of_scope t scope in
  (* Adding invariant to the right system. *)
  sys.invars <- invar :: sys.invars

(* Add an invariant to the transition system *)
let add_invariant t invar = add_scoped_invariant t t.scope invar

(* Return current status of all properties *)
let get_prop_status_all t = 
  
  List.map 
    (fun { prop_name; prop_status } -> (prop_name, prop_status))
    t.properties

(* Return current status of all properties *)
let get_prop_status_all_unknown t = 

  List.fold_left 
    (function accum -> function 

       | { prop_name; prop_status } 
         when not (prop_status_known prop_status) -> 

         (prop_name, prop_status) :: accum 

       | _ -> accum)
    []
    t.properties


(* Return current status of property *)
let get_prop_status trans_sys p = 

  try 

    (property_of_name trans_sys p).prop_status

  with Not_found -> PropUnknown


(* Mark property as invariant *)
let set_prop_invariant t prop =

  (* Get property by name *)
  let p = property_of_name t prop in

  (* Modify status *)
  p.prop_status <- 

    (* Check current status *)
    match p.prop_status with

      (* Mark property as invariant if it was unknown, k-true or
         invariant *)
      | PropUnknown
      | PropKTrue _
      | PropInvariant -> PropInvariant

      (* Fail if property was false or k-false *)
      | PropFalse _ -> raise (Failure "prop_invariant")

(* Changes the status of k-true properties as unknown. Used for
   contract-based analysis when lowering the abstraction depth. Since
   the predicates have changed they might not be k-true anymore. *)
let reset_prop_ktrue_to_unknown t =
  t.properties
  |> List.iter
       (fun ( { prop_status } as prop) ->
        match prop_status with
        | PropKTrue _ -> prop.prop_status <- PropUnknown
        | _ -> ())

let rec pp_print_trans_sys_contract_view ppf sys =
  Format.fprintf
    ppf
    "@[<hv 2>sys %s@ @[<v>@[<hv 2>contracts:@ %a@]@,@[<hv 2>properties:@ %a@]@,\
     @[<hv 2>subsystems:@ %a@]@]@]"
    (get_name sys)
    (pp_print_list pp_print_contract "@ ") sys.contracts
    (pp_print_list pp_print_property "@ ") sys.properties
    (pp_print_list pp_print_trans_sys_contract_view "@ ") sys.subsystems

(* Mark property as k-false *)
let set_prop_false t prop cex =

  (* Get property by name *)
  let p = property_of_name t prop in

  (* Modify status *)
  p.prop_status <- 

    (* Check current status *)
    match p.prop_status with

      (* Mark property as k-false if it was unknown, l-true for l <
         k or invariant *)
      | PropUnknown -> PropFalse cex

      (* Fail if property was invariant *)
      | PropInvariant -> 
        raise (Failure "prop_false")

      (* Fail if property was l-true for l >= k *)
      | PropKTrue l when l > (length_of_cex cex) -> 
        raise (Failure "prop_false")

      (* Mark property as false if it was l-true for l < k *)
      | PropKTrue _ -> PropFalse cex

      (* Keep if property was l-false for l <= k *)
      | PropFalse cex' when (length_of_cex cex') <= (length_of_cex cex) -> 
        p.prop_status

      (* Mark property as k-false *)
      | PropFalse _ -> PropFalse cex


(* Mark property as k-true *)
let set_prop_ktrue t k prop =

  (* Get property by name *)
  let p =
    try
      property_of_name t prop
    with
    | Not_found ->
       Format.printf
         "Trying to set [%s] true at %d on system [%s].@ "
         prop
         k
         (get_name t) ;
       raise Not_found
  in

  (* Modify status *)
  p.prop_status <- 

    (* Check current status *)
    match p.prop_status with

      (* Mark as k-true if it was unknown *)
      | PropUnknown -> PropKTrue k

      (* Keep if it was l-true for l > k *)
      | PropKTrue l when l > k -> p.prop_status

      (* Mark as k-true if it was l-true for l <= k *)
      | PropKTrue _ -> PropKTrue k

      (* Keep if it was invariant *)
      | PropInvariant -> p.prop_status

      (* Keep if property was l-false for l > k *)
      | PropFalse cex when (length_of_cex cex) > k -> p.prop_status

      (* Fail if property was l-false for l <= k *)
      | PropFalse _ -> 
        raise (Failure "prop_kfalse") 


(* Mark property status *)
let set_prop_status t p = function

  | PropUnknown -> ()

  | PropKTrue k -> set_prop_ktrue t k p

  | PropInvariant -> set_prop_invariant t p

  | PropFalse c -> set_prop_false t p c

(* Return true if the property is proved invariant *)
let is_proved t prop = 

  try 
    ( match (property_of_name t prop).prop_status with
      | PropInvariant -> true
      | _ -> false )
        
  with
    Not_found -> false


(* Return true if the property is proved not invariant *)
let is_disproved t prop = 

  try 
    ( match (property_of_name t prop).prop_status with
      | PropFalse _ -> true
      | _ -> false )
        
  with
    Not_found -> false



(* Return true if all properties are either valid or invalid *)
let all_props_proved t =

  List.for_all
    (fun p -> 
       try 
         (match p.prop_status with
           | PropUnknown
           | PropKTrue _ -> false
           | PropInvariant
           | PropFalse _ -> true)
       with Not_found -> false)
    t.properties

(* Return declarations for uninterpreted symbols *)
let uf_symbols_of_trans_sys { state_vars } = 
  List.map StateVar.uf_symbol_of_state_var state_vars

(* Return uninterpreted function symbol definitions sorted by
   topological order. *)
let uf_defs { uf_defs } =
  uf_defs
  |> List.fold_left
       ( fun list (init,trans) ->
         (* We'll reverse for topological order, so trans is first. *)
         trans :: init :: list )
       []
  (* Reversing for topological order. *)
  |> List.rev

(* Return uninterpreted function symbol definitions as pairs of
   initial state and transition relation definitions sorted by
   topological order. *)
let uf_defs_pairs { uf_defs } = uf_defs
      
 

(* Return [true] if the uninterpreted symbol is an initial state constraint *)
let is_init_uf_def { uf_defs } uf_symbol = 

  uf_defs
  |> List.exists
       (function ((i, _), _) ->
                 UfSymbol.equal_uf_symbols uf_symbol i)

(* Return [true] if the uninterpreted symbol is a transition relation *)
let is_trans_uf_def { uf_defs } uf_symbol = 

  uf_defs
  |> List.exists
       (function (_, (t, _)) ->
                 UfSymbol.equal_uf_symbols uf_symbol t)
 

(* Apply [f] to all uninterpreted function symbols of the transition
   system *)
let iter_state_var_declarations { state_vars } f = 
  List.iter (fun sv -> f (StateVar.uf_symbol_of_state_var sv)) state_vars
  
(* Apply [f] to all function definitions of the transition system *)
let iter_uf_definitions t f = 
  uf_defs_pairs t
  |> List.iter 
       (fun ((ui, (vi, ti)), (ut, (vt, tt))) -> f ui vi ti; f ut vt tt)

(* Define uf definitions, declare constant state variables and declare
   variables from [lbound] to [upbound]. *)
let init_define_fun_declare_vars_of_bounds
      ?(sub_define_top_only = false)
      t define declare lbound ubound =

  ( if sub_define_top_only then
      match t.callers with
      | [] ->
         (* Define ufs. *)
         iter_uf_definitions t define
      | _ -> ()
    else
      iter_uf_definitions t define ) ;

  let l_vars = vars_of_bounds t lbound lbound in

  (* Declaring constant variables. *)
  Var.declare_constant_vars declare l_vars ;

  (* Declaring other variables. *)
  declare_vars_of_bounds t declare lbound ubound
  
  

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


(* Return true if the value of the term in some instant satisfies [pred] *)
let rec exists_eval_on_path' uf_defs p term k path =

  try 

    (* Create model for current state, shrink path *)
    let model, path' = 
      List.fold_left 
        (function (model, path) -> function 

           (* No more values for one state variable *)
           | (_, []) -> raise Exit

           (* Take the first value for state variable *)
           | (sv, h :: tl) -> 

             let v = Var.mk_state_var_instance sv Numeral.zero in

             debug transSys 
                 "exists_eval_on_path' at k=%a: %a is %a"
                 Numeral.pp_print_numeral k
                 StateVar.pp_print_state_var sv
                 Term.pp_print_term h
             in

             (* Add pair of state variable and value to model, continue
                with remaining value for variable on path *)
             ((v, h) :: model, (sv, tl) :: path)

        )
        ([], [])
        path
    in

    (* Evaluate term in model *)
    let term_eval = Eval.eval_term uf_defs model term in

    debug transSys 
        "exists_eval_on_path' at k=%a: %a is %a"
        Numeral.pp_print_numeral k
        Term.pp_print_term term
        Eval.pp_print_value term_eval
    in

    (* Return true if predicate holds *)
    if p term_eval then true else

      (* Increment instant *)
      let k' = Numeral.succ k in

      (* Continue checking predicate on path *)
      exists_eval_on_path' uf_defs p term k' path'

  (* Predicate has never been true *)
  with Exit -> false 


(* Return true if the value of the term in some instant satisfies [pred] *)
let exists_eval_on_path uf_defs pred term path = 
  exists_eval_on_path' uf_defs pred term Numeral.zero path


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
