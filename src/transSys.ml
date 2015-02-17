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
  | PropFalse of (StateVar.t * Model.term_or_lambda list) list


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
      (* Source of the contract. *)
      source : TermLib.contract_source ;
      (* Requirements of the contract. *)
      requires : Term.t list ;
      (* Ensures of the contract. *)
      ensures: Term.t list ;

      (* Status of the contract. *)
      mutable status: prop_status }


(* Return the length of the counterexample *)
let length_of_cex = function 

  (* Empty counterexample has length zero *)
  | [] -> 0

  (* Length of counterexample from first state variable *)
  | (_, l) :: _ -> List.length l

(* Pretty prints an abstraction. *)
let pp_print_abstraction ppf =
  Format.fprintf
    ppf
    "@[<v>%a@]"
    (pp_print_list
       (pp_print_list Format.pp_print_string ".")
       ",@,")


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

(* Stores a list of systems to abstract, by scope. *)
type abstraction = string list list


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

  (* Properties of the transition system to prove invariant *)
  properties : property list ;

  (* The contracts of this system. *)
  contracts : ( StateVar.t * contract list) option ;

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
let get_contracts = function
  | { contracts = None } -> []
  | { contracts = Some(_,list) } ->
     list
     |> List.map
          ( fun { name ; source ; requires ; ensures } ->
            name, source, requires, ensures )

(* (\* For a system, returns [Some true] if all contracts are invariants, *)
(*    [Some false] if at least one of the contracts is falsified, and *)
(*    [None] otherwise. *\) *)
(* let verifies_contracts { properties } = *)
(*   contracts *)
(*   |> List.fold_left *)
(*        ( fun bool_opt -> *)
(*          function *)
(*          | { source = TermLib.Contract _ ; status } -> *)
(*             ( match status with *)
(*               | PropInvariant -> bool_opt *)
(*               |  *)
(*          | { status = PropFalse(_) } -> Some false *)
(*          | _ -> None ) *)
(*        (Some true) *)

(* (\* Returns the contracts of a system as a list of implications. *\) *)
(* let get_contracts_implications { contracts } = *)
(*   contracts *)
(*   |> List.map *)
(*        ( fun { name ; requires ; ensures } -> *)
(*          (name, *)
(*           (\* Building the implication between the requires and the *)
(*              ensures. *\) *)
(*           Term.mk_implies *)
(*             [ Term.mk_and requires ; *)
(*               Term.mk_and ensures ]) ) *)


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

let pp_print_trans_sys_name ppf { scope } =
  Format.fprintf
    ppf "%a"
    (pp_print_list Format.pp_print_string ".")
    scope

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
    "@[<hv 2>\
     %s %a@ \
     status:   %a@ \
     @[<v>\
     requires: @[<hv>%a@]@ \
     ensures:  @[<hv>%a@]@]@]"
    name
    pp_print_contract_source source
    pp_print_prop_status_pt status
    (pp_print_list Term.pp_print_term "@ ") requires
    (pp_print_list Term.pp_print_term "@ ") ensures

let pp_print_contracts ppf = function
  | None -> Format.fprintf ppf "None"
  | Some (actlit,contracts) ->
     Format.fprintf
       ppf
       "@[<hv>\
        Actlit: %a@ \
        @[<v 2>Contracts:@ %a@]"
       StateVar.pp_print_state_var actlit
       (pp_print_list pp_print_contract "@ ") contracts


let pp_print_trans_sys 
    ppf
    ({ uf_defs;
       state_vars;
       properties;
       contracts;
       invars;
       source;
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
          @[<hv 2>(callers@ (@[<v>%a@]))@]@."
    (pp_print_list pp_print_state_var "@ ") state_vars
    (pp_print_list pp_print_uf_defs "@ ") (uf_defs)
    Term.pp_print_term (init_term trans_sys)
    Term.pp_print_term (trans_term trans_sys)
    (pp_print_list pp_print_property "@ ") properties
    pp_print_contracts contracts
    (pp_print_list Term.pp_print_term "@ ") invars
    (pp_print_list (fun ppf { LustreNode.name } -> LustreIdent.pp_print_ident false ppf name) "@ ") (match source with Lustre l -> l | _ -> [])
    (pp_print_list pp_print_callers "@,") callers


(* Determine the required logic for the SMT solver 

   TODO: Fix this to QF_UFLIA for now, dynamically determine later *)
let get_logic _ = ((Flags.smtlogic ()) :> Term.logic)


(* Return the state variables of the transition system *)
let state_vars t = t.state_vars

(* Return the input used to create the transition system *)
let get_source t = t.source

(* Returns [Some (e,e')] iff [list] contains two elements [e] and [e']
   such that [f(e) == f(e')]. Not that this uses PHYSICAL
   comparison. *)
let find_element_clash f list =
  let rec loop = function
    | [] ->
       (* No clash. *)
       None
    | e :: tail ->
       ( match tail
               (* Looking for an element in [tail]... *)
               |> List.find
                    (* ...which clashes with [e] modulo [f]. *)
                    (fun e' -> f e == f e')
         with
         (* Clash detected. *)
         | e' -> Some (e,e')
         (* No clash, looping. *)
         | exception Not_found -> loop tail )
  in
  loop list

(* Create a transition system *)
let mk_trans_sys
      scope state_vars init trans
      subsystems props contracts_option
      source =

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

  let properties =
    props
    |> List.map
         (fun (n, s, t) -> 
          { prop_name = n;
            prop_source = s; 
            prop_term = t; 
            prop_status = PropUnknown })
  in

  (* let contract_prop name = *)
  (*   try *)
  (*     List.find *)
  (*       ( function *)
  (*         | { prop_source = *)
  (*               TermLib.Contract *)
  (*                 TermLib.ContractAnnot (name',_) } -> *)
  (*            name = name' *)
  (*         | _ -> false ) *)
  (*       properties *)
  (*   with *)
  (*   | Not_found -> *)
  (*      Format.sprintf *)
  (*        "Could not locate property for contract %s." *)
  (*        name *)
  (*      |> failwith *)
  (* in *)
           

  let contracts =
    match contracts_option with
    | None -> None
    | Some(actlit,list) ->
       Some
         ( actlit,
           list
           |> List.map
                ( fun (name, source, requires, ensures) ->
                  { name ;
                    (* Retrieving property from contract name. *)
                    (* prop = contract_prop name ; *)
                    source ;
                    requires ;
                    ensures ;
                    status = PropUnknown } ) )
  in

  (* Making sure all properties have different terms. The contracts
     should also be properties at this point, so this detects contract
     clashes as well. *)
  ( match
      properties
      |> find_element_clash
           (fun { prop_term } -> prop_term)
    with
    (* No clash detected. *)
    | None -> ()
    (* Clash between [p] and [p']. *)
    | Some(p,p') ->
       let pp_print_prop_err ppf { prop_source ; prop_term } =
         let pos, name =
           match prop_source with
           | TermLib.PropAnnot pos -> pos, None
           | TermLib.Contract
               TermLib.ContractAnnot (name, pos) ->
              pos, Some(name)
           | _ ->
              (* Should never happen. *)
              assert false
         in
         Format.fprintf
           ppf
           "@[<hv 1>property%a@ at %a@]"
           ( fun ppf opt ->
             match opt with
             | None -> Format.fprintf ppf ""
             | Some n ->
                Format.fprintf
                  ppf
                  " generated from contract %s" n )
           name
           pp_print_position pos
       in
       let name = scope |> String.concat "/" in
       (* Crashing with info. *)
       Format.printf
         "@[<hv 4>%s Property term clash detected for system [%s]:@ \
          %a@;<0 -2>\
          and@ \
          %a@;<0 -2>\
          correspond to the same term@ \
          %a\
          @]\n\n"
         error_tag
         name
         pp_print_prop_err p
         pp_print_prop_err p'
         Term.pp_print_term p.prop_term ;
       failwith(
           Format.sprintf
             "Redundant property terms in system [%s]."
             name
         )
  ) ;

  let system = 
    { scope = scope;
      uf_defs = get_uf_defs [ (init, trans) ] subsystems ;
      state_vars =
        state_vars |> List.sort StateVar.compare_state_vars ;
      init = init ;
      trans = trans ;
      properties = properties ;
      contracts = contracts ;
      subsystems = subsystems ;
      source = source ;
      invars = [] ;
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
  |> (fun vars ->
      Var.declare_vars declare vars)


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
let invars_of_bound ?(one_state_only = false) t i = 

  (* Create conjunction of property terms *)
  let invars_0 = 
    Term.mk_and 

      (* Only one-state invariants? *)
      (if one_state_only then

         (* Filter for invariants at zero *)
         List.filter
           (fun t -> match Term.var_offsets_of_term t with 
              | Some l, Some u when 
                  Numeral.(equal l zero) && Numeral.(equal u zero) -> 
                true
              | _ -> false)
           t.invars

       else
         
         (* Return all invariants *)
         t.invars) 

  in 

  (* Bump bound if greater than zero *)
  if Numeral.(i = zero) then invars_0 else Term.bump_state i invars_0

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

let contract_of_name ({ contracts } as sys) to_find =
  try
    match contracts with
    | None ->
       Format.asprintf
         "System %a has no contracts."
         pp_print_trans_sys_name sys
       |> failwith
    | Some (_, contracts) ->
       List.find
         (fun { name } -> to_find = name)
         contracts
  with
  | Not_found ->
     Format.sprintf
       "Cannot locate contract %s."
       to_find
     |> failwith

let subrequirements_valid { properties } =
  let rec loop = function
    | { prop_status = status ;
        prop_source = TermLib.SubRequirement (_,_,_) }
      :: tail ->
       if status = PropInvariant then loop tail
       else false
    | _ :: tail -> loop tail
    | [] -> true
  in
  loop properties

let proved_requirements_of { properties } scope =
  let rec loop = function

    (* Requirement for [scope]. *)
    | { prop_status = status ;
        prop_source =
          TermLib.SubRequirement (_, scope', _) }
      :: tail when scope = scope' ->
       
       ( match status with
         (* Right system and subreq holds, looping. *)
         | PropInvariant -> loop tail
         (* Otherwise subreqirement is not known to hold, returning
            false. *)
         | _ -> false )

    (* Not a subrequirement, skipping. *)
    | _ :: tail -> loop tail

    (* Did not exit early, so proved sub requirements. *)
    | [] -> true
  in

  loop properties

let is_contract_proved = function
  | { contracts = None } -> raise Not_found
  | { contracts = Some (_, contracts) } ->
     contracts
     |> List.for_all
          ( fun { status } -> status = PropInvariant )

(* Mark property as invariant *)
let set_prop_invariant t prop =

  (* Get property by name *)
  let p = property_of_name t prop in

  (* Modify status *)
  p.prop_status <- 

    (* Check current status *)
    ( match p.prop_status with

      (* Mark property as invariant if it was unknown, k-true or
         invariant *)
      | PropUnknown
      | PropKTrue _
      | PropInvariant -> PropInvariant

      (* Fail if property was false or k-false *)
      | PropFalse _ -> raise (Failure "prop_invariant") ) ;

  match p.prop_source with
  | TermLib.Contract (TermLib.ContractAnnot(name,_)) ->
     (* Property is a contract, updating. *)
     let contract = contract_of_name t name in
     contract.status <- PropInvariant
          
  | _ -> ()

(* Changes the status of k-true properties as unknown. Used for
   contract-based analysis when lowering the abstraction depth. Since
   the predicates have changed they might not be k-true anymore. *)
let reset_non_valid_props_to_unknown t =
  t.properties
  |> List.iter
       ( function
         | { prop_status = PropInvariant } -> ()
         | prop ->
            prop.prop_status <- PropUnknown )

let reset_invariants t =
  t.invars <- [] ;
  t.properties
  |> List.iter
       ( function
         | { prop_term = term ; prop_status = PropInvariant } ->
            t.invars <- term :: t.invars
         | _ -> () )

let rec pp_print_trans_sys_contract_view ppf sys =
  Format.fprintf
    ppf
    "@[<hv 2>sys %s@ @[<v>@[<hv 2>contracts:@ %a@]@,@[<hv 2>properties:@ %a@]@,\
     @[<hv 2>subsystems:@ %a@]@]@]"
    (get_name sys)
    pp_print_contracts sys.contracts
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
        raise 
          (Failure
             (Format.sprintf
                "prop_false: was %d-true before, now cex of length %d"
                l
                (length_of_cex cex)))

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

let all_props_actually_proved { properties } =

  List.for_all
    (function
      | { prop_status = PropInvariant } -> true
      | _ -> false)
    properties

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

(* Builds an abstraction. *)
let mk_abstraction = identity

(* An empty abstraction. *)
let empty_abstraction = []

(* Defines abstraction literals for a transition system base on some
   abstraction. *)
let define_abstraction_actlits
      systems abstraction define =

  let rec loop = function

    | { scope ; contracts = None } :: tail ->
       (* System cannot be abstracted, skipping. *)
       loop tail

    | { scope ; contracts = Some (actlit, _) } :: tail ->
       (* Value the actlit will be defined as. *)
       let value =
         if List.mem scope abstraction
         then Term.t_true else Term.t_false
       in
       (* Defining [actlit]. *)
       define
         (StateVar.uf_symbol_of_state_var actlit)
         []
         value ;
       (* Looping. *)
       loop tail

    | _ -> ()
  in

  (* Defining actlits for all subsystems of [sys]. *)
  loop systems

(* Initializes the solver for a system and an abstraction. *)
let init_solver
      (* Only declare top level variables. *)
      ?(declare_top_vars_only = true)
      (* System and abstraction. *)
      sys abstraction
      (* Solver related functions. *)
      comment define declare
      (* Bounds for variable declaration. *)
      lbound ubound =

  Format.asprintf
    "|=====| Setting up solver for system %a."
    pp_print_trans_sys_name sys
  |> comment ;


  (* All subsystems of [sys], including [sys]. *)
  let all_systems = get_all_subsystems sys in
  
  comment "|===| Defining abstraction actlits for all systems." ;
  Format.sprintf
    "|          abstracting [%s]"
    (abstraction
     |> List.map (String.concat ".")
     |> String.concat ", ")
  |> comment ;
  define_abstraction_actlits all_systems abstraction define ;


  (if declare_top_vars_only then [ sys ] else all_systems)
  |> List.iter
       ( fun sys ->

         Format.asprintf
           "|===| Declaring variables of %a for [%a,%a]."
           pp_print_trans_sys_name sys
           Numeral.pp_print_numeral lbound
           Numeral.pp_print_numeral ubound
         |> comment ;

         comment "Constants." ;

         (* Declaring constant variables. *)
         vars_of_bounds sys lbound lbound
         |> Var.declare_constant_vars declare ;

         comment "Non-constant state variables." ;

         (* Declaring other variables. *)
         declare_vars_of_bounds sys declare lbound ubound ) ;

  
  Format.asprintf
    "|===| Defining init and trans predicates."
  |> comment ;

  iter_uf_definitions sys define ;


  comment "|===| Done with initialization." ;
  comment ""
  
(*
  
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

*)

(* Return true if the value of the term in some instant satisfies [pred] *)
let exists_eval_on_path uf_defs pred term path = 

  Model.exists_on_path
    (fun model -> pred (Eval.eval_term uf_defs model term))
    path

(*
  exists_eval_on_path' uf_defs pred term Numeral.zero path
*)


  


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
