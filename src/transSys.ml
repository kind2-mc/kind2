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

module P = Property
module SVM = StateVar.StateVarMap
module SVS = StateVar.StateVarSet

(* Offset of state variables in initial state constraint *)
let init_base = Numeral.zero

(* Offset of primed state variables in transition relation *)
let trans_base = Numeral.one

(* Offset of primed state variables in properties and invariants *)
let prop_base = Numeral.zero

(* Predicate definition *)
type pred_def = UfSymbol.t * (Var.t list * Term.t)


(* Instance of a subsystem *)
type instance = 
  {

    (* Position as a unique identifier of the instance *)
    pos : position;

    (* Map from state variables of the called system to the state variables of
       the this system *)
    map_down : StateVar.t SVM.t;

    (* Map from the state variables of this system to the state
       variables of the instance *)
    map_up : StateVar.t SVM.t;

    (* Add a guard to the Boolean term such that it is true if the
       clock of the node instance is false *)
    guard_clock : Numeral.t -> Term.t -> Term.t;

  }

type t = 

  { 

    scope: Scope.t;
    (** Scope of transition system *)

    init_flag_state_var : StateVar.t;
    (** State variable that becomes true in the first instant and false
       again in the second and all following instants *)

    instance_state_var : StateVar.t option;
    (** State variable to be bound to a unique term for each
       instance of the transition system *)

    instance_var_bindings : (Var.t * Term.t) list;
    (** Assignments of unique terms to the instance variables of this
       transition system and its subsystems *)

    global_state_vars : (StateVar.t * Term.t list) list;
    (** State variables of global scope, used for arrays. Each state
       variable has a list of upper bounds for its indexes. 

       To get all defined values, evaluate the instance state
       variable, and the terms for the index bounds first, then
       evaluate the uninterpreted function with the value of the
       instance variable as the first, and all indexes as following
       parameters. TODO: add this functionality to Eval. *)

    global_consts : Var.t list;
    (** List of global free constants *)
    
    state_vars : StateVar.t list;
    (** State variables in the scope of this transition system 

       Also contains [instance_state_var] unless it is None, but not
       state variables in [global_state_vars]. *)

    state_var_bounds : 
      (LustreExpr.expr LustreExpr.bound_or_fixed list)
        StateVar.StateVarHashtbl.t;
    (** register indexes of state variables for later use *)

    subsystems : (t * instance list) list;
    (** Transition systems called by this system, and for each instance
       additional information to map between state variables of the
       different scopes *)

    ufs : UfSymbol.t list;
    (** Other function declarations *)
    
    logic : TermLib.logic;
    (** Logic fragment needed to express the transition system 

       TODO: Should this go somewhere more global? *)

    init_uf_symbol : UfSymbol.t;
    (** Predicate symbol for initial state constraint *)

    init_formals : Var.t list;
    (** Formal parameters of initial state constraint *)

    init : Term.t;
    (** Initial state constraint. *)

    trans_uf_symbol : UfSymbol.t;
    (** Predicate symbol for transition relation *)

    trans_formals : Var.t list;
    (** Formal parameters of transition relation *)

    trans : Term.t;
    (** Transition relation. *)

    properties : Property.t list;
    (** Properties to prove invariant for this transition system 

       Does not need to be mutable, because a Property.t is *)

    mode_requires: Term.t option * (Scope.t * Term.t) list ;
    (** Requirements of global and non-global modes for this system (used by
        test generation).
        List of [(is_mode_global, mode_name, require_term)]. *)

    invariants : Invs.t ;

  }

(* ********************************************************************** *)
(* Pretty-printing                                                        *)
(* ********************************************************************** *)


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
  
let pp_print_property_status ppf = function 
  | P.PropUnknown -> Format.fprintf ppf ":unknown"
  | P.PropKTrue k -> Format.fprintf ppf ":k-true %d" k
  | P.PropInvariant _ -> Format.fprintf ppf ":invariant"
  | P.PropFalse _ -> Format.fprintf ppf ":false"


let pp_print_property_source = P.pp_print_prop_source

let pp_print_property 
    ppf
    { P.prop_name; P.prop_source; P.prop_term; P.prop_status } =

  Format.fprintf ppf
    "(\"%s\"@ %a %a %a)" 
    prop_name
    Term.pp_print_term prop_term
    pp_print_property_status prop_status
    pp_print_property_source prop_source

let pp_print_state_var_pair ppf (sv1, sv2) = 

  Format.fprintf
    ppf
    "@[<hv 1>(%a@ %a)@]"
    StateVar.pp_print_state_var sv1
    StateVar.pp_print_state_var sv2

let pp_print_instance ppf { pos; map_down; map_up } =

  Format.fprintf 
    ppf
    "@[<hv 1>(%a@ \
              @[<hv 1>(%a)@]@ \
              @[<hv 1>(%a)@])@]" 
    pp_print_position pos
    (pp_print_list pp_print_state_var_pair "@ ") (SVM.bindings map_down) 
    (pp_print_list pp_print_state_var_pair "@ ") (SVM.bindings map_up) 

let pp_print_subsystem ppf ({ scope }, instances) = 

  Format.fprintf
    ppf
    "@[<hv 1>(%a@ @[<hv 1>(%a)@])@]"
    Scope.pp_print_scope scope
    (pp_print_list pp_print_instance "@ ") instances


let pp_print_uf ppf uf =
  Format.fprintf
    ppf
    "@[<hv>%a@ @[<hv 1>(%a)@]@ %a@]"
    UfSymbol.pp_print_uf_symbol uf
    (pp_print_list Type.pp_print_type "@ ") (UfSymbol.arg_type_of_uf_symbol uf)
    Type.pp_print_type (UfSymbol.res_type_of_uf_symbol uf)


let pp_print_trans_sys_name fmt { scope } =
  Format.fprintf fmt "%a" Scope.pp_print_scope scope
    
let pp_print_trans_sys 
    ppf
    { scope;
      instance_state_var;
      instance_var_bindings;
      global_state_vars;
      state_vars;
      ufs;
      init;
      init_formals;
      trans;
      trans_formals;
      subsystems;
      properties; } = 

  Format.fprintf 
    ppf
    "@[<v 1>(trans-sys %a@,\
     @[<hv 2>(state-vars@ (@[<v>%a@]))@]@,\
     @[<hv 2>(uf@ (@[<v>%a@]))@]@,\
     @[<hv 2>(init@ @[<hv 1>(%a)@]@ (@[<v>%a@]))@]@,\
     @[<hv 2>(trans@ @[<hv 1>(%a)@]@ (@[<v>%a@]))@]@,\
     @[<hv 2>(prop@ (@[<v>%a@]))@]@,\
     @[<hv 2>(sub@ @[<hv 1>(%a)@])@])"

    Scope.pp_print_scope scope
    (pp_print_list pp_print_state_var "@ ") state_vars
    (pp_print_list pp_print_uf "@ ") ufs
    (pp_print_list Var.pp_print_var "@ ") init_formals
    Term.pp_print_term init
    (pp_print_list Var.pp_print_var "@ ") trans_formals
    Term.pp_print_term trans
    (pp_print_list pp_print_property "@ ") properties
    (pp_print_list pp_print_subsystem "@ ") subsystems

(*
    "@[<v>@[<hv 2>(state-vars@ (@[<v>%a@]))@]@,\
          %a@,\
          @[<hv 2>(logic %a)@]@,\
          @[<hv 2>(init@ (@[<v>%a@]))@]@,\
          @[<hv 2>(trans@ (@[<v>%a@]))@]@,\
          @[<hv 2>(props@ (@[<v>%a@]))@]@,\
          @[<hv 2>(contracts@ (@[<v>%a@]))@]@,\
          @[<hv 2>(invar@ (@[<v>%a@]))@]@,\
          @[<hv 2>(source@ (@[<v>%a@]))@]@,\
          @[<hv 2>(callers@ (@[<v>%a@]))@]@."
    TermLib.pp_print_logic logic
    (pp_print_list pp_print_uf_defs "@ ") (uf_defs)
    Term.pp_print_term (init_term trans_sys)
    Term.pp_print_term (trans_term trans_sys)
    (pp_print_list pp_print_property "@ ") properties
    pp_print_contracts contracts
    (pp_print_list Term.pp_print_term "@ ") invars
    (pp_print_list (fun ppf { LustreNode.name } -> LustreIdent.pp_print_ident false ppf name) "@ ") (match source with Lustre l -> l | _ -> [])
    (pp_print_list pp_print_callers "@,") callers
*)


let rec pp_print_subsystems include_top fmt sys =
  if include_top then Format.fprintf fmt "%a@." pp_print_trans_sys sys;
  List.iter
    (fun (t,_) -> pp_print_subsystems true fmt t)
    sys.subsystems


(*

(* For each key append the list of the second map to the list of the
   first map, and assume the empty list for keys that are in one but not
   the other map. *)
let join_list_scope_maps m1 m2 = 
  Scope.Map.merge
    (fun k v1 v2 -> match v1, v2 with
       | None, None -> None
       | Some _, None -> v1
       | None, Some _ -> v2
       | Some l1, Some l2 -> Some (l1 @ l2))
    m1
    m2


(* Return an assoociation list of scopes of all subsystems, including
   the top system, to the list of instance variables of each
   instance lifted to the scope of the top system. *)
let rec collect_instances' accum = function 

  (* Stack is empty, instance variables of top system are in accumulator *)
  | [] -> accum

  (* Add instance variables of system at the top of the stack to
     accumulator *)
  | { scope; instance_state_var; subsystems } :: tl as l -> 

    if

      (* Transition system already seen? *)
      Scope.Map.mem scope accum

    then

      (* Do not add to accumulator twice *)
      collect_instances' accum tl

    else

      (* Add all subsystems not yet seen to the top of the stack *)
      let l' = 
        List.fold_left

          (* Add transition system to stack if not in accumulator *)
          (fun l ({ scope } as t, _) -> 

             if 

               (* Transition system already seen? *)
               Scope.Map.mem scope accum

             then 

               (* Use subsystem in accumulator *)
               l

             else

               (* Need to get instances of subsystem first

                  Add to the stack even if it is already there,
                  because the subsystem needs to be visited before the
                  system at the top of the stack. *)
               (t :: l))

          l
          subsystems 

      in

      (* Need to visit more subsystems? 

         We only add to the stack, that is, [l'] is constructed by
         pushing transition systems at the head of [l], and therefore
         we can simply compare lengths to check if [l'] is different
         from [l]. *)
      if List.length l' > List.length l then 

        (* Collect instance variables from subsystems first *)
        collect_instances' accum l' 

      (* All subsystems are in [accum] *)
      else

        (* Instance state variables in this transition system *)
        let scope_instance_state_vars =

          (* Iterate over all subsystems and lift instance variables
             to this transition system *)
          List.fold_left 

            (fun m ({ scope = subsystem_scope }, instances) ->

               (* Instance variables of the subsystem *)
               let subsystem_instance_state_vars = 

                 try 

                   (* Find instance variables of the subsystem as
                      previously collected *)
                   Scope.Map.find subsystem_scope accum

                 (* All subsystems are in the accumulator *)
                 with Not_found -> assert false

               in

               (* Lift all instance variables of all instances of the
                  subsystem to this transition system *)
               List.fold_left

                 (fun m (lift_map, _) ->

                    (* Add lifted state variables of this instance to
                       the map *)
                    join_list_scope_maps
                      m

                      (* Lift all state variables of the subsystem
                         with the state variable map of the
                         instance *)
                      (Scope.Map.map
                         (fun l -> 

                            List.map
                              (fun sv -> 
                                 try 

                                   (* Get state variable in this
                                      transition system instantiating
                                      the state variable in the
                                      subsystem *)
                                   (SVM.find sv lift_map)

                                 (* Every state variable must be in
                                    the map *)
                                 with Not_found -> assert false)
                              l)
                         subsystem_instance_state_vars))

                 m
                 instances)

            (* The initial map contains only a singleton list with the
               instance state variable for this transition system, or
               the empty list if the transition system does not have
               an instance variable. *)
            (Scope.Map.singleton 
               scope 
               (match instance_state_var with
                 | None -> []
                 | Some sv ->  [sv]))

            subsystems

        in

        (* Add instance variables of this transition system to
           accumulator *)
        let accum' =
          Scope.Map.add scope scope_instance_state_vars accum
        in



        (* Collect instance variables from following subsystems *)
        collect_instances' accum' tl


(* Return the list of instance state variables of all subsystems in
   the scope of the top system *)
let collect_instances ({ scope } as trans_sys) = 
  collect_instances' Scope.Map.empty [trans_sys] 
  |> Scope.Map.find scope
*)


(* ********************************************************************** *)
(* Access the transition system                                           *)
(* ********************************************************************** *)

(* Close term by binding variables to terms with a let binding *)
let close_term bindings term = 
  if bindings = [] then term else Term.mk_let bindings term


(* Bump the offsets of state variable instances at [base] to [i]
   and respectively for state variables at different offsets. *)
let bump_relative base i term = 

  (* Need to bump term to different offset? *)
  if Numeral.(i = base) then term else
    
    (* Bump to offset *)
    Term.bump_state Numeral.(i - base) term


(* Close the initial state constraint by binding all instance
   identifiers, and bump the state variable offsets to be at the given
   bound *)
let init_of_bound partial { instance_var_bindings; init } i = 
  let ib = close_term instance_var_bindings init |> bump_relative init_base i in
  match partial with
  | None -> ib
  | Some declare ->
    let ib, partial_ufs = Term.partial_selects ib in
    List.iter declare partial_ufs;
    ib


(* Close the initial state constraint by binding all instance
   identifiers, and bump the state variable offsets to be at the given
   bound *)
let trans_of_bound partial { instance_var_bindings; trans } i = 
  let tb =
    close_term instance_var_bindings trans |> bump_relative trans_base i in
  match partial with
  | None -> tb
  | Some declare ->
    let tb, partial_ufs = Term.partial_selects tb in
    List.iter declare partial_ufs;
    tb


(* Return the instance variables of this transition system, the
   initial state constraint at [init_base] and the transition relation
   at [trans_base] with the instance variables free. *)
let init_trans_open { instance_var_bindings; init; trans } = 

  (List.map 
     (fun (v, _) -> Var.state_var_of_state_var_instance v)
     instance_var_bindings, 
   init,
   trans)

let rec set_subsystem_equations t scope init trans =
  let aux (t, instances) =
    (set_subsystem_equations t scope init trans, instances)
  in
  let subsystems = List.map aux t.subsystems in
  let (init, trans) =
    if Scope.equal t.scope scope
    then (init, trans)
    else (t.init, t.trans)
  in
  { t with init; trans; subsystems }

(* Return the state variable for the init flag *)
let init_flag_state_var { init_flag_state_var } = init_flag_state_var


(* Return the init flag at the given bound *)
let init_flag_of_bound { init_flag_state_var } i = 
  Var.mk_state_var_instance init_flag_state_var i
  |> Term.mk_var

  

(* Return true if scopes of transition systems are equal *)
let equal_scope { scope = s1 } { scope = s2 } = Scope.equal s1 s2

(* Compare transition systems by their scope *)
let compare_scope { scope = s1 } { scope = s2 } = Scope.compare s1 s2


(* Return the logic fragment needed to express the transition system *)
let get_logic t = t.logic


(* Return the scope identifying the transition system *)
let scope_of_trans_sys t = t.scope

(* Returns the properties in the transition system. *)
let get_properties t = t.properties

(* Return all properties *)
let get_real_properties t = List.filter (
  function
  | { P.prop_source = P.Candidate _ } -> false
  | _ -> true
) t.properties


(** Returns the mode requirements for this system as a list of triplets
    [is_mode_global, mode_name, require_term].
    Used by test generation. *)
let get_mode_requires t = t.mode_requires

(** Returns the list of properties in a transition system, split by their
    status as [valid, invalid, unknown]. *)
let get_split_properties { properties } =
  properties |> List.fold_left (fun ( (valid, invalid, unknown) as all) ->
    function
    | { Property.prop_status = Property.PropInvariant _ } as p->
      p :: valid, invalid, unknown
    | { Property.prop_source = Property.Candidate _ } ->
      all
    | { Property.prop_status = Property.PropFalse _ } as p ->
      valid, p :: invalid, unknown
    | p ->
      valid, invalid, p :: unknown
  ) ([], [], [])

let get_function_symbols { ufs } = ufs

(* **************************************************************** *)
(* Iterate and Fold over Subsystems                                 *)
(* **************************************************************** *)

(* Fold bottom-up over subsystems in list without repeating subsystems
   already seen *)
let rec fold_subsystems' f accum visited = function 

  (* All subsystems visited, return *)
  | [] -> accum

  (* Subsystem already visited? *)
  | { scope } :: tl when Scope.Set.mem scope visited -> 

    (* Skip and continue *)
    fold_subsystems' f accum visited tl

  (* Subsystem not visited *)
  | ({ scope; subsystems } as trans_sys) :: tl -> 

    (* Add all not visisted subsystems before this system *)
    let tl' = 
      List.fold_left
        (fun a ({ scope = s } as t, _) -> 
           if Scope.Set.mem s visited then a else t :: a)
        (trans_sys :: tl)
        subsystems 
    in

    (* Were subsystems added to the stack? 

       The stack is at least as long as before *)
    if List.length tl' > (List.length tl + 1) then 

      (

        (* Iterate over not visited subsystems first *)
        fold_subsystems' f accum visited tl'

      )

    (* All subsystems visited *)
    else

      (

        (* Remember scope of transition system as visited, add subsystems
           to stack and continue *)
        fold_subsystems' 
          f
          (f accum trans_sys)
          (Scope.Set.add scope visited) 
          tl

      )


(* Stack for zipper in [fold_subsystem_instances'] *)
type fold_stack = 
  | FDown of t * (t * instance) list
  | FUp of t * (t * instance) list


(* Fold bottom-up over subsystem instances in list *)
let rec fold_subsystem_instances' 
    (f : t -> (t * instance) list -> 'a list -> 'a)
    (accum : 'a list list) = 

  let rec push k t s p = function  
    | [] -> k 
    | i :: tl -> push (FDown (s, (t, i) :: p) :: k) t s p tl
  in

  function 

    (* All systems visited, return result *)
    | [] -> 

      (match accum with
        | [[a]] -> a
        | _ -> assert false)

    (* We need to evaluate the subsystems first *)
    | FDown ({ subsystems } as t, p) :: tl -> 

      (* Push subsystems to stack, then return to this system *)
      let tl' = 
        List.fold_left 
          (fun a (s, i) -> push a t s p i)
          (FUp (t, p) :: tl)
          subsystems
      in

      (* Continue with subsytems and placeholder for results from
         subsystems in accumulator *)
      fold_subsystem_instances' 
        f 
        ([] :: accum)
        tl'

    (* Subsytems are in the accumulator, evaluate this system now *)
    | FUp (t, i) :: tl -> 

      (match accum with

        (* First element on accumulator is list of results for
           children, second element is list of results for
           siblings *)
        | a :: b :: c ->
          
          fold_subsystem_instances' f (((f t i a) :: b) :: c) tl
            
        | _ -> assert false)


(* Iterate bottom-up over subsystems, including the top level system
    without repeating subsystems already seen *)
let iter_subsystems ?(include_top = true) f ({ subsystems } as trans_sys) =
  fold_subsystems'
    (fun _ -> f)
    () 
    Scope.Set.empty 
    (if include_top then [trans_sys] else (List.map fst subsystems))

(* Fold bottom-up over subsystems, including the top level system
    without repeating subsystems already seen *)
let fold_subsystems ?(include_top = true) f accum ({ subsystems } as trans_sys) =
  fold_subsystems' 
    f
    accum
    Scope.Set.empty
    (if include_top then [trans_sys] else List.map fst subsystems)


(* Fold bottom-up over all subsystem instances *)
let fold_subsystem_instances f trans_sys = 

  fold_subsystem_instances'
    f
    [[]]
    [FDown (trans_sys, [])]

  
(* TODO: iterate over each instance of a subsystem *)
let iter_subsystem_instances f trans_sys = assert false


(* Return the direct subsystems of a system *)
let get_subsystems { subsystems } = List.map fst subsystems

(* Return direct subsystems of a system and their instances *)
let get_subsystem_instances { subsystems } = subsystems


(* Find the subsystem of the scope *)
let find_subsystem_of_scope trans_sys scope = 

  match 

    (* Iterate over each subsystem exactly once, add to accumulator if
       found *)
    fold_subsystems
      (fun a ({ scope = s } as t) -> 
         if Scope.equal scope s then Some t else a)
      None
      trans_sys 

  with

    (* No subsystem of scope *)
    | None -> raise Not_found 

    (* Return the subsystem *)
    | Some t -> t 


let get_max_depth trans_sys = 
  fold_subsystem_instances
    (fun _ _ a -> List.fold_left max 0 a |> succ)
    trans_sys

(* **************************************************************** *)
(* Set, Map, and Hash Table                                         *)
(* **************************************************************** *)


(* Compare and hash transistion systems by their scope *)
module T =
struct

  (* Prevent cyclic [type t = t] *)
  type z = t
  type t = z 

  (* Total order of transitions systems induced by total order of
     their scopes *)
  let compare { scope = s1 } { scope = s2 } = Scope.compare s1 s2

  (* Equality of transitions systems induced by equality of their
     scopes *)
  let equal { scope = s1 } { scope = s2 } = Scope.equal s1 s2

  (* Hash of a transition system is the hash of its scope *)
  let hash { scope } = Scope.hash scope

end

(* Map of transition systems *)
module Map = Map.Make (T)

(* Hash table of transition systems *)
module Hashtbl = Hashtbl.Make (T)



(* **************************************************************** *)
(* State Variables, Predicates and Declarations                     *)
(* **************************************************************** *)


(* Return state variables of the transition system *)
let state_vars { state_vars } = state_vars

(* Add a global constant to a transition system *)
let rec add_global_constant t v =
  let aux (t, instances) =
    (add_global_constant t v, instances)
  in
  let subsystems = List.map aux t.subsystems in
  let global_consts = v::t.global_consts in
  let state_vars = (Var.state_var_of_state_var_instance v)::t.state_vars in
  { t with subsystems ; global_consts ; state_vars }

(* Return global state variables of the transition system *)
let global_state_vars { global_state_vars } = global_state_vars


(* Add instances of the [state_vars] at [ubound] to [accum] if
   [ubound] is greater than [lbound]*)
let rec vars_of_bounds' state_vars lbound ubound accum =

  (* Return when upper bound below lower bound *)
  if Numeral.(ubound < lbound) then accum else
    
    (* Reverse to add in original order *)
    List.rev state_vars

    |> 

    (* Add state variables at upper bound instant *)
    List.fold_left
      (fun accum sv -> 
         Var.mk_state_var_instance sv ubound :: accum )
      accum

    |> 

    (* Recurse to next lower bound *)
    vars_of_bounds' state_vars lbound Numeral.(pred ubound)


(* Return instances of the state variables of the transition system
   between and including [lbound] and [uboud] *)
let vars_of_bounds
    ?(with_init_flag = true)
    { init_flag_state_var; state_vars } 
    lbound
    ubound =

  (* State variables to instantiate at bounds *)
  let state_vars = 

    (* All state variables including the init flag *)
    if with_init_flag then state_vars else

      (* Filter out the init flag state variable *)
       List.filter
         (fun sv -> 
            not
              (StateVar.equal_state_vars sv init_flag_state_var))
         state_vars
  in

  (* Instantiate state variables between bounds *)
  vars_of_bounds' state_vars lbound ubound []
    

(* Declare variables of the transition system at instants between and
   including [lbound] and [ubound] *)
let declare_vars_of_bounds
    ?(declare_init_flag = true)
    trans_sys 
    declare
    lbound
    ubound =

  (* Instantiate state variables and declare *)
  vars_of_bounds ~with_init_flag:declare_init_flag trans_sys lbound ubound
  |> Var.declare_vars declare


(* Declare constant state variable of the system *)
let declare_const_vars { state_vars } declare =

  (* Constant state variables of the top system *)
  List.filter StateVar.is_const state_vars

  (* Create variable of constant state variable *)
  |> List.map Var.mk_const_state_var

  (* Declare variables *)
  |> Var.declare_constant_vars declare


(* Return the init flag at the given bound *)
let declare_init_flag_of_bounds { init_flag_state_var } declare lbound ubound = 
  
  (* Instantiate the init flag only between the given bounds *)
  vars_of_bounds' [ init_flag_state_var ] lbound ubound []

  (* Evaluate declaration function *)
  |> Var.declare_vars declare 


(* Declare other functions symbols *)
let declare_ufs { ufs } declare =
  List.iter declare ufs

(* Declare other functions symbols *)
let declare_selects declare sys =
  if TermLib.logic_allow_arrays (get_logic sys) then
    List.iter declare (StateVar.get_select_ufs ())
  
(* Define initial state predicate *)
let define_init define { init_uf_symbol; init_formals; init } = 
  define init_uf_symbol init_formals init

(* Define transition relation predicate *)
let define_trans define { trans_uf_symbol; trans_formals; trans } =
  define trans_uf_symbol trans_formals trans

(* Declare the sorts, uninterpreted functions and const variables
   of this system and its subsystems. *)
let declare_sorts_ufs_const trans_sys declare declare_sort =
  (* declare uninterpreted sorts *)
  Type.get_all_abstr_types () |>
  List.iter (fun ty -> match Type.node_of_type ty with
      | Type.Abstr _ -> declare_sort ty
      | _ -> ());

  (* Declare monomorphized select symbols *)
  if not (Flags.Arrays.smt ()) then declare_selects declare trans_sys;

  (* Declare other functions of top system *)
  declare_ufs trans_sys declare;

  (* Declare constant state variables of top system *)
  declare_const_vars trans_sys declare ;

  (* Iterate over all subsystems *)
  trans_sys |> iter_subsystems ~include_top:false (fun t ->

    (* Declare other functions of sub system *)
    declare_ufs t declare
  )

(* Declare the init and trans functions of the subsystems *)
let define_subsystems trans_sys define =
  (* Iterate over all subsystems *)
  trans_sys |> iter_subsystems ~include_top:false (fun t ->

    (* Define initial state predicate *)
    define_init define t ;

    (* Define transition relation predicate *)
    define_trans define t
  )

(* Define predicates, declare constant and global state variables, and
   declare state variables of the top system between and including the
   given offsets *)
let define_and_declare_of_bounds
    ?(declare_sub_vars=false) 
    trans_sys
    define 
    declare
    declare_sort
    lbound
    ubound =

  (* declare uninterpreted sorts *)
  Type.get_all_abstr_types () |>
  List.iter (fun ty -> match Type.node_of_type ty with
      | Type.Abstr _ -> declare_sort ty
      | _ -> ());

    (* Declare monomorphized select symbols *)
  if not (Flags.Arrays.smt ()) then declare_selects declare trans_sys;

  (* Declare other functions of top system *)
  declare_ufs trans_sys declare;

  (* Declare constant state variables of top system *)
  declare_const_vars trans_sys declare;

  (* Iterate over all subsystems *)
  trans_sys |> iter_subsystems ~include_top:false (fun t ->

    (* Declare constant state variables of subsystem *)
    if declare_sub_vars then
      declare_vars_of_bounds t declare lbound ubound ;
  
    (* Declare other functions of sub system *)
    declare_ufs t declare;

    (* Define initial state predicate *)
    define_init define t ;

    (* Define transition relation predicate *)
    define_trans define t
  ) ;
       
  (* Declare constant state variables of top system *)
  declare_vars_of_bounds trans_sys declare lbound ubound
       

let init_uf_def { init_uf_symbol; init_formals; init } = 
  (init_uf_symbol, (init_formals, init))


let trans_uf_def { trans_uf_symbol; trans_formals; trans } = 
  (trans_uf_symbol, (trans_formals, trans))


(* Return the predicate for the initial state constraint *)
let init_uf_symbol { init_uf_symbol } = init_uf_symbol

(* Return the predicate for the transition relation *)
let trans_uf_symbol { trans_uf_symbol } = trans_uf_symbol

(* Return the variables in the initial state constraint *)
let init_formals { init_formals } = init_formals

(* Return the variables in the transition relation *)
let trans_formals { trans_formals } = trans_formals


(* Builds a call to the init function on state [k]. *)
let init_fun_of { init_uf_symbol; init_formals } k =

  let rec bump_as_needed res = function
    | var :: tail ->
      let bumped_term =
        if Var.is_const_state_var var then Term.mk_var var
        else (
          let offset = Var.offset_of_state_var_instance var in
          if Numeral. (offset = init_base ) then
            (* Primed state variable, bumping to k. *)
            Var.bump_offset_of_state_var_instance
              var Numeral.( k - offset )
            |> Term.mk_var
          else
            (* This cannot happen. *)
            assert false
        )
      in
      bump_as_needed (bumped_term :: res) tail
    | [] -> List.rev res
  in

  Term.mk_uf init_uf_symbol (bump_as_needed [] init_formals)

(* Builds a call to the transition relation function linking state [k]
   and [k']. *)
let trans_fun_of { trans_uf_symbol; trans_formals } k k' =

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
              var Numeral.( k' - offset )
            |> Term.mk_var
          else if Numeral. (offset = trans_base_pre ) then
            (* Primed state variable, bumping to k. *)
            Var.bump_offset_of_state_var_instance
              var Numeral.( k - offset )
            |> Term.mk_var
          else
            (* This cannot happen. *)
            assert false
        )
      in
      bump_as_needed (bumped_term :: res) tail
    | [] -> List.rev res
  in

  Term.mk_uf trans_uf_symbol (bump_as_needed [] trans_formals)


(* Return predicate definitions of initial state and transition
   relation of the top system and all its subsystem in reverse
   topological order 

   [uf_defs t] returns a list of predicate definitions of the top
   system [t] and all its subsystems such that the definitions of a
   subsystem precede the definitions of all systems containing it. The
   definition of the initial state predicate precedes the definition
   of the transition relation predicate.
*)
let uf_defs trans_sys = 

  (* Collect predicate definitions bottom up *)
  fold_subsystems
    (fun a t ->

       (* First transition relation then initial state because the list
          will be reversed *)
       trans_uf_def t :: init_uf_def t :: a)

    []
    trans_sys

  (* Reverse predicate definitions to have predicate definitions of
     subsystems before *)
  |> List.rev


(* Flatten the list of instances per subsystems ot a list of subsystem
   and instance pairs *)
let flatten_instances subsystems =

  List.fold_left 
    (fun a (t, i) -> 
       List.fold_left 
         (fun a i -> (t, i) :: a)
         a
         i)
    []
    subsystems 



let rec map_cex_prop_to_subsystem' 
    filter_out_values
    ({ scope; subsystems } as trans_sys) 
    instances
    cex = 

  function

    | ({
      P.prop_source = P.Instantiated (s, {
        P.prop_source = P.Assumption _
      } );
      P.prop_term
    } as p) ->
      (* Property is a requirement for a subnode. *)
      (trans_sys, instances, cex, p)

    | { P.prop_source = P.Instantiated (s, p'); P.prop_term } -> 

      (* Find subsystem the property is lifted from *)
      let trans_sys', instances = 

        try 

          (* Find subsystem by scope *)
          List.find
            (fun ({ scope }, _) -> scope = s)
            subsystems

        (* System must exist as subsystem *)
        with Not_found -> assert false 

      in

      (* State variables in property *)
      let prop_state_vars = 
        Term.state_vars_of_term prop_term
      in

      (* Find instance that contains at least one state variable of
         the property original property *)
      let { map_down } as instance = 
        match 
          List.find_all 
            (fun { map_down } -> 
               SVS.exists
                 (fun sv -> 
                    SVM.exists
                      (fun sv' _ -> StateVar.equal_state_vars sv sv')
                      map_down)
                 prop_state_vars)
            instances
        with
          | [i] -> i
          | _ -> assert false
      in

      (* Map counterexample to instance of subsystem *)
      let cex' = 
        List.fold_left
          (fun cex' (sv, v) -> 
             try 
               (SVM.find sv map_down, 
                filter_out_values scope instance cex v) ::
               cex'
             with Not_found -> 
               cex') 
          []
          cex
      in

      (* Continue to map to subsystem *)
      map_cex_prop_to_subsystem' 
        filter_out_values
        trans_sys'
        (instance :: instances)
        cex'
        p'

    (* Property is not instantiated *)
    | p -> 

      (trans_sys, instances, cex, p)


let map_cex_prop_to_subsystem filter_out_values trans_sys cex prop = 
  map_cex_prop_to_subsystem' filter_out_values trans_sys [] cex prop 


(*

(* Define uf definitions, declare constant state variables and declare
   variables from [lbound] to [upbound]. *)
let init_define_fun_declare_vars_of_bounds t define declare lbound ubound =

  (match t.callers with
    | [] ->
      (* Define ufs. *)
      iter_uf_definitions t define ;
    | _ -> () ) ;

  let l_vars = vars_of_bounds t lbound lbound in

  (* Declaring constant variables. *)
  Var.declare_constant_vars declare l_vars ;

  (* Declaring other variables. *)
  declare_vars_of_bounds t declare lbound ubound
  
*)

(* **************************************************************** *)
(* Properties                                                       *)
(* **************************************************************** *)

(* Get property by name *)
let property_of_name t name =

  (* Return the first property with the given name *)
  List.find
    (fun { P.prop_name } -> prop_name = name )
    t.properties


(* Get term of property by name *)
let get_prop_term t name = 

  (property_of_name t name).P.prop_term


(* Return current status of property *)
let get_prop_status trans_sys p = 

  try 

    (property_of_name trans_sys p).P.prop_status

  with Not_found -> P.PropUnknown

(* Tests if a term is an invariant. *)
let is_inv { invariants } = Invs.mem invariants


(* Return true if the property is proved invariant *)
let is_proved trans_sys prop = 

  try 
    ( match (property_of_name trans_sys prop).P.prop_status with
      | P.PropInvariant _ -> true
      | _ -> false )
        
  with
    Not_found -> false


(* Return true if the property is proved not invariant *)
let is_disproved trans_sys prop = 

  try 
    ( match (property_of_name trans_sys prop).P.prop_status with
      | P.PropFalse _ -> true
      | _ -> false )
        
  with
    Not_found -> false


(* Return current status of property *)
let set_prop_status { properties } p s =

  let found =
    properties |> List.fold_left (
      fun found -> function
      | { P.prop_name } as prop when prop_name = p ->
        P.set_prop_status prop s ;
        true
      | _ -> found
    ) false
  in

  if not found then raise Not_found


let set_prop_invariant trans_sys p cert = 
  set_prop_status trans_sys p (P.PropInvariant cert)
  

let set_prop_ktrue trans_sys k p =
  P.PropKTrue k |> set_prop_status trans_sys p


let set_prop_false trans_sys p c =
  P.PropFalse c |> set_prop_status trans_sys p

let set_prop_unknown { properties } p =
  let found =
    properties |> List.fold_left (
      fun found -> function
      | { P.prop_name } as prop when prop_name = p ->
        P.set_prop_unknown prop ;
        true
      | _ -> found
    ) false
  in
  if not found then raise Not_found

(* Return current status of all properties *)
let get_prop_status_all_nocands t = 
  List.fold_left (fun acc -> function
      | { P.prop_source = P.Candidate _ } -> acc
      | { P.prop_name; P.prop_status } -> (prop_name, prop_status) :: acc
    ) [] t.properties
  |> List.rev


(* Return current status of all properties *)
let get_prop_status_all_unknown t = 

  List.fold_left 
    (function accum -> function 
       
       | { P.prop_name; P.prop_status } 
         when not (P.prop_status_known prop_status) -> 

         (prop_name, prop_status) :: accum 

       | _ -> accum)
    []
    t.properties


(** Returns true iff sys has at least one property. *)
let has_properties = function
| { properties = [] } -> false
| _ -> true

let rec set_subsystem_properties t scope ps =
  let aux (t, instances) =
    (set_subsystem_properties t scope ps, instances)
  in
  let subsystems = List.map aux t.subsystems in
  let properties =
    if Scope.equal t.scope scope
    then ps
    else t.properties
  in
  { t with properties; subsystems }


(* Return true if all properties which are not candidates are either valid or
   invalid *)
let all_props_proved t =
  List.for_all
    (function
      | { P.prop_source = P.Candidate _ } -> true
      | { P.prop_status = (P.PropInvariant _ | P.PropFalse _) } -> true
      | _ -> false
    ) t.properties

(* Return true if at least one prop has been falsified *)
let at_least_one_prop_falsified t =
  List.exists
    (function
      | { P.prop_source = P.Candidate _ } -> false
      | { P.prop_status = (P.PropFalse _) } -> true
      | _ -> false
    ) t.properties

(* Instantiate terms in association list to the bound *)
let named_terms_list_of_bound l i = 

  (* Bump bound if greater than zero *)
  if
    Numeral.(i = zero)
  then
    List.map 
      (fun { Property.prop_name; Property.prop_term } -> 
         (prop_name, prop_term)) 
      l
  else
    List.map 
      (fun { Property.prop_name; Property.prop_term } -> 
         (prop_name, Term.bump_state i prop_term)) 
      l
      

(* Instantiate all properties to the bound *)
let props_list_of_bound t i = 
  named_terms_list_of_bound t.properties i


(* Add an invariant to the transition system. *)
let add_scoped_invariant t scope invar cert two_state =

  let invar =
    match Term.var_offsets_of_term invar with
    | None, None -> invar
    | Some lo, None
    | None, Some lo ->
      Term.bump_state Numeral.(~- lo) invar
    | Some lo, Some up ->
      if Numeral.(equal lo up) then (
        (* Make sure one state invariants have offset [0]. *)
        Term.bump_state Numeral.(~- lo) invar
      ) else (
        let lo_offset = Numeral.(~- one) in
        (* Make sure two-state invariants have offset [-1,0]. *)
        if Numeral.(lo < lo_offset) then
          Term.bump_state Numeral.(~- lo_offset - lo) invar
        else if Numeral.(lo > lo_offset) then
          Term.bump_state Numeral.(lo - lo_offset) invar
        else invar
      )
  in

  iter_subsystems (
    fun { scope = s ; invariants } -> if Scope.equal scope s then (
      if two_state then
        Invs.add_ts invariants invar cert
      else
        Invs.add_os invariants invar cert
    )
  ) t ;

  invar


let add_properties t props =
  { t with
    properties = List.rev_append (List.rev props) t.properties }


(* Adds an invariant to the transition system. *)
let add_invariant t = add_scoped_invariant t t.scope


(* Instantiate the invariant constraint to the bound *)
let invars_of_bound ?(one_state_only = false) { invariants } =
  Invs.of_bound invariants (not one_state_only)
  


(*************************************************************************)
(* Candidates                                                            *)
(*************************************************************************)

(* Return true if the property is a candidate invariant *)
let is_candidate t prop =
  match (property_of_name t prop).P.prop_source with
  | P.Candidate _ -> true
  | _ -> false

let get_candidates t =
  List.fold_left (fun acc p ->
    match p.P.prop_source with
    | P.Candidate _ -> p.P.prop_term :: acc
    | _ -> acc
    ) [] t.properties
  |> List.rev

let get_candidate_properties t = List.filter (
  function
  | { P.prop_source = P.Candidate _ } -> true
  | _ -> false
) t.properties

let get_unknown_candidates t =
  List.fold_left (fun acc p ->
      if true (* || p.P.prop_source = P.Candidate *) then
        match p.P.prop_status with
        | P.PropUnknown | P.PropKTrue _ -> p.P.prop_term :: acc
        | P.PropInvariant _ | P.PropFalse _ -> acc
      else acc
    ) [] t.properties
  |> List.rev


let get_invariants { invariants } = invariants

let get_all_invariants t =
  t |> fold_subsystems (
    fun map { scope ; invariants } ->
      Scope.Map.add scope invariants map
  ) Scope.Map.empty

let clear_invariants { invariants } =
  Invs.clear invariants

let clear_all_invariants =
  iter_subsystems ~include_top:true clear_invariants

(* ********************************************************************** *)
(* Construct a transition system                                          *)
(* ********************************************************************** *)

let copy t =
  let copy subsystems_copy_f t =
    { t with invariants = Invs.copy t.invariants ;
    properties = List.map Property.copy t.properties ;
    subsystems = List.map (fun (s,i) -> (subsystems_copy_f s,i)) t.subsystems }
  in
  let copies = fold_subsystems ~include_top:true (
    fun copies t ->
      let subsystems_copy_f t =
        Scope.Map.find (scope_of_trans_sys t) copies
      in
      Scope.Map.add (scope_of_trans_sys t) (copy subsystems_copy_f t) copies
  ) Scope.Map.empty t in
  Scope.Map.find (scope_of_trans_sys t) copies

let mk_trans_sys 
  ?(instance_var_id_start = 0)
  scope
  instance_state_var
  init_flag_state_var
  global_state_vars
  state_vars
    state_var_bounds
    global_consts
  ufs
  init_uf_symbol
  init_formals
  init
  trans_uf_symbol
  trans_formals
  trans
  subsystems
  properties
  mode_requires
  invariants
=

  (* Map instance variables of this system and all subsystems to a
     unique term *)
  let instance_var_bindings = 

    (* Collect all instance state variables from subsystems *)
    List.fold_left (
      fun accum ({ instance_var_bindings }, instances) -> 

        (* Get state variables from bindings in subsystem *)
        let instance_state_vars = 
          List.map (
            fun (v, _) -> Var.state_var_of_state_var_instance v
          ) instance_var_bindings
        in

        (* Lift instance variables of all instances of the subsystem
          to this transition system *)
        List.fold_left (
          fun a { map_up } ->
            List.map (
              fun sv ->
                (* Get state variable in this transition system
                instantiating the state variable in the
                subsystem *)
                try SVM.find sv map_up

                (* Every state variable must be in the map *)
                with Not_found -> assert false
              ) instance_state_vars @ a
        ) accum instances
    ) (
      (* Start with instance state variable of this system if any *)
      match instance_state_var with
      | None -> []
      | Some sv -> [sv]
    )
    subsystems
    (* Create unique term for each instance variable *)
    |> List.mapi (
      fun i sv -> (
        Var.mk_const_state_var sv,
        (* Add start value of fresh instance identifiers *)
        Term.mk_num_of_int (i + instance_var_id_start)
      )
    )

  in

  (* Logic fragment of transition system  *)
  let logic = match Flags.Smt.logic () with

    (* Logic fragment should not be declared *)
    | `None -> `None

    (* Logic fragment given by option *)
    | `Logic s -> `SMTLogic s

    (* Find the logic fragment by going through terms and
       subsystems of the transition system *)
    | `detect ->

      let fun_symbols =
        List.fold_left
          (fun a ({trans_uf_symbol; init_uf_symbol},_) ->
            trans_uf_symbol :: init_uf_symbol :: a
          )
          []
          subsystems
      in

      `Inferred

        (List.fold_left
           
           (* Append logic of property term to list *)
           (fun acc { P.prop_term }  -> 
              TermLib.logic_of_term fun_symbols prop_term :: acc)
           
           (* Initial list of logics *)
           (

             (* Logic of initial state constraint *)
             TermLib.logic_of_term fun_symbols init ::

             (* Logic of transition relation *)
               TermLib.logic_of_term fun_symbols trans ::
             
             (* Logics of subsystems *)
             List.map
               (fun (t, _) -> match t.logic with
                  | `Inferred l -> l

                  (* If the logic for this system is being inferred,
                     the logics of the subsystems have been
                     inferred *)
                  | _ -> assert false) 
               subsystems

           )
           
           (* Add logics of properties *)
           properties

         (* Add logics from types of state variables *)
         |> List.rev_append
           (List.rev_map (fun sv ->
                StateVar.type_of_state_var sv
                |> TermLib.logic_of_sort
              ) state_vars)
           
         (* Join logics to the logic required for this system *)
         |> TermLib.sup_logics)

  in

  (* Increment start value of fresh instance identifier for next
     transition system *)
  let instance_var_id_start' = 
    instance_var_id_start + List.length instance_var_bindings
  in

  (* Make sure name scope is unique in transition system *)
  List.iter (
    fun (t, _) ->
      iter_subsystems (
        fun { scope = s } ->
          if Scope.equal scope s then
            Invalid_argument "mk_trans_sys: scope is not unique" |> raise
      ) t
  ) subsystems ;

  let state_vars =
    List.rev_append
      (List.rev_map Var.state_var_of_state_var_instance global_consts)
      state_vars in
  
  (* Transition system containing only the subsystems *)
  let trans_sys = 
    { scope;
      instance_state_var;
      init_flag_state_var;
      instance_var_bindings;
      global_state_vars;
      state_vars;
      state_var_bounds;
      subsystems;
      global_consts;
      ufs;
      init_uf_symbol;
      init_formals;
      init;
      trans_uf_symbol;
      trans_formals;
      trans;
      properties;
      mode_requires;
      logic;
      invariants}
  in

  trans_sys, instance_var_id_start'
  



(* Instantiates a term for the top system by going up the system
   hierarchy, for all instantiations of the input system. Returns the
   top system and the corresponding terms, paired with the
   intermediary systems and terms. Note that the input system term of
   the function will be in the result, either as intermediary or top
   level. *)
let instantiate_term_cert_all_levels
    trans_sys offset scope (term, cert) two_state = 

  (* merge maps of term -> certificate by keeping simplest certificate *)
  let merge_term_cert_maps _ (
    v1: Certificate.t option
  ) (
    v2: Certificate.t option
  ) =
    match v1, v2 with
    | Some ((k1, _) as c1), Some ((k2, _) as c2) ->
      if k1 < k2 then Some c1
      else if k1 > k2 then Some c2
      else
        let size_comp =
          compare (Certificate.size c1) (Certificate.size c2)
        in
        if size_comp <= 0 then Some c1 else Some c2
    | Some c1, None -> Some c1
    | None, Some c2 -> Some c2
    | None, None -> None
  in

  (* merge maps whose values are sets of terms by union *)
  let merge_term_set_maps _ v1 v2 = 
    match v1, v2 with
      | Some s1, Some s2 -> Some (
        Term.TermMap.merge merge_term_cert_maps s1 s2
      )
      | Some s1, None -> Some s1
      | None, Some s2 -> Some s2
      | None, None -> None
  in

  (* Instantiate term at all systems, add the instance at the top
     level to a list, and the instances at the intermediate levels
     to a map *)
  let rec instantiate_to_top offset term cert accum = function 

    (* At the top system *)
    | [] -> 

      (* Add to the list of terms at the top level only, not to the
          intermediate terms *)
      (Term.TermMap.singleton term cert, accum)
      
    (* At a system that is not the top system *)
    | (trans_sys, { map_up; guard_clock }) :: tl -> 

      (* Instantiate term to this system *)
      let inst_term t =
        Term.map_state_vars
          (fun sv -> 
             try SVM.find sv map_up with
               | Not_found ->
                 Format.eprintf "Not found in map up %a@." StateVar.pp_print_state_var sv;
                 assert false)
          t
        |> fun t ->
        (* let is_one_state = *)
        (*   match Term.var_offsets_of_term t with *)
        (*   | Some lo, Some up -> Numeral.(equal lo up) *)
        (*   | _ -> true *)
        (* in *)
        (* if is_one_state then t else guard_clock offset t *)
        if two_state then guard_clock offset t else t
      in

      let term' = inst_term term in
      let cert' = let k, phi = cert in k, inst_term phi in

      (* Add instaniated term to intermediate systems *)
      let accum' = 
        match tl with
          | [] -> accum
          | _ -> Map.add trans_sys (Term.TermMap.singleton term' cert') accum 
      in

      (* Continue instantiating *)
      instantiate_to_top offset term' cert' accum' tl

  in


  let merge_accum (t, i) (t', i') = 
    (Term.TermMap.merge merge_term_cert_maps t t', 
     Map.merge merge_term_set_maps i i')
  in

  let top_terms, intermediate_terms = 
    fold_subsystem_instances
      (fun ({ scope = s } as t) instances accum -> 
         
         let res = 
           
         (* Subsystem of scope of the term? *)
         if Scope.equal scope s then 
           
           (* Instantate term at all levels up to the top, return
              singleton lists *)
           instantiate_to_top 
             offset
             term
             cert
             (match instances with
               | [] -> Map.empty
               | _ -> Map.singleton t (Term.TermMap.singleton term cert))
             instances

       else

         (* Start with empty lists *)
         (Term.TermMap.empty, Map.empty)

       in

       (* Combine instances from subsystems and instances from this
          system *)
       List.fold_left merge_accum res accum
           
    )
    trans_sys
  in

  let res_set_to_list (t, s) = (t, Term.TermMap.bindings s) in

  (
    (trans_sys, top_terms) |> res_set_to_list, 
    Map.bindings intermediate_terms |> List.map res_set_to_list
  )


let get_state_var_bounds { state_var_bounds } = state_var_bounds



(* Same as above without certificates *)
let instantiate_term_all_levels trans_sys offset scope term two_state =
  let dummy_cert = -1, term in
  let (sys_top, t_top), inter_c =
    instantiate_term_cert_all_levels trans_sys offset scope (term, dummy_cert)
      two_state
  in
  (sys_top, List.map fst t_top),
  List.map (fun (subsys, t_subs) ->
      subsys, List.map fst t_subs) inter_c




(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
