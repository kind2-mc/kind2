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
module SVT = StateVar.StateVarHashtbl

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

    (* Scope of transition system *)
    scope: Scope.t;

    (* State variable that becomes true in the first instant and false
       again in the second and all following instants *)
    init_flag_state_var : StateVar.t;

    (* State variable to be bound to a unique term for each
       instance of the transition system *)
    instance_state_var : StateVar.t option;

    (* Assignments of unique terms to the instance variables of this
       transition system and its subsystems *)
    instance_var_bindings : (Var.t * Term.t) list;

    (* State variables of global scope, used for arrays. Each state
       variable has a list of upper bounds for its indexes. 

       To get all defined values, evaluate the instance state
       variable, and the terms for the index bounds first, then
       evaluate the uninterpreted function with the value of the
       instance variable as the first, and all indexes as following
       parameters. TODO: add this functionality to Eval. *)
    global_state_vars : (StateVar.t * Term.t list) list;

    (* State variables in the scope of this transition system 

       Also contains [instance_state_var] unless it is None, but not
       state variables in [global_state_vars]. *)
    state_vars : StateVar.t list;

    (* Transition systems called by this system, and for each instance
       additional information to map between state variables of the
       different scopes *)
    subsystems : (t * instance list) list;

    (* Other function declarations *)
    ufs : UfSymbol.t list;
    
    (* Logic fragment needed to express the transition system 

       TODO: Should this go somewhere more global? *)
    logic : TermLib.logic;

    (* Predicate symbol for initial state constraint *)
    init_uf_symbol : UfSymbol.t;

    (* Formal parameters of initial state constraint *)
    init_formals : Var.t list;

    (* Initial state constraint *)
    init : Term.t;

    (* Predicate symbol for transition relation *)
    trans_uf_symbol : UfSymbol.t;

    (* Formal parameters of transition relation *)
    trans_formals : Var.t list;

    (* Transition relation *)
    trans : Term.t;

    (* Properties to prove invariant for this transition system 

       Does not need to be mutable, because a Property.t is *)
    properties : Property.t list;

    (* Invariants about the current state *)
    mutable invariants_one_state : Term.t list;

    (* Invariants about current and previous state pairs *)
    mutable invariants_two_state : Term.t list;

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
  | P.PropInvariant -> Format.fprintf ppf ":invariant"
  | P.PropFalse _ -> Format.fprintf ppf ":false"


let pp_print_property_source ppf = function 
  | P.PropAnnot _ -> Format.fprintf ppf ":annotation"
  | P.Contract _ -> Format.fprintf ppf ":contract"
  | P.Generated _ -> Format.fprintf ppf ":generated"
  | P.ContractGlobalRequire _ -> Format.fprintf ppf ":global-req"
  | P.ContractModeRequire _ -> Format.fprintf ppf ":mode-req"
  | P.ContractGlobalEnsure _ -> Format.fprintf ppf ":global-ens"
  | P.ContractModeEnsure _ -> Format.fprintf ppf ":mode-ens"
  | P.Instantiated _ -> Format.fprintf ppf ":instantiated"
  | P.Requirement _ -> Format.fprintf ppf ":requirement"

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
      properties;
      invariants_one_state;
      invariants_two_state } = 

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
let init_of_bound { instance_var_bindings; init } i = 

  close_term instance_var_bindings init
  |> bump_relative init_base i 
  

(* Close the initial state constraint by binding all instance
   identifiers, and bump the state variable offsets to be at the given
   bound *)
let trans_of_bound { instance_var_bindings; trans } i = 

  close_term instance_var_bindings trans
  |> bump_relative trans_base i 
  

(* Return the instance variables of this transition system, the
   initial state constraint at [init_base] and the transition relation
   at [trans_base] with the instance variables free. *)
let init_trans_open { instance_var_bindings; init; trans } = 

  (List.map 
     (fun (v, _) -> Var.state_var_of_state_var_instance v)
     instance_var_bindings, 
   init,
   trans)




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

(* Set of transition systems *)
module Set = Set.Make (T)

(* Map of transition systems *)
module Map = Map.Make (T)

(* Hash table of transition systems *)
module Hashbtl = Hashtbl.Make (T)



(* **************************************************************** *)
(* State Variables, Predicates and Declarations                     *)
(* **************************************************************** *)


(* Return state variables of the transition system *)
let state_vars { state_vars } = state_vars


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

  |> 

  (* Create variable of constant state variable *)
  List.map Var.mk_const_state_var

  |>

  (* Declare variables *)
  Var.declare_constant_vars declare


(* Return the init flag at the given bound *)
let declare_init_flag_of_bounds { init_flag_state_var } declare lbound ubound = 
  
  (* Instantiate the init flag only between the given bounds *)
  vars_of_bounds' [ init_flag_state_var ] lbound ubound []

  (* Evaluate declaration function *)
  |> Var.declare_vars declare 


(* Declare other functions symbols *)
let declare_ufs { ufs } declare =
  List.iter declare ufs
    
      
(* Define initial state predicate *)
let define_init define { init_uf_symbol; init_formals; init } = 
  define init_uf_symbol init_formals init


(* Define transition relation predicate *)
let define_trans define { trans_uf_symbol; trans_formals; trans } =
  define trans_uf_symbol trans_formals trans


(* Define predicates, declare constant and global state variables, and
   declare state variables of the top system between and including the
   given offsets *)
let define_and_declare_of_bounds
    ?(declare_sub_vars=false) 
    trans_sys
    define 
    declare
    lbound
    ubound =

  (* Iterate over all subsystems *)
  iter_subsystems 
    ~include_top:false
    (fun t -> 

       (* Declare constant state variables of subsystem *)
       if declare_sub_vars then 
         (declare_const_vars t declare; 
          declare_vars_of_bounds t declare lbound ubound);
       
       (* Define initial state predicate *)
       define_init define t;

       (* Define transition relation predicate *)
       define_trans define t)

    trans_sys;
  
  (* Declare other functions of top system *)
  declare_ufs trans_sys declare;
       
  (* Declare constant state variables of top system *)
  declare_const_vars trans_sys declare;
       
  (* Declare constant state variables of top system *)
  declare_vars_of_bounds trans_sys declare lbound ubound
       

let init_uf_def { init_uf_symbol; init_formals; init } = 
  (init_uf_symbol, (init_formals, init))


let trans_uf_def { trans_uf_symbol; trans_formals; trans } = 
  (trans_uf_symbol, (trans_formals, trans))



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

    (* Add definition of the top system *)
    [ trans_uf_def trans_sys; init_uf_def trans_sys ]
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
        P.prop_source = P.Requirement _
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


(* Return true if the property is proved invariant *)
let is_proved trans_sys prop = 

  try 
    ( match (property_of_name trans_sys prop).P.prop_status with
      | P.PropInvariant -> true
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
let set_prop_status trans_sys p s = 

  try 
    
    P.set_prop_status (property_of_name trans_sys p) s

  with Not_found -> raise Not_found


let set_prop_invariant trans_sys p = 

  try 
    
    P.set_prop_invariant (property_of_name trans_sys p)

  with Not_found -> raise Not_found
  

let set_prop_ktrue trans_sys k p = 

  try 
    
    P.set_prop_ktrue (property_of_name trans_sys p) k

  with Not_found -> raise Not_found


let set_prop_false trans_sys p c = 

  try 
   
    P.set_prop_false (property_of_name trans_sys p) c

  with Not_found -> raise Not_found
  

(* Return current status of all properties *)
let get_prop_status_all t = 
  
  List.map 
    (fun { P.prop_name; P.prop_status } -> (prop_name, prop_status))
    t.properties


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


(* Return true if all properties are either valid or invalid *)
let all_props_proved t =
  
  List.for_all
    (fun { P.prop_status } -> match prop_status with
       | P.PropUnknown
       | P.PropKTrue _ -> false
       | P.PropInvariant
       | P.PropFalse _ -> true)
    t.properties



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


(* Add an invariant to the transition system *)
let add_scoped_invariant t scope invar =

  let is_one_state = 
    match Term.var_offsets_of_term invar with
      | None, None 
      | Some _, None 
      | None, Some _ -> true 
      | Some l, Some u -> Numeral.(equal l u)
  in

  iter_subsystems
    (fun ({ scope = s; invariants_two_state; invariants_one_state } as t) -> 
       
       if Scope.equal scope s then
         if is_one_state then 
           t.invariants_one_state <- invar :: invariants_one_state
         else
           t.invariants_two_state <- invar :: invariants_two_state)
    t


(* Add an invariant to the transition system *)
let add_invariant t invar = add_scoped_invariant t t.scope invar


(* Instantiate the initial state constraint to the bound *)
let invars_of_bound
    ?(one_state_only = false)
    { invariants_one_state; invariants_two_state } 
    i = 

  (* Create conjunction of property terms *)
  let invars_0 = 

    (* Only one-state invariants? *)
    (if one_state_only then

       (* Return only one-state invariants *)
       invariants_one_state

     else

       (* Return all invariants *)
       invariants_one_state @ invariants_two_state)

  in 

  (* Bump bound if greater than zero *)
  if Numeral.(i = zero) then invars_0 else List.map (Term.bump_state i) invars_0


(* ********************************************************************** *)
(* Construct a transition system                                          *)
(* ********************************************************************** *)

let mk_trans_sys 
    ?(instance_var_id_start = 0)
    scope
    instance_state_var
    init_flag_state_var
    global_state_vars
    state_vars
    ufs
    init_uf_symbol
    init_formals
    init
    trans_uf_symbol
    trans_formals
    trans
    subsystems
    properties
    invariants_one_state 
    invariants_two_state = 

  (* Map instance variables of this system and all subsystems to a
     unique term *)
  let instance_var_bindings = 

    (* Collect all instance state variables from subsystems *)
    List.fold_left
      (fun accum ({ instance_var_bindings }, instances) -> 

         (* Get state variables from bindings in subsystem *)
         let instance_state_vars = 
           List.map 
             (fun (v, _) -> Var.state_var_of_state_var_instance v)
             instance_var_bindings
         in

         (* Lift instance variables of all instances of the subsystem
            to this transition system *)
         List.fold_left
           (fun a { map_up } -> 
              List.map
                (fun sv -> 
                   try 

                     (* Get state variable in this transition system
                        instantiating the state variable in the
                        subsystem *)
                     (SVM.find sv map_up)

                   (* Every state variable must be in the map *)
                   with Not_found -> assert false)
                instance_state_vars
              @ a)
           accum
           instances)

      (* Start with instance state variable of this system if any *)
      (match instance_state_var with
        | None -> []
        | Some sv -> [sv])

      subsystems

    |> 

    (* Create unique term for each instance variable *)
    List.mapi
      (fun i sv -> 
         (Var.mk_const_state_var sv,

          (* Add start value of fresh instance identifiers *)
          Term.mk_num_of_int (i + instance_var_id_start)))

  in

  (* Logic fragment of transition system  *)
  let logic = match Flags.smtlogic () with

    (* Logic fragment should not be declared *)
    | `None -> `None

    (* Logic fragment given by option *)
    | `Logic s -> `SMTLogic s

    (* Find the logic fragment by going through terms and
       subsystems of the transition system *)
    | `detect ->

      `Inferred

        (List.fold_left
           
           (* Append logic of property term to list *)
           (fun acc { P.prop_term }  -> 
              TermLib.logic_of_term prop_term :: acc)
           
           (* Initial list of logics *)
           (

             (* Logic of initial state constraint *)
             TermLib.logic_of_term init ::

             (* Logic of transition relation *)
               TermLib.logic_of_term trans ::
             
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
           
         (* Join logics to the logic required for this system *)
         |> TermLib.sup_logics)

  in

  (* Increment start value of fresh instance identifier for next
     transition system *)
  let instance_var_id_start' = 
    instance_var_id_start + List.length instance_var_bindings
  in

  (* Make sure name scope is unique in transition system *)
  List.iter
    (fun (t, _) ->
       iter_subsystems 
         (fun { scope = s } -> 
            if Scope.equal scope s then
              raise (Invalid_argument "mk_trans_sys: scope is not unique"))
         t)
       subsystems;
  
  (* Transition system containing only the subsystems *)
  let trans_sys = 
    { scope;
      instance_state_var;
      init_flag_state_var;
      instance_var_bindings;
      global_state_vars;
      state_vars;
      subsystems;
      ufs;
      init_uf_symbol;
      init_formals;
      init;
      trans_uf_symbol;
      trans_formals;
      trans;
      properties;
      logic;
      invariants_one_state;
      invariants_two_state }
  in

  trans_sys, instance_var_id_start'
  





let instantiate_term_all_levels trans_sys offset scope term = 

  (* Merge two maps of terms sets by forming the union of the two sets

     Use in a [Map.S.merge]. *)
  let merge_term_set_maps _ v1 v2 = 
    match v1, v2 with
      | Some s1, Some s2 -> Some (Term.TermSet.union s1 s2)
      | Some s1, None -> Some s1
      | None, Some s2 -> Some s2
      | None, None -> None
  in

  (* Instantiate term at all systems, add the instance at the top
     level to a list, and the instances at the intermediate levels
     to a map *)
  let rec instantiate_to_top offset term accum = function 

    (* At the top system *)
    | [] -> 

      (* Add to the list of terms at the top level only, not to the
          intermediate terms *)
      (Term.TermSet.singleton term, accum)
      
    (* At a system that is not the top system *)
    | (trans_sys, { map_up; guard_clock }) :: tl -> 

      (* Instantiate term to this system *)
      let term' = 
        Term.map_state_vars
          (fun sv -> 
             try SVM.find sv map_up with
               | Not_found -> 
                 assert false)
          term
        |> guard_clock offset
      in

      (* Add instaniated term to intermediate systems *)
      let accum' = 
        match tl with
          | [] -> accum
          | _ -> Map.add trans_sys (Term.TermSet.singleton term') accum 
      in

      (* Continue instantiating *)
      instantiate_to_top offset term' accum' tl

  in


  let merge_accum (t, i) (t', i') = 
    (Term.TermSet.union t t', 
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
             (match instances with
               | [] -> Map.empty
               | _ -> Map.singleton t (Term.TermSet.singleton term))
             instances

       else

         (* Start with empty lists *)
         (Term.TermSet.empty, Map.empty)

       in

       (* Combine instances from subsystems and instances from this
          system *)
         List.fold_left merge_accum res accum
           
    )
    trans_sys
  in

  let res_set_to_list (t, s) = (t, Term.TermSet.elements s) in

  ((trans_sys, top_terms) |> res_set_to_list, 
   Map.bindings intermediate_terms
   |> List.map res_set_to_list)

(*



type pred_def = (UfSymbol.t * (Var.t list * Term.t)) 

(* Offset of state variables in initial state constraint *)
let init_base = Numeral.zero

(* Offset of primed state variables in transition relation *)
let trans_base = Numeral.one

(* Offset of primed state variables in properties and invariants *)
let prop_base = Numeral.zero

type t = {
  
  (* Scope of state variables *)
  scope: string list;

  (* State variables of top node *)
  state_vars: StateVar.t list ;

  (* Initial predicate of the system. *)
  init: pred_def ;

  (* Transition predicate of the system. *)
  trans: pred_def ;

  (* The subsystems of this system. *)
  subsystems: t list ;

  (* Properties of the transition system to prove invariant *)
  properties : property list; 

  (* The source which produced this system. *)
  source: source ;

  (* The logic fragment in which is expressed the system and its properties. *)
  logic: TermLib.logic;
  
  (* Invariants *)
  mutable invars: Term.t list;

  (* Systems instantiating this system, and for each instantiation a
     map from state variables of this system to the state variables of
     the instantiating system as well as a function to guard Boolean
     terms. *)
  mutable callers : 
            (t
             * ( ( (StateVar.t * StateVar.t) list
                   * (Term.t -> Term.t)
                 ) list )
            ) list ;

  (* Abstraction of the transition system. Contains the scopes of the
     systems to abstract. Mutable, because it is changed by
     compositional analysis. *)
  mutable abstraction: string list list ;

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
        caller'.scope = caller.scope ->
      ((caller', (c :: c')) :: accum) @ tl
    | h :: tl -> add_caller' (h :: accum) tl 
  in

  callee.callers <- add_caller' [] callee.callers

let get_callers { callers } = List.map fst callers

(* Number of times this system is instantiated in other systems. *)
let instantiation_count { callers } =
  callers
  |> List.fold_left
       ( fun sum (sys,maps) ->
         sum + (List.length maps) )
       0

(* Pretty prints an abstraction. *)
let pp_print_trans_sys_abstraction ppf { abstraction } =
  Format.fprintf
    ppf
    "@[<v>%a@]"
    (pp_print_list
       (pp_print_list Format.pp_print_string ".")
       ",@,")
    abstraction

(* The abstraction of the system. *)
let get_abstraction { abstraction } = abstraction

(* Sets the abstraction for a system. *)
let set_abstraction sys abstraction =
  sys.abstraction <- abstraction

(* Returns [Some(true)] if the contract is global, [Some(false)] if it's not,
   and [None] if the system has no contracts. *)
let contract_is_global t contract_name =
  let rec loop = function
    | Global (_,_,n) :: tail ->
      if n = contract_name then Some true else loop tail
    | Mode (_,_,n) :: tail ->
      if n = contract_name then Some false else loop tail
    | [] -> None
  in
  match t.contracts with
  | None -> None
  | Some (_,_,contracts) -> loop contracts

(* Returns the contracts of a system. *)
let get_contracts = function
  | { contracts = None } -> []
  | { contracts = Some(_,_,list) } ->
     list |> List.map info_of_contract

(* Returns the subsystems of a system. *)
let get_subsystems { subsystems } = subsystems

(* Return the input used to create the transition system *)
let get_scope t = t.scope

(* Name of the system. *)
let get_name t = t.scope |> String.concat "/"

(* Source name of the system. *)
let get_source_name t =
  let rec loop = function
    | [ last ] -> last.LustreNode.name |> LustreIdent.string_of_ident false
    | _ :: tail -> loop tail
    | [] -> get_name t
  in

  callers
  |> List.map
       ( fun (sys, maps) ->

         (* Building one new term per instantiation mapping for
            sys. *)
         let terms =
           maps
           |> List.map
               (* For each map of this over-system, substitute the
                  variables of term according to map. *)
               ( fun (map,f) ->
                 Term.map
                   (substitute_fun_of_map map)
                   term
                 |> f )
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

  let rec iterate_over_subsystems ({subsystems} as sys) continuation result =
    insert_subsystem sys result
    |> continue subsystems continuation

  and continue subsystems continuation result =

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

(* Returns a triplet of the concrete subsystems, the refined ones, and the
   abstracted ones. Does not contain the input system. *)
let get_abstraction_split ({ abstraction } as sys) =
  let rec loop c r a = function
    | [ top ] -> assert ( top.scope = sys.scope ) ; c, r, a
    | subsys :: tail ->
      if List.mem subsys.scope abstraction then loop c r (subsys::a) tail
      else ( match subsys.contracts with
        | None -> loop (subsys::c) r a tail
        | Some _ -> loop c (subsys::r) a tail
      )
    | [] -> c, r, a
  in
  get_all_subsystems sys |> loop [] [] [] 

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

let pp_print_contract ppf contract =
  let name, desc = match contract with
    | Global (_,_,n) -> n,"global"
    | Mode (_,_,n) -> n,"mode"
  in
    
  Format.fprintf
    ppf
    "%s contract %s"
    desc
    name

let pp_print_contracts ppf = function
  | None -> Format.fprintf ppf "None"
  | Some (actlit,req,contracts) ->
     Format.fprintf
       ppf
       "@[<hv>\
        Actlit: %a@ \
        Requirement: %a@ \
        @[<v 2>Contracts:@ %a@]"
       StateVar.pp_print_state_var actlit
       StateVar.pp_print_state_var req
       (pp_print_list pp_print_contract "@ ") contracts


let pp_print_trans_sys 
    ppf
    ({ uf_defs;
       state_vars;
       logic;
       properties;
       contracts;
       invars;
       source;
       callers } as trans_sys) = 

  Format.fprintf 
    ppf
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
    (pp_print_list pp_print_state_var "@ ") state_vars
    TermLib.pp_print_logic logic
    (pp_print_list pp_print_uf_defs "@ ") (uf_defs)
    Term.pp_print_term (init_term trans_sys)
    Term.pp_print_term (trans_term trans_sys)
    (pp_print_list pp_print_property "@ ") properties
    pp_print_contracts contracts
    (pp_print_list Term.pp_print_term "@ ") invars
    (pp_print_list (fun ppf { LustreNode.name } -> LustreIdent.pp_print_ident false ppf name) "@ ") (match source with Lustre l -> l | _ -> [])
    (pp_print_list pp_print_callers "@,") callers


(* Determine the required logic for the SMT solver *)
let get_logic t = t.logic

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
let mk_trans_sys scope state_vars init trans subsystems props source =

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

(* FIXME: Why is this unused?

  (* Looks in the subsystems for one such that 'f' applied to the
     subsys is uf. *)
  let find_subsystem f uf =
    List.find (fun subsys -> uf == f subsys) subsystems
  in
*)

(* FIXME: Why is this unused?

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
           | TermLib.Contract (pos, name) ->
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

  (* Getting all abstraction activation literals from subsystems. *)
  let abstraction_state_vars =

    (* Iterates over a list of systems, maintaining the set of the
       abstraction variables encountered so far as a set. *)
    let rec loop svars = function

      | sys :: tail ->
         (* Getting all subsystems of [sys], including [sys]. *)
         let all_systems = get_all_subsystems sys in

         (* Removing subsystems of [sys] from the tail. *)
         let tail =
           tail
           |> List.filter
                (fun sys ->
                 List.exists
                   (fun sys' -> sys.scope <> sys'.scope)
                   all_systems)
         in
         let svars =
           (* Retrieving abstraction actlits from all systems. *)
           all_systems
           |> List.fold_left
                (fun set sys ->
                 match sys.contracts with
                 | None  -> set
                 | Some (sv,_,_) ->
                    StateVar.StateVarSet.add sv set)
                svars
         in
         loop svars tail

      | [] -> StateVar.StateVarSet.elements svars
    in

    let abs_svars =
      match contracts_option with
      | None -> StateVar.StateVarSet.empty
      | Some (sv,_,_) ->
         StateVar.StateVarSet.of_list [sv]
    in

    loop abs_svars subsystems
  in
*)

  (* find the logic of the transition system by goint through its terms and its
     subsystems *)
  let logic = match Flags.smtlogic () with
    | `None -> `None
    | `Logic s -> `SMTLogic s
    | `detect ->
      `Inferred
        (List.fold_left (fun acc (_, _, p) -> TermLib.logic_of_term p :: acc)
           ((init  |> snd |> snd |> TermLib.logic_of_term) ::
            (trans |> snd |> snd |> TermLib.logic_of_term) ::
            List.map (fun sys -> match sys.logic with
                | `Inferred l -> l
                | _ -> assert false) subsystems)
           props
         |> TermLib.sup_logics)
  in
  
  let system =
    { scope = scope;
      uf_defs = get_uf_defs [ (init, trans) ] subsystems ;
      state_vars =
        (abstraction_state_vars @ state_vars)
        |> List.sort StateVar.compare_state_vars ;
      init = init ;
      trans = trans ;
      properties = properties ;
      contracts = contracts_option ;
      subsystems = subsystems ;
      logic = logic;
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
let vars_of_bounds'' skip trans_sys lbound ubound =
  vars_of_bounds'
    ( trans_sys.state_vars
      |> List.filter
           ( fun sv -> List.memq sv skip
                       |> not ) )
    lbound
    ubound
    []

(* Returns the variables of the transition system between two
   bounds. *)
let vars_of_bounds t lb ub = vars_of_bounds'' [] t lb ub


(* Declares variables of the transition system between two offsets. *)
let declare_vars_of_bounds'
      skip t declare lbound ubound =
  (* Declaring non-constant variables. *)
  vars_of_bounds'' skip t lbound ubound
  |> (fun vars ->
      Var.declare_vars declare vars)

(* Declares variables of the transition system between two offsets. *)
let declare_vars_of_bounds t declare assert_term lbound ubound =
  declare_vars_of_bounds' [] t declare lbound ubound ;

  (* Force top level contract requirement. *)
  match t.contracts with
    | Some (_,req,_) ->
       vars_of_bounds' [req] lbound ubound []
       |> List.iter
            ( fun var -> Term.mk_var var |> assert_term )
    | None -> ()


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
let props_list_of_bound_not_valid t i = 
  named_terms_list_of_bound
    ( t.properties
      |> List.filter (function
                       | { prop_status = PropInvariant } -> false
                       | _ -> true) )
    i

(* Instantiate all properties to the bound *)
let props_list_of_bound_unknown t i = 
  named_terms_list_of_bound
    ( t.properties
      |> List.filter (function
         | { prop_status = PropInvariant } -> false
         | { prop_status = PropFalse _ } -> false
         | _ -> true
      ) )
    i


(* Instantiate all properties to the bound *)
let props_of_bound t i = 
  Term.mk_and (List.map snd (props_list_of_bound t i))

(* Instantiate all properties to the bound *)
let props_of_bound_not_valid t i = 
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



let contract_of_name ({ contracts } as sys) to_find =
  try
    match contracts with
    | None ->
       Format.asprintf
         "System %a has no contracts."
         pp_print_trans_sys_name sys
       |> failwith
    | Some (_, _, contracts) ->
       List.find
         (fun contract ->
          to_find = name_of_contract contract)
         contracts
  with
  | Not_found ->
     Format.sprintf
       "Cannot locate contract %s."
       to_find
     |> failwith

(* Returns [true] iff all subrequirement properties of the system are
   invariants. *)
let subrequirements_valid { properties } =
  let rec loop = function
    | { prop_status = status ;
        prop_source = TermLib.Requirement (_,_,_) }
      :: tail ->
       if status = PropInvariant then loop tail
       else false
    | _ :: tail -> loop tail
    | [] -> true
  in
  loop properties

(* Returns true iff all subrequirements related to a scope are
   invariants. *)
let proved_requirements_of { properties } scope =
  let rec loop = function

    (* Requirement for [scope]. *)
    | { prop_status = status ;
        prop_source =
          TermLib.Requirement (_, scope', _) }
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

(* Returns true if the contract of the input system is an
   invariant. @raise Not_found if the system has no contracts. *)
let is_contract_proved = function
  | { contracts = None } -> raise Not_found
  | { properties } ->
     properties
     |> List.for_all
          (function
            | { prop_source = TermLib.Contract(_);
                prop_status } ->
               ( match prop_status with
                 | PropInvariant -> true
                 | _ -> false )
            | _ -> true)

(* Mark property as invariant *)
let set_prop_invariant t prop =

  (* Get property by name *)
  let p = property_of_name t prop in

  (* Check current status *)
  match p.prop_status with

  | PropUnknown
  | PropKTrue _ ->
     (* Property was not known to be invariant. *)
     
     ( match p.prop_source with
       | TermLib.Requirement (_,_,guarantees) ->
          (* Property is a requirement, setting prop_status and
                 returning guarantees. *)
          p.prop_status <- PropInvariant ;
          (* guarantees *)
          (* |> List.map ( fun sv -> *)
          (*               Var.mk_state_var_instance sv init_base *)
       (*               |> Term.mk_var ) *)
          []
       | _ ->
          p.prop_status <- PropInvariant ;
          [] )

  | PropInvariant ->
     p.prop_status <- PropInvariant ;
     []

  (* Fail if property was false or k-false *)
  | PropFalse _ -> raise (Failure "prop_invariant")

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

(* Resets the list of invariants of the system. *)
let reset_invariants t =
  t.invars <- [] ;
  t.properties
  |> List.iter
       ( function
         | { prop_term = term ; prop_status = PropInvariant } ->
            t.invars <- term :: t.invars
         | _ -> () )

(* Lifts valid properties of the system. ONLY lifts properties from
   annotations or generated ones. *)
let lift_valid_properties =
  let rec lift_props
            to_update
            { scope ; properties ; callers } =
    match
      properties
      |> List.filter
           ( function
             | { prop_source = TermLib.PropAnnot _ ;
                 prop_status = PropInvariant }
             | { prop_source = TermLib.Instantiated _ ;
                 prop_status = PropInvariant }
             | { prop_source = TermLib.Generated _ ;
                 prop_status = PropInvariant } -> true
             | _ -> false )

    with

    (* Nothing to lift, continuing. *)
    | [] -> continue to_update

    | props ->
       
       props
       |> List.iter
            ( fun { prop_name } ->

              (* Iterate on all callers. *)
              callers
              |> List.iter
                   ( fun (caller, _) ->

                     (* Iterate on all properties of the caller. *)
                     caller.properties
                     |> List.iter
                          ( function

                            (* Find the correct instantiated property. *)
                            | ({ prop_source =
                                   TermLib.Instantiated (scope',name')
                               } as prop) ->

                               if scope = scope' && prop_name = name'
                               then
                                 (* Update its status. *)
                                 prop.prop_status <- PropInvariant

                            | prop -> () ) ) ) ;

       ( callers
         |> List.map (fun (caller,_) -> caller) )
       @ to_update
       |> continue

  and continue = function
    | [] -> ()
    | head :: tail ->
       lift_props
         (* Removing redundant systems in continuation. *)
         ( tail |> List.filter (fun sys -> sys.scope != head.scope) )
         head
  in

  lift_props []
       

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
         "Trying to set [%s] true at %d on system [%s].@.  @[<v>%a@]@."
         prop
         k
         (get_name t)
         (pp_print_list (fun ppf { prop_name ; prop_status } ->
           Format.fprintf
            ppf
            "%s %a"
            prop_name
            pp_print_prop_status_pt
            prop_status
         ) "@," )
         t.properties ;
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

  | PropInvariant ->
     let invars =
       set_prop_invariant t p
     in
     t.invars <- invars @ t.invars

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
         
  


let pp_print_trans_sys 
    ppf
    ({ uf_defs;
       state_vars;
       properties;
       invars;
       source;
       logic;
       callers } as trans_sys) = 

  Format.fprintf 
    ppf
    "@[<v>@[<hv 2>(state-vars@ (@[<v>%a@]))@]@,\
          %a@,\
          @[<hv 2>(init@ (@[<v>%a@]))@]@,\
          @[<hv 2>(trans@ (@[<v>%a@]))@]@,\
          @[<hv 2>(props@ (@[<v>%a@]))@]@,\
          @[<hv 2>(invar@ (@[<v>%a@]))@]@,\
          @[<hv 2>(source@ (@[<v>%a@]))@]@,\
          @[<hv 2>(logic %a)@]@,\
          @[<hv 2>(callers@ (@[<v>%a@]))@]@."
    (pp_print_list pp_print_state_var "@ ") state_vars
    (pp_print_list pp_print_uf_defs "@ ") (uf_defs)
    Term.pp_print_term (init_term trans_sys)
    Term.pp_print_term (trans_term trans_sys)
    (pp_print_list pp_print_property "@ ") properties
    (pp_print_list Term.pp_print_term "@ ") invars
    (pp_print_list (fun ppf { LustreNode.name } -> LustreIdent.pp_print_ident false ppf name) "@ ") (match source with Lustre l -> l | _ -> [])
    TermLib.pp_print_logic logic
    (pp_print_list pp_print_callers "@,") callers
      
 

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

(* Defines abstraction literals for a transition system base on some
   abstraction. *)
let constrain_abstraction_actlits
      systems abstraction assert_term =

  let rec loop = function

    | { scope ; contracts = None } :: tail ->
       (* System cannot be abstracted, skipping. *)
       loop tail

    | { scope ; contracts = Some (actlit, req, _) } :: tail ->
       (* Value the actlit will be defined as. *)
       let term =
         Var.mk_const_state_var actlit
         |> Term.mk_var
         |> (if List.mem scope abstraction
             then identity else Term.mk_not)
       in
       (* Declaring [actlit]. *)
       (* declare *)
       (*   (StateVar.uf_symbol_of_state_var actlit) ; *)
       assert_term term ;
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
      sys
      (* Solver related functions. *)
      comment
      define
      declare
      assert_term
      (* Bounds for variable declaration. *)
      lbound
      ubound =

  Format.asprintf
    "|=====| Setting up solver for system %a."
    pp_print_trans_sys_name sys
  |> comment ;


  (* All subsystems of [sys], including [sys]. *)
  let all_systems = get_all_subsystems sys in
       
  let req_svar = match sys.contracts with
    | Some (_,req,_) -> [ req ]
    | None -> []
  in

  (if declare_top_vars_only then [ sys ] else all_systems)
  |> List.fold_left
       ( fun common_svars sys' ->

         Format.asprintf
           "|===| Declaring variables of %a for [%a,%a]."
           pp_print_trans_sys_name sys'
           Numeral.pp_print_numeral lbound
           Numeral.pp_print_numeral ubound
         |> comment ;

         comment "Constants." ;

         (* Declaring constant variables, skipping common ones. *)
         vars_of_bounds'' common_svars sys' lbound lbound
         |> Var.declare_constant_vars declare ;

         comment "Non-constant state variables." ;

         (* Declaring state variables, skipping common ones. *)
         declare_vars_of_bounds'
           common_svars sys' declare lbound ubound ;

         (* A system has all its subsystems abstraction actlits as
            state variables. We go through all systems in topological
            order, remembering the abstraction actlits. *)
         match sys'.contracts with
         | None -> common_svars
         | Some (abs_svar,_,_) -> abs_svar :: common_svars )
       [] ;

  ( match req_svar with
    | [] -> ()
    | _ ->
       comment "|===| Forcing contract requirement." ;
       vars_of_bounds' req_svar lbound ubound []
       |> List.iter
            ( fun var -> var |> Term.mk_var |> assert_term ) );
  
  comment "|===| Constraining abstraction actlits for all systems." ;
  Format.sprintf
    "|          abstracting [%s]"
    (sys.abstraction
     |> List.map (String.concat ".")
     |> String.concat ", ")
  |> comment ;
  constrain_abstraction_actlits
    all_systems sys.abstraction assert_term ;
  
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
let instantiate_term top { callers } term =

  let legal_systems = get_all_subsystems top in

  callers
  |> List.fold_left
       ( fun list (sys, maps) ->

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

         (* Only lift to legal systems. *)
         if List.memq sys legal_systems then
           
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

           (sys, terms) :: list

         else list )
       []

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
let instantiate_term_all_levels top_t t term =
    

  let is_top sys = sys == top_t || is_top sys in

  let rec loop at_top intermediary = function
    | (sys, (term :: term_tail)) :: tail ->

      debug transSys "[loop] sys: %s" (sys.scope |> String.concat "/") in

       (* Instantiating this term upward. *)
       let at_top', intermediary', recursive' =
         instantiate_term top_t sys term
         |> List.fold_left
              ( fun (at_top'', intermediary'', recursive'')
                    ((sys',_) as pair) ->

                debug transSys
                      "[loop] inst sys: %s"
                      (sys'.scope |> String.concat "/") in

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
let instantiate_term_top top_t t term =

  let rec loop at_top = function
      
    | (sys, ((term :: term_tail) as list)) :: tail ->
       
       (* Instantiating this term upward. *)
       ( match instantiate_term top_t sys term with
           
         | [] ->
            (* Nothing, so sys is the top node. *)
            loop (List.rev_append list at_top) tail

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

  loop [] (instantiate_term top_t t term)

*)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
