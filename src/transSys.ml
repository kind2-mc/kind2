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

(* Abbreviations *)
module SVS = StateVar.StateVarSet
module SVT = StateVar.StateVarHashtbl

(* The transition system *)
type t = 
    { 

      (* INIT: constraints on system variables 

	 A list of formulas over system variables, no previous state
	 variables occur here *)
      mutable init : (StateVar.t * Term.t) list;

      (* CONSTR: global state constraints 

	 An equations defining the next-state value for each state
	 variabe from current-state and next-state variables *)
      mutable constr : Term.t SVT.t;

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

      (* Variable dependencies in CONSTR *)
      constr_dep : SVS.t SVT.t;
      
    }


(* Return list of pairs of entries in hash table *)
let def_list_of_constr t = SVT.fold (fun v t a -> (v, t) :: a) t.constr []

(* Add definitions in list to hash table *)
let constr_of_def_list c l = 
  List.iter
    (function (v, t) -> SVT.add c v t)
    l


(* Pretty-print the variable declarations *)
let pp_print_var ppf v =
  Format.fprintf
    ppf
    "@[<hv 1>%a@ %a@]"
    StateVar.pp_print_state_var v
    Type.pp_print_type (StateVar.type_of_state_var v)


(* Pretty-print an assignments of a terms to a state variable *)
let pp_print_assign ppf (var, term) = 

  Format.fprintf 
    ppf
    "@[<hv>%a :=@ %a@]"
    StateVar.pp_print_state_var var
    Term.pp_print_term term
    
(* Pretty-print an assignments of a terms to a state variable instance *)
let pp_print_var_assign ppf (var, term) = 

  Format.fprintf 
    ppf
    "@[<hv>%a :=@ %a@]"
    Var.pp_print_var var
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
    ( { init = i; constr = c; trans = g; invars = n; props = p  } as t) =

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
    (pp_print_list pp_print_assign "@ ") i
    (pp_print_list pp_print_assign "@ ") (def_list_of_constr t)
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
  let init_0 = 
    Term.mk_and 
      (List.map 
         (function (v, t) -> 
           Term.mk_eq 
             [Term.mk_var (Var.mk_state_var_instance v num_zero); t])
         z.init)
  in 


  (* Bump bound if greater than zero *)
  if i = 0 then init_0 else bump_state i init_0 


(* Instantiate the transition relation constraint to the bound *)
let constr_of_bound i z = 

  (* Create conjunction of initial state formulas *)
  let constr_1 = 
    Term.mk_and 
      (List.map 
         (function (v, t) -> 
           Term.mk_eq 
             [Term.mk_var (Var.mk_state_var_instance v num_one); t])
         (def_list_of_constr z))
  in 

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
  let invars_1 = Term.mk_and z.invars in 

  (* Bump bound if greater than zero *)
  if i = 1 then invars_1 else bump_state i invars_1 


(* Get all state variables at a given offset in the term *)
let state_vars_at_offset_of_term i term = 

  let i' = numeral_of_int i in

  (* Collect all variables in a set *)
  let var_set = 
    Term.eval_t
      (function 
        | Term.T.Var v 
            when 
              Var.offset_of_state_var_instance v = i' && 
              not (StateVar.is_definition (Var.state_var_of_state_var_instance v)) -> 
          (function [] -> Var.VarSet.singleton v | _ -> assert false)
        | Term.T.Var _ 
        | Term.T.Const _ -> 
          (function [] -> Var.VarSet.empty | _ -> assert false)
        | Term.T.App _ -> List.fold_left Var.VarSet.union Var.VarSet.empty)
      term
  in

  (* Return elements of a set as list *)
  Var.VarSet.elements var_set

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
            SVS.singleton 
              (Var.state_var_of_state_var_instance v)
          | _ -> assert false)
      | Term.T.Const _ -> 
        (function [] -> SVS.empty | _ -> assert false)
      | Term.T.App _ -> 
        List.fold_left 
          SVS.union 
          SVS.empty)
    term
  

(*

(* Get all state variables of a transition system *)
let state_vars_of_sys z = 

  (* List of sets of state variables in all terms *)
  let state_var_sets = 
    (List.map state_vars_of_term z.init) @
      (List.map state_vars_of_term z.constr) @
      (List.map (function (_, t) -> state_vars_of_term t) z.props)
  in

  (* Return elements of a set as list *)
  SVS.elements
    (List.fold_left 
       SVS.union
       SVS.empty
       state_var_sets)
  
*)
  
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
    (fun sv a -> if true then sv :: a else a)
    []
(*
  StateVar.fold
    (fun sv a -> if not (StateVar.is_definition sv) then sv :: a else a)
    []
*)

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
module StateVar =
struct

  type t = int

  let equal_state_vars = (=)
  let hash s = s
  let compare_state_vars = compare 

  module OrderedT = struct type t = int let compare = compare end

  module HashedT = struct type t = int let equal = (=) let hash = hash end

  module StateVarSet = Set.Make (OrderedT)

  module StateVarHashtbl = Hashtbl.Make (HashedT)

end


let dep = SVT.create 10;;

module S = SVS;;

let s1 = S.add 5 (S.add 3 (S.singleton 2));;
let s2 = S.singleton 4;;
let s3 = S.singleton 4;;
let s4 = S.singleton 6;;
let s5 = S.singleton 6;;
let s6 = S.singleton 7;;

module H = SVT;;

H.add dep 1 s1;;
H.add dep 2 s2;;
H.add dep 3 s3;;
H.add dep 4 s4;;
H.add dep 5 s5;;
H.add dep 6 s6;;
H.add dep 7 S.empty;;


*)


(* Return the dependencies between state variables *)
let dependencies_of_constr t = 

  (* Hash table of dependencies not initialized? *)
  if SVT.length t.constr_dep = 0 then
    
    (* Iterate over assignments and add dependencies to hash table *)
    SVT.iter
      (function state_var -> function term -> 
        
        (* Collect primed variables in assigned term *)
        let defining_vars = 
          Term.eval_t
            (function 
              | Term.T.Var v when Var.offset_of_state_var_instance v = num_one -> 
                (function 
                  | [] -> SVS.singleton (Var.state_var_of_state_var_instance v) 
                  | _ -> SVS.empty)
              | Term.T.Var _ -> 
                (function [] -> SVS.empty | _ -> assert false)
              | Term.T.Const _ -> 
                (function [] -> SVS.empty | _ -> assert false)
              | Term.T.App _ -> List.fold_left SVS.union SVS.empty)
            term
        in
        SVT.add t.constr_dep state_var defining_vars)
      t.constr;
  
  (* Return dependency hash table *)
  t.constr_dep


(* Return true if sv depends on any of the state variables in the list or any of the variables they depend on *)
let rec depends_on dep sv visited = function 

  (* Recursed into all children *)
  | [] -> false

  (* Take the first state variable *)
  | h :: tl -> 

    (* Found state variable in dependencies *)
    if StateVar.equal_state_vars sv h then true else

      (* Dependencies already seen? *)
      if SVS.mem h visited then 
      
        (* Continue with siblings *)
        depends_on dep sv visited tl

      else

        (* Recurse to children, mark variable as visited *)
        depends_on 
          dep 
          sv 
          (SVS.add h visited) 
          (try List.rev_append (SVS.elements (SVT.find dep h)) tl with Not_found -> tl)

(*
      
(* Order state variables by dependencies: a variables is smaller than all the variables is depends on *)
let compare_state_vars_depend_order dep sv1 sv2 =

  (* Compare state variables for equality and default if independent *)
  let sv1_sv2_order = StateVar.compare_state_vars sv1 sv2 in

  (* State variables are equal *)
  if sv1_sv2_order = 0 then 0 else 

    (* First state variable depends on second *)
    let sv1_depends_on_sv2 = depends_on dep sv1 (SVS.empty) [sv2] in
    
    (* Second state variable depends on first *)
    let sv2_depends_on_sv1 = depends_on dep sv2 (SVS.empty) [sv1] in
    
    (* Compare dependencies *)
    match sv1_depends_on_sv2, sv2_depends_on_sv1 with
        
      (* Make dependent state variable smaller *)
      | true, false -> -1
      | false, true -> 1
        
      (* State variables must not depend on each other *)
      | true, true -> failwith "Circular dependency"

      (* Default to order if state variables are independent *)
      | false, false -> sv1_sv2_order 


(* Order state variables by dependency in CONSTR: a variables is smaller than all the variables is depends on *)
let compare_state_vars_constr_dep t sv1 sv2 = 
  compare_state_vars_depend_order (dependencies_of_constr t) sv1 sv2   
        
    
(* Return true if sv depends on any of the state variables in the list or any of the variables they depend on *)
let rec defs_of_state_vars t dep visited accum = function 

  (* Recursed into all children *)
  | [] -> accum

  (* Take the first state variable *)
  | h :: tl -> 

    (* Dependencies already seen? *)
    if SVS.mem h visited then 
      
      (* Continue with siblings *)
      defs_of_state_vars t dep visited accum tl
        
    else

      (* Add definition if found, skip input or otherwise unspecified variables *)
      let accum' = 
        try (h, (SVT.find t.constr h)) :: accum with Not_found -> accum
      in

      (* Recurse to children, mark variable as visited *)
      defs_of_state_vars
        t
        dep 
        (SVS.add h visited) 
        accum'
        (try List.rev_append (SVS.elements (SVT.find dep h)) tl with Not_found -> tl)


*)


(* Recursively unfold definitions of state variables in dependency
   order: leaf definitions at the head of the list 

   Idea: check if the head element of the list is dependent on any of
   the elements in the tail of the list. If it is, skip it, because
   its definition will be unfolded later.
*)

let rec defs_of_state_vars t dep accum = function 

  (* Return list of definitions *)
  | [] -> accum

  | h :: tl -> 

    (* State variable depends on a state variable in tail? *)
    if depends_on dep h SVS.empty tl then 
      
      (* Skip and unfold definition later *)
      defs_of_state_vars t dep accum tl 

    else
      
      (* Add definition if found, skip input or otherwise unspecified variables *)
      let accum' = 
        try (Var.mk_state_var_instance h num_one, (SVT.find t.constr h)) :: accum with Not_found -> accum
      in
      
      (* Recurse for tail of list *)
      defs_of_state_vars 
        t 
        dep 
        accum' 
        (try List.rev_append (SVS.elements (SVT.find dep h)) tl with Not_found -> tl)


let constr_defs_of_state_vars t state_vars =

  (* Get hash table of dependencies *)
  let dep = dependencies_of_constr t in

  
  let res = defs_of_state_vars t dep [] state_vars in

  debug transSys
    "@[<v>Definitions from CONSTR:@,%a@]"
    (pp_print_list pp_print_var_assign "@ ") res
  in

  List.rev res


(*
let constr_defs_of_state_vars t state_vars =

  (* Get hash table of dependencies *)
  let dep = dependencies_of_constr t in

  (* Get definitions of all state variables *)
  let all_defs = defs_of_state_vars t dep SVS.empty [] state_vars in

  (* Sort definitions in dependency order of the state variables *)
  let defs_dep_order = 
    List.sort (function (v1, _) -> function (v2, _) -> compare_state_vars_constr_dep t v1 v2) all_defs 
  in 

  debug transSys
    "@[<v>Definitions from CONSTR:@,%a@]"
    (pp_print_list pp_print_assign "@ ") defs_dep_order
  in

  (* Turn state variables into primed variables *)
  List.rev (List.map (function (sv, t) -> (Var.mk_state_var_instance sv num_one, t)) defs_dep_order)
*)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
