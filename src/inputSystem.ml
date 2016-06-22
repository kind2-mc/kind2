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

module S = SubSystem
module Lus = LustreNode

module SVM = StateVar.StateVarMap

type _ t =
| Lustre : (LustreNode.t S.t * LustreGlobals.t) -> LustreNode.t t
| Native : TransSys.t S.t -> TransSys.t t
| Horn : unit S.t -> unit t

let read_input_lustre input_file = Lustre (LustreInput.of_file input_file)

let translate_contracts_lustre = ContractsToProps.translate_file

let read_input_native input_file = Native (NativeInput.of_file input_file)

let read_input_horn input_file = assert false

let ordered_scopes_of (type s) : s t -> Scope.t list = function
  | Lustre (subsystem, _) ->
    S.all_subsystems subsystem
    |> List.map (fun { S.scope } -> scope)

  | Native subsystem ->
    S.all_subsystems subsystem
    |> List.map (fun { S.scope } -> scope)

  | Horn subsystem -> assert false

(* Uid generator for test generation params.

/!\
    This is _wrong_.
    There's gonna be collision with the UIDs for regular analysis. Right now
    analyses and testgen are separate so that's fine, but be careful in the
    future.
/!\

*)
let testgen_uid_ref = ref 1
let get_testgen_uid () =
  let uid = !testgen_uid_ref in
  testgen_uid_ref := uid + 1 ;
  uid

(** Returns the analysis param for [top] that abstracts all its abstractable
    subsystems if [top] has a contract. *)
let maximal_abstraction_for_testgen (type s)
: s t -> Scope.t -> (Scope.t * Term.t) list -> Analysis.param option = function

  | Lustre (subsystem, globals) -> (fun top assumptions ->

    (* Collects all subsystems, abstracting them if possible. *)
    let rec collect map = function
      | sub :: tail ->
        collect (Scope.Map.add sub.S.scope sub.S.has_contract map) tail
      | [] -> Some map
    in

    (* Finds [top] in the subsystems, and then calls [collect]. *)
    let rec get_abstraction_for_top = function
      | sub :: tail ->
        if sub.S.scope = top then
          (* Sub is the system we're looking for. *)
          if sub.S.has_contract then
            (* System has contracts, collecting subsystems. *)
            collect (Scope.Map.add sub.S.scope false Scope.Map.empty) tail
          else
            (* System has no contracts. *)
            None
        else
          (* Sub is not the system we're looking for, skipping. *)
          get_abstraction_for_top tail
      | [] ->
        Format.asprintf
          "system %a does not exist, cannot generate param for testgen"
          Scope.pp_print_scope top
        |> failwith
    in

    match
      S.all_subsystems subsystem |> get_abstraction_for_top
    with

    (* Top is not abstractable. *)
    | None -> None

    (* All good. *)
    | Some map -> Some (
      Analysis.First {
        Analysis.top = top ;
        Analysis.uid = get_testgen_uid () ;
        Analysis.abstraction_map = map ;
        Analysis.assumptions = assumptions ;
      }
    )

  )

  | Native subsystem -> assert false
  | Horn subsystem -> assert false

let next_analysis_of_strategy (type s)
: s t -> 'a -> Analysis.param option = function

  | Lustre (subsystem, globals) -> (fun results -> 
      (* let nodes = 
         LustreNode.nodes_of_subsystem subsystem
         in

         assert (nodes <> []) ;

         Some {
         Analysis.top = List.hd nodes |> LustreNode.scope_of_node ;

         Analysis.abstraction_map =
          nodes |> List.fold_left (fun m n ->
            Scope.Map.add (LustreNode.scope_of_node n) false m
          ) Scope.Map.empty ;

         Analysis.assumptions = []
         } *)

      let subs_of_scope scope =
        let { S.subsystems } = S.find_subsystem subsystem scope in
        subsystems
        |> List.map (fun { S.scope ; S.has_contract; S.has_modes } ->
            scope, has_contract, has_modes)
      in


      S.all_subsystems subsystem
      |> List.map (fun { S.scope ; S.has_contract ; S.has_modes } ->
          scope, has_contract, has_modes)
      |> Strategy.next_analysis results subs_of_scope
    )

  | Native subsystem -> (fun results ->
      let subs_of_scope scope =
        let { S.subsystems } = S.find_subsystem subsystem scope in
        subsystems
        |> List.map (fun { S.scope ; S.has_contract; S.has_modes } ->
            scope, has_contract, has_modes)
      in
      
      S.all_subsystems subsystem
      |> List.map (fun { S.scope ; S.has_contract ; S.has_modes } ->
          scope, has_contract, has_modes)
      |> Strategy.next_analysis results subs_of_scope)
         
  | Horn subsystem -> (function _ -> assert false)


(* Return a transition system with [top] as the main system, sliced to
   abstractions and implementations as in [abstraction_map]. *)
let trans_sys_of_analysis (type s) ?(preserve_sig = false)
: s t -> Analysis.param -> TransSys.t * s t = function

  | Lustre (subsystem, globals) -> (function analysis ->
    let t, s, g =
      LustreTransSys.trans_sys_of_nodes
        ~preserve_sig:preserve_sig subsystem globals analysis
    in
      (t, Lustre (s, g))
    )

  | Native sub -> (fun _ -> sub.SubSystem.source, Native sub)
    
  | Horn _ -> assert false



let pp_print_path_pt
(type s) (input_system : s t) trans_sys instances first_is_init ppf model =

  match input_system with 

  | Lustre (subsystem, globals) ->
    LustrePath.pp_print_path_pt
      trans_sys instances subsystem globals first_is_init ppf model

  | Native sub ->
    Format.eprintf "pp_print_path_pt not implemented for native input@.";
    ()
    (* assert false *)

  | Horn _ -> assert false


let pp_print_path_xml
(type s) (input_system : s t) trans_sys instances first_is_init ppf model =

  match input_system with 

  | Lustre (subsystem, globals) ->
    LustrePath.pp_print_path_xml
      trans_sys instances subsystem globals first_is_init ppf model

  | Native _ ->
    Format.eprintf "pp_print_path_xml not implemented for native input@.";
    assert false;


  | Horn _ -> assert false


let pp_print_path_in_csv
(type s) (input_system : s t) trans_sys instances first_is_init ppf model =
  match input_system with

  | Lustre (subsystem, globals) ->
    LustrePath.pp_print_path_in_csv
      trans_sys instances subsystem globals first_is_init ppf model

  | Native _ ->
    Format.eprintf "pp_print_path_in_csv not implemented for native input";
    assert false

  | Horn _ -> assert false


let reconstruct_lustre_streams (type s) (input_system : s t) state_vars =
  match input_system with 
  | Lustre (subsystem, _) ->
    LustrePath.reconstruct_lustre_streams subsystem state_vars
  | Native _ -> assert false
  | Horn _ -> assert false

let is_lustre_input (type s) (input_system : s t) =
  match input_system with 
  | Lustre _ -> true
  | Native _ -> false
  | Horn _ -> false


let slice_to_abstraction_and_property
(type s) (input_sys: s t) analysis trans_sys cex prop
: TransSys.t * TransSys.instance list * (StateVar.t * _) list * Term.t * s t = 

  (* Filter values at instants of subsystem. *)
  let filter_out_values = match input_sys with 

    | Lustre (subsystem, globals) -> (fun scope { TransSys.pos } cex v -> 
          
      (* Get node cals in subsystem of scope. *)
      let { S.source = { LustreNode.calls } } = 
        S.find_subsystem subsystem scope 
      in
    
      (* Get clock of node call identified by its position. *)
      let { LustreNode.call_clock } = 
        List.find (fun {
            LustreNode.call_node_name; LustreNode.call_pos
          } -> call_pos = pos
        ) calls
      in

      (* Node call has an activation condition? *)
      match call_clock with 

        (* Keep all instants for node calls without activation
           condition. *)
        | None -> v

        (* State variable for activation condition. *)
        | Some clock_state_var -> 

          (* Get values of activation condition from model. *)
          let clock_values = List.assq clock_state_var cex in

          (* Need to preserve order of values *)
          List.fold_right2 (fun cv v a -> match cv with

            (* Value of clock at this instant. *)
            | Model.Term t -> 

             (* Clock is true: keep value at instant. *)
             if Term.equal t Term.t_true then 
               v :: a

             (* Clock is false: skip instant. *)
             else if Term.equal t Term.t_false then 
               a

             (* Clock must be Boolean. *)
             else 
               assert false

            (* TODO: models with arrays. *)
            | Model.Lambda _ -> assert false
          ) clock_values v []
    )

    (* Clocked node calls are only in Lustre, no filtering of instants in
       models for native input. *)
    | Native subsystem -> (fun _ _ _ v -> v)

    (* Clocked node calls are only in Lustre, no filtering of instants in
       models for Horn input. *)
    | Horn subsystem -> (fun _ _ _ v -> v)

  in  

  (* Map counterexample and property to S. *)
  let trans_sys', instances, cex', prop' =
    TransSys.map_cex_prop_to_subsystem 
      filter_out_values trans_sys cex prop
  in

  (* Replace top system with subsystem for slicing. *)
  let analysis' =
    Analysis.First {
      Analysis.info_of_param analysis
      with Analysis.top = TransSys.scope_of_trans_sys trans_sys'
    }
  in

  (* Return subsystem that contains the property *)
  trans_sys', instances, cex', prop'.Property.prop_term, (

    (* Slicing is input-specific *)
    match input_sys with 

    (* Slice Lustre subnode to property term *)
    | Lustre (subsystem, globals) ->

      let vars = match prop'.Property.prop_source with
        | Property.Assumption _ ->
          TransSys.state_vars trans_sys' |> StateVar.StateVarSet.of_list
        | _ ->
          Term.state_vars_of_term prop'.Property.prop_term
      in

      let subsystem', globals' = 
        LustreSlicing.slice_to_abstraction_and_property
          analysis' vars subsystem globals
      in

      Lustre (subsystem', globals')

    (* No slicing in native input *)
    | Native subsystem -> Native subsystem

    (* No slicing in Horn input *)
    | Horn subsystem -> Horn subsystem
  )


let inval_arg s = invalid_arg (
  Format.sprintf "expected lustre input, got %s input" s
)

let compile_to_rust (type s): s t -> Scope.t -> string -> unit =
fun sys top_scope target ->
  match sys with
  | Lustre (sub, _) ->
    LustreToRust.implem_to_rust target (
      fun scope -> (S.find_subsystem sub scope).S.source
    ) sub.S.source
  | Native _ ->
    Format.printf "can't compile from native input: unsupported"
  | Horn _ ->
    Format.printf "can't compile from horn clause input: unsupported"

let compile_oracle_to_rust (type s): s t -> Scope.t -> string -> (
  string *
  (Lib.position * int) list *
  (string * Lib.position * int) list
) =
fun sys top_scope target ->
  match sys with
  | Lustre (sub, _) ->
    LustreToRust.oracle_to_rust target (
      fun scope -> (S.find_subsystem sub scope).S.source
    ) sub.S.source
  | Native _ ->
    failwith "can't compile from native input: unsupported"
  | Horn _ ->
    failwith "can't compile from horn clause input: unsupported"

let contract_gen_param (type s): s t -> (Analysis.param * (Scope.t -> LustreNode.t)) =
fun sys ->
  match sys with
  | Lustre(sub, _) -> (
    match
      S.all_subsystems sub
      |> List.map (fun { S.scope ; S.has_contract ; S.has_modes } ->
        scope, has_contract, has_modes
      )
      |> Strategy.monolithic
    with
    | None -> failwith "aaahhh"
    | Some param ->
      param, (fun scope -> (S.find_subsystem sub scope).S.source)
  )
  | Native _ ->
    failwith "can't generate contracts from native input: unsupported"
  | Horn _ ->
    failwith "can't generate contracts from horn clause input: unsupported"


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
