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

module Strat = Strategy

type _ t =
| Lustre : (LustreNode.t SubSystem.t * LustreGlobals.t) -> LustreNode.t t
| Native : unit SubSystem.t -> unit t
| Horn : unit SubSystem.t -> unit t

let read_input_lustre input_file = Lustre (LustreInput.of_file input_file) 

let read_input_native input_file = assert false

let read_input_horn input_file = assert false

let ordered_scopes_of (type s)
: s t -> Scope.t list = function
  | Lustre (subsystem, _) ->
    SubSystem.all_subsystems subsystem
    |> List.map (fun { SubSystem.scope } -> scope)

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
      let { SubSystem.subsystems } =
        SubSystem.find_subsystem subsystem scope
      in
      subsystems |> List.map (
        fun { SubSystem.scope ; SubSystem.has_contract } -> scope, has_contract
      )
    in

    SubSystem.all_subsystems subsystem
    |> List.map (fun { SubSystem.scope ; SubSystem.has_contract } ->
      scope, has_contract
    )
    |> Strategy.next_analysis results subs_of_scope
  )

  | Native subsystem -> (function _ -> assert false)
  | Horn subsystem -> (function _ -> assert false)


(* Return a transition system with [top] as the main system, sliced to
   abstractions and implementations as in [abstraction_map]. *)
let trans_sys_of_analysis (type s)
: s t -> Analysis.param -> TransSys.t * s t = function

  | Lustre (subsystem, globals) -> (function analysis ->
    let t, s, g =
      LustreTransSys.trans_sys_of_nodes subsystem globals analysis
    in
    (t, Lustre (s, g))
  )
    
  | Native _ -> assert false
    
  | Horn _ -> assert false



let pp_print_path_pt
(type s) (input_system : s t) trans_sys instances first_is_init ppf model =

  match input_system with 

  | Lustre (subsystem, _) ->
    LustrePath.pp_print_path_pt
      trans_sys instances subsystem first_is_init ppf model

  | Native _ -> assert false

  | Horn _ -> assert false


let pp_print_path_xml
(type s) (input_system : s t) trans_sys instances first_is_init ppf model =

  match input_system with 

  | Lustre (subsystem, _) ->
    LustrePath.pp_print_path_xml
      trans_sys instances subsystem first_is_init ppf model

  | Native _ -> assert false

  | Horn _ -> assert false


let pp_print_path_in_csv
(type s) (input_system : s t) trans_sys instances first_is_init ppf model =
  match input_system with

  | Lustre (subsystem, _) ->
    LustrePath.pp_print_path_in_csv
      trans_sys instances subsystem first_is_init ppf model

  | Native _ -> assert false

  | Horn _ -> assert false



let slice_to_abstraction_and_property
(type s) (input_sys: s t) analysis trans_sys cex prop
: TransSys.t * TransSys.instance list * (StateVar.t * _) list * Term.t * s t = 

  (* Filter values at instants of subsystem. *)
  let filter_out_values = match input_sys with 

    | Lustre (subsystem, globals) -> (fun scope { TransSys.pos } cex v -> 
          
      (* Get node cals in subsystem of scope. *)
      let { SubSystem.source = { LustreNode.calls } } = 
        SubSystem.find_subsystem subsystem scope 
      in
    
      (* Get clock of node call identified by its position. *)
      let { LustreNode.call_clock } = 
        List.find
          (fun { LustreNode.call_node_name; 
                 LustreNode.call_pos } -> call_pos = pos)
          calls
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

  (* Map counterexample and property to subsystem. *)
  let trans_sys', instances, cex', { Property.prop_term } =
    TransSys.map_cex_prop_to_subsystem 
      filter_out_values trans_sys  cex prop
  in

  (* Replace top system with subsystem for slicing. *)
  let analysis' =
    { analysis with Analysis.top =
        TransSys.scope_of_trans_sys trans_sys' }
  in

  (* Return subsystem that contains the property *)
  trans_sys', instances, cex', prop_term, (

    (* Slicing is input-specific *)
    match input_sys with 

    (* Slice Lustre subnode to property term *)
    | Lustre (subsystem, globals) -> 

     let subsystem', globals' = 
       LustreSlicing.slice_to_abstraction_and_property
         analysis' prop_term subsystem globals
     in

     Lustre (subsystem', globals')

    (* No slicing in native input *)
    | Native subsystem -> Native subsystem

    (* No slicing in Horn input *)
    | Horn subsystem -> Horn subsystem
  )



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
