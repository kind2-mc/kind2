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
open TermLib
open Actlit

module Smt = SMTSolver
module Sys = TransSys
module Prop = Property

type term = Term.t

let solver_ref = ref None

let prefix = "IND2 "

(* Clean up before exit. *)
let on_exit _ =
  try (
    (* Deleting solver instance if created. *)
    match ! solver_ref with
    | None -> ()
    | Some solver ->
      SMTSolver.delete_instance solver |> ignore ;
      solver_ref := None ;
      ()
  ) with e ->
    Event.log L_error
      "%s@[<v>Error deleting solver:@ %s@]"
      prefix (Printexc.to_string e)

(* Alias for fresh actlits. *)
let fresh_actlit = Actlit.fresh_actlit

(* Alias for actlit UF to term. *)
let actlit_term = Actlit.term_of_actlit

(* Alias for [Term.bump_state]. *)
let unroll = Term.bump_state

(* Deactivates an actlit. *)
let deactivate solver actlit =
  Term.mk_not actlit |> Smt.assert_term solver

(* Asserts an invariant at [k]. *)
let assert_invariant_at solver k inv =
  unroll k inv |> Smt.assert_term solver

(* Asserts invariants from 0 to 2.

  Returns [true] iff the list of invariants is not empty. *)
let add_invariants solver = function
| [] -> false
| invs ->
  let inv = Term.mk_and invs in
  assert_invariant_at solver Numeral.zero       inv ;
  assert_invariant_at solver Numeral.one        inv ;
  assert_invariant_at solver Numeral.(succ one) inv ;
  true

(* Context of the 2-induction engine. *)
type 'a ctx = {
  (* Solver used for the analysis. *)
  solver: Smt.t ;
  (* Input system. *)
  in_sys: 'a InputSystem.t ;
  (* Analysis. *)
  param: Analysis.param ;
  (* System we're analyzing. *)
  sys: Sys.t ; 
  (* Property to (positive actlit, negative actlit, prop term) map. *)
  mutable map: ( string * (term * term * term) ) list ;
}

(* Creates a solver, memorizes it for clean exit, asserts transition relation
  [(0,1)] and [(1,2)], creates actlits for unknown properties, creates positive
  and negative activation literals and asserts relevant implications. *)
let mk_ctx in_sys param sys =
  let solver =
    Smt.create_instance
      ~produce_assignments:true
      (Sys.get_logic sys)
      (Flags.smtsolver())
  in
  (* Memorizing solver for clean exit. *)
  solver_ref := Some solver ;

  (* Defining UFs and declaring variables. *)
  Sys.define_and_declare_of_bounds
    sys
    (Smt.define_fun solver)
    (Smt.declare_fun solver)
    Numeral.(~- one) Numeral.(succ one) ;

  (* Invariants of the system at 0, 1 and 2. *)
  Sys.invars_of_bound sys Numeral.zero
  |> add_invariants solver |> ignore ;

  (* Transition relation (0,1). *)
  Sys.trans_of_bound sys Numeral.one
  |> Smt.assert_term solver ;
  (* Transition relation (1,2). *)
  Sys.trans_of_bound sys Numeral.(succ one)
  |> Smt.assert_term solver ;

  {
    solver ; in_sys ; param ; sys ;
    (* Creating map from properties to positive/negative actlit pairs. *)
    map = Sys.get_prop_status_all_unknown sys |> List.fold_left (
      fun map (name,_) ->
        (* Getting fresh actlit UFs. *)
        let pactlit, nactlit = fresh_actlit (), fresh_actlit () in
        (* Declaring them. *)
        Smt.declare_fun solver pactlit ;
        Smt.declare_fun solver nactlit ;
        (* Building terms. *)
        let pactlit, nactlit = actlit_term pactlit, actlit_term nactlit in
        (* Retrieving prop term. *)
        let prop = Sys.get_prop_term sys name in
        (* Positive implications. *)
        Term.mk_implies [ pactlit ; unroll Numeral.zero prop ]
        |> Smt.assert_term solver ;
        Term.mk_implies [ pactlit ; unroll Numeral.one prop ]
        |> Smt.assert_term solver ;
        (* Negative implication. *)
        Term.mk_implies [
          nactlit ; unroll Numeral.(succ one) prop |> Term.mk_not
        ] |> Smt.assert_term solver ;
        (* Appending mapping. *)
        (name, (pactlit, nactlit, prop)) :: map
    ) [] ;
  }

(* Communication, updates the transition system.
  Also asserts whatever invariants were received.

  Loops until something new is received. *)
let rec check_new_things ({ solver ; sys ; map } as ctx) =
  match Event.recv () |> Event.update_trans_sys ctx.in_sys ctx.param sys with
    (* Nothing new property-wise, keep going. *)
    | (invs, []) ->
      let new_things = add_invariants solver invs in
      if not new_things then (
        (* No new invariants, sleeping and looping. *)
        minisleep 0.07 ;
        check_new_things ctx
      )
    (* Some properties changed status. *)
    | (invs, _) ->

      let map, invs =
        map |> List.fold_left (
          (* Go through map and inspect property status. *)
          fun (map,invs) ( (name, (pos,neg,prop)) as p ) ->
            match Sys.get_prop_status sys name with
            | Prop.PropFalse _ ->
              (* Deactivate actlits and remove from map. *)
              deactivate solver pos ;
              deactivate solver neg ;
              map, invs

            | Prop.PropInvariant ->
              (* Deactivate actlits, remove from map, add to invariants. *)
              deactivate solver pos ;
              deactivate solver neg ;
              map, prop :: invs

            | _ ->
              (* Still unknown. *)
              p :: map, invs
        ) ([], invs)
      in

      (* Update map in context. *)
      ctx.map <- map ;
      (* Adding new invariants. *)
      add_invariants solver invs |> ignore ;
      (* We got new stuff we don't loop. *)
      ()

(* Returns the properties that cannot be falsified. *)
let split ({ solver ; map } as ctx) =

  let rec loop falsifiable =
    if (List.length falsifiable) = (List.length map) then
      (* All falsifiable, done. *)
      []
    else (
      (* Check if termination was requested. *)
      Event.check_termination () ;

      (* Actlits for unknown properties. *)
      let actlits =
        map |> List.fold_left (fun l (prop, (pos,neg,_)) ->
          (* Ignore falsifiable properties. *)
          if List.mem prop falsifiable |> not
          then pos :: neg :: l else l
        ) []
      in

      (* Check-sat. *)
      match
        actlits
        |> Smt.check_sat_assuming
          solver
          (fun _ -> (* If sat. *)
            (* Maps prop terms at 2 to their name. *)
            let props_2 =
              map |> List.map (
                fun (name, (_,_,t)) -> unroll Numeral.(succ one) t, name
              )
            in
            (* Retrieve values. *)
            props_2 |> List.map fst |> Smt.get_term_values solver
            |> List.fold_left (
              fun l (term, value) ->
                if value == Term.t_false then
                  (List.assq term props_2) :: l
                else l
            ) []
            |> fun l -> Some l
          )
          (fun _ -> (* If unsat. *)
            None
          )
      with
      | None -> (* Unsat, remaining properties are unfalsifiable. *)
        map |> List.map fst
      | Some nu_falsifiable ->
        (* Sat, we need to check the remaining properties. *)
        List.rev_append nu_falsifiable falsifiable |> loop
    )
  in

  loop []

(* Checks if unfalsifiable properties are 1-true or more, and broadcasts them
  as invariants if they do. Also updates the solver accordingly by asserting
  invariant properties as invariants. *)
let broadcast_if_safe ({ solver ; sys ; map } as ctx) unfalsifiable =
  let rec loop confirmed = function
    | prop :: tail -> (
      let ok =
        match Sys.get_prop_status sys prop with
        | Prop.PropKTrue n -> n >= 1
        | Prop.PropInvariant -> true
        | _ -> false
      in
      if ok then
        (* Property confirmed, need to check the other ones. *)
        loop (prop :: confirmed) tail
      else
        (* Property unconfirmed, unsafe to communicate, aborting. *)
        ()
    )
    | [] ->
      (* All properties confirmed, broadcasting as invariant. *)
      confirmed |> List.iter (
        fun prop ->
          Event.prop_status Prop.PropInvariant ctx.in_sys ctx.param sys prop
      ) ;
      (* Removing from map and updating solver. *)
      let map =
        map |> List.filter (fun (name, (pos,neg,t)) ->
          if List.mem name confirmed then (
            (* Deactivating actlits. *)
            deactivate solver pos ;
            deactivate solver neg ;
            (* Adding invariant. *)
            add_invariants solver [t] ;
            (* Don't keep. *)
            false
          ) else true
        )
      in
      (* Update context. *)
      ctx.map <- map
  in

  loop [] unfalsifiable

(* Find unfalsifiable properties, communicate if any (and if safe), loop when
  new invariants are discovered. *)
let rec run ctx =

  (* Get unfalsifiable properties. *)
  ( match split ctx with
    | [] -> ()
    | unfalsifiable ->
      Event.log
        L_info
        "%s@[<v>%d unfalsifiable properties"
        prefix (List.length ctx.map) ;
      broadcast_if_safe ctx unfalsifiable ) ;

  match ctx.map with
  | [] ->
    (* Stopping if nothing else to do. *)
    Event.log
      L_info
      "%s@[<v>No more properties to analyze.@]"
      prefix ;
    ()
  | _ ->
    (* Keep going when new things arrive. *)
    check_new_things ctx ;
    Event.log
      L_info
      "%s@[<v>Restarting with %d properties@]"
      prefix (List.length ctx.map) ;
    run ctx

(* Entry point. *)
let main in_sys param sys =
  (* Building context. *)
  let ctx = mk_ctx in_sys param sys in
  match ctx.map with
  | [] -> 
    (* Don't start if nothing to run on. *)
    Event.log
      L_info
      "%s@[<v>No properties to analyze.@]"
      prefix ;
    ()
  | _ ->
    Event.log
      L_info
      "%s@[<v>%d properties to check@]"
      prefix (List.length ctx.map) ;
    ctx |> run
