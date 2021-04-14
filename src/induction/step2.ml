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
open Actlit

module Smt = SMTSolver
module Sys = TransSys
module Prop = Property
module Num = Numeral

let zero = Num.zero
let one = Num.one
let two = Num.(succ one)

type term = Term.t

let prefix = "[IND2] "

(* Clean up before exit. *)
let on_exit _ = ()

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
  assert_invariant_at solver zero inv ;
  assert_invariant_at solver one  inv ;
  assert_invariant_at solver two  inv ;
  true

let add_all_invariants solver sys =
  ( match Sys.invars_of_bound ~one_state_only:true sys zero with
    | [] -> ()
    | invs -> Term.mk_and invs |> assert_invariant_at solver zero
  ) ;
  ( match Sys.invars_of_bound ~one_state_only:false sys zero with
    | [] -> ()
    | invs ->
      let terms = Term.mk_and invs in
      assert_invariant_at solver one terms ;
      assert_invariant_at solver two terms
  )

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
  (* Property to (positive actlit, prop term) map. *)
  mutable map: ( string * (term * term) ) list ;
}

(* Creates a solver, memorizes it for clean exit, asserts transition relation
  [(0,1)] and [(1,2)], creates actlits for unknown properties, creates positive
  activation literals and asserts relevant implications. *)
let mk_ctx in_sys param sys =
  let solver =
    Smt.create_instance
      ~produce_assignments:true
      (Sys.get_logic sys)
      (Flags.Smt.solver())
  in

  (* Defining UFs and declaring variables. *)
  Sys.define_and_declare_of_bounds
    sys
    (Smt.define_fun solver)
    (Smt.declare_fun solver)
    (Smt.declare_sort solver)
    Numeral.zero Numeral.(succ one) ;

  (* Invariants of the system at 0, 1 and 2. *)
  add_all_invariants solver sys ;

  (* Transition relation (0,1). *)
  Sys.trans_of_bound (Some (Smt.declare_fun solver)) sys Numeral.one
  |> Smt.assert_term solver ;
  (* Transition relation (1,2). *)
  Sys.trans_of_bound (Some (Smt.declare_fun solver)) sys Numeral.(succ one)
  |> Smt.assert_term solver ;

  {
    solver ; in_sys ; param ; sys ;
    (* Creating map from properties to positive actlit/term pairs. *)
    map = Sys.get_prop_status_all_unknown sys |> List.fold_left (
      fun map (name,_) ->
        (* Getting fresh actlit UFs. *)
        let pactlit = fresh_actlit () in
        (* Declaring them. *)
        Smt.declare_fun solver pactlit ;
        (* Building terms. *)
        let pactlit = actlit_term pactlit in
        (* Retrieving prop term. *)
        let prop = Sys.get_prop_term sys name in
        (* Positive implications. *)
        Term.mk_implies [ pactlit ; unroll Numeral.zero prop ]
        |> Smt.assert_term solver ;
        Term.mk_implies [ pactlit ; unroll Numeral.one prop ]
        |> Smt.assert_term solver ;
        (* Appending mapping. *)
        (name, (pactlit, prop)) :: map
    ) [] ;
  }

(* Communication, updates the transition system.
  Also asserts whatever invariants were received.

  Loops until something new is received. *)
let rec check_new_things new_stuff ({ solver ; sys ; map } as ctx) =
  let new_invariants, props =
    KEvent.recv () |> KEvent.update_trans_sys ctx.in_sys ctx.param sys
  in
  let new_stuff_invs =
    ( new_invariants |> fst |> Term.TermSet.is_empty |> not ) ||
    ( new_invariants |> snd |> Term.TermSet.is_empty |> not )
  in
  let new_stuff =
    new_stuff || new_stuff_invs
  in

  if new_stuff_invs then
    (* Forcing to assert invs to [3], since upper-bound's exclusive. *)
    Unroller.assert_new_invs_to solver Num.(succ two) new_invariants ;

  match props with
    (* Nothing new property-wise, keep going if no new invariant. *)
    | [] -> if not new_stuff then (
      (* No new invariants, sleeping and looping. *)
      minisleep 0.07 ;
      check_new_things false ctx
    )
    (* Some properties changed status. *)
    | props ->

      let map, new_stuff =
        map |> List.fold_left (
          (* Go through map and inspect property status. *)
          fun (map, new_stuff) ( (name, (pos, prop)) as p ) ->
            match Sys.get_prop_status sys name with
            | Prop.PropFalse _ ->
              (* Deactivate actlits and remove from map. *)
              deactivate solver pos ;
              map, new_stuff

            | Prop.PropInvariant _ ->
              (* Deactivate actlits, remove from map, add to invariants. *)
              deactivate solver pos ;
              map, true

            | Prop.PropKTrue n ->
              p :: map, new_stuff || n >= 1

            | _ ->
              (* Still unknown. *)
              p :: map, new_stuff
        ) ([], new_stuff)
      in

      (* Update map in context. *)
      ctx.map <- map ;
      (* We got new stuff we don't loop. *)
      if not new_stuff then (
        minisleep 0.07 ;
        check_new_things false ctx
      )

(* Returns the properties that cannot be falsified. *)
let split { solver ; map } =

  let rec loop falsifiable =
    if (List.length falsifiable) = (List.length map) then
      (* All falsifiable, done. *)
      []
    else (
      (* Check if termination was requested. *)
      KEvent.check_termination () ;

      (* Positive actlits for unknown properties. *)
      let actlits, unknowns, map_back=
        map |> List.fold_left (
          fun (actlits,terms,map_back) (prop, (pos,term)) ->
            (* Ignore falsifiable properties. *)
            if List.mem prop falsifiable |> not
            then
              let term_at_2 = Term.bump_state (Numeral.of_int 2) term in
              pos :: actlits,
              term_at_2 :: terms,
              (term_at_2, prop) :: map_back
            else actlits, terms, map_back
        ) ([],[], [])
      in

      (* Negative actlit. *)
      let nactlit =
        let nactlit = fresh_actlit () in
        Smt.declare_fun solver nactlit ;
        let nactlit = term_of_actlit nactlit in
        Term.mk_implies [ nactlit ; Term.mk_and unknowns |> Term.mk_not ]
        |> Smt.assert_term solver ;
        nactlit
      in

      (* Deactivation function. *)
      let deactivate () = Term.mk_not nactlit |> Smt.assert_term solver in

      (* Check-sat. *)
      match
        Smt.check_sat_assuming_and_get_term_values
          solver
          (fun s term_values -> (* If sat. *)
            (* Retrieve values. *)
            term_values |> List.fold_left (
              fun l (term, value) ->
                if value == Term.t_false then
                  (List.assq term map_back) :: l
                else l
            ) []
            |> fun l -> Some l
          )
          (fun _ -> (* If unsat. *)
            None
          )
          (nactlit :: actlits) unknowns
      with
      | None -> (* Unsat, remaining properties are unfalsifiable. *)
        deactivate () ;
        unknowns |> List.map (fun t -> List.assq t map_back)
      | Some [] ->
        failwith "got empty list of falsifiable properties"
      | Some nu_falsifiable ->
        deactivate () ;
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
      let ok_cert =
        match Sys.get_prop_status sys prop with
        | Prop.PropKTrue n when n >= 1 ->
          Some (2, Sys.get_prop_term sys prop)
        | Prop.PropInvariant ((k, phi) as cert) ->
          if k <= 2 then Some cert
          else Some (2, Sys.get_prop_term sys prop)
        | _ -> None
      in
      match ok_cert with
      | Some cert ->
        (* Property confirmed, need to check the other ones. *)
        loop ((prop, cert) :: confirmed) tail
      | None ->
        (* Property unconfirmed, unsafe to communicate, aborting. *)
        false
    )
    | [] ->
      (* All properties confirmed, broadcasting as invariant,
         and getting new inferred invariants
      *)
      let new_os_invs =
        confirmed |> List.fold_left (
          fun acc (prop, cert) ->
            KEvent.prop_invariant sys prop cert |> Term.TermSet.union acc
        )
        Term.TermSet.empty
      in
      if not (Term.TermSet.is_empty new_os_invs) then (
        let new_invariants = (new_os_invs, Term.TermSet.empty) in
        (* Forcing to assert invs to [3], since upper-bound's exclusive. *)
        Unroller.assert_new_invs_to solver Num.(succ two) new_invariants
      ) ;
      (* Removing from map and updating solver. *)
      let map =
        map |> List.filter (fun (name, (pos,t)) ->
          if List.mem_assoc name confirmed then (
            (* Deactivating actlits. *)
            deactivate solver pos ;
            (* Adding invariant. *)
            add_invariants solver [t] |> ignore ;
            (* Don't keep. *)
            false
          ) else true
        )
      in
      (* Update context. *)
      ctx.map <- map ;
      true
  in

  loop [] unfalsifiable

(* Find unfalsifiable properties, communicate if any (and if safe), loop when
  new invariants are discovered. *)
let rec run ctx =

  (* Get unfalsifiable properties. *)
  let new_stuff = match split ctx with
    | [] ->
      KEvent.log
        L_info
        "%s@[<v>%d falsifiable properties@]"
        prefix (List.length ctx.map) ;
      false
    | unfalsifiable ->
      KEvent.log
        L_info
        "%s@[<v>Proved %d properties%t@]"
        prefix (List.length unfalsifiable)
        (fun fmt ->
          match ctx.map with
          | [] -> ()
          | _ ->
            Format.fprintf
              fmt "@ %d falsifiable properties" (List.length ctx.map)
        ) ;
      broadcast_if_safe ctx unfalsifiable
  in

  match ctx.map with
  | [] ->
    (* Stopping if nothing else to do. *)
    KEvent.log
      L_info
      "%s@[<v>No more properties to analyze.@]"
      prefix ;
    ()
  | _ ->
    (* Keep going when new things arrive. *)
    check_new_things new_stuff ctx ;
    run ctx

(* Entry point. *)
let main in_sys param sys =
  (* Building context. *)
  let ctx = mk_ctx in_sys param sys in
  match ctx.map with
  | [] -> 
    (* Don't start if nothing to run on. *)
    KEvent.log
      L_info
      "%s@[<v>No properties to analyze.@]"
      prefix ;
    ()
  | _ ->
    KEvent.log
      L_info
      "%s@[<v>%d properties to check@]"
      prefix (List.length ctx.map) ;
    ctx |> run
