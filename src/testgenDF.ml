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

module Solver = TestgenSolver
module Tree = TestgenTree
module TSys = TransSys
module Num = Numeral
module N = LustreNode

module IO = TestgenIO


(* Reference to the solver for clean exit. *)
let solver_ref = ref None

(* Ref to function for IO clean exit. *)
let close_io_ref = ref None

(* Number of restarts performed. *)
let restart_count_ref = ref 0

(* Communicate testcase count every 50 testcases generated. *)
let delta_tc_comm = 50
let next_tc_comm = ref delta_tc_comm

let log_id = "[TESTGEN] "

(* Output statistics *)
let print_stats () = Event.stat [
  Stat.misc_stats_title, Stat.misc_stats ;
  Stat.testgen_stats_title, Stat.testgen_stats ;
  Stat.smt_stats_title, Stat.smt_stats
]

(* Destroys the solver reference if any. *)
let on_exit _ =
  Stat.testgen_stop_timers () ;
  Stat.smt_stop_timers () ;
  print_stats () ;
  ( match !solver_ref with
    | None -> ()
    | Some solver -> Solver.rm solver ) ;
  ( match !close_io_ref with
    | None -> ()
    | Some close -> close () ) ;
  ()

let get_model = SMTSolver.get_model

let unit_of _ = ()

let active_modes_of_map map =
  List.fold_left (fun (act,deact) (m,v) ->
    if v == Term.t_true then m :: act, deact else act, m :: deact
  ) ([],[]) map
  (* |> fun (act,deact) ->
    Format.printf "  active: @[<v>%a@]@."
      (pp_print_list Format.pp_print_string "@,") act ;
    act, deact *)

type result = Ok | Deadlock

let rec enumerate io solver tree modes contract_term =
  (* Format.printf "@.enumerate@." ; *)
  Stat.start_timer Stat.testgen_enumerate_time ;
  Solver.comment solver "enumerate" ;
  let rec loop () =
    (* Log if it's time to do so. *)
    let tc_count = IO.testcase_count io in
    if tc_count >= !next_tc_comm then (
      next_tc_comm := tc_count + delta_tc_comm ;
      Event.log L_info "%s%d testcases generated." log_id tc_count
    ) ;

    (* Format.printf "  tree: %a@." Tree.pp_print_tree tree ; *)
    let k = Tree.depth_of tree in
    let modes = modes |> List.map (fun (n,t) -> n, Term.bump_state k t) in
    let contract_term = Term.bump_state k contract_term in
    let mode_path =
      Term.mk_and [ contract_term ; Tree.blocking_path_of tree ]
    in

    match Solver.checksat solver k mode_path [] modes get_model with
    | Some (map, model) ->
      (* Extracting modes activated @k by the model. *)
      active_modes_of_map map |> Tree.update tree ;
      let modes = Tree.mode_path_of tree |> List.map fst in
      IO.log_testcase io modes model k ;
      loop ()
    | None -> ()
  in

  (* Let's find the first mode we can activate @k+1. *)

  (* Format.printf "  tree: %a@." Tree.pp_print_tree tree ; *)
  let k = Tree.depth_of tree |> Num.succ in
  (* Format.printf "  at %a@." Num.pp_print_numeral k ; *)
  let modes' = modes |> List.map (fun (n,t) -> n, Term.bump_state k t) in
  let contract_term' = Term.bump_state k contract_term in
  let mode_path = Tree.path_of tree in
  let term = Term.mk_and [ contract_term' ; mode_path ] in

  ( match Solver.checksat solver k term [] modes' get_model with
    | Some (map, model) ->
      (* Extracting modes activated @k by the model. *)
      active_modes_of_map map |> Tree.push tree ;
      let modes_str = Tree.mode_path_of tree |> List.map fst in
      IO.log_testcase io modes_str model k ;
      (* Enumerating the other mode conjunctions from the path. *)
      loop ()
    | None ->
      (* If we get unsat right away then it's a deadlock. *)
      (* Format.printf "  deadlock@." ; *)
      let k = Num.pred k in
      ( match Solver.checksat solver k mode_path [] [] get_model with
        | None -> assert false
        | Some (_, model) ->
          let modes_str = Tree.mode_path_of tree |> List.map fst in
          IO.log_deadlock io modes_str model k ) ) ;
  Stat.record_time Stat.testgen_enumerate_time ;
  (* Let's go backward now. *)
  backward io solver tree modes contract_term



and forward io solver tree modes contract_term =
  Stat.start_timer Stat.testgen_forward_time ;
  (* Resetting if too many fresh actlits have been created. *)
  let solver = if Actlit.fresh_actlit_count () >= 250 then (
      Stat.incr Stat.testgen_restarts ;
      Event.log L_info "%sRestarting solver." log_id ;
      Actlit.reset_fresh_actlit_count () ;
      let solver = Solver.restart solver in
      solver_ref := Some solver ;
      restart_count_ref := !restart_count_ref + 1 ;
      solver
    ) else solver
  in
  (* Format.printf "@.forward@." ; *)
  Solver.comment solver "forward" ;
  let rec loop () =
    (* Format.printf "  tree: %a@." Tree.pp_print_tree tree ; *)
    let k = Tree.depth_of tree |> Num.succ in
    if Flags.testgen_len () > Num.to_int k then (
      (* We haven't reached the max depth yet, keep going forward. *)
      (* Format.printf "  at %a@." Num.pp_print_numeral k ; *)
      let modes = modes |> List.map (fun (n,t) -> n, Term.bump_state k t) in
      let contract_term = Term.bump_state k contract_term in
      let mode_path = Tree.path_of tree in
      let term = Term.mk_and [ contract_term ; mode_path ] in

      match Solver.checksat solver k term [] modes unit_of with
      | Some (map,()) ->
        (* Extracting modes activated @k by the model. *)
        let active = active_modes_of_map map in
        (* Event.log L_info "%sGoing forward (%a): @[<hov><%a>@]."
          log_id
          Num.pp_print_numeral k
          (pp_print_list
            Format.pp_print_string
            ">,@ <")
          (fst active) ; *)
        Tree.push tree active ;
        loop ()
      | None ->
        (* Deadlock. *)
        Event.log
          L_info "%sDeadlock found (%a)" log_id Tree.pp_print_tree tree ;
        let k = Num.pred k in
        ( match Solver.checksat solver k mode_path [] [] get_model with
          | None -> assert false
          | Some (_, model) ->
            let modes_str = Tree.mode_path_of tree |> List.map fst in
            IO.log_deadlock io modes_str model k ) ;
        Deadlock
    ) else Ok
  in
  let result = loop () in
  Stat.record_time Stat.testgen_forward_time ;
  (* Going forward. *)
  match result with
  | Ok ->
    (* Max depth reached, enumerate reachable modes. *)
    enumerate io solver tree modes contract_term
  | Deadlock ->
    (* Deadlock found, going backward. *)
    backward io solver tree modes contract_term

and backward io solver tree modes contract_term =
  Stat.update_time Stat.testgen_total_time ;
  Stat.start_timer Stat.testgen_backward_time ;
  (* Format.printf "@.backward@." ; *)
  Solver.comment solver "backward" ;
  (* Format.printf "  tree: %a@." Tree.pp_print_tree tree ; *)
  let rec loop () =
    Tree.pop tree ;
    (* Format.printf "  popped tree: %a@." Tree.pp_print_tree tree ; *)
    let k = Tree.depth_of tree in
    (* Event.log L_info "%sGoing backward (%a)."
      log_id Num.pp_print_numeral (Num.succ k) ; *)
    let modes = modes |> List.map (fun (n,t) -> n, Term.bump_state k t) in
    let contract_term = Term.bump_state k contract_term in
    let mode_path =
      Term.mk_and [ contract_term ; Tree.blocking_path_of tree ]
    in

    match Solver.checksat solver k mode_path [] modes unit_of with
    | Some (map,()) ->
        (* Extracting modes activated @k by the model. *)
        let active = active_modes_of_map map in
        (* Event.log L_info "%sGoing up (%a): @[<hov><%a>@]."
          log_id
          Num.pp_print_numeral (Num.succ k)
          (pp_print_list
            Format.pp_print_string
            ">,@ <")
          (fst active) ; *)
        Tree.update tree active
    | None ->
      (* Cannot activate any other mode conjunction, going backward. *)
      loop ()
  in
  (* Going backwards. *)
  loop () ;
  Stat.record_time Stat.testgen_backward_time ;
  (* Found a different path, going forward now. *)
  forward io solver tree modes contract_term


(* Entry point. *)
let main (type s)
: Analysis.param -> s InputSystem.t -> TSys.t -> unit
= fun param input_sys sys ->
  (* Separating abstract and concrete systems. *)
  let abstract, concrete =
    Scope.Map.fold (fun key value (a,c) ->
      if value then key :: a, c else a, key :: c
    ) (Analysis.info_of_param param).Analysis.abstraction_map ([],[])
  in
  Event.log L_info "%s@[<v>\
      Launching on %a.@ \
      concrete subsystems: [ @[<hov>%a@] ]@ \
      abstract subsystems: [ @[<hov>%a@] ]\
    @]"
    log_id
    Scope.pp_print_scope (TransSys.scope_of_trans_sys sys)
    (pp_print_list Scope.pp_print_scope ",@ ") concrete
    (pp_print_list Scope.pp_print_scope ",@ ") abstract ;

  (* Creating solver. *)
  let solver = Solver.mk sys in
  (* Memorizing solver for clean exit. *)
  solver_ref := Some solver ;

  (* Retrieve the name of the transition system. *)
  let sys_name =
    TSys.scope_of_trans_sys sys
    |> Format.asprintf "%a" Scope.pp_print_scope
  in

  (* Creating system directory if needed. *)
  let root =
    Format.sprintf "%s/%s"
      (Flags.testgen_out_dir ()) sys_name
  in
  IO.mk_dir root ;

  Event.log L_info "%sGenerating oracle." log_id ;
  (* |===| Begin messy temporary stuff to generate outputs for each mode. *)
  (* let nodes = match TransSys.get_source sys with
    | TransSys.Lustre nodes -> nodes
    | TransSys.Native -> assert false
  in
  let (top, subs) =
    let rec last_rev_tail acc = function
      | [ h ] -> (h, acc)
      | h :: t -> last_rev_tail (h :: acc) t
      | [] -> assert false
    in
    last_rev_tail [] nodes
  in
  let mk_and = function
    | [] -> LustreExpr.t_true
    | [ e ] -> e
    | e :: tail ->
      let rec loop e = function
        | e' :: tail -> loop (LustreExpr.mk_and e e') tail
        | [] -> e
      in
      loop e tail
  in
  let mk_impl = LustreExpr.mk_impl in
  let mk_out_ident id =
    LustreIdent.mk_string_ident
      ("output_" ^ ( (LustreIdent.string_of_ident false) id ))
  in
  let mk_out_ident_req id =
    LustreIdent.mk_string_ident
      ("output_" ^ ( (LustreIdent.string_of_ident false) id ) ^ "_req")
  in
  let contracts = match top.N.contract_spec with
    | None ->
      assert false
    | Some (_, _, globl, modes, _) ->
      modes
      |> List.fold_left
        ( fun l (m: N.contract) -> (
            m,
            mk_out_ident m.N.name,
            mk_impl (mk_and m.N.reqs) (mk_and m.N.enss)
          ) :: (
            m,
            mk_out_ident_req m.N.name,
            mk_and m.N.reqs
          ) :: l )
        []
      |> List.rev
      |> (fun l -> match globl with
        | None -> l
        | Some c ->
          (c, mk_out_ident_req c.N.name, mk_and c.N.reqs) ::
          (c, mk_out_ident c.N.name, mk_and c.N.enss) :: l
      )
  in
  (* |===| End of messy stuff. *)
   *)


  let globals, modes = match TestgenModes.modes_of sys with
    | (Some global, modes), _ -> [global], modes
    | (None, modes), _ -> [], modes
  in
  let oracle_path = "fts"
    (* globals @ modes |> IO.generate_oracles sys root *)
  in

  (* Creating io context. *)
  let io = IO.mk input_sys sys root "unit" "unit tests" in
  close_io_ref := Some (fun () -> IO.rm io) ;

  (* Event.log L_info
    "%s@[<v>globals: @[<v>%a@]@ modes: @[<v>%a@]@]"
    log_id
    (pp_print_list (fun ppf (n,t) ->
        Format.fprintf ppf "%s -> %a" n Term.pp_print_term t
      ) "@,"
    ) globals
    (pp_print_list (fun ppf (n,t) ->
        Format.fprintf ppf "%s -> %a" n Term.pp_print_term t
      ) "@,"
    ) modes ; *)

  let global_terms = globals |> List.map snd in
  let mode_terms = modes |> List.map snd in

  let mode_term =
    (mode_terms |> Term.mk_or) :: global_terms |> Term.mk_and
  in

  let init_modes =
    match
      Solver.checksat
        solver Numeral.zero mode_term [] modes unit_of
    with
    | None -> failwith "no mode activable in init"
    | Some (map, ()) -> active_modes_of_map map
  in

  let tree =
    Tree.mk (fun name -> List.assoc name modes) init_modes
  in

  Event.log L_info "%sGenerating test cases." log_id ;

  (* Starting the timer. *)
  Stat.start_timer Stat.testgen_total_time ;

  ( try forward io solver tree modes mode_term with
    | TestgenTree.TopReached ->
      Stat.get Stat.testgen_testcases
      |> Event.log L_info "%sDone, %d testcases generated." log_id ;
      ( match Stat.get Stat.testgen_deadlocks with
        | 0 -> ()
        | n -> Event.log L_warn "%s/!\\ %d deadlocks found /!\\" log_id n) ) ;
  Stat.testgen_stop_timers () ;
  Stat.smt_stop_timers () ;

  let all_modes = TestgenModes.modes_of sys in

  ()

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
