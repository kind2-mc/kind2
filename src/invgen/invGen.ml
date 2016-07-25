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

module type GraphSig = InvGenGraph.Graph




(* |===| IO stuff to log graphs and so on. *)


(* Opens a file in write mode, creating it if needed. *)
let openfile path = Unix.openfile path [
  Unix.O_TRUNC ; Unix.O_WRONLY ; Unix.O_CREAT
] 0o640

(* Formatter of a file descriptor. *)
let fmt_of_file file =
  Unix.out_channel_of_descr file |> Format.formatter_of_out_channel

(* Writes a graph in graphviz to file [<path>/<name>_<suff>.dot]. *)
let write_dot_to path name suff fmt_graph graph =
  mk_dir path ; (* Create directory if needed. *)
  let desc = (* Create descriptor for log file. *)
    Format.sprintf "%s/%s_%s.dot" path name suff |> openfile
  in
  (* Log graph in graphviz. *)
  Format.fprintf (fmt_of_file desc) "%a@.@." fmt_graph graph ;
  (* Close log file descriptor. *)
  Unix.close desc



(* |===| Module and type aliases *)


(* LSD module. *)
module Lsd = LockStepDriver

(* Term hash table. *)
module Map = Term.TermHashtbl
(* Term set. *)
module Set = Term.TermSet


(*

(* Attempt at an implementation similar to Term.TermSet using HashTbl. *)

module Set = struct
  type t = unit Map.t
  let empty () = Map.create 107
  let remove term set = Map.remove set term ; set
  let add term set = Map.replace set term () ; set
  let of_set set =
    Term.TermSet.cardinal set
    |> Map.create
    |> Term.TermSet.fold (
      fun t set -> add t set
    ) set
  let cardinal = Map.length
  let is_empty set = cardinal set = 0
  let iter f set = Map.iter (fun t _ -> f t) set
  let fold f = Map.fold (fun t _ acc -> f t acc)
  exception Found of Term.t
  let choose set =
    try (
      match fold (fun t _ -> raise (Found t)) set [] with
      | [] -> raise Not_found
      | _ -> failwith "unreachable: choose function over sets"
    ) with Found t -> t
  let union lft rgt =
    (* Want to fold over the smallest set. *)
    let lft, rgt =
      if cardinal rgt > cardinal lft then rgt, lft else lft, rgt
    in
    rgt |> fold (fun t lft -> add t lft) lft
  let elements set = fold (fun e l -> e :: l) set []
  let mem t set = Map.mem set t
  exception NotTrue
  let for_all f set =
    try (
      iter (fun t -> if f t |> not then raise NotTrue) set ;
      true
    ) with NotTrue -> false
end *)

(* Transition system module. *)
module Sys = TransSys
(* System hash table. *)
module SysMap = Sys.Hashtbl

(* Numerals. *)
module Num = Numeral

(* Term. *)
type term = Term.t
(* A representative is just a term. *)
type rep = term

(* Maps terms to something. *)
type 'a map = 'a Map.t
(* Set of terms. *)
type set = Set.t

(* Term formatter. *)
let fmt_term = Term.pp_print_term



(* |===| Communication stuff. *)

(** Name of a transition system. *)
let sys_name sys =
  Sys.scope_of_trans_sys sys |> Scope.to_string

(* Guards a term with init if in two state mode. *)
let sanitize_term two_state sys term =
  if two_state then (
    (* We need to sanitize systematically in two state as it DOES NOT check
    anything in the initial state. That is, even one state "invariants" could
    be false in the initial state, and thus must be guarded. *)
    Term.mk_or [ Sys.init_flag_of_bound sys Num.zero ; term ]
  ) else term

(* Guards a term and certificate with init if in two state mode. *)
let sanitize_term_cert two_state sys =
  if two_state then fun (term, (k, phi)) ->
    let term' = sanitize_term two_state sys term in
    if Term.equal term phi then term', (k, term')
    else term', (k, sanitize_term two_state sys phi)
  else identity



(* |===| Functor stuff *)

(** Signature of the module returned by the [Make] invariant generation functor
when given a module with signature [In]. *)
module type Out = sig
  (** Runs the invariant generator. *)
  val main :
    Num.t option -> bool -> bool -> bool -> 'a InputSystem.t ->
    Analysis.param -> Sys.t -> (
      Sys.t * Set.t * Set.t
    ) list
  (** Clean exit for the invariant generator. *)
  val exit : unit -> unit
end



(** Constructs an invariant generation module from a value module.

The central notion used in the graph splitting algorithm is "chains". A chain
is just a list of representative / value pairs that represent the new nodes
obtained after splitting an old node.

Throughout the different algorithms, a chain is ordered by decreasing values.

Once a node is split, the chain is inserted in all the parents of the old node.
The update algorithm is designed such that a node is split iff all its parents
have already be split (that is, their value is known).

Inserting a chain in the parents consists in extracting the longest prefix from
the chain such that all the values are greater than that of the parent. So for
instance when inserting the chain [7, 3, 2, -1] (omitting the representatives)
for a parent with value 1, then the longest prefix is [7, 3, 2]. The graph is
thus updated by linking the parent to the representative with value 2. The rest
of the chain ([-1]) is inserted in all the parents of the parent. *)
module Make (Graph : GraphSig) : Out = struct

  (* Domain we're working with. *)
  module Domain = Graph.Domain

  (* Reference to base checker for clean exit. *)
  let base_ref = ref None
  (* Reference to step checker for clean exit. *)
  let step_ref = ref None
  (* Reference to pruning checkers for clean exit. *)
  let prune_ref = ref []

  (* Kills the LSD instance. *)
  let no_more_lsd () =
    ( match !base_ref with
      | None -> ()
      | Some lsd -> Lsd.kill_base lsd ) ;
    ( match !step_ref with
      | None -> ()
      | Some lsd -> Lsd.kill_step lsd ) ;
    ! prune_ref |> List.iter (
      fun lsd -> Lsd.kill_pruning lsd
    )

  (* Clean exit. *)
  let exit () =
    no_more_lsd () ;
    exit 0

  (** Prefix used for logging. *)
  let pref = Format.sprintf "[%s Inv Gen]" Domain.name
  (** Prefix used for logging. *)
  let pref_s two_state =
    if two_state then Format.sprintf "[%s Inv Gen 2]" Domain.name
    else Format.sprintf "[%s Inv Gen 1]" Domain.name

  let mk_and_invar_certs invariants_certs =
    let invs, certs = List.split invariants_certs in
    Term.mk_and invs, Certificate.merge certs

  (* Instantiates [invariants] for all the systems calling [sys] and
  communicates them to the framework. Also adds invariants to relevant pruning
  checker from the [sys -> pruning_checker] map [sys_map].

  Returns the number of top level invariants sent and the invariants for [sys],
  sanitized. *)
  let communicate_invariants top_sys sys_map two_state sys = function
    | [] -> (0,[])
    | invariants_certs ->

      let sanitized =
        mk_and_invar_certs invariants_certs
        (* Guarding with init if needed. *)
        |> sanitize_term_cert two_state sys
      in

      (* All intermediary invariants and top level ones. *)
      let ((_, top_invariants), intermediary_invariants) =
        if top_sys == sys then
          (
            top_sys,
            List.map (sanitize_term_cert two_state sys) invariants_certs
          ), []
        else
          sanitized
          (* Instantiating at all levels. *)
          |> Sys.instantiate_term_cert_all_levels 
            top_sys Sys.prop_base (Sys.scope_of_trans_sys sys)
      in

      intermediary_invariants |> List.iter (
        fun (sub_sys, term_certs) ->
          (* Adding invariants to the transition system. *)
          term_certs
          |> List.iter (fun (i, c) -> Sys.add_invariant sub_sys i c) ;
          (* Adding invariants to the pruning checker. *)
          (
            try (
              let pruning_checker = SysMap.find sys_map sub_sys in
              Lsd.pruning_add_invariants pruning_checker term_certs
            ) with Not_found -> (
              (* System is abstract, skipping. *)
            )
          ) ;
          (* Broadcasting invariants. *)
          term_certs |> List.iter (
            fun (i, c) -> Event.invariant (Sys.scope_of_trans_sys sub_sys) i c
          )
      ) ;
      
      let _ =
        try (
          let pruning_checker = SysMap.find sys_map top_sys in
          Lsd.pruning_add_invariants pruning_checker top_invariants
        ) with Not_found -> (
          (* System is abstract, skipping. *)
        )
      in

      let top_scope = Sys.scope_of_trans_sys top_sys in

      top_invariants |> List.iter (
        fun (inv, cert) ->
          (* Adding top level invariants to transition system. *)
          Sys.add_invariant top_sys inv cert ;
          (* Communicate invariant. *)
          Event.invariant top_scope inv cert
      ) ;

      (List.length top_invariants, [sanitized])


  (** Communicates some invariants and adds them to the trans sys. *)
  let communicate_and_add
    two_state top_sys sys_map sys k blah non_trivial trivial
  =
    ( match (non_trivial, trivial) with
      | [], [] -> ()
      | _, [] ->
        Event.log L_info
          "%s @[<v>\
            On system [%s] at %a: %s@ \
            found %d non-trivial invariants\
          @]"
          (pref_s two_state)
          (sys_name sys)
          Num.pp_print_numeral k
          blah
          (List.length non_trivial)
      | [], _ ->
        Event.log L_info
          "%s @[<v>\
            On system [%s] at %a: %s@ \
            found %d trivial invariants\
          @]"
          (pref_s two_state)
          (sys_name sys)
          Num.pp_print_numeral k
          blah
          (List.length trivial)
      | _, _ ->
        Event.log L_info
          "%s @[<v>\
            On system [%s] at %a: %s@ \
            found %d non-trivial invariants and %d trivial ones\
          @]"
          (pref_s two_state)
          (sys_name sys)
          Num.pp_print_numeral k
          blah
          (List.length non_trivial)
          (List.length trivial)
    ) ;
    List.map (fun i -> i, (Numeral.to_int k + 1, i)) non_trivial
    |> communicate_invariants top_sys sys_map two_state sys
    (* (* Broadcasting invariants. *)
    non_trivial |> List.iter (
      fun term ->
        Sys.add_invariant sys term ;
        Event.invariant (Sys.scope_of_trans_sys sys) term
    ) *)


  (** Receives messages from the rest of the framework.

  Updates all transition systems through [top_sys].

  Adds the new invariants to the pruning solvers in the transition system /
  pruning solver map [sys_map].

  Returns the new invariants for the system [sys]. *)
  let recv_and_update input_sys aparam top_sys sys_map sys =

    let rec update_pruning_checkers sys_invs = function
      | [] -> sys_invs
      | (_, (scope, inv, cert)) :: tail ->
        let this_sys = Sys.find_subsystem_of_scope top_sys scope in
        (* Retrieving pruning checker for this system. *)
        (
          try (
            let pruning_checker = SysMap.find sys_map this_sys in
            Lsd.pruning_add_invariants pruning_checker [inv, cert]
          ) with Not_found -> (
            (* System is abstract, skipping it. *)
          )
        ) ;
        update_pruning_checkers (
          if this_sys == sys then (inv, cert) :: sys_invs else sys_invs
        ) tail
    in

    (* Receiving messages. *)
    Event.recv ()
    (* Updating transition system. *)
    |> Event.update_trans_sys_sub input_sys aparam top_sys
    (* Only keep new invariants. *)
    |> fst
    (* Update everything. *)
    |> update_pruning_checkers []


  (** Queries step to identify invariants, prunes trivial ones away,
  communicates non-trivial ones and adds them to the transition system. *)
  let find_invariants
    blah two_state lsd sys_map top_sys sys pruner k f candidates
  =
    (* Format.printf "find_invariants (%d)@.@." (List.length candidates) ;
    Format.printf "  query_step@.@." ; *)
    let invs = Lsd.query_step two_state lsd candidates in
    
    (* Applying client function. *)
    let invs = f invs in

    (* Extracting non-trivial invariants. *)
    (* Format.printf "  pruning@.@." ; *)
    let (non_trivial, trivial) = Lsd.query_pruning pruner invs in

    (* Communicating and adding to trans sys. *)
    let top_level_inc, sanitized =
      communicate_and_add
        two_state top_sys sys_map sys k blah non_trivial trivial
    in
    
    (* Adding sanitized non-trivial to pruning checker. *)
    Lsd.pruning_add_invariants pruner sanitized ;
    (* Adding sanitized non-trivial to step checker. *)
    Lsd.step_add_invariants lsd sanitized ;

    non_trivial, trivial, top_level_inc

  let candidate_count = 200

  let rec take res count = function
  | head :: tail when count <= candidate_count ->
    take (head :: res) (count + 1) tail
  | rest -> res, rest

  let controlled_find_invariants
    blah two_state lsd sys_map top_sys sys pruner k f
  =
    let rec loop non_trivial trivial non_invs top_level_inc candidates =
      let candidates, postponed = take non_invs 1 candidates in
      (* Format.printf "find_invariants %d (%d postponed)@.@."
        (List.length candidates) (List.length postponed) ; *)
      let non_trivial', trivial', top_level_inc' =
        find_invariants
          blah two_state lsd sys_map top_sys sys pruner k f candidates
      in
      let non_invs =
        candidates |> List.fold_left (
          fun acc ((eq, _) as pair) ->
            if (
              List.memq eq non_trivial'
            ) || (
              List.memq eq trivial'
            ) then acc else pair :: acc
        ) []
      in
      let non_trivial, trivial, top_level_inc =
        List.rev_append non_trivial' non_trivial,
        List.rev_append trivial' trivial,
        top_level_inc + top_level_inc'
      in
      match postponed with
      | [] -> non_trivial, trivial, non_invs, top_level_inc
      | _ -> loop non_trivial trivial non_invs top_level_inc postponed
    in

    loop [] [] [] 0



  (** Goes through all the (sub)systems for the current [k]. Then loops
  after incrementing [k]. *)
  let rec system_iterator
    max_depth two_state
    input_sys param top_sys memory k sys_map top_level_count
  = function

  | (sys, graph, non_trivial, trivial) :: graphs ->
    let blah = if sys == top_sys then " (top)" else "" in
    Event.log L_info
      "%s Running on %a%s at %a (%d candidate terms)"
      (pref_s two_state) Scope.pp_print_scope (Sys.scope_of_trans_sys sys) blah
      Num.pp_print_numeral k (Graph.term_count graph) ;

    (* Receiving messages, don't care about new invariants for now as we
    haven't create the base/step checker yet. *)
    let _ = recv_and_update input_sys param top_sys sys_map sys in

    (* Retrieving pruning checker for this system. *)
    let pruning_checker =
      try SysMap.find sys_map sys with Not_found -> (
        Event.log L_fatal
          "%s could not find pruning checker for system [%s]"
          (pref_s two_state) (sys_name sys) ;
        exit ()
      )
    in

    (* Creating base checker. *)
    let lsd = Lsd.mk_base_checker sys k in
    (* Memorizing LSD instance for clean exit. *)
    base_ref := Some lsd ;

    (* Format.printf "LSD instance is at %a@.@." Num.pp_print_numeral (Lsd.get_k lsd sys) ; *)

    (* Prunes known invariants from a list of candidates. *)
    let prune cand =
      Set.mem cand non_trivial || Set.mem cand trivial || Sys.is_inv sys cand
    in
    let prune =
      if two_state then (
        fun cand -> prune cand ||  (
          match Term.var_offsets_of_term cand with
          | (Some _, Some hi) when Num.(hi = ~- one) -> true
          | _ -> false
        ) || (
          if max_depth = None then (
            match Term.var_offsets_of_term cand with
            | (Some lo, Some hi) when lo != hi -> false
            | _ -> true
          ) else false
        )
      ) else prune
    in

    (* Checking if we should terminate before doing anything. *)
    Event.check_termination () ;

    (* Format.printf "%s stabilizing graph...@.@." (pref_s two_state) ; *)

    (* Stabilize graph. *)
    ( try Graph.stabilize graph sys prune lsd with
      | Event.Terminate -> exit ()
      | e -> (
        Event.log L_fatal "caught exception %s" (Printexc.to_string e) ;
        minisleep 0.5 ;
        exit ()
      )
    ) ;
    (* write_dot_to
      "graphs/" "classes" (Format.asprintf "%a" Num.pp_print_numeral k)
      fmt_graph_classes_dot graph ; *)

    (* Format.printf "%s done stabilizing graph@.@." (pref_s two_state) ; *)
    
    (* Event.log_uncond
      "%s Done stabilizing graph, checking consistency" (pref_s two_state) ;
    check_graph graph ;
    Event.log_uncond "%s Done checking consistency" (pref_s two_state) ; *)

    let lsd = Lsd.to_step lsd in
    base_ref := None ;
    step_ref := Some lsd ;

    (* Receiving messages. *)
    let new_invs_for_sys =
      recv_and_update input_sys param top_sys sys_map sys
    in
    Lsd.step_add_invariants lsd new_invs_for_sys ;

    (* Receiving messages. *)
    let new_invs_for_sys =
      recv_and_update input_sys param top_sys sys_map sys
    in
    Lsd.step_add_invariants lsd new_invs_for_sys ;

    (* Check class equivalence first. *)
    let equalities = Graph.equalities_of graph prune in
    (* Extract invariants. *)
    (* Format.printf "(equality) checking for invariants (%d)@.@." (List.length equalities) ; *)
    let non_trivial_eqs, trivial_eqs, non_inv_eqs, top_level_inc =
      controlled_find_invariants
        ( Format.asprintf
            "class equalities (%d candidates)"
            (List.length equalities)
        )
        two_state lsd sys_map top_sys sys pruning_checker k
        (
          List.map (
            fun (eq, (rep, term)) ->
              Graph.drop_class_member graph rep term ;
              eq
          )
        )
        equalities
    in

    (* Extract non invariant equality candidates to check with edges
    candidates. *)
    (* let non_inv_eqs =
      equalities |> List.fold_left (
        fun acc (eq, _) ->
          if (
            List.memq eq non_trivial_eqs
          ) || (
            List.memq eq trivial_eqs
          ) then acc else (eq, ()) :: acc
      ) []
    in *)

    (* Updating set of non-trivial invariants for this system. *)
    let non_trivial =
      non_trivial_eqs |> List.fold_left (
        fun non_trivial inv -> Set.add inv non_trivial
      ) non_trivial
    in

    (* Updating set of trivial invariants for this system. *)
    let trivial =
      trivial_eqs |> List.fold_left (
        fun trivial inv -> Set.add inv trivial
      ) trivial
    in

    let top_level_count = top_level_count + top_level_inc in

    (* Checking graph edges now. *)
    let relations =
      Graph.relations_of graph
        ( List.map (fun (eq, _) -> eq, ()) non_inv_eqs ) prune
    in
    (* Extracting invariants. *)
    (* Format.printf "(relations) checking for invariants@.@." ; *)
    let non_trivial_rels, trivial_rels, _, top_level_inc =
      controlled_find_invariants
        ( Format.asprintf
            "graph relations (%d candidates)"
            (List.length relations)
        )
        two_state lsd sys_map top_sys sys pruning_checker k
        (List.map fst)
        relations
    in

    (* Updating set of non-trivial invariants for this system. *)
    let non_trivial =
      non_trivial_rels |> List.fold_left (
        fun non_trivial inv -> Set.add inv non_trivial
      ) non_trivial
    in

    (* Updating set of trivial invariants for this system. *)
    let trivial =
      trivial_rels |> List.fold_left (
        fun trivial inv -> Set.add inv trivial
      ) trivial
    in

(*  
    (* Next is step graph stabilization. deactivated for now. *)

    let invs =
      Format.printf "step_stabilize:@." ;
      Graph.step_stabilize
        two_state graph sys prune lsd (
          fun l -> Format.printf "  found %d eq invariants@." (List.length l)
        )
    in

    communicate_and_add
      two_state top_sys sys_map sys k "blah" invs [] ;

    Format.printf "  found %d rel invariants@.@." (List.length invs) ; *)

    (* Not adding to lsd, we won't use it anymore. *)
    (* Destroying LSD. *)
    Lsd.kill_step lsd ;
    (* Unmemorizing LSD instance. *)
    step_ref := None ;

    let top_level_count = top_level_count + top_level_inc in


    (* Format.printf "%s non_trivial: @[<v>%a@]@.@."
      pref (pp_print_list fmt_term "@ ") (Set.elements non_trivial) ;

    Format.printf "%s trivial: @[<v>%a@]@.@."
      pref (pp_print_list fmt_term "@ ") (Set.elements trivial) ; *)

    (* write_dot_to "." "graph" "blah" fmt_graph_dot graph ;
    write_dot_to "." "classes" "blah" fmt_graph_classes_dot graph ; *)
    (* minisleep 2.0 ;
    exit () ; *)

    (* Looping. *)
    system_iterator
      max_depth two_state input_sys param top_sys (
        (sys, graph, non_trivial, trivial) :: memory
      ) k sys_map top_level_count graphs

  | [] ->
    (* Done for all systems for this k, incrementing. *)
    let k = Num.succ k in
    match max_depth with
    | Some kay when Num.(k > kay) ->
      Event.log_uncond "%s Reached max depth (%a), stopping."
        (pref_s two_state) Num.pp_print_numeral kay ;
        memory |> List.map (fun (sys, _, nt, t) -> sys, nt, t)
    | _ ->
      (* Format.printf
        "%s Looking for invariants at %a (%d)@.@."
        (pref_s two_state) Num.pp_print_numeral k
        (List.length memory) ; *)
      List.rev memory
      |> system_iterator
        max_depth two_state
        input_sys param top_sys [] k sys_map top_level_count


  (** Invariant generation entry point. *)
  let main max_depth top_only modular two_state input_sys aparam sys =

    (* Format.printf "Starting (%b)@.@." two_state ; *)

    (* Initial [k]. *)
    let k = if two_state then Num.one else Num.zero in

    (* Maps systems to their pruning solver. *)
    let sys_map = SysMap.create 107 in

    (* Generating the candidate terms and building the graphs. Result is a list
    of quadruples: system, graph, non-trivial invariants, trivial
    invariants. *)
    Graph.mine top_only two_state aparam sys (
      fun sys ->
        let pruning_checker = Lsd.mk_pruning_checker sys in
        prune_ref := pruning_checker :: (! prune_ref) ;
        SysMap.replace sys_map sys pruning_checker
    ) |> (
      if modular then 
        (* If in modular mode, we already ran on the subsystems.
        Might as well start with the current top system since it's new. *)
        identity
      else List.rev
    )
    |> fun syss ->
      (* Format.printf "Running on %d systems@.@." (List.length syss) ; *)
      syss
    |> system_iterator max_depth two_state input_sys aparam sys [] k sys_map 0

end




(* |===| Actual invariant generators. *)

(** Boolean invariant generation. *)
module BoolInvGen = Make(InvGenGraph.Bool)

(** Integer invariant generation. *)
module IntInvGen = Make(InvGenGraph.Int)

(** Real invariant generation. *)
module RealInvGen = Make(InvGenGraph.Real)





let main two_state in_sys param sys =
  BoolInvGen.main None (Flags.Invgen.top_only ()) (Flags.modular () |> not) two_state in_sys param sys
  |> ignore




let exit _ = BoolInvGen.exit ()




(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)