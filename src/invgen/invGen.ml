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



(* |===| Module and type aliases *)


(* LSD module. *)
module Lsd = LockStepDriver

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
(* type term = Term.t *)
(* A representative is just a term. *)
(* type rep = term *)

(* Maps terms to something. *)
(* type 'a map = 'a Map.t *)
(* Set of terms. *)
(* type set = Set.t *)

(* Term formatter. *)
let fmt_term = Term.pp_print_term



(* |===| Communication stuff. *)

(** Name of a transition system. *)
let sys_name sys =
  Sys.scope_of_trans_sys sys |> Scope.to_string



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
  val exit : 'a -> unit
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
      | Some lsd -> try Lsd.kill_base lsd with _ -> () ) ;
    ( match !step_ref with
      | None -> ()
      | Some lsd -> try Lsd.kill_step lsd with _ -> () ) ;
    ! prune_ref |> List.iter (
      fun lsd -> try Lsd.kill_pruning lsd with _ -> ()
    )

  (* Clean exit. *)
  let exit _ =
    no_more_lsd () ;
    exit 0

  (** Prefix used for logging one state invariants. *)
  let pref = Format.sprintf "[%s Inv Gen]" Domain.name

  (** Prefix used for logging two state invariants. *)
  let pref_s two_state =
    if two_state then Format.sprintf "[%s Inv Gen 2]" Domain.name
    else Format.sprintf "[%s Inv Gen 1]" Domain.name

  let mk_and_invar_certs invariants_certs =
    let invs, certs = List.split invariants_certs in
    Term.mk_and invs, Certificate.merge certs

  (* Instantiates [invariants] for all the systems calling [sys] and
  communicates them to the framework. Also adds invariants to relevant pruning
  checker from the [sys -> pruning_checker] map [sys_map].

  Returns the number of top level invariants sent and the invariants for
  [sys], one state and two state. *)
  let communicate_invariants top_sys sys_map two_state sys invs =
    (* Function adding invariant to pruner. *)
    let pruner_add_of sys =
      try (
        let pruning_checker = SysMap.find sys_map sys in
        fun inv ->
          Lsd.pruning_add_invariants pruning_checker two_state [inv]
      ) with Not_found -> (
        (* System is abstract, skipping. *)
        ignore
      )
    in

    match invs with
    | [] -> 0, []
    | invars_certs when top_sys == sys ->
      let pruner_add = pruner_add_of sys in
      (* No instantiation in this case. *)
      invars_certs |> List.fold_left (
        fun (cnt, invs) (inv, cert) ->
          let cnt = cnt + 1 in
          (* Adding top level invariants to transition system. *)
          let inv = Sys.add_invariant top_sys inv cert two_state in
          (* Add to pruner. *)
          pruner_add inv ;
          (* Communicate invariant. *)
          KEvent.invariant (Sys.scope_of_trans_sys top_sys) inv cert two_state ;
          cnt, inv :: invs
      ) (0, [])

    | invars_certs -> invars_certs |> List.fold_left (
      fun (cnt, invs) ( (invar, cert) as inv_c ) ->

        (* All intermediary invariants and top level ones, obtained by
        instantiating invariant at all levels. *)
        let (top_invariants, intermediary_invariants) =
          Sys.instantiate_term_cert_all_levels 
            top_sys Sys.prop_base (Sys.scope_of_trans_sys sys) inv_c two_state
        in

        (* Add intermediary invariants to sys and pruner, broadcast, add to
        [os] and [ts] for [sys]. *)
        top_invariants :: intermediary_invariants |> List.fold_left (
          fun (cnt, invs) (sub_sys, term_certs) ->
            let pruner_add = pruner_add_of sub_sys in
            (* Are we at top level? *)
            let at_top_sys = sub_sys == sys in

            term_certs |> List.fold_left (
              fun (cnt, invs) (inv, cert) ->
                (* Add to transition system. *)
                let inv = Sys.add_invariant sub_sys inv cert two_state in
                (* Add to pruner. *)
                pruner_add inv ;
                (* Broadcast. *)
                KEvent.invariant
                  (Sys.scope_of_trans_sys sub_sys) inv cert two_state ;
                (* Remember if at top sys. *)
                if at_top_sys then cnt + 1, inv :: invs else cnt, invs
            ) (cnt, invs)
        ) (cnt, invs)
    ) (0, [])


  (** Communicates some invariants and adds them to the trans sys. *)
  let communicate_and_add
    two_state top_sys sys_map sys k blah non_trivial trivial
  =
    (* Format.printf "trivial: @[<v>%a@]@.@."
      (pp_print_list fmt_term "@ ") trivial ;
    Format.printf "non trivial: @[<v>%a@]@.@."
      (pp_print_list fmt_term "@ ") non_trivial ; *)
    ( match (non_trivial, trivial) with
      | [], [] -> ()
      | _, [] ->
        KEvent.log L_info
          "%s @[<v>\
            On system [%a] at %a: %s@ \
            found %d non-trivial invariants:@   @[<v>%a@]\
          @]"
          (pref_s two_state)
          Scope.pp_print_scope (Sys.scope_of_trans_sys sys)
          Num.pp_print_numeral k
          blah
          (List.length non_trivial)
          (pp_print_list fmt_term "@ ") non_trivial
      | [], _ ->
        KEvent.log L_info
          "%s @[<v>\
            On system [%a] at %a: %s@ \
            found %d trivial invariants\
          @]"
          (pref_s two_state)
          Scope.pp_print_scope (Sys.scope_of_trans_sys sys)
          Num.pp_print_numeral k
          blah
          (List.length trivial)
      | _, _ ->
        KEvent.log L_info
          "%s @[<v>\
            On system [%a] at %a: %s@ \
            found %d non-trivial invariants and %d trivial ones:\
            @   @[<v>%a@]\
          @]"
          (pref_s two_state)
          Scope.pp_print_scope (Sys.scope_of_trans_sys sys)
          Num.pp_print_numeral k
          blah
          (List.length non_trivial)
          (List.length trivial)
          (pp_print_list fmt_term "@ ") non_trivial
    ) ;
    List.map (fun i -> i, (Numeral.to_int k + 1, i)) non_trivial
    |> communicate_invariants top_sys sys_map two_state sys


  (** Receives messages from the rest of the framework.

  Updates all transition systems through [top_sys].

  Adds the new invariants to the pruning solvers in the transition system /
  pruning solver map [sys_map].

  Returns the new invariants for the system [sys]. *)
  let recv_and_update input_sys aparam top_sys sys_map sys =

    let update_pruning_checkers sys_invs map =
      Scope.Map.fold (
        fun scope (os, ts) acc ->
          let this_sys = Sys.find_subsystem_of_scope top_sys scope in
          let os, ts = Set.elements os, Set.elements ts in
          (* Retrieving pruning checker for this system. *)
          (
            try (
              let pruning_checker = SysMap.find sys_map this_sys in
              Lsd.pruning_add_invariants pruning_checker false os ;
              Lsd.pruning_add_invariants pruning_checker true ts
            ) with Not_found -> (
              (* System is abstract or was discarded, skipping it. *)
            )
          ) ;
        if this_sys == sys then (os, ts) else acc
      ) map ([], [])
    in

    (* Receiving messages. *)
    KEvent.recv ()
    (* Updating transition system. *)
    |> KEvent.update_trans_sys_sub input_sys aparam top_sys
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
    let (non_trivial, trivial) =
      if Flags.Invgen.prune_trivial () then
        Lsd.query_pruning pruner invs
      else (invs, [])
    in

    (* Communicating and adding to trans sys. *)
    let top_level_inc, invs =
      communicate_and_add
        two_state top_sys sys_map sys k blah non_trivial trivial
    in

    (* Adding sanitized non-trivial to step checker. *)
    Lsd.step_add_invariants lsd two_state invs ;

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


  (** Destroys the pruning solvers in a sys map. *)
  let kill_solvers sys_map =
    SysMap.iter (
      fun _ pruner -> Lsd.kill_pruning pruner
    ) sys_map ;
    no_more_lsd ()


  (** Goes through all the (sub)systems for the current [k]. Then loops
  after incrementing [k]. *)
  let rec system_iterator
    max_depth two_state
    input_sys param top_sys res memory
    k sys_map top_level_count
  = function

  | (sys, graph, non_trivial, trivial) :: graphs ->
    let blah = if sys == top_sys then " (top)" else "" in
    KEvent.log L_info
      "%s Running on %a%s at %a (%d candidate terms, %d classes)"
      (pref_s two_state) Scope.pp_print_scope (Sys.scope_of_trans_sys sys) blah
      Num.pp_print_numeral k (Graph.term_count graph)
      (Graph.class_count graph) ;

    (* Receiving messages, don't care about new invariants for now as we
    haven't create the base/step checker yet. *)
    let _ = recv_and_update input_sys param top_sys sys_map sys in

    (* Retrieving pruning checker for this system. *)
    let pruning_checker =
      try SysMap.find sys_map sys with Not_found -> (
        KEvent.log L_fatal
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
    let is_inv cand =
         Set.mem cand non_trivial
      || Set.mem cand trivial
      || Sys.is_inv sys cand
    in

    let one_state_running = Domain.is_os_running () in
    (* Prunes known invariants and irrelevant ones. *)
    let prune =
      if two_state then (
        fun cand -> is_inv cand || (
          match Term.var_offsets_of_term cand with
          | (Some lo, Some hi)
          when Num.(lo = hi) && (
            one_state_running || Num.(lo = ~- one)
          ) -> true
          | (None, None) -> true
          | _ -> false
        )
      ) else is_inv
    in

    (* Format.printf "%s stabilizing graph...@.@." (pref_s two_state) ; *)

    (* Checking if we should terminate before doing anything. *)
    KEvent.check_termination () ;

    (* Stabilize graph.

    Note that we use `is_inv` here and not `prune`. The latter also removes
    terms that **might** be invariant in the one-state version, but which at
    this stage might cause the graph to split. *)
    Graph.stabilize graph sys is_inv lsd ;

    (* InvGenGraph.write_dot_to
      "./" "classes" "after"
      Graph.fmt_graph_classes_dot graph ; *)

    (* Format.printf "%s done stabilizing graph@.@." (pref_s two_state) ; *)
    
    (* KEvent.log_uncond
      "%s Done stabilizing graph, checking consistency" (pref_s two_state) ;
    if Graph.check_graph graph |> not then
      failwith "inconsistent graph" ;
    KEvent.log_uncond "%s Done checking consistency" (pref_s two_state) ; *)

    let lsd = Lsd.to_step lsd in
    base_ref := None ;
    step_ref := Some lsd ;

    (* Receiving messages. *)
    let new_os, new_ts =
      recv_and_update input_sys param top_sys sys_map sys
    in
    Lsd.step_add_invariants lsd false new_os ;
    Lsd.step_add_invariants lsd true new_ts ;

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

    (* let suff =
      Format.asprintf "%a_%s" Num.pp_print_numeral k (sys_name sys)
    in
    InvGenGraph.write_dot_to
      "./dot" "graph" suff Graph.fmt_graph_dot graph ;
    InvGenGraph.write_dot_to
      "./dot" "classes" suff Graph.fmt_graph_classes_dot graph ; *)
    (* minisleep 2.0 ;
    exit () ; *)

    (* Forget the graph if it is stale. *)
    let memory, res =
      (* if Graph.is_stale graph then (
        KEvent.log L_info
          "%s Graph for system %a is stale, forgetting it."
          (pref_s two_state)
          Scope.pp_print_scope (Sys.scope_of_trans_sys sys) ;
        (
          try
            SysMap.find sys_map sys |> Lsd.kill_pruning
          with Not_found ->
            KEvent.log L_warn
              "%s Could not find pruning checker for system %a."
              (pref_s two_state)
              Scope.pp_print_scope (Sys.scope_of_trans_sys sys) ;
        ) ;
        SysMap.remove sys_map sys ;
        prune_ref := SysMap.fold (
          fun _ prune acc -> prune :: acc
        ) sys_map [] ;
        memory, (sys, non_trivial, trivial) :: res
      ) else *)
        (sys, graph, non_trivial, trivial) :: memory, res
    in

    (* Looping. *)
    system_iterator
      max_depth two_state input_sys param top_sys
      res memory k sys_map top_level_count graphs

  | [] -> (
    (* Done for all systems for this k, incrementing. *)
    let k = Num.succ k in
    match max_depth with
    | Some kay when Num.(k > kay) ->
      KEvent.log L_info "%s Reached max depth (%a), stopping."
        (pref_s two_state) Num.pp_print_numeral kay ;
      kill_solvers sys_map ;
      memory |> List.map (fun (sys, _, nt, t) -> sys, nt, t)
    | _ -> (
      match memory with
      | [] ->
        KEvent.log L_info
          "%s No more system to run on, stopping."
          (pref_s two_state) ;
        kill_solvers sys_map ;
        res
      | _ ->
        (* Format.printf
          "%s Looking for invariants at %a (%d)@.@."
          (pref_s two_state) Num.pp_print_numeral k
          (List.length memory) ; *)
        List.rev memory
        |> system_iterator
          max_depth two_state
          input_sys param top_sys res [] k sys_map top_level_count
    )
  )


  (** Invariant generation entry point. *)
  let main max_depth top_only modular two_state input_sys aparam sys =
    try (
    
      (* Format.printf "Starting (%b)@.@." two_state ; *)

      (* Initial [k]. *)
      let k = if two_state then Num.one else Num.zero in

      (* Maps systems to their pruning solver. *)
      let sys_map = SysMap.create 107 in

      (* Generating the candidate terms and building the graphs. Result is a
      list of quadruples: system, graph, non-trivial invariants, trivial
      invariants. *)
      Graph.mine top_only two_state aparam sys (
        fun sys ->
          let pruning_checker = Lsd.mk_pruning_checker sys in
          prune_ref := pruning_checker :: (! prune_ref) ;
          SysMap.replace sys_map sys pruning_checker
      )
      |> List.filter (
        fun (_, graph, _, _) ->
          Graph.has_svars graph
      )
      (* If in modular mode, we already ran on the subsystems.
      Might as well start with the current top system since it's new. *)
      |> ( if modular then identity else List.rev )
      |> function
        | [] ->
          KEvent.log L_info "%s no candidate to run on" (pref_s two_state) ;
          exit ()
        | graphs ->
          system_iterator
            max_depth two_state input_sys aparam sys [] [] k sys_map 0 graphs

    ) with
    | KEvent.Terminate -> exit ()
    | Failure msg -> (
      KEvent.log L_fatal "Caught failure in invariant generator: %s" msg ;
      minisleep 0.5 ;
      exit ()
    )
    | e -> (
      KEvent.log L_fatal "Caught exception in invariant generator: %s" (Printexc.to_string e) ;
      minisleep 0.5 ;
      exit ()
    )

end




(* |===| Actual invariant generators. *)

(** Boolean invariant generation. *)
module BoolInvGen = Make(InvGenGraph.Bool)

(** Integer invariant generation. *)
module IntInvGen = Make(InvGenGraph.Int)

(** Int8 invariant generation. *)
module Int8InvGen = Make(InvGenGraph.Int8)

(** Int16 invariant generation. *)
module Int16InvGen = Make(InvGenGraph.Int16)

(** Int32 invariant generation. *)
module Int32InvGen = Make(InvGenGraph.Int32)

(** Int64 invariant generation. *)
module Int64InvGen = Make(InvGenGraph.Int64)

(** UInt8 invariant generation. *)
module UInt8InvGen = Make(InvGenGraph.UInt8)

(** UInt16 invariant generation. *)
module UInt16InvGen = Make(InvGenGraph.UInt16)

(** UInt32 invariant generation. *)
module UInt32InvGen = Make(InvGenGraph.UInt32)

(** UInt64 invariant generation. *)
module UInt64InvGen = Make(InvGenGraph.UInt64)

(** Real invariant generation. *)
module RealInvGen = Make(InvGenGraph.Real)

(** Graph modules for equivalence-only invgen. *)
module EqOnly = struct

  (** Graph of booleans. *)
  module BoolInvGen = Make( InvGenGraph.EqOnly.Bool )

  (** Graph of integers. *)
  module IntInvGen = Make( InvGenGraph.EqOnly.Int )

  (** Graph of int8s. *)
  module Int8InvGen = Make( InvGenGraph.EqOnly.Int8 )

  (** Graph of int16s. *)
  module Int16InvGen = Make( InvGenGraph.EqOnly.Int16 )

  (** Graph of int32s. *)
  module Int32InvGen = Make( InvGenGraph.EqOnly.Int32 )

  (** Graph of int64s. *)
  module Int64InvGen = Make( InvGenGraph.EqOnly.Int64 )

  (** Graph of uint8s. *)
  module UInt8InvGen = Make( InvGenGraph.EqOnly.UInt8 )

  (** Graph of uint16s. *)
  module UInt16InvGen = Make( InvGenGraph.EqOnly.UInt16 )

  (** Graph of uint32s. *)
  module UInt32InvGen = Make( InvGenGraph.EqOnly.UInt32 )

  (** Graph of uint64s. *)
  module UInt64InvGen = Make( InvGenGraph.EqOnly.UInt64 )

  (** Graph of reals. *)
  module RealInvGen = Make( InvGenGraph.EqOnly.Real )

end



let max_depth () = match Flags.Invgen.max_depth () with
  | Some n -> Some Num.(of_int n)
  | None -> None

let run_main eq_cond eq_main main two_state in_sys param sys =
    (
      if eq_cond () then eq_main else main
    ) (
      max_depth ()
    ) (
      Flags.Invgen.top_only ()
    ) (
      Flags.modular () |> not
    ) two_state in_sys param sys
    |> ignore ;
    exit 0

let main_bool two_state in_sys param sys =
  run_main Flags.Invgen.bool_eq_only EqOnly.BoolInvGen.main BoolInvGen.main
           two_state in_sys param sys

let main_int two_state in_sys param sys =
  run_main Flags.Invgen.arith_eq_only EqOnly.IntInvGen.main IntInvGen.main
           two_state in_sys param sys

let main_int8 two_state in_sys param sys =
  run_main Flags.Invgen.arith_eq_only EqOnly.Int8InvGen.main Int8InvGen.main
           two_state in_sys param sys

let main_int16 two_state in_sys param sys =
  run_main Flags.Invgen.arith_eq_only EqOnly.Int16InvGen.main Int16InvGen.main
           two_state in_sys param sys

let main_int32 two_state in_sys param sys =
  run_main Flags.Invgen.arith_eq_only EqOnly.Int32InvGen.main Int32InvGen.main
           two_state in_sys param sys

let main_int64 two_state in_sys param sys =
  run_main Flags.Invgen.arith_eq_only EqOnly.Int64InvGen.main Int64InvGen.main
           two_state in_sys param sys

let main_uint8 two_state in_sys param sys =
  run_main Flags.Invgen.arith_eq_only EqOnly.UInt8InvGen.main UInt8InvGen.main
           two_state in_sys param sys

let main_uint16 two_state in_sys param sys =
  run_main Flags.Invgen.arith_eq_only EqOnly.UInt16InvGen.main UInt16InvGen.main
           two_state in_sys param sys

let main_uint32 two_state in_sys param sys =
  run_main Flags.Invgen.arith_eq_only EqOnly.UInt32InvGen.main UInt32InvGen.main
           two_state in_sys param sys

let main_uint64 two_state in_sys param sys =
  run_main Flags.Invgen.arith_eq_only EqOnly.UInt64InvGen.main UInt64InvGen.main
           two_state in_sys param sys

let main_real two_state in_sys param sys =
  run_main Flags.Invgen.arith_eq_only EqOnly.RealInvGen.main RealInvGen.main
           two_state in_sys param sys

let exit _ =
  ( if Flags.Invgen.bool_eq_only () then
      EqOnly.BoolInvGen.exit ()
    else
      BoolInvGen.exit ()
  ) ;
  if Flags.Invgen.arith_eq_only () then (
    EqOnly.IntInvGen.exit () ;
    EqOnly.RealInvGen.exit ()
  ) else (
    IntInvGen.exit () ;
    RealInvGen.exit ()
  )




(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
