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


(* |===| Aliases. *)


(* LSD module. *)
module Lsd = LockStepDriver

(* Term hash table. *)
module Map = Term.TermHashtbl
(* Term set. *)
module Set = Term.TermSet

(* Values. *)
module type DomainSig = InvGenDomain.Domain



(* Term. *)
type term = Term.t
(* Maps terms to something. *)
type 'a map = 'a Map.t
(* Set of terms. *)
type set = Set.t



(* |===| Helper stuff. *)


(* Term formatter. *)
let fmt_term = Term.pp_print_term

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




(* |===| Preliminary functor stuff. *)


(** Signature of the modules created by the graph functor. *)
module type Graph = sig
  (** Domain with an order relation. *)
  module Domain : DomainSig

  (** A graph. *)
  type graph

  (** Creates a graph from a single equivalence class and its
  representative. *)
  val mk_graph : term -> set -> graph

  (** Total number of terms in the graph. *)
  val term_count : graph -> int

  (** Drops a term from the class corresponding to a representative. *)
  val drop_class_member : graph -> term -> term -> unit

  (** Formats a graph in dot format. Only the representatives will appear. *)
  val fmt_graph_dot : Format.formatter -> graph -> unit
  (** Formats the eq classes of a graph in dot format. *)
  val fmt_graph_classes_dot : Format.formatter -> graph -> unit

  (** Checks that a graph makes sense. Dumps the graph and its classes in dot
  format in the current directory if the graph does not make sense. *)
  val check_graph : graph -> bool

  (** Minimal list of terms encoding the current state of the graph. Contains
  - equality between representatives and their class, and
  - comparison terms between representatives.

  Input function returns true for candidates we want to ignore, typically
  candidates we have already proved true.

  Used when querying the base instance of the LSD (graph stabilization).
  See also [equalities_of] and [relations_of], used for the step instance
  (induction check). *)
  val terms_of : graph -> (term -> bool) -> term list

  (** Equalities coming from the equivalence classes of a graph.

  Input function returns true for candidates we want to ignore, typically
  candidates we have already proved true.

  Generates a list of pairs [term * (term * term)]. The first term is the
  candidate invariant, while the second element stores the representative
  of the class the candidate comes from, and the term that can be dropped
  from it if the candidate is indeed invariant. *)
  val equalities_of : graph -> (term -> bool) -> (term * (term * term)) list

  (** Appends the relations from a graph to the input term list.

  Input function returns true for candidates we want to ignore, typically
  candidates we have already proved true.

  More precisely, generates implications between representatives and the
  representative and terms of each equivalence class they're a parent of.

  Generates a list of pairs [term * unit]. The useless [unit] second element
  is just there to be compatible with the signature of the lsd step query
  function. This is to accomodate with the information we need to keep around
  for the equalities of a graph (see [equalities_of]). *)
  val relations_of :
    graph -> (term * unit) list -> (term -> bool) -> (term * unit) list

  (** Queries the lsd and updates the graph. Terminates when the graph is
  stable, meaning all terms the graph represents are unfalsifiable in the
  current lsd.

  Input function returns true for candidates we want to ignore, typically
  candidates we have already proved true. *)
  val update : graph -> TransSys.t -> (term -> bool) -> Lsd.base -> unit
end






(* |===| Functor! *)


(** Functor creating value specific graphs. *)
module Make (Dom: DomainSig) : Graph = struct

  (** Domain with an order relation. *)
  module Domain = Dom

  (** Structure storing all the graph information. *)
  type graph = {
    (** Maps representatives [t] to the set [{t_i}] of representatives such
    that, for all models seen so far and for all [t_i]s, [In.cmp t t_i]. *)
    map_up: set map ;
    (** Maps representatives [t] to the set [{t_i}] of representatives such
    that, for all models seen so far and for all [t_i]s, [In.cmp t_i t]. *)
    map_down: set map ;
    (** Maps representatives [t] to the set of terms [{t_i}] they represent.
    That is, for all models seen so far and for all [t_i]s,
    [In.value_eq t t_i]. *)
    classes: set map ;
    (** Maps representatives to the value they evaluate to in the current
    model. Cleared between each iteration ([clear] not [reset]). *)
    values: Domain.t map ;
  }

  (** Graph constructor. *)
  let mk_graph rep candidates = {
    map_up = (
      let map = Map.create 107 in
      Map.replace map rep Set.empty ;
      map
    ) ;
    map_down = (
      let map = Map.create 107 in
      Map.replace map rep Set.empty ;
      map
    ) ;
    classes = (
      let map = Map.create 107 in
      Map.replace map rep candidates ;
      map
    ) ;
    values = Map.create 107 ;
  }

  (** Total number of terms in the graph. *)
  let term_count { classes } =
    Map.fold (
     fun rep cl4ss sum -> sum + 1 + (Set.cardinal cl4ss)
    ) classes 0

  (** Forgets a member of an equivalence class. *)
  let drop_class_member { classes } rep term =
    try
      Map.find classes rep
      |> Set.remove term
      |> Map.replace classes rep
    with Not_found ->
      Event.log L_fatal
        "drop_class_member asked to drop term [%a] for inexistant rep [%a]"
        fmt_term term fmt_term rep ;
      raise Not_found

  (** Formats a graph to graphviz format. *)
  let fmt_graph_dot fmt { map_up ; map_down ; classes ; values } =
    Format.fprintf fmt
    "\
digraph mode_graph {
 graph [bgcolor=black margin=0.0] ;
 node [
   style=filled
   fillcolor=black
   fontcolor=\"#1e90ff\"
   color=\"#666666\"
 ] ;
 edge [color=\"#1e90ff\" fontcolor=\"#222222\"] ;

\
   @[<v>" ;

    map_up |> Map.iter (
      fun key ->
        let key_len = 1 + (Set.cardinal (Map.find classes key)) in
        let key_value =
          try Map.find values key |> Format.asprintf "%a" Domain.fmt
          with Not_found -> "_mada_"
        in
        Set.iter (
          fun kid ->
            let kid_len = 1 + (Set.cardinal (Map.find classes kid)) in
            let kid_value =
              try Map.find values kid |> Format.asprintf "%a" Domain.fmt
              with Not_found -> "_mada_"
            in
            Format.fprintf
              fmt "\"%a (%d, %s)\" -> \"%a (%d, %s)\" [\
                constraint=false\
              ] ;@ "
              fmt_term key key_len key_value
              fmt_term kid kid_len kid_value
        )
    ) ;

    map_down |> Map.iter (
      fun key ->
        let key_len = 1 + (Set.cardinal (Map.find classes key)) in
        let key_value =
          try Map.find values key |> Format.asprintf "%a" Domain.fmt
          with Not_found -> "_mada_"
        in
        Set.iter (
          fun kid ->
            let kid_len = 1 + (Set.cardinal (Map.find classes kid)) in
            let kid_value =
              try Map.find values kid |> Format.asprintf "%a" Domain.fmt
              with Not_found -> "_mada_"
            in
            Format.fprintf
              fmt "\"%a (%d, %s)\" -> \"%a (%d, %s)\" [\
                color=\"red\"\
              ] ;@ "
              fmt_term key key_len key_value
              fmt_term kid kid_len kid_value
        )
    ) ;

    Format.fprintf fmt "@]@.}@."


  (** Logs the equivalence classes of a graph to graphviz. *)
  let fmt_graph_classes_dot fmt { classes ; values } =
    Format.fprintf fmt
      "\
digraph mode_graph {
  graph [bgcolor=black margin=0.0] ;
  node [
    style=filled
    fillcolor=black
    fontcolor=\"#1e90ff\"
    color=\"#666666\"
  ] ;
  edge [color=\"#1e90ff\" fontcolor=\"#222222\"] ;

\
    @[<v>" ;

    classes |> Map.iter (
      fun rep set ->
        let rep_value =
          try Map.find values rep |> Format.asprintf "%a" Domain.fmt
          with Not_found -> "_mada_"
        in
        Format.fprintf fmt "\"%a (%s)\" ->\"%a\" ;@ "
          fmt_term rep rep_value
          (pp_print_list
            (fun fmt term -> Format.fprintf fmt "@[<h>%a@]" fmt_term term)
            "\n")
          (Set.elements set)
    ) ;

    Format.fprintf fmt "@]@.}@."

  (* Checks that a graph makes sense. *)
  let check_graph ( { map_up ; map_down ; classes } as graph ) =
    (* Format.printf "Checking graph...@.@." ; *)
    Map.fold (
      fun rep reps ok ->

        let is_ok = ref true in

        if ( (* Fail if [rep] has no kids and is not [true] or [false]. *)
          Set.is_empty reps && rep <> Term.t_false && rep <> Term.t_true
        ) then (
          Event.log L_fatal
            "Inconsistent graph:@   \
            @[<v>representative [%a] has no kids@]"
            Term.pp_print_term rep ;
          is_ok := false
        ) ;

        ( try let _ = Map.find classes rep in ()
          with Not_found -> (
            Event.log L_fatal
              "Inconsistent graph:@   \
              @[<v>representative [%a] has no equivalence class@]"
              Term.pp_print_term rep ;
            is_ok := false
          )
        ) ;

        reps |> Set.iter (
          fun kid ->
            try (
              let kid_parents = Map.find map_down kid in
              if Set.mem rep kid_parents |> not then (
                (* Fail if [rep] is not a parent of [kid]. *)
                Event.log L_fatal
                  "Inconsistent graph:@   \
                  @[<v>representative [%a] is a kid of [%a]@ \
                  but [%a] is not a parent of [%a]@]"
                  Term.pp_print_term kid Term.pp_print_term rep
                  Term.pp_print_term rep Term.pp_print_term kid ;
                is_ok := false
              )
            ) with Not_found -> (
              (* Fail if [kid] does not appear in [map_down]. *)
              Event.log L_fatal
                "Inconsistent graph:@   \
                @[<v>representative [%a] does not appear in [map_down]@]"
                Term.pp_print_term kid ;
              is_ok := false
            )
        ) ;

        ok && ! is_ok
    ) map_up true
    |> function
    | true -> true
    | false -> (
      Event.log L_fatal
        "Stopping invariant generation due to graph inconsistencies" ;
      let dump_path = "./" in
      Event.log L_fatal
        "Dumping current graph as graphviz in current directory" ;
      write_dot_to
        dump_path "inconsistent" "graph" fmt_graph_dot graph ;
      Event.log L_fatal
        "Dumping current classes as graphviz in current directory" ;
      write_dot_to
        dump_path "inconsistent" "classes" fmt_graph_classes_dot graph ;
      false
    )


  (** Clears the [values] field of the graph ([clear] not [reset]). *)
  let clear { values } = Map.clear values

  (** Minimal list of terms encoding the current state of the graph. Contains
  - equality between representatives and their class, and
  - comparison terms between representatives.

  Used when querying the base instance of the LSD (graph stabilization).
  See also [all_terms_of], used for the step instance (induction check). *)
  let terms_of { map_up ; classes } known =
    let cond_cons cand l = if known cand then l else cand :: l in
    let eqs =
      Map.fold (
        fun rep set acc ->
          if Set.is_empty set then acc else
            cond_cons (rep :: Set.elements set |> Term.mk_eq) acc
      ) classes []
    in
    Map.fold (
      fun rep above acc ->
        if Domain.is_bot rep then acc else
          above |> Set.elements |> List.fold_left (
            fun acc rep' ->
              if Domain.is_top rep' then acc
              else cond_cons (Domain.mk_cmp rep rep') acc
          ) acc
    ) map_up eqs

  (** Maximal list of terms encoding the current state of the graph. Contains
  - equality between representatives and their class, and
  - comparison terms between all members of the classes.

  Ignores all terms for which [known] is [true].

  Used when querying the step instance of the LSD (induction check). The idea
  is that while the comparison terms between representatives may not be
  inductive, some comparison terms between member of their respective class
  may be.

  See also [terms_of], used for the base instance (graph stabilization).
  This version produces a much larger number of terms. *)
  let all_terms_of {map_up ; classes} known =
    let cond_cons cand l = if known cand then l else cand :: l in
    (* let eqs =
      Map.fold (
        fun rep set acc ->
          if Set.is_empty set then acc else
            cond_cons (rep :: Set.elements set |> Term.mk_eq) acc
      ) classes []
    in *)
    Map.fold (
      fun rep above acc ->
        Set.fold (
          fun rep' acc ->
            (cond_cons (Domain.mk_cmp rep rep') acc, true)
            |> Set.fold (
              fun rep_eq' (acc, fst) ->
                cond_cons (Domain.mk_cmp rep rep_eq') acc
                |> Set.fold (
                  fun rep_eq acc ->
                    let acc =
                      if fst then (
                        cond_cons (Domain.mk_cmp rep_eq rep') acc
                        |> cond_cons (Term.mk_eq [rep ; rep_eq])
                      ) else acc
                    in
                    cond_cons (Domain.mk_cmp rep_eq rep_eq') acc
                ) (Map.find classes rep),
                false
            ) (Map.find classes rep')
            |> fst
        ) above acc
    ) map_up []


  (** Equalities coming from the equivalence classes of a graph. *)
  let equalities_of { classes } known =
    let cond_cons l cand info =
      if known cand then l else (cand, info) :: l
    in
   
    let rec loop rep pref suff = function
      | term :: tail ->
        let pref =
          cond_cons pref (Term.mk_eq [ rep ; term ]) (rep, term)
        in
        let suff =
          List.fold_left (
            fun suff term' ->
              cond_cons suff (Term.mk_eq [ term ; term' ]) (rep, term')
          ) suff tail
        in
        loop rep pref suff tail
      | [] -> List.rev_append pref suff
    in

    Map.fold (
      fun rep terms acc ->
        if Set.cardinal terms < 50 then
          Set.elements terms |> loop rep [] acc
        else
          Set.fold (
            fun term acc ->
              ( Term.mk_eq [rep ; term], (rep, term) ) :: acc
          ) terms acc
    ) classes []


  (** Relations between representatives coming from a graph. *)
  let relations_of { map_up ; classes } acc known =
    let cond_cons l cand =
      if known cand then l else (cand, ()) :: l
    in

    (* For each [rep -> term] in [map_up]. *)
    Map.fold (
      fun rep reps acc ->
        if Domain.is_bot rep then acc else
          Set.fold (
            fun rep' acc ->
              if (
                Domain.is_bot rep
              ) || (
                Domain.is_top rep'
              ) then acc else (
                let acc = Domain.mk_cmp rep rep' |> cond_cons acc in
                let cl4ss = Map.find classes rep' in
                Set.fold (
                  fun term acc -> Domain.mk_cmp rep term |> cond_cons acc
                ) cl4ss acc
              )
          ) reps acc
    ) map_up acc

  (* Formats a chain. *)
  let fmt_chain fmt =
    Format.fprintf fmt "[%a]" (
      pp_print_list
      (fun fmt (rep, value) ->
        Format.fprintf fmt "<%a, %a>" fmt_term rep Domain.fmt value)
      ", "
    )

  (** Applies a function [f] to the value [key] is bound to in [map].

  Optional parameter [not_found] is used if [key] is not bound in [map]:
  - if it's [None], [apply] fails
  - if it's [Some default], then a binding between [key] and [f default] will
   be created
  *)
  let apply ?(not_found=None) f key map =
    try
      Map.find map key |> f |> Map.replace map key
    with Not_found -> (
      match not_found with
      | None ->
        Format.asprintf "could not find %a in map" fmt_term key
        |> failwith
      | Some default -> f default |> Map.replace map key
    )

  (** Transitive closure of the parent relation. *)
  let parent_trc map_down =
    let rec loop to_do set rep =
      let kids = Map.find map_down rep in
      let set, to_do =
        Set.fold (
          fun kid (set, to_do) ->
            if Set.mem kid set then set, to_do
            else Set.add kid set, Set.add kid to_do
        ) kids (Set.add rep set, to_do)
      in
      try (
        let rep = Set.choose to_do in
        loop (Set.remove rep to_do) set rep
      ) with Not_found -> set
    in
    loop Set.empty

  (** Adds an edge to the graph. Updates [map_up] and [map_down]. *)
  let add_up { map_up ; map_down } rep kid =
    apply ~not_found:(Some Set.empty) (Set.add kid) rep map_up ;
    apply ~not_found:(Some Set.empty) (Set.add rep) kid map_down


  (** Splits the class of a representative based on a model. Returns the
  resulting chain sorted in DECREASING order on the values of the reps. *)
  let split sys new_reps { classes ; values ; map_up ; map_down } model rep =
    (* Format.printf "  splitting %a@." fmt_term rep ; *)

    (* Domain of the representative. *)
    let rep_val = Domain.eval sys model rep in

    (* Class of the representative. Terms evaluating to a different value will
    be removed from this set. *)
    let rep_cl4ss = ref (Map.find classes rep) in

    (* Insertion in a list of triples composed of
    - a representative
    - its value in the model
    - its class (set of terms
    The list is ordered by decreasing values.

    Used to evaluate all the terms in [rep_cl4ss] and create the new classes.

    If a representative for the value we're inserting does not exist, then
    a new triple [term, value, Set.empty] is created at the right place in the
    sorted list. Otherwise, if the value is different from [rep_val], it is
    inserted in the set of the representative with that value.
    In both these cases, the term is removed from [rep_cl4ss].
    If the value is equal to [rep_val], nothing happens.

    The idea is that if all terms evaluate to the representative's value, no
    operation is performed. Once all terms in [rep_cl4ss] have been evaluated
    and "inserted", then the representative is inserted with the remaining
    terms form [rep_cl4ss]. *)
    let rec insert ?(is_rep=false) pref sorted term value =
      if is_rep || value <> rep_val then (
        let default = if is_rep then !rep_cl4ss else Set.empty in
        if not is_rep then rep_cl4ss := Set.remove term !rep_cl4ss ;

        match sorted with

        | [] ->
          (* No more elements, inserting. *)
          (term, value, default) :: pref |> List.rev

        | (rep, value', set) :: tail when value = value' ->
          (* Inserting. *)
          (rep, value', Set.add term set) :: tail |> List.rev_append pref

        | ( ((_, value', _) :: _) as tail) when Domain.cmp value' value ->
          (* Found a value lower than [value], inserting. *)
          (term, value, default) :: tail |> List.rev_append pref

        | head :: tail ->
          (* [head] is greater than [value], looping. *)
          insert ~is_rep:is_rep (head :: pref) tail term value

      ) else sorted
    in

    (* Creating new classes if necessary. *)
    let sorted =
      Set.fold (
        fun term sorted -> insert [] sorted term (Domain.eval sys model term)
      ) !rep_cl4ss []
    in

    match sorted with

    (* No new class was created, all terms evaluate to the value of the 
    representative. *)
    | [] ->
      (* Update values, no need to update classes. *)
      Map.replace values rep rep_val ;
      (* All terms in the class yield the same value. *)
      [ (rep, rep_val) ], new_reps

    (* New classes were created. *)
    | _ ->
      (* Representative's class was split, inserting [rep] and its updated
      class. *)
      let new_reps = ref new_reps in
      let chain =
        insert ~is_rep:true [] sorted rep rep_val
        |> List.map (
          fun (rep, value, set) ->
            (* TODO: add [is_bot] and [is_top] to input modules and use that
            instead. *)
            let rep, set =
              if Set.mem Term.t_true set
              then Term.t_true, set |> Set.add rep |> Set.remove Term.t_true
              else rep, set
            in
            new_reps := ! new_reps |> Set.add rep ;
            (* Update class map. *)
            Map.replace classes rep set ;
            (* Update values. *)
            Map.replace values rep value ;
            (* Insert with empty kids and parents if not already there. *)
            apply ~not_found:(Some Set.empty) identity rep map_up ;
            apply ~not_found:(Some Set.empty) identity rep map_down ;

            (rep, value)
        )
      in

      chain, ! new_reps


  (** Inserts a chain obtained by splitting [rep] in a graph.

  ASSUMES the chain is in DECREASING order.

  Remember that a node can be split iff all its parents have been split. *)
  let insert ({ map_up ; map_down ; values } as graph) rep chain =

    (* Nodes above [rep]. *)
    let above = Map.find map_up rep in
    (* Nodes below [rep]. *)
    let below = Map.find map_down rep in

    (* Greatest value in the chain. *)
    let greatest_rep, greatest_val = List.hd chain in

    (* Break all links to [rep], except if rep is the top of the chain. These
    links will be used to update the kids of [rep] in the future. Remember that
    a node can be split iff all its parents have been split. Hence all the kids
    of the current representative have not been split yet. *)
    if Term.equal rep greatest_rep |> not then (
      (* Format.printf "    breaking all links from %a@." fmt_term rep ; *)
      map_up |> apply (
        fun set ->
          (* Break downlinks. *)
          set |> Set.iter (
            fun rep' ->
              (* Format.printf
                "      breaking %a -> %a@." fmt_term rep fmt_term rep' ; *)
              map_down |> apply (Set.remove rep) rep'
          ) ;
          (* Break uplinks. *)
          Set.empty
      ) rep ;
      (* Format.printf "    linking greatest to above@." ; *)
      above |> Set.iter (
        fun above ->
          map_up |> apply (Set.add above) greatest_rep ;
          map_down |> apply (Set.add greatest_rep) above
      )
    ) ;

    (* Break all links to [rep]. *)
    map_down |> apply (
      fun set ->
        (* Break uplinks. *)
        set |> Set.iter (
          fun rep' ->
            (* Format.printf
              "      breaking %a -> %a@." fmt_term rep' fmt_term rep ; *)
            map_up |> apply (Set.remove rep) rep'
        ) ;
        (* Break uplinks. *)
        Set.empty
    ) rep ;

    (* Format.printf "    creating chain links@." ; *)
   
    (* Create links between the elements of the chain.

    Has to be done after we disconnect [rep], otherwise these links would also
    be disconnected. *)
    let rec link_chain last = function
      | (next, _) :: tail ->
        (* Format.printf
          "      creating %a -> %a@." fmt_term next fmt_term last ; *)
        add_up graph next last ;
        link_chain next tail
      | [] -> ()
    in
    ( match chain with
      | (head, _) :: tail -> link_chain head tail
      (* This case IS unreachable, because of the [List.hd chain] above that
      would crash if [chain] was empty. *)
      | [] -> failwith "unreachable"
    ) ;

    (* Returns the longest subchain above [value'], in INCREASING order.
    Assumes the chain is in DECREASING order. *)
    let rec longest_above pref value' = function
      | (rep, value) :: tail when Domain.cmp value' value ->
        (* [value'] lower than the head, looping. *)
        longest_above (rep :: pref) value' tail
      | rest ->
        (* [value'] greaten than the head, done. *)
        pref, rest
    in

    (* Inserts a chain.
    - [known]: nodes below [rep] we have already seen
    - [continuation]: list of (sub)chain / parent left to handle
    - [chain]: (sub)chain we're currently inserting
    - [node]: the node we're trying to link to the chain *)
    let rec insert known continuation chain node =
      let value = Map.find values node in

      (* Longest chain above current node. *)
      let chain_above, rest = longest_above [] value chain in

      (* Format.printf "    %d above, %d below@."
        (List.length chain_above) (List.length rest) ; *)

      (* Creating links. *)
      ( match chain_above with
        | [] ->
          (* [value] is greater than the greatest value in the (sub)chain. *)

          (* Linking [node] with [above] if [node] is in [below]. (This means
          [node] is a direct parent of [rep] that's greater than any element of
          the chain.) *)
          if Set.mem node below then (
            (* Format.printf "    linking node to above@." ; *)
            map_up |> apply (Set.union above) node ;
            above |> Set.iter (
              fun above -> map_down |> apply (Set.add node) above
            )
          )
        | lowest :: _ ->
          (* [lowest] is the LOWEST element of the chain above [node]. We thus
          link [node] to [lowest]. *)

          add_up graph node lowest ;

          (* I had this thing at some point, but it should not be needed.
          Keeping it just in case. *)

          (* (* Also linking with [above] is [node] is in [below]. *)
          if Set.mem node below then (
            (* Format.printf "    linking greatest to above@." ; *)
            map_up |> apply (Set.union above) greatest_rep ;
            above |> Set.iter (
              fun above -> map_down |> apply (Set.add greatest_rep) above
            )
          ) *)
      ) ;

      (* Anything left to insert below? *)
      match rest with
      | [] ->
        (* Chain completely inserted, add everything below [node] to
        [known]. *)
        let known = parent_trc map_down known node in
        (* Continuing. *)
        continue known continuation
      | _ ->
        (* Not done inserting the chain. *)
        (rest, Map.find map_down node |> Set.elements) :: continuation
        |> continue known

    (* Continuation for chain insertion. *)
    and continue known = function
      | ( chain, [node]) :: continuation ->
        if Set.mem node known then (
          continue known continuation
        ) else (
          insert (Set.add node known) continuation chain node
        )
      | ( chain, node :: rest) :: continuation ->
        if Set.mem node known then (
          continue known ( (chain, rest) :: continuation )
        ) else (
          insert (Set.add node known) (
            (chain, rest) :: continuation
          ) chain node
        )
      | (_, []) :: continuation -> continue known continuation
      | [] -> ()
    in

    match Set.elements below with

    (* Nothing below the node that was split. Linking everything above to
    greatest. Future splits will insert things in the right place. *)
    | [] ->
      map_up |> apply (Set.union above) greatest_rep ;
      above |> Set.iter (
        fun above -> map_down |> apply (Set.add greatest_rep) above
      )

    (* Need to insert the chain. *)
    | node :: rest ->
      insert Set.empty [ (chain), rest ] chain node

  (* Finds a node that's not been split, but with all its parents split. *)
  let next_of_continuation { map_down ; values } continuation =
    if Set.is_empty continuation then None else (
      try (
        let next, continuation =
          Set.partition (
            fun rep ->
              try
                Map.find map_down rep
                |> Set.for_all (
                  fun rep -> Map.mem values rep
                )
              with Not_found ->
                Format.asprintf
                  "could not find rep %a in map down" fmt_term rep
                |> failwith
          ) continuation
        in
        Some (next, continuation)
      ) with Not_found ->
        failwith "could not find legal next rep in continuation"
    )

  (* Splits a graph based on the current model.

  Returns the representatives created and modified. *)
  let split_of_model sys new_reps model ({ map_down ; map_up } as graph) =
    let rec loop new_reps continuation next =
      (* Format.printf "@.starting update %d / %d@.@." out_cnt in_cnt ; *)
      (* Format.printf "  nxt is %a@.@." fmt_term nxt ; *)
      let new_reps, continuation =
        Set.fold (
          fun rep (new_reps, continuation) ->
            (* Add nodes above current rep to [continuation].
            These nodes CANNOT be in [nxt] because they had an outdated parent:
            the current rep. *)
            let continuation =
              Map.find map_up rep |> Set.union continuation
            in
            (* Split and insert chain. *)
            let new_reps =
              let chain, new_reps = split sys new_reps graph model rep in
              insert graph rep chain ;
              new_reps
            in
            (* Moving on. *)
            new_reps, continuation
        ) next (new_reps, continuation)
      in
      (* write_dot_to
        "graphs/" "graph" (Format.sprintf "%d_%d" out_cnt in_cnt)
        fmt_graph_dot graph ; *)
      match next_of_continuation graph continuation with
      | None -> new_reps
      | Some (next, continuation) ->
        loop new_reps continuation next
    in

    (* Retrieve all nodes that have no parents. *)
    Map.fold (
      fun rep parents acc ->
        if Set.is_empty parents then Set.add rep acc else acc
    ) map_down Set.empty
    (* And start with that. *)
    |> loop new_reps Set.empty

  (** Stabilizes the equivalence classes.
  Stabilizes classes one by one to send relatively few candidates to lsd. *)
  let update_classes sys known lsd ({ classes } as graph) =

    let rec loop count reps_to_update =
      try (

        (* Checking if we should terminate before doing anything. *)
        Event.check_termination () ;

        (* Will raise `Not_found` if no more reps to update (terminal case). *)
        let rep = Set.choose reps_to_update in
        let reps_to_update = Set.remove rep reps_to_update in

        try (

          (* Retrieve class. *)
          let cl4ss = Map.find classes rep in
          (* Building equalities. *)
          let eqs, _ =
            Set.fold (
              fun rep (acc, last) ->
                (Term.mk_eq [last ; rep]) :: acc, rep
            ) cl4ss ([], rep)
          in
          match
            (* Is this set of equalities falsifiable?. *)
            Lsd.query_base lsd eqs
          with
          | None ->
            (* Stable, moving on. *)
            loop (count + 1) reps_to_update
          | Some model ->
            (* Format.printf "  sat@.@." ; *)
            (* Checking if we should terminate before doing anything. *)
            Event.check_termination () ;
            (* Clear (NOT RESET) the value map for update. *)
            clear graph ;
            (* Stabilize graph. *)
            let reps_to_update =
              split_of_model sys reps_to_update model graph
            in
            (* Loop after adding new representatives (includes old one). *)
            loop (count + 1) reps_to_update
        ) with Not_found ->
          Format.asprintf "could not find rep %a in class map" fmt_term rep
          |> failwith

      ) with Not_found ->
        Event.log_uncond
          "update classes done in %d iterations" count
    in

    (* Retrieve all representatives. *)
    Map.fold ( fun rep _ set -> Set.add rep set ) classes Set.empty
    |> loop 0

  (** Stabilizes the relations. *)
  let rec update_rels sys known lsd count ({ map_up ; classes } as graph) =
    (* Checking if we should terminate before doing anything. *)
    Event.check_termination () ;

    (* Building relations. *)
    let rels =
      Map.fold (
        fun rep reps acc ->
          Set.fold (
            fun rep' acc -> (Domain.mk_cmp rep rep') :: acc
          ) reps acc
      ) map_up []
    in

    match
      (* Are these relations falsifiable?. *)
      Lsd.query_base lsd rels
    with
    | None ->
      (* Format.printf "update_rels done after %d iterations@.@." count ; *)
      (* Stable, done. *)
      ()
    | Some model ->
      (* Format.printf "  sat@.@." ; *)
      (* Checking if we should terminate before doing anything. *)
      Event.check_termination () ;
      (* Clear (NOT RESET) the value map for update. *)
      clear graph ;
      (* Stabilize graph. *)
      let reps_to_update =
        split_of_model sys Set.empty model graph
      in
      (
        if Set.is_empty reps_to_update |> not then
          Event.log L_warn
            "[graph splitting] @[<v>\
              Some classes were split during relation stabilization.@ \
              This should not be possible.\
            "
      ) ;
      (* Loop after adding new representatives (includes old one). *)
      update_rels sys known lsd (count + 1) graph

  (** Queries the lsd and updates the graph. Iterates until the graph is
  stable. That is, when the lsd returns unsat. *)
  let rec update_loop
   sys known lsd ({ map_up ; map_down } as graph)
  = match terms_of graph known |> Lsd.query_base lsd with

  | None ->
    (* Format.printf "%s   unsat@.@." pref ; *)
    ()

  | Some model ->
    (* Format.printf "%s   sat@.@." pref ; *)
    (* Checking if we should terminate before doing anything. *)
    Event.check_termination () ;

    (* Event.log L_info "%s stabilization: check" pref ; *)

    (* Format.printf "@.sat, updating graph: %d@." out_cnt ; *)

    (* Clear (NOT RESET) the value map for update. *)
    clear graph ;
   
    (* Stabilize graph. *)
    split_of_model sys Set.empty model graph |> ignore ;

    (* Checking if we should terminate before looping. *)
    Event.check_termination () ;

    (* Check if new graph is stable. *)
    update_loop sys known lsd graph

  (** Queries the lsd and updates the graph. Iterates until the graph is
  stable. That is, when the lsd returns unsat. *)
  let update graph sys known lsd =
    (* update_loop sys known lsd graph *)
    update_classes sys known lsd graph ;
    (* Format.printf "done stabilizing classes@.@." ; *)
    update_rels sys known lsd 0 graph

end


(* |===| Actual graph modules. *)

(** Graph of booleans with implication. *)
module Bool = Make( InvGenDomain.Bool )

(** Graph of integers with less than or equal. *)
module Int = Make( InvGenDomain.Int )

(** Graph of reals with less than or equal. *)
module Real = Make( InvGenDomain.Real )



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)