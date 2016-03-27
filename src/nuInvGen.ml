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




(* |===| IO stuff *)


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




(* |===| Functor stuff *)


(** Signature of the modules describing an order relation over some values. *)
module type In = sig
  (** Short string description of the values, used in the logging prefix. *)
  val name : string
  (** Type of the values of the candidate terms. *)
  type t
  (** Value formatter. *)
  val fmt : Format.formatter -> t -> unit
  (** Equality over values. *)
  val eq : t -> t -> bool
  (** Ordering relation. *)
  val cmp : t -> t -> bool
  (** Creates the term corresponding to the ordering of two terms. *)
  val mk_cmp : Term.t -> Term.t -> Term.t
  (** Evaluates a term. *)
  val eval : TransSys.t -> Model.t -> Term.t -> t
  (** Mines a transition system for candidate terms. *)
  val mine : TransSys.t -> Term.TermSet.t
end

(** Signature of the module returned by the [Make] invariant generation functor
when given a module with signature [In]. *)
module type Out = sig
  (** Runs the invariant generator. *)
  val main : TransSys.t -> unit
  (** Clean exit for the invariant generator. *)
  val exit : unit -> unit
end


module Bool: In = struct
  (* Evaluates a term to a boolean. *)
  let eval_bool sys model term =
    Eval.eval_term (TransSys.uf_defs sys) model term
    |> Eval.bool_of_value

  let name = "Bool"
  type t = bool
  let fmt = Format.pp_print_bool
  let eq lhs rhs = lhs = rhs
  let cmp lhs rhs = rhs || not lhs
  let mk_cmp lhs rhs = Term.mk_implies [ lhs ; rhs ]
  let eval = eval_bool
  let mine sys =
    sys
    |> InvGenCandTermGen.generate_graphs false sys
    |> function
      | (_, head, _) :: _, _ ->
        ImplicationGraph.eq_classes head |> List.hd
      | [], _ -> failwith "blah"
end



(** Constructs an invariant generation module from a value module. *)
module Make (Value : In) : Out = struct

  (* Reference to LSD for clean exit. *)
  let lsd_ref = ref None

  (* Clean exit. *)
  let exit () =
    ( match !lsd_ref with
      | None -> ()
      | Some lsd -> Lsd.delete lsd ) ;
    exit 0

  (** Prefix used for logging. *)
  let pref = Format.sprintf "[%s Inv Gen]" Value.name

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
    values: Value.t map ;
  }

  (* Formats a graph to graphviz format. *)
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

    @[<v>" ;

    map_up |> Map.iter (
      fun key ->
        let key_len = 1 + (Set.cardinal (Map.find classes key)) in
        let key_value =
          try Map.find values key |> Format.asprintf "%a" Value.fmt
          with Not_found -> "_mada_"
        in
        Term.TermSet.iter (
          fun kid ->
            let kid_len = 1 + (Set.cardinal (Map.find classes kid)) in
            let kid_value =
              try Map.find values kid |> Format.asprintf "%a" Value.fmt
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
          try Map.find values key |> Format.asprintf "%a" Value.fmt
          with Not_found -> "_mada_"
        in
        Term.TermSet.iter (
          fun kid ->
            let kid_len = 1 + (Set.cardinal (Map.find classes kid)) in
            let kid_value =
              try Map.find values kid |> Format.asprintf "%a" Value.fmt
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

    @[<v>" ;

    classes |> Map.iter (
      fun rep set ->
        let rep_value =
          try Map.find values rep |> Format.asprintf "%a" Value.fmt
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


  (** Clears the [values] field of the graph ([clear] not [reset]). *)
  let clear { values } = Map.clear values

  (** Minimal list of terms encoding the current state of the graph. Contains
  - equality between representatives and their class, and
  - comparison terms between representatives.

  Used when querying the base instance of the LSD (graph stabilization).
  See also [all_terms_of], used for the step instance (induction check). *)
  let terms_of {map_up ; classes} known =
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
        above |> Set.elements |> List.fold_left (
          fun acc rep' -> cond_cons (Value.mk_cmp rep rep') acc
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
            (cond_cons (Value.mk_cmp rep rep') acc, true)
            |> Set.fold (
              fun rep_eq' (acc, fst) ->
                cond_cons (Value.mk_cmp rep rep_eq') acc
                |> Set.fold (
                  fun rep_eq acc ->
                    let acc =
                      if fst then (
                        cond_cons (Value.mk_cmp rep_eq rep') acc
                        |> cond_cons (Term.mk_eq [rep ; rep_eq])
                      ) else acc
                    in
                    cond_cons (Value.mk_cmp rep_eq rep_eq') acc
                ) (Map.find classes rep),
                false
            ) (Map.find classes rep')
            |> fst
        ) above acc
    ) map_up []

  (* Formats a chain. *)
  let fmt_chain fmt =
    Format.fprintf fmt "[%a]" (
      pp_print_list
      (fun fmt (rep, value) ->
        Format.fprintf fmt "<%a, %a>" fmt_term rep Value.fmt value)
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

  (** Transitive recursive closure of the kid relation. *)
  let kid_trc map_down =
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

  (** Adds an edge to the graph. *)
  let add_up { map_up ; map_down } rep kid =
    apply ~not_found:(Some Set.empty) (Set.add kid) rep map_up ;
    apply ~not_found:(Some Set.empty) (Set.add rep) kid map_down


  (** Splits the graph based on a model. *)
  let split sys { classes ; values ; map_up ; map_down } model rep =
    (* Format.printf "  splitting %a@." fmt_term rep ; *)
    let rep_val = Value.eval sys model rep in
    let rep_cl4ss = ref (Map.find classes rep) in

    let rec insert ?(is_rep=false) pref sorted term value =
      if is_rep || value <> rep_val then (
        let default = if is_rep then !rep_cl4ss else Set.empty in
        if not is_rep then rep_cl4ss := Set.remove term !rep_cl4ss ;
        match sorted with
        | [] -> (term, value, default) :: pref |> List.rev
        | (rep, value', set) :: tail when value = value' ->
          (rep, value', Set.add term set) :: tail |> List.rev_append pref
        | ( (_, value', _) :: _ as tail) when Value.cmp value' value ->
          (term, value, default) :: tail |> List.rev_append pref
        | head :: tail -> insert ~is_rep:is_rep (head :: pref) tail term value
      ) else sorted
    in

    let sorted =
      Set.fold (
        fun term sorted -> insert [] sorted term (Value.eval sys model term)
      ) !rep_cl4ss []
    in

    match sorted with
    | [] ->
      (* Format.printf "    all terms evaluate to %a@.@." Value.fmt rep_val ; *)
      (* Update values. *)
      Map.replace values rep rep_val ;
      (* All terms in the class yield the same value. *)
      [ (rep, rep_val) ]
    | _ ->
      (* Format.printf "    class was split@.@." ; *)
      (* Representative's class was split, updating. *)
      insert ~is_rep:true [] sorted rep rep_val
      |> List.map (
        fun (rep, value, set) ->
          (* Update class map. *)
          Map.replace classes rep set ;
          (* Update values. *)
          Map.replace values rep value ;
          (* Insert with empty kids and parents if not already there. *)
          apply ~not_found:(Some Set.empty) identity rep map_up ;
          apply ~not_found:(Some Set.empty) identity rep map_down ;

          (rep, value)
      )


  (** Inserts a chain in a graph. *)
  let insert ({ map_up ; map_down ; values } as graph) rep chain =
    (* Format.printf "  inserting chain for %a@." fmt_term rep ;
    Format.printf "    chain: %a@." fmt_chain chain ; *)
    (* Nodes above [rep]. *)
    let above = Map.find map_up rep in
    (* Nodes below [rep]. *)
    let below = Map.find map_down rep in
    (* Format.printf
      "    %d above, %d below@." (Set.cardinal above) (Set.cardinal below) ; *)
    (* Greatest value in the chain. *)
    let greatest_rep, greatest_val = List.hd chain in

    (* Break all links to and from [rep]. *)
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
    ) else (
      (* Format.printf "    keeping uplinks: (original) %a = %a (greatest)@."
        fmt_term rep fmt_term greatest_rep ; *)
    ) ;
    (* Format.printf "    breaking all links to %a@." fmt_term rep ; *)
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
    (* Create chain links. *)
    let rec loop last = function
      | (next, _) :: tail ->
        (* Format.printf "      creating %a -> %a@." fmt_term next fmt_term last ; *)
        add_up graph next last ;
        loop next tail
      | [] -> ()
    in
    ( match chain with | (head, _) :: tail -> loop head tail | [] -> () ) ;

    (* Returns the longest subchain above [value'], in DECREASING order.
    Assumes the chain is in INCREASING order. *)
    let rec longest_above pref value' = function
      | (rep, value) :: tail when Value.cmp value' value ->
        longest_above (rep :: pref) value' tail
      | rest -> pref, rest
    in

    (* Inserts a chain. *)
    let rec insert known continuation chain node =
      (* Format.printf "  inserting for %a@." fmt_term node ; *)

      let value = Map.find values node in
      (* Longest chain above current node. *)
      let chain_above, rest = longest_above [] value chain in
      (* Format.printf "    %d above, %d below@."
        (List.length chain_above) (List.length rest) ; *)
      (* Creating links. *)
      ( match chain_above with
        | [] ->
          (* Linking with [above] is [node] is in [below]. *)
          if Set.mem node below then (
            (* Format.printf "    linking node to above@." ; *)
            map_up |> apply (Set.union above) node ;
            above |> Set.iter (
              fun above -> map_down |> apply (Set.add node) above
            )
          )
        | chain_above :: _ ->
          apply (Set.add chain_above) node map_up ;
          apply (Set.add node) chain_above map_down ;
          (* Also linking with [above] is [node] is in [below]. *)
          if Set.mem node below then (
            (* Format.printf "    linking greatest to above@." ; *)
            map_up |> apply (Set.union above) greatest_rep ;
            above |> Set.iter (
              fun above -> map_down |> apply (Set.add greatest_rep) above
            )
          )
      ) ;
      match rest with
      | [] ->
        (* Chain successfully inserted, add everything below [none] to
        [known]. *)
        let known = kid_trc map_down known node in
        (* Continuing. *)
        continue known continuation
      | _ ->
        (* Not done inserting the chain. *)
        (rest, Map.find map_down node |> Set.elements) :: continuation
        |> continue known

    (* Continuation handling for chain insertion. *)
    and continue known = function
      | ( chain, [node]) :: continuation ->
        if Set.mem node known then (
          (* Format.printf "    skipping known rep %a@." fmt_term node ; *)
          continue known continuation
        ) else (
          insert (Set.add node known) continuation chain node
        )
      | ( chain, node :: rest) :: continuation ->
        if Set.mem node known then (
          (* Format.printf "    skipping known rep %a@." fmt_term node ; *)
          continue known continuation
        ) else (
          insert (Set.add node known) (
            (chain, rest) :: continuation
          ) chain node
        )
      | (_, []) :: continuation -> continue known continuation
      | [] -> ()
    in

    match Set.elements below with
    | [] ->
      (* Format.printf "    linking greatest to above@." ; *)
      map_up |> apply (Set.union above) greatest_rep ;
      above |> Set.iter (
        fun above -> map_down |> apply (Set.add greatest_rep) above
      )
    | node :: rest -> insert Set.empty [ (chain), rest ] chain node


  let next_of_continuation { map_down ; values } =
    let rec loop skipped = function
      | [] -> None
      | (nxt :: rest) :: tail ->
        (* Next rep of continuation is legal if all kids have been
        evaluated. *)
        let legal_nxt =
          try
            Map.find map_down nxt
            |> Set.for_all (
              fun rep -> Map.mem values rep
            )
          with Not_found ->
            Format.asprintf "could not find rep %a in map down" fmt_term nxt
            |> failwith
        in
        if legal_nxt then
          Some (nxt, (List.rev_append skipped rest) :: tail)
        else
          loop (nxt :: skipped) (rest :: tail)
      | [] :: tail -> loop skipped tail
    in
    loop []

  (** Queries the lsd and updates the graph. Iterates until a fixedpoint is
  reached. *)
  let rec update sys known lsd out_cnt ({ map_up } as graph) = match
    terms_of graph known |> Lsd.query_base lsd sys
  with
  | None ->
    (* Format.printf "unsat, done@.@." ; *)
    ()
  | Some model ->
    (* Format.printf "@.sat, updating graph: %d@." out_cnt ; *)

    (* Splits the graph based on the current model. *)
    let rec loop in_cnt continuation =
      (* Format.printf "@.starting update %d / %d@.@." out_cnt in_cnt ; *)
      match next_of_continuation graph continuation with
      | None -> ()
      | Some (nxt, continuation) -> (
        (* Format.printf "  nxt is %a@.@." fmt_term nxt ; *)
        (* Remember nodes above [nxt]. *)
        let above = Map.find map_up nxt |> Set.elements in
        (* Split and insert chain. *)
        split sys graph model nxt |> insert graph nxt ;
        (* Format.printf "@.  logging graph for %d / %d@." out_cnt in_cnt ; *)
        write_dot_to
          "graphs/" "graph" (Format.sprintf "%d_%d" out_cnt in_cnt)
          fmt_graph_dot graph ;
        (* Add nodes above [nxt] to continuation if any. *)
        match above with
        | [] -> ()
        | _ -> above :: continuation |> loop (in_cnt + 1)
      )
    in
    
    loop 0 [ [ Term.t_false ] ] ;

    clear graph ;

    update sys known lsd (out_cnt + 1) graph


  (** Goes through all the (sub)systems for the current [k]. Then loops
  after incrementing [k]. *)
  let rec system_iterator memory k = function
  | (sys, graph, non_trivial, trivial) :: graphs ->
    (* Format.printf "Running on %a for %a@.@."
      Scope.pp_print_scope (TransSys.scope_of_trans_sys sys)
      Numeral.pp_print_numeral k ; *)
    (* Creating LSD instance. *)
    let lsd = Lsd.create false true sys in
    (* Memorizing LSD instance for clean exit. *)
    lsd_ref := Some lsd ;
    (* Unrolling to [k]. *)
    Lsd.unroll_sys_to lsd sys k ;

    (* Format.printf "LSD instance is at %a@.@." Numeral.pp_print_numeral (Lsd.get_k lsd sys) ; *)

    (* Prunes known invariant from a list of candidates. *)
    let prune cand = Set.mem cand non_trivial || Set.mem cand trivial in

    (* Stabilize graph. *)
    ( try update sys prune lsd 0 graph with
      | e -> (
        Format.printf "caught exception %s@.@." (Printexc.to_string e) ;
        exit ()
      )
    ) ;
    write_dot_to
      "graphs/" "classes" (Format.asprintf "%a" Numeral.pp_print_numeral k)
      fmt_graph_classes_dot graph ;

    (* Check for invariants. *)
    let non_trivial', trivial' =
      all_terms_of graph prune |> Lsd.query_step lsd sys
    in
    let non_trivial, trivial =
      non_trivial' |> List.fold_left (
        fun set inv -> Set.add inv set
      ) non_trivial,
      trivial' |> List.fold_left (
        fun set inv -> Set.add inv set
      ) trivial
    in
    ( match non_trivial', trivial' with
      | [], [] -> ()
      | [], _ ->
        Event.log L_info
          "%s @[<v>system %a at %a (%d/%d)@ found %d trivial invariants@]"
          pref
          Scope.pp_print_scope (TransSys.scope_of_trans_sys sys)
          Numeral.pp_print_numeral k
          (Set.cardinal non_trivial)
          (Set.cardinal trivial)
          (List.length trivial')
      | _ ->
        let trivial_blah fmt = match trivial' with
          | [] -> ()
          | _ ->
            Format.fprintf fmt "@ and %d trivial invariants"
              (List.length trivial')
        in
        Event.log L_info
          "%s @[<v>system %a at %a (%d/%d)@ found %d invariants%t@]"
          pref
          Scope.pp_print_scope (TransSys.scope_of_trans_sys sys)
          Numeral.pp_print_numeral k
          (Set.cardinal non_trivial)
          (Set.cardinal trivial)
          (List.length non_trivial')
          trivial_blah
    ) ;

    (* Destroying LSD. *)
    Lsd.delete lsd ;
    (* Unmemorizing LSD instance. *)
    lsd_ref := None ;
    exit () ;
    (* Looping. *)
    system_iterator ( (sys, graph, non_trivial, trivial) :: memory ) k graphs
  | [] ->
    (* Done for all systems for this k, incrementing. *)
    let k = Numeral.succ k in
    Event.log L_info
      "%s Looking for invariants at %a." pref Numeral.pp_print_numeral k ;
    List.rev memory |> system_iterator [] k


  (** Invariant generation entry point. *)
  let main sys =

    (* Generating the candidate terms and building the graphs. Result is a list
       of triplets: system, graph, invariants. *)
    let candidate_terms = Value.mine sys |> Set.remove Term.t_false in

    let graph =
      {
        map_up = (
          let map = Map.create 107 in
          Map.replace map Term.t_false Set.empty ;
          map
        ) ;
        map_down = (
          let map = Map.create 107 in
          Map.replace map Term.t_false Set.empty ;
          map
        ) ;
        classes = (
          let map = Map.create 107 in
          Map.replace map Term.t_false candidate_terms ;
          map
        ) ;
        values = Map.create 107 ;
      }
    in

    system_iterator [] Numeral.zero [ sys, graph, Set.empty, Set.empty ]

end

(** Boolean invariant generation. *)
module BoolInvGen = Make(Bool)

let main _ _ = BoolInvGen.main
let exit _ = BoolInvGen.exit ()




(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)