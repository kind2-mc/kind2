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

module Lsd = LockStepDriver
module CandTerm = InvGenCandTermGen

(* Prefix for invariant generation log. *)
let pref = "[TIG]"

(* Evaluates a term to a boolean. *)
let eval_bool sys model term =
  Eval.eval_term (TransSys.uf_defs sys) model term
  |> Eval.bool_of_value

(* Formats a term. *)
let fmt_term = Term.pp_print_term

(* Formats a chain. *)
let fmt_chain fmt =
  Format.fprintf fmt "[%a]" (
    pp_print_list
    (fun fmt (rep, value) -> Format.fprintf fmt "<%a, %b>" fmt_term rep value)
    ", "
  )


let lsd_ref = ref None
let exit () =
  ( match !lsd_ref with
    | None -> ()
    | Some lsd -> Lsd.delete lsd ) ;
  exit 0


module Bool = struct
  (* Type of the values of the candidate terms. *)
  type value = bool
  (* Ordering relation. *)
  let cmp lhs rhs = rhs || not lhs
  (* Creates the term corresponding to the ordering of two terms. *)
  let mk_cmp lhs rhs = Term.mk_implies [ lhs ; rhs ]
  (* Evaluates a term. *)
  let eval = eval_bool
end


module Map = Term.TermHashtbl
module Set = Term.TermSet

type term = Term.t
type rep = term

type 'a map = 'a Map.t
type set = Set.t

let apply ?(not_found=None) f elm map =
  try
    Map.find map elm |> f |> Map.replace map elm
  with Not_found -> (
    match not_found with
    | None ->
      Format.asprintf "could not find %a in map" fmt_term elm
      |> failwith
    | Some default -> f default |> Map.replace map elm
  )

type graph = {
  map_up: set map ;
  map_down: set map ;
  classes: set map ;
  values: Bool.value map ;
}

let clear { values } = Map.clear values

let terms_of {map_up ; classes} =
  let eqs =
    Map.fold (
      fun rep set acc ->
        if Set.is_empty set then acc else
          (rep :: Set.elements set |> Term.mk_eq) :: acc
    ) classes []
  in
  Map.fold (
    fun rep above acc ->
      above |> Set.elements |> List.fold_left (
        fun acc rep' -> (Bool.mk_cmp rep rep') :: acc
      ) acc
  ) map_up eqs

let all_terms_of {map_up ; classes} =
  let eqs =
    Map.fold (
      fun rep set acc ->
        if Set.is_empty set then acc else
          (rep :: Set.elements set |> Term.mk_eq) :: acc
    ) classes []
  in
  Map.fold (
    fun rep above acc ->
      above |> Set.elements |> List.fold_left (
        fun acc rep' ->
          (Bool.mk_cmp rep rep') :: acc |> Set.fold (
            fun rep_eq acc ->
              (Bool.mk_cmp rep_eq rep') :: acc |> Set.fold (
                fun rep_eq' acc ->
                  (Bool.mk_cmp rep rep_eq') ::
                  (Bool.mk_cmp rep_eq rep_eq') :: acc
              ) (Map.find classes rep')
          ) (Map.find classes rep)
      ) acc
  ) map_up eqs


let add_trc_down map_down =
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

let add_up rep kid { map_up ; map_down } =
  apply ~not_found:(Some Set.empty) (Set.add kid) rep map_up ;
  apply ~not_found:(Some Set.empty) (Set.add rep) kid map_down

(* Dot formatter for graphs. *)
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
        try Map.find values key |> Format.sprintf "%b"
        with Not_found -> "_mada_"
      in
      Term.TermSet.iter (
        fun kid ->
          let kid_len = 1 + (Set.cardinal (Map.find classes kid)) in
          let kid_value =
            try Map.find values kid |> Format.sprintf "%b"
            with Not_found -> "_mada_"
          in
          Format.fprintf
            fmt "\"%a (%d, %s)\" -> \"%a (%d, %s)\" ;@ "
            fmt_term key key_len key_value
            fmt_term kid kid_len kid_value
      )
  ) ;

  map_down |> Map.iter (
    fun key ->
      let key_len = 1 + (Set.cardinal (Map.find classes key)) in
      let key_value =
        try Map.find values key |> Format.sprintf "%b"
        with Not_found -> "_mada_"
      in
      Term.TermSet.iter (
        fun kid ->
          let kid_len = 1 + (Set.cardinal (Map.find classes kid)) in
          let kid_value =
            try Map.find values kid |> Format.sprintf "%b"
            with Not_found -> "_mada_"
          in
          Format.fprintf
            fmt "\"%a (%d, %s)\" -> \"%a (%d, %s)\" [\
              color=\"red\", constraint=false\
            ] ;@ "
            fmt_term key key_len key_value
            fmt_term kid kid_len kid_value
      )
  ) ;

  Format.fprintf fmt "@]@.}@."


let openfile path = Unix.openfile path [
  Unix.O_TRUNC ; Unix.O_WRONLY ; Unix.O_CREAT
] 0o640

let fmt_of_file file =
  Unix.out_channel_of_descr file |> Format.formatter_of_out_channel

let write_dot_to iter1 iter2 =
  (* Log current graph. *)
  let fmt =
    Format.sprintf "graphs/graph_%d_%d.dot" iter1 iter2
    |> openfile |> fmt_of_file
  in
  Format.fprintf fmt "%a@.@." fmt_graph_dot



let split sys { classes ; values ; map_up ; map_down } model rep =
  Format.printf "  splitting %a@." fmt_term rep ;
  let rep_val = Bool.eval sys model rep in
  let rep_cl4ss = ref (Map.find classes rep) in

  let rec insert ?(is_rep=false) pref sorted term value =
    if is_rep || value <> rep_val then (
      let default = if is_rep then !rep_cl4ss else Set.empty in
      if not is_rep then rep_cl4ss := Set.remove term !rep_cl4ss ;
      match sorted with
      | [] -> (term, value, default) :: pref |> List.rev
      | (rep, value', set) :: tail when value = value' ->
        (rep, value', Set.add term set) :: tail |> List.rev_append pref
      | ( (_, value', _) :: _ as tail) when Bool.cmp value' value ->
        (term, value, default) :: tail |> List.rev_append pref
      | head :: tail -> insert ~is_rep:is_rep (head :: pref) tail term value
    ) else sorted
  in

  let sorted =
    Set.fold (
      fun term sorted -> insert [] sorted term (Bool.eval sys model term)
    ) !rep_cl4ss []
  in

  match sorted with
  | [] ->
    Format.printf "    all terms evaluate to %b@.@." rep_val ;
    (* Update values. *)
    Map.replace values rep rep_val ;
    (* All terms in the class yield the same value. *)
    [ (rep, rep_val) ]
  | _ ->
    Format.printf "    class was split@.@." ;
    (* Representative's class was split, updating. *)
    insert ~is_rep:true [] sorted rep rep_val
    |> List.map (
      fun (rep, value, set) ->
        (* Update class map. *)
        Map.replace classes rep set ;
        (* Update values. *)
        Map.replace values rep value ;
        apply ~not_found:(Some Set.empty) identity rep map_up ;
        apply ~not_found:(Some Set.empty) identity rep map_down ;
        (rep, value)
    )


let insert { map_up ; map_down ; values } rep chain =
  Format.printf "  inserting chain for %a@." fmt_term rep ;
  Format.printf "    chain: %a@." fmt_chain chain ;
  (* Nodes above [rep]. *)
  let above = Map.find map_up rep in
  (* Nodes below [rep]. *)
  let below = Map.find map_down rep in
  Format.printf
    "    %d above, %d below@." (Set.cardinal above) (Set.cardinal below) ;
  (* Greatest value in the chain. *)
  let greatest_rep, greatest_val = List.hd chain in

  (* Break all links to and from [rep]. *)
  if Term.equal rep greatest_rep |> not then (
    Format.printf "    breaking all links from %a@." fmt_term rep ;
    map_up |> apply (
      fun set ->
        (* Break downlinks. *)
        set |> Set.iter (
          fun rep' ->
            Format.printf
              "      breaking %a -> %a@." fmt_term rep fmt_term rep' ;
            map_down |> apply (Set.remove rep) rep'
        ) ;
        (* Break uplinks. *)
        Set.empty
    ) rep ;
    Format.printf "    linking greatest to above@." ;
    above |> Set.iter (
      fun above ->
        map_up |> apply (Set.add above) greatest_rep ;
        map_down |> apply (Set.add greatest_rep) above
    )
  ) else (
    Format.printf "    keeping uplinks: (original) %a = %a (greatest)@."
      fmt_term rep fmt_term greatest_rep ;
  ) ;
  Format.printf "    breaking all links to %a@." fmt_term rep ;
  map_down |> apply (
    fun set ->
      (* Break uplinks. *)
      set |> Set.iter (
        fun rep' ->
          Format.printf
            "      breaking %a -> %a@." fmt_term rep' fmt_term rep ;
          map_up |> apply (Set.remove rep) rep'
      ) ;
      (* Break uplinks. *)
      Set.empty
  ) rep ;

  Format.printf "    creating chain links@." ;
  (* Create chain links. *)
  let rec loop last = function
    | (next, _) :: tail ->
      Format.printf "      creating %a -> %a@." fmt_term next fmt_term last ;
      apply ~not_found:(Some Set.empty) (Set.add next) last map_down ;
      apply ~not_found:(Some Set.empty) (Set.add last) next map_up ;
      loop next tail
    | [] -> ()
  in
  ( match chain with | (head, _) :: tail -> loop head tail | [] -> () ) ;

  (* Returns the longest subchain above [value'], in DECREASING order.
  Assumes the chain is in INCREASING order. *)
  let rec longest_above pref value' = function
    | (rep, value) :: tail when Bool.cmp value' value ->
      longest_above (rep :: pref) value' tail
    | rest -> pref, rest
  in

  let rec insert known continuation chain node =
    Format.printf "  inserting for %a@." fmt_term node ;

    let value = Map.find values node in
    (* Longest chain above current node. *)
    let chain_above, rest = longest_above [] value chain in
    Format.printf "    %d above, %d below@."
      (List.length chain_above) (List.length rest) ;
    (* Creating links. *)
    ( match chain_above with
      | [] ->
        (* Linking with [above] is [node] is in [below]. *)
        if Set.mem node below then (
          Format.printf "    linking node to above@." ;
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
          Format.printf "    linking greatest to above@." ;
          map_up |> apply (Set.union above) greatest_rep ;
          above |> Set.iter (
            fun above -> map_down |> apply (Set.add greatest_rep) above
          )
        )
    ) ;
    match rest with
    | [] ->
      (* Chain successfully inserted, add everything below to [known]. *)
      let known = add_trc_down map_down known node in
      (* Continuing. *)
      continue known continuation
    | _ ->
      (* Not done inserting the chain. *)
      (rest, Map.find map_down node |> Set.elements) :: continuation
      |> continue known
  and continue known = function
    | ( chain, [node]) :: continuation ->
      if Set.mem node known then (
        Format.printf "    skipping known rep %a@." fmt_term node ;
        continue known continuation
      ) else (
        insert (Set.add node known) continuation chain node
      )
    | ( chain, node :: rest) :: continuation ->
      if Set.mem node known then (
        Format.printf "    skipping known rep %a@." fmt_term node ;
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
    Format.printf "    linking greatest to above@." ;
    map_up |> apply (Set.union above) greatest_rep ;
    above |> Set.iter (
      fun above -> map_down |> apply (Set.add greatest_rep) above
    )
  | node :: rest -> insert Set.empty [ (chain), rest ] chain node


let next_of_continuation { map_down ; values } =
  let rec loop skipped = function
    | [] -> None
    | (nxt :: rest) :: tail ->
      (* Next rep of continuation is legal if all kids have been evaluated. *)
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

let rec update sys lsd out_cnt ({ map_up } as graph) = match
  terms_of graph |> Lsd.query_base lsd sys
with
| None ->
  Format.printf "unsat, done@.@."
| Some model ->
  Format.printf "@.sat, updating graph: %d@." out_cnt ;

  let rec loop in_cnt continuation =
    Format.printf "@.starting update %d / %d@.@." out_cnt in_cnt ;
    match next_of_continuation graph continuation with
    | None -> ()
    | Some (nxt, continuation) -> (
      Format.printf "  nxt is %a@.@." fmt_term nxt ;
      (* Remember nodes above [nxt]. *)
      let above = Map.find map_up nxt |> Set.elements in
      (* Split and insert chain. *)
      split sys graph model nxt |> insert graph nxt ;
      Format.printf "@.  logging graph for %d / %d@." out_cnt in_cnt ;
      write_dot_to out_cnt in_cnt graph ;
      (* Add nodes above [nxt] to continuation if any. *)
      match above with
      | [] -> ()
      | _ -> above :: continuation |> loop (in_cnt + 1)
    )
  in
  
  loop 0 [ [ Term.t_false ] ] ;

  clear graph ;

  update sys lsd (out_cnt + 1) graph


let rec system_iterator memory k = function
| (sys, graph) :: graphs ->
  Format.printf "Running on %a for %a@.@."
    Scope.pp_print_scope (TransSys.scope_of_trans_sys sys)
    Numeral.pp_print_numeral k ;
  (* Creating LSD instance. *)
  let lsd = Lsd.create true true sys in
  (* Memorizing LSD instance for clean exit. *)
  lsd_ref := Some lsd ;
  (* Unrolling to [k]. *)
  Lsd.unroll_sys_to lsd sys k ;

  Format.printf "LSD instance is at %a@.@." Numeral.pp_print_numeral (Lsd.get_k lsd sys) ;

  (* Stabilize graph. *)
  ( try update sys lsd 0 graph with
    | e -> (
      Format.printf "caught exception %s@.@." (Printexc.to_string e) ;
      exit ()
    )
  ) ;

  (* Check for invariants. *)
  ( match all_terms_of graph |> Lsd.query_step lsd sys with
    | [], [] -> ()
    | [], trivial ->
      Format.printf "found %d trivial invariants for %a at %a"
        (List.length trivial)
        Scope.pp_print_scope (TransSys.scope_of_trans_sys sys)
        Numeral.pp_print_numeral k
    | invs, trivial ->
      let trivial_blah fmt = match trivial with
        | [] -> ()
        | _ ->
          Format.fprintf fmt "@ and %d trivial invariants"
            (List.length trivial)
      in
      Event.log L_info
        "%s @[<v>found %d invariants%t@ for system %a at %a@]"
        pref
        (List.length invs)
        trivial_blah
        Scope.pp_print_scope (TransSys.scope_of_trans_sys sys)
        Numeral.pp_print_numeral k
  ) ;

  (* Destroying LSD. *)
  Lsd.delete lsd ;
  (* Unmemorizing LSD instance. *)
  lsd_ref := None ;
  (* Looping. *)
  system_iterator ( (sys, graph) :: memory ) k graphs
| [] ->
  (* Done for all systems for this k, incrementing. *)
  let k = Numeral.succ k in
  Event.log L_info
    "%s Moving on to %a." pref Numeral.pp_print_numeral k ;
  List.rev memory |> system_iterator [] k



let main _ _ sys =
  (* Creating lsd instance. *)
  let lsd =
    Lsd.create
      true
      (Flags.Invgen.top_only ())
      sys
  in
  lsd_ref := Some lsd ;

  (* Generating the candidate terms and building the graphs. Result is a list
     of triplets: system, graph, invariants. *)
  let candidate_terms =
    sys
    |> CandTerm.generate_graphs false sys
    |> function
      | (_, head, _) :: _, _ ->
        ImplicationGraph.eq_classes head |> List.hd
      | [], _ -> failwith "blah"
    |> Set.remove Term.t_false
  in

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

  system_iterator [] Numeral.zero [ sys, graph ]



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)