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

(* Evaluates a term to a boolean. *)
let eval_bool sys model term =
  Eval.eval_term (TransSys.uf_defs sys) model term
  |> Eval.bool_of_value

(* Formats a term. *)
let fmt_term = Term.pp_print_term

(* Ordering relation. *)
let cmp lhs rhs = rhs || not lhs


let lsd_ref = ref None
let exit () =
  ( match !lsd_ref with
    | None -> ()
    | Some lsd -> Lsd.delete lsd ) ;
  exit 2


(* Contains the structures representing an graph, and the functions to
modify it. *)
module Graph = struct

  (* A term is a term. *)
  type term = Term.t

  (* A representative is just a term. *)
  type rep = term

  (* An equivalence class is a set of terms.

  An equivalence class DOES NOT contain its representative. *)
  module EqClass = Term.TermSet
  type eq_class = EqClass.t

  (* Maps representatives to their equivalence class.

  An equivalence class DOES NOT contain its representative. *)
  module Map = Term.TermMap
  type class_map = eq_class Map.t

  (* Class map formatter. *)
  let fmt_map fmt map =
    Map.bindings map
    |> Format.fprintf fmt "@[<v>%a@]" (
      pp_print_list (
        fun fmt (key, cl4ss) ->
        EqClass.elements cl4ss
        |> Format.fprintf fmt "%a -> [@[<hov 4>%a@]]" Term.pp_print_term key (
          pp_print_list Term.pp_print_term "@ "
        )
      ) "@ "
    )

  let find_class rep classes =
    try Map.find rep classes with Not_found ->
      Format.asprintf
        "could not find class for representative %a" fmt_term rep
      |> failwith


  (* Result of splitting of an equivalence class. *)
  type split_res' =
  (* Split happened, equivalence class evaluating to true is first. *)
  | Split of (rep * eq_class) * (rep * eq_class)
  (* No split happened, contains the value the class evaluates to. *)
  | NoSplit of bool

  (* Splits an equivalence class in two.

  In case of splitting, the input representative will be one of the two new
  representatives. *)
  let split sys model rep cl4ss =
    (* Evaluate representative. *)
    let rep_val = eval_bool sys model rep in

    (* Iterate over the class to create the result.

    In the fold, we start with a [NoSplit] result based on the value the
    representative evaluates to. If we see we must split, we associate the
    original, UNMODIFIED class to the rerpresentative. The elements that do
    not evaluate to the same value will be removed as we iterate ovec them. *)
    EqClass.elements cl4ss
    |> List.fold_left (
      fun res term ->
        let term_val = eval_bool sys model term in (* Evaluate term. *)
        match res with
        (* Already split. *)
        | Split (
          (lft_rep, lft_cl4ss), (rgt_rep, rgt_cl4ss)
        ) ->
          let lft_cl4ss, rgt_cl4ss = match (rep_val, term_val) with
            (* Representative is right, term is left. *)
            | true, false ->
              EqClass.add term lft_cl4ss, EqClass.remove term rgt_cl4ss
            (* Representative is left, term is right. *)
            | false, true ->
              EqClass.remove term lft_cl4ss, EqClass.add term rgt_cl4ss
            (* Representative and term evaluate to the same value, no
            modification. *)
            | _ -> lft_cl4ss, rgt_cl4ss
          in
          Split (
            (lft_rep, lft_cl4ss), (rgt_rep, rgt_cl4ss)
          )
        (* Not split, same value as representative. *)
        | NoSplit b when b = term_val -> res
        (* Not split, different value from representative. *)
        | _ ->
          if term_val then Split (
            (* Representative is left, term is right. *)
            (rep, EqClass.remove term cl4ss), (term, EqClass.empty)
          ) else Split (
            (* Representative is right, term is left. *)
            (term, EqClass.empty), (rep, EqClass.remove term cl4ss)
          )
    ) (NoSplit rep_val)


  (* A graph is a map from representatives to the representatives they
  imply. *)
  type graph = Term.TermSet.t Map.t

  (* Checks the graph is a lattice. *)
  let check_graph graph =
    let rec loop seen = function
      | [] -> ()
      | rep :: tail when Term.TermSet.mem rep seen -> loop seen tail
      | rep :: tail ->
        let kids = Map.find rep graph in
        if rep <> Term.t_true && Term.TermSet.is_empty kids then (
          Format.asprintf
            "representative %a has no kids@.@." fmt_term rep
          |> failwith
        ) ;
        (Term.TermSet.elements kids) @ tail
        |> loop (Term.TermSet.add rep seen)
    in
    try
      Map.find Term.t_false graph
      |> Term.TermSet.elements
      |> loop (Term.TermSet.empty |> Term.TermSet.add Term.t_true)
    with Not_found ->
      failwith "could not find false"

  (* Dot formatter for graphs. *)
  let fmt_graph_dot fmt (cache, classes, graph) =
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

    graph |> Map.iter (
      fun key ->
        let key_len = 1 + (EqClass.cardinal (Map.find key classes)) in
        let key_split =
          try Map.find key cache |> fst |> List.length
          with Not_found -> -1
        in
        let key_unatt =
          try Map.find key cache |> snd |> List.length
          with Not_found -> -1
        in
        Term.TermSet.iter (
          fun value ->
            let value_len = 1 + (EqClass.cardinal (Map.find value classes)) in
            let value_split =
              try Map.find value cache |> fst |> List.length
              with Not_found -> -1
            in
            let value_unatt =
              try Map.find value cache |> snd |> List.length
              with Not_found -> -1
            in
            Format.fprintf
              fmt "\"%a (%d, %d, %d)\" -> \"%a (%d, %d, %d)\" ;@ "
              fmt_term key key_len key_split key_unatt
              fmt_term value value_len value_split value_unatt
        )
    ) ;

    Format.fprintf fmt "@]@.}@."
      

  (* Adds a kid to a representative in a graph. *)
  let graph_add_kid rep kid graph =
    try
      Map.add
        rep (
          Map.find rep graph
          |> fun s -> Term.TermSet.add kid s
        ) graph
    with Not_found ->
      Map.add rep (Term.TermSet.empty |> Term.TermSet.add kid) graph

  (* Removes a kid to a representative in a graph. *)
  let graph_rm_kid ?(fail_if_not_found=true) rep kid graph =
    try
      Map.add
        rep (
          Map.find rep graph
          |> Term.TermSet.remove kid
        ) graph
    with Not_found ->
      if fail_if_not_found then
        Format.asprintf
          "removing kid to undefined representative %a" fmt_term rep
        |> failwith
      else graph


  (* Terms of a graph (lightweight version).

  Returns the terms for
  - equality of all members of the equivalence classes
  - implications between the representatives in the graph *)
  let terms_of classes graph =
    let eqs =
      Map.fold (
        fun rep cl4ss acc ->
          if EqClass.is_empty cl4ss |> not then
            (rep :: (EqClass.elements cl4ss) |> Term.mk_eq ) :: acc
          else acc
      ) classes []
    in
    Map.fold (
      fun lhs rhs acc ->
        (Term.mk_implies [
          lhs ; Term.mk_and (Term.TermSet.elements rhs)
        ]) :: acc
    ) graph eqs


  (* A cache maps representatives to the the [(value * rep) list] they
  split to, and the [(value * rep) list] representing their unattended
  kids. *)
  type cache = ((bool * rep) list * (bool * rep) list) Map.t

  (* Empty cache. *)
  let empty_cache = Map.empty

  (* Adds a result to a representative in a cache. *)
  let cache_add_res rep res cache =
    assert (Map.mem rep cache |> not) ;
    Map.add rep (res, []) cache

  let sorted_insert ((v', _) as elm) =
    let rec loop pref = function
      | ((v, _) :: _) as l when cmp v' v -> elm :: l |> List.rev_append pref
      | elm :: tail -> loop (elm :: pref) tail
      | [] -> [elm]
    in
    loop []

  (* Adds an unattended kid to a representative in a cache. *)
  let cache_add_unattended rep kids cache =
    try
      Map.add rep (
        let res, unatt = Map.find rep cache in
        res,
        kids |> List.fold_left (fun acc kid -> sorted_insert kid acc) unatt
      ) cache
    with Not_found ->
      Map.add rep (
        [], kids |> List.fold_left (fun acc kid -> sorted_insert kid acc) []
      ) cache
    (*   Format.asprintf
        "adding unattended kids to undefined representative %a" fmt_term rep
      |> failwith *)

  (* Result of a split. *)
  type split_res =
  | Known of (bool * rep) list * (bool * rep) list
  | New of (bool * rep) list * cache * class_map

  (* Splits the class corresponding to a representative based on a model.
  Updates the cache and the classes. *)
  let split sys model cache classes rep =
    try
      let res = Map.find rep cache in
      Known (fst res, snd res)
    with Not_found -> (
      let cl4ss = find_class rep classes in

      let res, classes = match split sys model rep cl4ss with

        | NoSplit b ->
          let res = [ (b, rep) ] in
          res,
          (* Classes are unchanged. *)
          classes

        | Split ( (lft_rep, lft_class), (rgt_rep, rgt_class) ) ->
          let res = [ (true, rgt_rep) ; (false, lft_rep) ] in
          res,
          (* Updating classes. *)
          classes |> Map.add lft_rep lft_class |> Map.add rgt_rep rgt_class
      in

      (* Updating cache. *)
      let cache = cache_add_res rep res cache in

      New ( res, cache, classes )
    )

  (* A path in the graph is a list of representatives and their value. *)
  type path = (bool * rep) list

  let fmt_path fmt =
    Format.fprintf fmt "[ %a ]" (
      pp_print_list
        (fun fmt (v,r) -> Format.fprintf fmt "(%b, %a)" v fmt_term r)
        ", "
    )

  let fmt_cont fmt =
    Format.fprintf fmt
      "@[<v>%a@]"
      (pp_print_list
        (fun fmt (path, ignore_split , kids) ->
          Format.fprintf fmt
            "%a (%b)@   -> [ %a ]"
            fmt_path path
            ignore_split
            (pp_print_list fmt_term ", ") kids
        )
        "@ "
      )

  (* Inserts a representative [rep] in a path based on its value.

  Assumes the input list of elements to insert is sorted by decreasing values.

  The insertion is conceptual, the path is actually unchanged.

  Takes the cache as input because it will update the unattended kids of the
  elements in the path that are above [rep].
  Also updates the graph itself. *)
  let path_insert continuation cache graph path elms =

    let rec insert acc path graph last rep' value' = function
      | ((value, rep) as elm) :: tail when cmp value' value ->
        let graph =
          path |> List.fold_left (
            fun graph (_, rep') ->
              graph_rm_kid ~fail_if_not_found:false rep' rep graph
          ) graph
        in
        insert (elm :: acc) path graph (Some rep) rep' value' tail
      | elms -> (
        match last with
        | None -> None
        | Some rep ->
          Format.printf
            "    inserting %a -> %a@.@." fmt_term rep' fmt_term rep ;
          (* Update graph. *)
          let graph = graph_add_kid rep' rep graph in
          (* Remove edges between representatives below [rep'] and [rep]. *)
          let graph =
            path |> List.fold_left (
              fun graph (_, rep') ->
                graph_rm_kid ~fail_if_not_found:false rep' rep graph
            ) graph
          in
          Some (rep, acc, graph, elms)
      )
    in

    let rec loop child_less last rev_cont cache graph elms = function
      | ( ((value', rep') as elm) :: tail as path) -> (
        Format.printf "    looping on path: %a@." fmt_term rep' ;
        (* Inserting longest chain. *)
        match insert [] tail graph None rep' value' elms with
        | None ->
          (* Inserted nothing, adding unattended kid. *)
          let cache = cache_add_unattended rep' elms cache in
          let child_less =
            if last = None then elm :: child_less else child_less
          in
          loop child_less None rev_cont cache graph elms tail
        | Some (nu_last, path_suf, graph, elms) -> (
          let rev_cont = match last with
            | None ->
              (* Format.printf "    | None -> adding cont to %a@." fmt_term nu_last ;
              Format.printf "      path_suf: %a@." fmt_path path_suf ;
              Format.printf "      path:     %a@." fmt_path path ;
              Format.printf "      nu_last:  %a@.@." fmt_term nu_last ;
              (* Adding to continuation. *)
              (path, [nu_last]) :: rev_cont *)
              rev_cont
            | Some last ->
              (* Format.printf "    | Some -> adding cont to %a@." fmt_term last ;
              Format.printf "      path_suf: %a@." fmt_path path_suf ;
              Format.printf "      path:     %a@." fmt_path path ;
              Format.printf "      nu_last:  %a@.@." fmt_term nu_last ; *)
              (* Adding to continuation. *)
              (List.rev path_suf, true, [last]) :: rev_cont
          in
          match elms with (* Are we done? *)
          | [] ->
            List.rev child_less,
            List.rev_append rev_cont continuation, cache, graph
          | _ ->
            (* Adding unattended kids. *)
            let cache = cache_add_unattended rep' elms cache in
            loop child_less (Some nu_last) rev_cont cache graph elms tail
        )
      )
      | [] ->
        List.rev child_less,
        List.rev_append rev_cont continuation,
        cache, graph
    in

    match elms with
    | [] -> [], continuation, cache, graph
    | _ -> loop [] None [] cache graph elms path


  let openfile path = Unix.openfile path [
    Unix.O_TRUNC ; Unix.O_WRONLY ; Unix.O_CREAT
  ] 0o640

  let fmt_of_file file =
    Unix.out_channel_of_descr file |> Format.formatter_of_out_channel

  (* Updates a graph. *)
  let rec update count sys lsd classes (graph: graph) = match
    Lsd.query_base lsd sys (terms_of classes graph)
  with
  | None ->
    Format.printf "unsat, done@.@." ;
    classes, graph
  | Some model ->

    let rec loop
      ignore_split in_count continuation path cache classes graph rep
    =

      Format.printf "working on %a@." fmt_term rep ;
      Format.printf "  continuation:@.  %a@." fmt_cont continuation ;
      Format.printf "  path: @.  %a@." fmt_path path ;
      Format.printf "@." ;

      (* Splitting. *)
      let continuation, graph, cache, classes, path, nxt =
        match split sys model cache classes rep with

        | Known (split, unattended) ->
          Format.printf "known@." ;
          Format.printf "  split:@.  @[<v>%a@]@." fmt_path split ;
          Format.printf "  unattended:@.  @[<v>%a@]@." fmt_path unattended ;
          Format.printf "@." ;
          assert (path <> []) ;
          (* Retrieving path top element. *)
          let (value', rep') = List.hd path in
(*           (* Creating edges with split result. *)
          let graph, unattended' =
            split |> List.fold_left (
              fun (graph, unatt) ((value, rep) as elm) ->
                if cmp value' value then
                  graph_add_kid rep' rep graph, unatt
                else graph, elm :: unatt
            ) (graph, [])
          in
          (* Creating edges with unattended kids. *)
          let graph, unattended =
            unattended |> List.fold_left (
              fun (graph, unatt) ((value, rep) as elm) ->
                if cmp value' value then
                  graph_add_kid rep' rep graph, unatt
                else graph, elm :: unatt
            ) (graph, unattended')
          in *)

          (* Insert node split. *)
          let continuation, cache, graph =
            if not ignore_split then (
              (* Removing edge with split node. *)
              (* let graph = graph_rm_kid rep' rep graph in *)
              Format.printf
                "  inserting split in path (%d)@." (List.length path) ;
              let child_less, continuation, cache, graph =
                path_insert continuation cache graph path split
              in
              let continuation =
                if child_less <> [] then (
                  let top_most = List.hd split |> snd in
                  (
                    child_less,
                    false,
                    Map.find top_most graph |> Term.TermSet.elements
                  ) :: continuation
                ) else continuation
              in
              continuation, cache, graph
            ) else continuation, cache, graph
          in

          Format.printf "  inserting unattended (%d) in path (%d)@."
            (List.length unattended) (List.length path) ;

          (* Insert unattended kids. *)
          let _, continuation, cache, graph =
            path_insert continuation cache graph path unattended
          in

          continuation, graph, cache, classes, path, None

        | New (split, cache, classes) -> (
          Format.printf "new (%d)@." (List.length split) ;
          Format.printf "  @[<v>%a@]@.@."
            (pp_print_list
              (fun fmt (value, rep) ->
                Format.fprintf fmt "%b / %a" value fmt_term rep
              ) "@ "
            ) split ;
          (* Kids of the node we just split. *)
          let kids =
            try Map.find rep graph |> Term.TermSet.elements
            with Not_found -> []
          in
          (* Remove kids. *)
          let graph = Map.remove rep graph in

          Format.printf "  creating edges@.@." ;

          (* Creating edges for the node we just split. *)
          let _, graph =
            split |> List.fold_left (
              function
              | (None, graph) -> fun (_, rep) ->
                Some rep, graph
              | (Some pre, graph) -> fun (_, rep) ->
                Format.printf "    %a -> %a@.@." fmt_term rep fmt_term pre ;
                Some rep, graph_add_kid rep pre graph
            ) (None, graph)
          in

          Format.printf "  inserting in path (%d)@.@." (List.length path) ;

          (* Insert new nodes in path. *)
          let child_less, continuation, cache, graph =
            path_insert continuation cache graph path split
          in

          let continuation =
            if child_less <> [] then (
              (
                child_less,
                ignore_split,
                kids
              ) :: continuation
            ) else continuation
          in

          let path = split @ path in

          let continuation, nxt = match kids with
            | [] -> continuation, None
            | [ kid ] -> continuation, Some kid
            | kid :: rest -> (path, false, rest) :: continuation, Some kid
          in

          continuation,
          graph,
          cache,
          classes,
          path,
          nxt
        )

      in

      Format.printf
        "logging (%d, %d_%d)@.@." (Map.cardinal graph) count in_count ;
      (* Log current graph. *)
      let fmt =
        Format.sprintf "graphs/graph_%d_%d.dot" count in_count
        |> openfile
        |> fmt_of_file
      in
      Format.fprintf fmt "%a" fmt_graph_dot (cache, classes, graph) ;

      match nxt with
      | Some nxt ->
        Format.printf "moving on (%d)@.@." (List.length path) ;
        loop false (in_count + 1) continuation path cache classes graph nxt
      | None -> (
        Format.printf "continuation:@.  %a@.@." fmt_cont continuation ;
        match continue continuation with
        | None ->
          Format.printf "nothing to continue on, exiting loop@.@." ;
          classes, graph
        | Some ((path, ignore_split, nxt), continuation) ->
          Format.printf "continuing@.@." ;
          (* if in_count >= 3 then exit () else *)
            loop
              ignore_split (in_count + 1)
              continuation path cache classes graph nxt
      )

    and continue = function
      | ( path, ignore_split, nxt :: tail ) :: continuation ->
        Some (
          (path, ignore_split, nxt),
          match tail with
          | [] -> continuation
          | _ -> (path, ignore_split, tail) :: continuation
        )
      | (_, _, []) :: continuation -> failwith "unreachable"
      | [] -> None
    in

    let classes, graph =
      loop false 0 [] [] empty_cache classes graph Term.t_false
    in

    (* Checks the graph is legal. *)
    check_graph graph ;

    if count >= 6 then exit () else (
      Format.printf "@.@.|=========================|@.@." ;
      update (count + 1) sys lsd classes graph
    )

end


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
    |> Term.TermSet.remove Term.t_false
  in

  let classes =
    Term.TermMap.empty
    |> Term.TermMap.add Term.t_false candidate_terms
  in
  let graph =
    Term.TermMap.empty
    |> Term.TermMap.add Term.t_false Term.TermSet.empty
  in

  (
    try
      let _ = Graph.update 0 sys lsd classes graph in
      ()
    with e ->
      Format.printf "exception:@.  %s@.@." (Printexc.to_string e)
  ) ;

  exit ()



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
