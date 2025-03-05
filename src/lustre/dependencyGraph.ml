module SVM = StateVar.StateVarMap
module SVS = StateVar.StateVarSet

module Vertex = struct
  type t = StateVar.t

  let compare = StateVar.compare_state_vars
  let pp_print_t = StateVar.pp_print_state_var
end

module VarGraph = Graph.Make (Vertex)

let args term = try Term.node_args_of_term term with _ -> [term]

(** [get_vars term] is a sequence containing the state vars of [term]*)
let get_vars (term : Term.t) =
  Term.vars_of_term term |> Var.VarSet.to_seq
  |> Seq.filter_map (fun var ->
         try Some (Var.state_var_of_state_var_instance var) with _ -> None)

(** [subgraph_of_term definition_set term] builds a dependency_graph for the
    individual term. If the term is a definition, for example `(= a b)`, then an
    edge is drawn from the lhs to every state variable of the rhs. For any other
    term an edge is drawn between every state variable in the term. *)
let subgraph_of_term (definition_set : Term.TermSet.t) (term : Term.t) =
  if Term.is_node term && Term.node_symbol_of_term term |> Symbol.is_uf then
    let vars = get_vars term in
    Seq.fold_left VarGraph.add_vertex VarGraph.empty vars
  else
    match Term.TermSet.mem term definition_set with
    | false ->
        let vars = get_vars term |> List.of_seq in
        let graph = List.fold_left VarGraph.add_vertex VarGraph.empty vars in
        List.fold_left VarGraph.connect graph vars
    | true -> (
        match args term with
        | [ dependant; dependencies ] ->
            let dependants = get_vars dependant |> List.of_seq in
            let dependencies = get_vars dependencies in
            let graph =
              Seq.fold_left VarGraph.add_vertex VarGraph.empty dependencies
            in
            let graph = List.fold_left VarGraph.add_vertex graph dependants in
            List.fold_left VarGraph.connect graph dependants
        | _ -> VarGraph.empty)

(** [dependency_graph definition_set term] builds a dependency_graph for the
    individual term. If the term is a definition, for example `(= a b)`, then an
    edge is drawn from the lhs to every state variable of the rhs. For any other
    term an edge is drawn between every state variable in the term. *)
let dependency_graph (definition_set : Term.TermSet.t) (term : Term.t) =
  args term |> List.to_seq
  |> Seq.map (subgraph_of_term definition_set)
  |> Seq.fold_left VarGraph.union VarGraph.empty

let graph_of_instances (definition_set : Term.TermSet.t)
    (trans_sys : TransSys.t) (instances : (TransSys.t * TransSys.instance) list)
    (subgraphs : VarGraph.t list) =
  (* 1. Merge all the subgraphs *)
  let result = List.fold_left VarGraph.union VarGraph.empty subgraphs in

  (* 2. Construct the graph of the given transition system *)
  let transition_term =
    TransSys.trans_of_bound None trans_sys TransSys.trans_base
  in
  let initial_term = TransSys.init_of_bound None trans_sys TransSys.init_base in

  let result = TransSys.get_properties trans_sys
        |> List.to_seq
        |> Seq.map Property.get_prop_term
        |> Seq.map (dependency_graph definition_set)
        |> Seq.fold_left VarGraph.union result
  in

  let result =
    initial_term |> dependency_graph definition_set |> VarGraph.union result
  in
  let result =
    transition_term |> dependency_graph definition_set |> VarGraph.union result
  in

  (* 3. Connect edges along node calls *)
  List.to_seq instances
  |> Seq.map (fun (_, instance) -> instance)
  |> Seq.flat_map (fun { TransSys.map_up } -> SVM.to_seq map_up)
  |> Seq.fold_left
       (fun graph (sv1, sv2) ->
         let open VarGraph in
         let graph = add_vertex graph sv1 in
         let graph = add_vertex graph sv2 in
         let graph = add_edge graph (mk_edge sv1 sv2) in
         add_edge graph (mk_edge sv2 sv1))
       result

(*
  When slicing we draw an arrow `a -> b` if `b` is used in the definition of
  `a`. Constraints need a biderectional arrow. That is `guarantee x > y` should
  add both arrows `x -> y` and `y -> x`. However constraints need to be viral.
  For example in the following case:
    ```
     b = x > y;
     guarantee b;
    ```
  we need to add all the edges `b <-> x`, `b <-> y`, and `x <-> y`. To do this
  we remove `b = x > y` from
  the definition set. We prune the definition set as follows:

   1. mark variables which are present in guarantees
   2. for each marked variable:
     1. remove their definitions from the definition set
     2. mark all variables on the rhs of their defintion
   3. repeat until there are no more variables to mark
*)
let prune_definitions trans_sys definition_set =

  (* look up table mapping variables -> defintions *)
  let definition_map =
    Term.TermSet.to_seq definition_set
    |> Seq.filter_map (fun term ->
           let args = Term.node_args_of_term term in
           match args with
           | lhs :: _ -> Some (Term.state_vars_of_term lhs |> SVS.choose, term)
           | [] -> None)
    |> Seq.fold_left
         (fun map (var, term) ->
           let set =
             SVM.find_opt var map
             |> Option.value ~default:Term.TermSet.empty
             |> Term.TermSet.add term
           in
           SVM.add var set map)
         SVM.empty
  in

  let rec remove_definitions (definition_map : Term.TermSet.t SVM.t)
      (state_vars : StateVar.t List.t) =
    match state_vars with
    | [] -> definition_map
    | state_var :: state_vars ->
        let new_vars =
          SVM.find_opt state_var definition_map
          |> Option.to_seq
          |> Seq.flat_map Term.TermSet.to_seq
          |> Seq.map Term.state_vars_of_term
          |> Seq.flat_map SVS.to_seq
          |> Seq.filter (fun sv -> SVM.mem sv definition_map)
          |> List.of_seq
        in
        let definition_map = SVM.remove state_var definition_map in
        remove_definitions definition_map (state_vars @ new_vars)
  in

  (* a constraint is any non-definition *)
  let get_constraints trans_sys =
    let init_term = TransSys.init_of_bound None trans_sys TransSys.init_base in
    let trans_term = TransSys.trans_of_bound None trans_sys TransSys.trans_base in
    [init_term ; trans_term]
    |> List.to_seq
    |> Seq.flat_map (fun t -> try Term.node_args_of_term t |> List.to_seq with _ -> Seq.return t)
    |> Seq.filter (fun t -> Term.TermSet.mem t definition_set |> not)
    |> Seq.map Term.state_vars_of_term
    |> Seq.flat_map SVS.to_seq
  in

  let constraints =
    TransSys.fold_subsystems
      (fun constraints trans_sys ->
        constraints @ (get_constraints trans_sys |> List.of_seq))
      [] trans_sys
  in

  remove_definitions definition_map constraints
  |> SVM.to_seq
  |> Seq.flat_map (fun (_, term) -> Term.TermSet.to_seq term)
  |> Term.TermSet.of_seq

let dependency_graph_of_system definition_set trans_sys =
  let definition_set = prune_definitions trans_sys definition_set in
  TransSys.fold_subsystem_instances
    (graph_of_instances definition_set)
    trans_sys

let cone_of_influence dependency_graph roots =
  let memo = ref VarGraph.VMap.empty in

  let reachable var =
    VarGraph.memoized_reachable memo dependency_graph var
    |> VarGraph.to_vertex_list |> SVS.of_list
  in
  SVS.to_seq roots |> Seq.map reachable |> Seq.fold_left SVS.union SVS.empty

let pp_print_dot ?(cone_of_influence = SVS.empty) ppf graph =
  let background = "whitesmoke" in
  let foreground = "black" in
  let highlight = "plum" in

  (* Formatting rules for the graph *)
  Format.fprintf ppf "@[<v 2>digraph G {";
  Format.fprintf ppf "@;bgcolor=\"%s\";" background;
  Format.fprintf ppf "@;fontcolor=\"%s\";" foreground;
  Format.fprintf ppf "@;node[fontcolor=\"%s\", color=\"%s\"];" foreground
    foreground;
  Format.fprintf ppf "@;edge[fontcolor=\"%s\", color=\"%s\"];" foreground
    foreground;
  Format.fprintf ppf "@;overlap=scale;";
  Format.fprintf ppf "@;concentrate=true;";

  (* All the Vertices *)
  VarGraph.get_vertices graph
  |> VarGraph.to_vertex_list
  |> List.iter (fun vertex ->
         if SVS.mem vertex cone_of_influence then
           Format.fprintf ppf "@;\"%s\" [color=\"%s\" style=filled];"
             (StateVar.string_of_state_var vertex)
             highlight
         else
           Format.fprintf ppf "@;\"%s\";" (StateVar.string_of_state_var vertex));

  (* All the edges *)
  VarGraph.get_edges graph |> VarGraph.to_edge_list |> List.to_seq
  |> Seq.filter (fun (sv1, sv2) -> sv1 != sv2)
  |> Seq.iter (fun (sv1, sv2) ->
         Format.fprintf ppf "@;\"%s\" -> \"%s\";"
           (StateVar.string_of_state_var sv1)
           (StateVar.string_of_state_var sv2));

  Format.fprintf ppf "@]@.}@;"
