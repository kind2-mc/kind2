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

(* Abbreviations *)
module D = LustreIndex
module E = LustreExpr
module Contract = LustreContract
module N = LustreNode
module NI = NodeId
module GI = GeneratedIdentifiers

module A = Analysis
module S = SubSystem

module SVS = StateVar.StateVarSet 
module SVM = StateVar.StateVarMap 


(********************)
(* Helper functions *)
(********************)

(* Returns [true] if the variable is an array index variable *)
let is_index_var v =
  Var.is_free_var v &&
  let s = Var.hstring_of_free_var v |> HString.string_of_hstring in
  try
    Scanf.sscanf s ("__index_%s")
      (fun _ -> true)
  with Scanf.Scan_failure _ -> false


(* Returns the offset of an index in an array access, e.g. k-1 in A[k-1] has
   offset -1. *)
let offset_of_index expr =
  let t = E.unsafe_term_of_expr expr in
  let tv =
    match Term.vars_of_term t
          |> Var.VarSet.elements
          |> List.filter is_index_var with
    | [v] -> Term.mk_var v
    | _ ->
      Var.mk_fresh_var Type.t_int |> Term.mk_var
  in
  let offset = Term.mk_minus [t; tv] in
  (* The simplification is disabled until it supports bitvector variables *)
  (* Simplify.simplify_term [] offset *)
  offset


(* Checks if the state variable appears in some accumulator [accum] or if there
   exists a cycle, then checks that this same variable is also on the cycle. *)
let break_cycle accum parents state_var sv _ =
  List.exists (fun (sv', _) -> StateVar.equal_state_vars sv sv') accum
  ||
  List.exists (fun path ->
      List.exists (fun (sv', _) -> StateVar.equal_state_vars state_var sv') path
      && List.exists (fun (sv', _) -> StateVar.equal_state_vars sv sv') path
    ) parents


(* Add reverse dependency to the parents of a given state variable. We don't
   bother negating the offsets so we can do the same test for children and
   parents (< 0). *)
let add_dep_to_parents sv indgrps parents =
  if indgrps = [] then
    if parents = [] then [[sv, None]]
    else List.map (fun path -> (sv, None) :: path) parents
  else
    let offsets_inds = List.map (fun inds ->
        List.map offset_of_index inds
        |> Term.mk_plus
        (* The simplification is disabled until it supports bitvector variables *)
        (* |> Simplify.simplify_term [] *)
      ) indgrps in
    List.fold_left (fun acc i ->
        let np =
          if parents = [] then [[sv, Some i]]
          else
            List.map (fun path -> (sv, Some i) :: path) parents in
        List.rev_append np acc
      ) [] offsets_inds


(* Strategy for merging dependencies on indexes of array accesses (we keep them
   all). *)
let merge_deps _ oind1 oind2 = match oind1, oind2 with
  | Some i1, Some i2 -> Some (i1 @ i2)
  | Some i, None | None, Some i -> Some i
  | _ -> None

(* Union of a map of dependecies/index with a set of dependencies *)
let union_noind_set m s =
  let m' = SVS.fold (fun sv -> SVM.add sv []) s SVM.empty in
  SVM.merge merge_deps m' m

let rec state_vars_of_bounds acc = function
  | [] -> acc
  | E.Unbound None :: l -> state_vars_of_bounds acc l
  | (E.Bound e | E.Fixed e | E.Unbound (Some e)) :: l ->
    let acc =
      Term.state_vars_of_term (E.unsafe_term_of_expr e) |> SVS.union acc in
    state_vars_of_bounds acc l

let state_vars_of_bounds = state_vars_of_bounds SVS.empty


(* ********************************************************************** *)
(* Dependency order of definitions and cycle detection                    *)
(* ********************************************************************** *)

(* For each state variable return the list of state variables in the current
   instant that are used in its definition, and transitively in their
   definitions, and fail if the definitions contain a cycle. The returned list
   also contains offsets for arrays accesses on which the variable definition
   depends. This allows to find cycles for non weel-founded (mutually)
   recurively defined arrays while allowing correct definitions.

   We don't need to consider assertions and node calls here, since we only need
   the ordering only to sort equations and detect cycles.

   We could find potential cycles when a node does not have an implementation,
   but this is more trouble than it's worth. We need to distinguish between
   strong and weak dependencies. If variable is undefined, it weakly depends on
   all inputs. Then we can find weak dependencies through nodes where an input
   is underspecified. However, we then need to eliminate that cycle by
   backtracking over the children we explored and that's where the troubles
   start. *)
let rec node_state_var_dependencies' init output_input_deps
    ({ N.equations; N.calls } as node)
    accum = function

  (* Return all calculated dependencies *)
  | [] -> accum

  (* Calculate dependency of variable [state_var], which all
     variables in [parents] depend on *)
  | (state_var, parents) :: tl ->

    (* All state variables at the current instant in the equation
        defining the state variable *)
    let children = 

      (* Find equations defining the state variable 

          A state variable can be defined in more than one equation
          if an array is defined pointwise *)
      List.find_all
        (fun ((sv, _), _) -> StateVar.equal_state_vars sv state_var)
        equations

      |> 
      List.fold_left

        (* State variable depends on state variables in equation *)
        (fun accum (((_, bnds), expr)) ->
            (* Format.eprintf "Equation: %a@." *)
            (*   (N.pp_print_node_equation false) eq; *)

            let state_vars = 
              if init then E.base_state_vars_of_init_expr expr
              else E.cur_state_vars_of_step_expr expr in
            
            (* (\* add bounds *\) *)
            let state_vars =
              state_vars_of_bounds bnds |> SVS.union state_vars in
            
            (* add indexes. They come from the selects of the
               expression, and finding those of a state variable takes
               a traversal of the expression: an expression with no
               select, the most common by far, gives every state
               variable no indexes, without a traversal for each of
               them. Each state variable is added to the map on its
               own, as merging a map of one would rebuild the whole
               map. *)
            let has_select =
              Term.has_select
                (if init then expr.E.expr_init else expr.E.expr_step :> Term.t)
            in
            SVS.fold (fun sv acc ->
                let indexes =
                  if not has_select then []
                  else if init then E.indexes_of_state_vars_in_init sv expr
                  else E.indexes_of_state_vars_in_step sv expr in
                SVM.update sv (function
                    | None -> Some indexes
                    | Some i -> Some (indexes @ i))
                  acc
              ) state_vars accum

        ) SVM.empty

    in

    (* All state variables at the current instant in the node call
        defining the state variable *)
    let children = 

        (* Find node calls defining the state variable *)
        List.find_all
          (fun { N.call_outputs } -> 
              D.exists 
                (fun _ sv -> StateVar.equal_state_vars state_var sv)
                call_outputs)
          calls
          
        |>
        
        List.fold_left
          
          (fun
            accum
            { N.call_node_id; 
              N.call_inputs;
              N.call_outputs; 
              N.call_defaults;
              N.call_cond } -> 
          (* Index of state variable in outputs *)
          let output_index = 
            try
              (* Find state variable in outputs and return its index *)
              D.bindings call_outputs 
              |> List.find
                (fun (_, sv) -> StateVar.equal_state_vars state_var sv)
              |> fst
            (* State variable is an output, has been found before *)
            with Not_found -> assert false 
          in

          (* Get computed dependencies of outputs on inputs for called
              node *)
          let output_input_dep =
            try List.assoc call_node_id output_input_deps
                |> if init then fst else snd
            with Not_found -> D.empty
          in

          (* Get indexes of inputs the output depends on.

             The dependencies of the callee have been computed before those of
             this node, except when the callee is the node itself, or another
             function of the same recursive group: a dependency is then still
             being computed, and there is nothing to read. Fall back on the
             assumption that the output depends on every input, which is the
             worst a fixed point could converge to, and is safe for the two
             things these dependencies are used for: keeping a variable in the
             cone of influence of another, and ordering equations by what they
             read. *)
          (try D.find output_index output_input_dep
            with Not_found -> D.keys call_inputs)

          |> List.fold_left (fun accum i -> 
              (* Get actual input by index, and add as dependency *)
              try SVM.add (D.find i call_inputs) [] accum 
              (* Invalid map *)
              with Not_found -> assert false)
            SVM.empty

          (* Defaults of a condact are children *)
          |> (fun children ->

              (* Only if computing dependencies in the initial state *)
              if init then
                (* Add state variables at the initial state from the default
                    expressions *)
                match call_defaults with 
                | None -> children
                | Some d -> 
                  D.fold (fun _ default accum -> 
                      E.base_state_vars_of_init_expr default
                      |> union_noind_set accum
                    ) d children

              (* Default expressions are only evaluated at the initial
                  state *)
              else children)

            (* Clock of condact or restart is a child *)
            |> fun children ->
                List.fold_left (fun children -> function
                (* | N.CNone -> children *)
                | N.CActivate clk
                | N.CRestart clk -> SVM.add clk [] children
              ) children call_cond
              

          (* Add to set of children from equations *)
          |> SVM.merge merge_deps accum)

        children
    in

    (* Some variables have had their dependencies calculated
        already *)
    let children_visited, children_not_visited =
      SVM.partition (break_cycle accum parents state_var) children
    in

    (* All children visited? *)
    if SVM.is_empty children_not_visited then 

      (* Dependencies of this variable is set of dependencies of its
          variables *)
      let children =
        SVM.fold (fun sv ind a -> 
            try 
              (* Add child as strong dependency to accumulator *)
              SVM.merge merge_deps a (SVM.singleton sv ind)

              (* Add grandchildren as strong or weak dependencies *)
              |> SVM.merge merge_deps
                (try List.find 
                        (fun (sv', _) -> StateVar.equal_state_vars sv sv')
                        accum |> snd
                  with Not_found -> SVM.empty)

            with Not_found -> assert false
          ) children_visited SVM.empty
      in

      (* Add variable and its dependencies to accumulator *)
      node_state_var_dependencies' 
        init
        output_input_deps
        node 
        ((state_var, children) :: accum)
        tl

    else

      (* First get dependencies of all dependent variables *)
      node_state_var_dependencies' 
        init
        output_input_deps
        node
        accum
        (SVM.fold (fun sv ind a ->
              (sv, add_dep_to_parents state_var ind parents) :: a
            ) children_not_visited ((state_var, parents) :: tl))


(* Given an association list of state variables to the set of the
   state variables they depend on, return the state variables in
   toplogical order 

   There must be no cyclic dependencies, otherwise this function will
   loop forever. *)
let rec order_state_vars accum seen = function

  (* All variables in the accumulator *)
  | [] -> accum

  (* Skip if state variable is already in the accumulator *)
  | (h, _) :: tl when List.exists (StateVar.equal_state_vars h) accum ->
    order_state_vars accum seen tl

  (* State variable and the variables it depends on *)
  | (h, d) :: tl -> 
    

    (* All dependencies of state variables, except themselves, in the
       accumulator? *)
    if
      SVM.for_all
        (fun sv _ -> List.exists (StateVar.equal_state_vars sv) accum) d
      || List.exists (StateVar.equal_state_vars h) seen

    then

      (* Add state variable to accumulator and continue *)
      order_state_vars (h :: accum) [] tl
      
    else

      (* Push all dependent variables to the top of the stack *)
      let tl' = 
        SVM.fold
          (fun sv _ a ->
             try 
               (* Find dependencies of state variable *)
               (List.find 
                  (fun (sv', _) -> StateVar.equal_state_vars sv sv')
                  tl) :: a
             (* All dependent state variables must be in stack *)
             with Not_found -> assert false)
          d
          ((h, d) :: tl)
      in

      (* Must add dependent state variables to accumulator first *)
      order_state_vars accum (h :: seen) tl'
      
      
(* Compute dependencies of outputs on inputs 

   Return a trie that maps each index of a state variable in the
   outputs to the list of indexes of input state variables the output
   depends on. *)
let output_input_dep_of_dependencies dependencies inputs outputs = 

  (* Map trie of output state variables to trie of indexes *)
  D.mapi

    (fun _ output -> 

       (* State variables this state variables depends on *)
       let output_dep = 

         try

           (* Get state variables the state variable depends on *)
           List.find 
             (fun (sv', _) -> StateVar.equal_state_vars output sv')
             dependencies

           |> snd 

         (* All dependencies must have been computed *)
         with Not_found -> assert false

       in

       (* Get indexes of all state variables that are inputs *)
       SVM.fold
         (fun sv _ a -> 

            match 

              (* Find state variable in inputs *)
              D.filter
                (fun _ sv' -> StateVar.equal_state_vars sv sv')
                inputs 
              |> D.keys

            with 

              (* State variable is not an input *)
              | [] -> a

              (* Add index of state variable in input to
                 accumulator *)
              | [i] -> i :: a

              (* State variable occurs in input twice *)
              | _ -> assert false)

         output_dep
         [])

    outputs


let state_var_dependencies'
    init
    output_input_deps
    ({ N.outputs; N.equations ; N.calls } as node)
    roots =

  (* Compute dependencies for state variables on the left-hand side of
     definitions, that is, in equations and node calls *)
  let state_vars =
    (* State variables on the left-hand side of equations *)
    List.map (fun ((sv, _), _) -> (sv, [])) equations
    |> D.fold (fun _ sv a -> (sv, []) :: a) outputs
    (* Add state variables capturing outputs of node calls *)
    |> (fun accum -> 
        List.fold_left (fun a { N.call_outputs } -> 
            D.fold (fun _ sv a -> (sv, []) :: a) call_outputs a
          ) accum calls)
  in

  (* Compute dependencies of state variable *)
  node_state_var_dependencies' init output_input_deps node roots state_vars


let state_var_dependencies
  init
  output_input_deps
  ({ N.inputs; N.outputs } as node) =

  let dependencies =
    state_var_dependencies' init output_input_deps node []
  in

  let deps =
    List.map
     (fun (sv, deps) ->
       (sv, SVM.fold (fun sv' _ acc -> SVS.add sv' acc) deps SVS.empty)
     )
     dependencies
  in

  (* Dependency of output variables on input variables *)
  let output_input_dep =
    output_input_dep_of_dependencies dependencies inputs outputs
  in

  deps, output_input_dep


(* Order equations of node topologically by their dependencies to have leaf
   equations first, and set the map of outputs to the inputs they depend on *)
let order_equations
    init
    output_input_deps
    ({ N.inputs; N.outputs; N.equations } as node) =

  let dependencies =
    state_var_dependencies' init output_input_deps node []
  in

  let deps =
    List.map
     (fun (sv, deps) ->
       (sv, SVM.fold (fun sv' _ acc -> SVS.add sv' acc) deps SVS.empty)
     )
     dependencies
  in

  (* Order state variables by dependencies *)
  let state_vars_ordered = order_state_vars [] [] dependencies in

  (* Order equations by state variables *)
  let equations' = List.fold_left (fun a sv ->
      (* Find equations of state variable and add to accumulator.
         There may be more than one equation per state variable if the state
         variable is an array. *)
        List.fold_left (fun a (((sv', _), _) as e) -> 
            if StateVar.equal_state_vars sv sv' then e :: a else a
          ) a equations
      ) [] state_vars_ordered 
  in

  (* Dependency of output variables on input variables *)
  let output_input_dep = 
    output_input_dep_of_dependencies dependencies inputs outputs
  in

  equations', deps, output_input_dep

          
(* ********************************************************************** *)
(* Cone of influence slicing                                              *)
(* ********************************************************************** *)


(* Return state variables from properties *)
let roots_of_props props =
  List.map (fun (sv, _, _, _, _) -> sv) props
  |> SVS.of_list

let rec contract_proof_obligation = function
  | Property.Generated (_, _, Property.Contract) -> true
  | Property.Candidate { source = Some s ; _ } -> contract_proof_obligation s
  | Property.Generated (_, _, Property.Body) 
  | Property.PropAnnot _ 
  | Property.Candidate { source = None ; _ }
  | Property.NonVacuityCheck _
  | Property.TerminationCheck _
  | Property.Assumption _
  | Property.Guarantee _
  | Property.GuaranteeOneModeActive _
  | Property.GuaranteeModeImplication _
  | Property.Instantiated _ ->
    false

let  filter_props_contract props =
  List.filter (fun (_, _, src, _, _) -> contract_proof_obligation src) props

let roots_of_props_contract props =
  filter_props_contract props |> roots_of_props


(* Initially empty node for slicing *)
let slice_all_of_node 
    ?(keep_props = true)
    ?(keep_contracts = true)
    ?(keep_asserts = true)
    ?(for_contract = false)
    { N.node_id;
      N.is_extern;
      N.opacity;
      N.instance;
      N.init_flag;
      N.inputs; 
      N.oracles; 
      N.outputs; 
      N.asserts;
      N.adt_constraints;
      N.props; 
      N.contract;
      N.is_main;
      N.comp_type;
      N.state_var_source_map;
      N.oracle_state_var_map;
      N.state_var_expr_map;
      N.assumption_svars;
      N.history_svars
    } = 

  (* Copy of the node with the same signature, but without local
     variables, equations, assertions and node calls. Keep signature,
     properties, assertions, contracts and main annotation *)
  { N.node_id;
    N.is_extern;
    N.opacity;
    N.instance;
    N.init_flag;
    N.inputs;
    N.oracles; 
    N.outputs; 
    N.locals = [];
    N.equations = [];
    N.calls = [];
    N.asserts = if keep_asserts then asserts else [] ;
    N.adt_constraints;
    N.props =
      if not keep_props then []
      else if for_contract then
        filter_props_contract props
      else props;
    N.contract = if keep_contracts then contract else None;
    N.is_main;
    N.comp_type;
    N.state_var_source_map = state_var_source_map;
    N.oracle_state_var_map = oracle_state_var_map;
    N.state_var_expr_map = state_var_expr_map;
    N.assumption_svars = assumption_svars;
    N.history_svars = history_svars
  }


(* Add roots of cone of influence from node call to roots *)
let add_roots_of_node_call
    roots
    { N.call_cond;
      N.call_context;
      N.call_inputs;
      N.call_oracles;
      N.call_defaults;
      N.call_ties } =

  (* Add dependencies from defaults as roots *)
  let roots' =
    match call_defaults with
      | None -> roots
      | Some d -> 

        D.fold
          (fun _ e a -> 
             (E.state_vars_of_expr e |> SVS.elements) @ a) 
          d
          roots
  in

  let roots' =
    match call_context with
    | None -> roots'
    | Some sv -> sv :: roots'
  in

  (* The candidate invariants generated for a when-block tie mention the tie
     variables; keep them (and hence their defining equations) in the cone of
     influence whenever the call is kept. *)
  let roots' =
    List.fold_left (fun roots' (tie, init_tie, _) ->
      tie :: (match init_tie with Some sv -> sv :: roots' | None -> roots')
    ) roots' call_ties
  in

  (* Add inputs, oracles and clock as roots *)
  let roots' =

    (* Need dependecies of inputs to node call *)
    D.values call_inputs @

    (* Need dependencies of oracles *)
    call_oracles @

    (* Need dependencies of clock and restart if call has one *)
    List.fold_left (fun roots' -> function
      (* | N.CNone -> roots' *)
        | N.CActivate c
        | N.CRestart c -> c :: roots') roots' call_cond

  in

  (* Return with new roots added *)
  roots'

(* Add roots of cone of influence from equation to roots *)
let add_roots_of_equation roots ((_,bnds), expr) = 
  (E.state_vars_of_expr expr
   |> SVS.union (state_vars_of_bounds bnds)
   |> SVS.elements) @ roots

(* Return state variables from contracts *)
let roots_of_contract ?(with_sofar_var=true) = function
| None -> SVS.empty
| Some contract -> Contract.svars_of ~with_sofar_var contract

let roots_of_contract_ass = function
| None -> SVS.empty
| Some ({ Contract.assumes } as contract) ->
  let with_sofar_var = assumes <> [] in
  Contract.svars_of ~with_sofar_var contract

(* A call whose outputs are dead -- an inlined call, or the instance retained
   for a call compiled to an application of the functional symbol of the callee
   -- carries no information of its own: its arguments are free constants
   standing for the enclosing quantified variables, and nothing reads its
   outputs. It is worth keeping only for a property that comes from it, that
   is, one instantiated from the call or an assumption of it: the values of the
   instance are then what the property is about. *)
let keep_inline_call c prop =
  match prop with
  | None -> true
  | Some prop ->
    let rec check prop =
      match prop.Property.prop_source with
      | Property.Instantiated ((_, pos), prop') ->
        pos = c.N.call_pos || check prop'
      | Property.Assumption (_, (_, p)) when p = c.N.call_pos -> true
      | _ -> false
    in
    check prop


let roots_of_inlined_calls prop calls =
  List.fold_left
    (fun acc c ->
      if c.N.call_inlined && (c.N.call_uf_applied || keep_inline_call c prop)
      then
        SVS.union acc (D.values c.call_outputs |> SVS.of_list)
      else
        acc
    )
    SVS.empty
    calls

(* Returns [true] if [sv] is a variable introduced to capture the (otherwise
   discarded) result of a call statement, e.g. a lemma application like
   'double(n-1);' (see lustreNameCalls.ml). *)
let is_discarded_output_svar sv =
  GI.svar_is_discarded_output
    (StateVar.name_of_state_var sv |> HString.mk_hstring)

(* Add discarded call-statement results as roots so that the corresponding
   calls are not sliced away.

   A call statement whose results are discarded (e.g. a lemma application like
   'double(n-1);') captures each result in a fresh discarded-output variable.
   These variables are dead from a data-flow perspective, so cone-of-influence
   slicing would normally drop them along with the call. We keep them by adding
   the discarded-output variables as roots: slicing then preserves their
   defining equations and, transitively, the calls feeding them.

   In addition, a lemma is lowered to a function with a synthetic output (the
   result of its body). When the lemma calls itself recursively, that output is
   referenced by the call, so we keep the node's outputs as roots too; otherwise
   the call's output trie would no longer match the (sliced) node output trie
   when building the transition system. *)
let roots_of_lemma_calls { N.outputs; N.equations; N.calls; N.comp_type } =
  (* Discarded-output variables defined in equations *)
  let discarded_roots =
    List.fold_left
      (fun acc ((sv, _), _) ->
        if is_discarded_output_svar sv then SVS.add sv acc else acc)
      SVS.empty
      equations
  in
  (* Discarded-output variables that are directly call outputs, if any *)
  let discarded_roots =
    List.fold_left
      (fun acc { N.call_outputs } ->
        D.fold
          (fun _ sv acc ->
            if is_discarded_output_svar sv then SVS.add sv acc else acc)
          call_outputs
          acc)
      discarded_roots
      calls
  in
  (* Keep the synthetic output of a lemma so that a recursive call to it and
     the lemma signature stay consistent *)
  match comp_type with
  | N.Function { N.is_lemma = true } ->
    SVS.union discarded_roots (D.values outputs |> SVS.of_list)
  | _ -> discarded_roots

(* Add state variables in assertion *)
let add_roots_of_asserts asserts roots = 
  List.fold_left 
    (fun accum (_,sv) -> SVS.add sv accum)
    roots
    asserts

(* Reduce nodes to cone of influence

   The last argument is a stack of quadruples [(roots, leaves, sliced,
   unsliced)]. For each state variable in [roots], all [equations],
   [calls] and [locals] that mention the state variable are to be
   moved from the node [unsliced] to the node [sliced]. If the state
   variable is in [leaves], either the state variables mentioned in
   equations, asserts or node calls are already in [roots], or the
   definitions of the state variable should not be expanded.

   If a state variable in [roots] is defined by a node call, find the
   called node in [nodes], obtain an initial quadruple for the stack
   with [init_slicing_of_node] and push it to the top of the stack so
   that the called node is sliced first. 

   Call this function with *)
let rec slice_nodes
    preserve_sig
    init_slicing_of_node
    nodes
    accum = 

  function 

    (* All nodes are sliced and in the accumulator *)
    | [] -> accum

    (* Node is sliced to all equations *)
    | ([], 
       leaves, 
       ({ N.inputs; 
          N.outputs; 
          N.locals } as node_sliced), 
        _ (* node_unsliced *)) :: tl ->
      
      (* If this is the top node, slice away inputs and outputs *)
      let inputs', outputs' = 
        if tl = [] && not preserve_sig then 
          (

            (* Only keep inputs that have been visited *)
            D.filter
              (fun _ sv -> List.exists (StateVar.equal_state_vars sv) leaves)
              inputs,

            (* Only keep inputs that have been visited *)
            D.filter
              (fun _ sv -> List.exists (StateVar.equal_state_vars sv) leaves)
              outputs)
        else
          inputs, outputs
      in
      
      (* Local variables related by an index have been moved together,
         now discard not visited indexes *)
      let locals' = 
        List.fold_left 
          (fun a l ->
             D.fold
               (fun i sv a -> 
                  if 

                    (* Has state variable been visited ? *)
                    List.exists (StateVar.equal_state_vars sv) leaves 

                  then

                    (* Keep its definition as a local state variable *)
                    D.add i sv a

                  else

                    (* Remvoe definition of not visited state
                       variable *)
                    a)
               l
               D.empty :: a)
          []
          locals 
      in

      (* Replace inputs and outputs in sliced node *)
      let node_sliced = 
        { node_sliced with
            N.inputs = inputs'; 
            N.outputs = outputs';
            N.locals = List.rev locals' }
      in

      (* Continue with next nodes *)
      slice_nodes
        preserve_sig
        init_slicing_of_node
        nodes
        (node_sliced :: accum)
        tl

    (* State variable is a leaf, that is no dependencies have to be
       added, because it has been visited, or should not be expanded *)
    | (state_var :: roots_tl, leaves, node_sliced, node_unsliced) :: tl 
      when List.exists (StateVar.equal_state_vars state_var) leaves -> 

      slice_nodes
        preserve_sig
        init_slicing_of_node
        nodes
        accum
        ((roots_tl, leaves, node_sliced, node_unsliced) :: tl)

    (* State variable is not a leaf, need to add all dependencies *)
    | (state_var :: roots', 
       leaves, 
       ({ N.node_id;
          N.equations = equations_in_coi;
          N.calls = calls_in_coi;
          N.locals = locals_in_coi } as node_sliced),
       ({ N.equations = equations_not_in_coi; 
          N.calls = calls_not_in_coi;
          N.locals = locals_not_in_coi } as node_unsliced)) :: tl as l -> 
      
      try 

        (* State variable is an output of a called node that is not
           already sliced? *)
        let { N.call_node_id } =
          List.find
            (function { N.call_node_id; N.call_outputs } ->

              (* Called node is not already sliced? *)
              (not (N.exists_node_of_name call_node_id accum)

               &&

               (* State variable is an output of the called node? *)
               D.exists
                 (fun _ sv -> StateVar.equal_state_vars state_var sv)
                 call_outputs)
            
               &&

               (* It is not a recursive call to itself *)
               not (NodeId.equal node_id call_node_id)

               &&

               (* It is not a call to a mutually recursive function that
                  is already in the stack *)
               not (List.exists (fun (_, _, {N.node_id = id_in_stack}, _) ->
                      NodeId.equal id_in_stack call_node_id) tl)
            )
            calls_not_in_coi
        in

        (* Get called node by name *)
        let node = N.node_of_node_id call_node_id nodes in

        (* Slice called node first, then return to this node

           TODO: Detect cycles in node calls here, but that should not
           be possible with the current format. *)
        slice_nodes
          preserve_sig
          init_slicing_of_node
          nodes
          accum
          (init_slicing_of_node node :: l)

      (* State variable is not defined by a node call *)
      with Not_found -> 

        (* Equations with defintion of variable added, and new roots
           from dependencies of equation *)
        let equations_in_coi', equations_not_in_coi', roots' = 

          List.fold_left 

            (fun
              (equations_in_coi, equations_not_in_coi, roots')
              (((sv, _), _) as eq) -> 

              (* Equation defines variable? *)
              if StateVar.equal_state_vars state_var sv then

                (* Add equation to sliced node *)
                (eq :: equations_in_coi, 

                 (* Remove equation from unsliced node *)
                 equations_not_in_coi,

                 (* Add variables in equation as roots *)
                 add_roots_of_equation roots' eq)

              else

                (* Do not add equation to sliced node, keep in unsliced
                   node, and no new roots *)
                (equations_in_coi, eq :: equations_not_in_coi, roots')

            )

            (* Modify equations in sliced and unsliced node, and roots *)
            (equations_in_coi, [], roots')

            (* Iterate over all equations in unsliced node *)
            equations_not_in_coi

        in

        (* Node calls with call returning state variable added, and new
           roots from dependencies of node call *)
        let calls_in_coi', calls_not_in_coi', roots' = 

          List.fold_left 

            (fun
              (calls_in_coi, calls_not_in_coi, roots')
              ({ N.call_outputs } as node_call) ->

              if

                (* State variable is an output of the called node? *)
                LustreIndex.exists
                  (fun _ sv -> StateVar.equal_state_vars state_var sv)
                  call_outputs


              then

                (* Add equation to sliced node *)
                (node_call :: calls_in_coi, 

                 (* Remove equation from unsliced node *)
                 calls_not_in_coi,

                 (* Add variables in equation as roots *)
                 add_roots_of_node_call roots' node_call)


              else

                (* Do not add node call to sliced node, keep in unsliced
                   node, and no new roots *)
                (calls_in_coi, node_call :: calls_not_in_coi, roots')

            )

            (* Modify node calls in sliced and unsliced node, and roots *)
            (calls_in_coi, [], roots')

            (* Iterate over all node calls in unsliced node *)
            calls_not_in_coi

        in

        (* Move definitions containing the state variable from the
           unsliced to sliced node

           We move definitions of all local variables related by an
           index together and eliminate the not visited ones at the
           end. If we wanted to move indexed state variables one by one,
           we would need to have a way to find out which local state
           variable trie to insert it into.*)
        let locals_in_coi', locals_not_in_coi' =

          List.fold_left

            (fun (locals_in_coi, locals_not_in_coi) l -> 

               if 

                 (* Local definition contains the state variable? *)
                 (D.exists
                    (fun _ sv -> StateVar.equal_state_vars sv state_var))
                   l

               then

                 (* Add all state variables related by an index to this
                    state variable as local variables, but do not add
                    them as roots *)
                 (l :: locals_in_coi, locals_not_in_coi)

               else

                 (* Do not add local variable to sliced node, keep in
                    unsliced node *)
                 (locals_in_coi, l :: locals_not_in_coi))

            (* Modify local variables in sliced and unsliced node *)
            (locals_in_coi, [])

            (* Iterate over all local variables in unsliced node *)
            locals_not_in_coi

        in

        (* Modify slicecd node *)
        let node_sliced' =
          { node_sliced with
              N.locals = locals_in_coi';
              N.equations = equations_in_coi';
              N.calls = calls_in_coi'; } 
        in

        (* Modify slicecd node *)
        let node_unsliced' =
          { node_unsliced with
              N.equations = equations_not_in_coi';
              N.calls = calls_not_in_coi';
              N.locals = locals_not_in_coi' }
        in

        (* Continue with modified sliced node and roots *)
        slice_nodes
          preserve_sig
          init_slicing_of_node
          nodes
          accum
          ((roots', (state_var :: leaves), node_sliced', node_unsliced') :: tl)


(* The outputs of the calls of a recursive function to the functions of its
   recursive group, among [nodes], and the inputs and outputs of the
   function.

   The termination checks of a recursive call are generated with the call,
   so slicing a call away would leave its termination unchecked. In the
   analysis of the function itself, where the termination of every recursive
   call is proved for all the inputs of the function, nothing need depend on
   a call for it to be kept: a function with no contract and no property, or
   a call whose value no guarantee depends on, is still checked. A call of
   the function to itself refers to the signature of the function, which is
   kept whole, for the arguments and the outputs of the call to match it (see
   [roots_of_lemma_calls]): an input that nothing reads is still passed by
   the call. *)
let roots_of_recursive_calls
    nodes { N.comp_type; N.calls; N.inputs; N.outputs } =
  let group_of node_id =
    match N.node_of_node_id node_id nodes with
    | { N.comp_type = N.Function { N.rec_info = Some (group, _) } } ->
      Some group
    | _ -> None
    | exception Not_found -> None
  in
  match comp_type with
  | N.Function { N.rec_info = Some (group, _) } ->
    List.fold_left
      (fun acc { N.call_node_id; N.call_outputs } ->
         if group_of call_node_id = Some group then
           D.fold (fun _ sv acc -> SVS.add sv acc) call_outputs acc
         else acc)
      (D.values inputs @ D.values outputs |> SVS.of_list) calls
  | _ -> SVS.empty

(* Whether the properties of the node [call_node_id], other than those that
   come from assumptions, are lifted into the calling node, at a call that
   is [relevant] (see [relevant_calls]). The properties of an internal node,
   a node Kind 2 generates for a part of the calling node (see
   [NodeId.is_internal]), are lifted in any case. Those of another node are
   lifted in a non-modular analysis only, according to
   --check_subproperties. This is the rule of
   [LustreTransSys.call_terms_of_node_call], which slicing has to follow:
   a call whose properties are lifted must not be sliced away. *)
let props_lifted_from_call ~relevant call_node_id =
  NI.is_internal call_node_id
  || (not (Flags.modular ())
      && (match Flags.check_subproperties () with
          | `True -> true
          | `Relevant -> relevant
          | `False -> false))

(* A predicate that holds for the identifiers of the nodes, among [nodes],
   whose calls carry proof obligations into the calling node (see
   [LustreTransSys.call_terms_of_node_call]). They are of two kinds:

   - the assumptions of the contract of the called node, and those of the
     calls inside it, at any depth, which are lifted into the calling node
     in any case;

   - the other properties of the called node, including those it lifts from
     its own calls, which are lifted as [props_lifted_from_call] says. With
     --check_subproperties relevant, the properties of a node that is not
     internal are lifted only from a call in the cone of influence of the
     properties of the top node (see [relevant_calls]), so they do not make
     a call relevant.

   A node for which [is_abstract] holds is replaced by its contract, and
   only the properties of its contract are lifted from it. If
   [assumptions] is [false], the obligations of the first kind are left
   out.

   A call carries these obligations whether or not anything in the calling
   node depends on its outputs, so slicing it away would leave them
   unchecked. *)
let has_lifted_obligations ~assumptions is_abstract nodes =
  let lifts_props = props_lifted_from_call ~relevant:false in
  (* For each node, whether the assumptions of its contract and its other
     properties are obligations, and its callees *)
  let info ({ N.node_id; N.props; N.contract; N.calls } as node) =
    let abstract = is_abstract node in
    let props = if abstract then filter_props_contract props else props in
    let assumes, guarantees =
      match contract with
      | None -> false, false
      | Some { Contract.assumes; Contract.guarantees; Contract.modes } ->
        assumes <> [], not abstract && (guarantees <> [] || modes <> [])
    in
    let own_props =
      guarantees
      || List.exists
        (function
          | (_, _, Property.Candidate _, _, _) -> false
          | _ -> true)
        props
    in
    let callees =
      if abstract then []
      else
        List.filter_map
          (fun { N.call_node_id; N.call_inlined } ->
             if call_inlined then None else Some call_node_id)
          calls
    in
    node_id, assumes, own_props, callees
  in
  (* The callees come after their callers in [nodes] *)
  let info = List.rev_map info nodes in
  (* The nodes whose calls carry obligations of the first kind, and the
     nodes with properties of the second kind, as a least fixpoint, which
     takes several rounds only for the calls in a recursive group *)
  let rec fix ((with_assumptions, with_props) as sets) =
    let (with_assumptions', with_props') as sets' =
      List.fold_left
        (fun (with_assumptions, with_props)
          (node_id, assumes, own_props, callees) ->
          let with_assumptions =
            if assumes
            || List.exists (fun c -> NI.Set.mem c with_assumptions) callees
            then NI.Set.add node_id with_assumptions
            else with_assumptions
          in
          let with_props =
            if own_props
            || List.exists
              (fun c -> lifts_props c && NI.Set.mem c with_props) callees
            then NI.Set.add node_id with_props
            else with_props
          in
          with_assumptions, with_props)
        sets info
    in
    if NI.Set.equal with_assumptions with_assumptions'
    && NI.Set.equal with_props with_props'
    then sets
    else fix sets'
  in
  let with_assumptions, with_props = fix (NI.Set.empty, NI.Set.empty) in
  fun node_id ->
    (assumptions && NI.Set.mem node_id with_assumptions)
    || (lifts_props node_id && NI.Set.mem node_id with_props)

(* The outputs of the calls in [calls] to a node with obligations lifted
   into the calling node, see [has_lifted_obligations] *)
let roots_of_calls_with_obligations has_obligations calls =
  List.fold_left
    (fun acc { N.call_node_id; N.call_inlined; N.call_outputs } ->
       if not call_inlined && has_obligations call_node_id then
         D.fold (fun _ sv acc -> SVS.add sv acc) call_outputs acc
       else acc)
    SVS.empty calls

(* Slice a node to its implementation, starting from the outputs,
   contracts and properties *)
let root_and_leaves_of_impl  
    nodes
    has_obligations
    outputs_demanded
    property
    is_top
    roots
    ({ N.outputs;
       N.contract;
       N.props;
       N.calls;
       N.asserts } as node) =

  (* Slice everything from node *)
  let node_sliced =
    slice_all_of_node
      ~keep_props:true
      ~keep_contracts:true
      node
  in
  
  (* Slice starting with outputs, contracts and properties *)
  let node_roots = 
    ( match roots node true with
      
      (* No roots given? *)
      | None -> 

        (* Consider properties and contracts as roots *)

        (* Adding sofar variables in implementations may be not necessary, but
           the code should be revised carefully before applying the change
           (roots_of_contract ~with_sofar:false contract) 
        *)
        (roots_of_contract_ass contract)
        |> SVS.union (roots_of_props props)
                                          
      (* Use instead of roots from properties and contracts *)
      | Some r -> 
        (roots_of_contract_ass contract)
        |> SVS.union r )

    |> add_roots_of_asserts asserts

    (* Consider outputs as roots except at the top node, and at a node
       whose outputs nothing reads (see [relevant_calls]) *)
    |> SVS.union (
      if is_top || not (outputs_demanded node.N.node_id) then SVS.empty
      else D.values outputs |> SVS.of_list
    )
    |> SVS.union (roots_of_inlined_calls property calls)

    (* Do not slice the calls that carry obligations into this node, unless
       slicing to a single property *)
    |> SVS.union
      (if property = None then
         roots_of_calls_with_obligations (Lazy.force has_obligations) calls
       else SVS.empty)

    (* Do not slice calls to lemmas *)
    |> SVS.union (roots_of_lemma_calls node)

    (* Do not slice the recursive calls of the top node, whose termination
       the analysis checks *)
    |> SVS.union
      (if is_top then roots_of_recursive_calls nodes node else SVS.empty)

    |> SVS.elements
  in

  (* Consider all streams *)
  let node_leaves = [] in

  (node_roots, node_leaves, node_sliced, node)


(* Slice a node to its contracts, starting from contracts, stopping at
   outputs *)
let root_and_leaves_of_contracts
    property
    is_top
    roots
    ({ N.outputs;
       N.calls;
       N.props;
       N.contract } as node) =

  (* Slice everything from node *)
  let node_sliced = 
    slice_all_of_node
      ~keep_props:true
      ~keep_contracts:true
      ~keep_asserts:false
      ~for_contract:true
      node 
  in
    
  (* Slice starting with contracts. The obligations of the contract are
     kept in the abstraction (see [slice_all_of_node]), so their
     definitions must be kept too, whatever the roots given *)
  let node_roots =
    ( match roots node false with
      | None ->
        roots_of_contract ~with_sofar_var:(not is_top) contract
        |> SVS.union (roots_of_inlined_calls property calls)
      | Some r -> r )
    |> SVS.union (roots_of_props_contract props)
    |> SVS.elements
  in

  (* Do not consider anything below outputs *)
  let node_leaves = D.values outputs in

  (node_roots, node_leaves, node_sliced, node)


(* Return [true] if the node is flagged as abstract in
   [abstraction_map]. Default to [false] if the node is not in the
   map. *)
let node_is_abstract analysis { N.node_id } = 

  [NI.get_internal_name node_id |> HString.string_of_hstring]
  |> Analysis.param_scope_is_abstract analysis


(* Return roots for slicing to contracts or implementation as
   indicated by [abstraction_map]. Use the implementation if a node is
   not in the map. *)
let root_and_leaves_of_abstraction_map 
  nodes has_obligations outputs_demanded property is_top roots
  abstraction_map node
=
  if node_is_abstract abstraction_map node
  then (* Node is to be abstract *)
    root_and_leaves_of_contracts property is_top roots node 
  else (* Node is to be concrete *)
    root_and_leaves_of_impl
      nodes has_obligations outputs_demanded property is_top roots node


(* Slice nodes to abstraction or implementation as indicated in
   [abstraction_map] *)
let slice_to_abstraction'
  ?(preserve_sig = false) ?(assumptions = true)
  ?(outputs_demanded = fun _ -> true) ?property analysis roots subsystem
=

  let { A.top } = A.info_of_param analysis in

  (* Get list of nodes from subsystem in toplogical order with the top
     node at the head of the list *)
  let nodes =
    S.find_subsystem subsystem top |> N.nodes_of_subsystem 
  in

  (* Only needed when not slicing to a single property *)
  let has_obligations =
    lazy
      (has_lifted_obligations ~assumptions (node_is_abstract analysis) nodes)
  in

  (* Slice all nodes to either abstraction or implementation *)
  let nodes' = 

    slice_nodes
      preserve_sig
      (root_and_leaves_of_abstraction_map
         nodes has_obligations outputs_demanded property false roots
         analysis)
      nodes
      []
      [root_and_leaves_of_abstraction_map
         nodes has_obligations outputs_demanded property true roots analysis
         (List.hd nodes)]

  in

  (* Create subsystem from list of nodes *)
  let { N.node_id = top; } = List.hd nodes in
  N.subsystem_of_nodes top nodes'


let no_slice {N.inputs; N.outputs ; N.locals ; N.contract; N.props } is_impl =
  let vars =
    if is_impl then
      (roots_of_contract ~with_sofar_var:true contract)
      |> SVS.union (roots_of_props props)
      |> SVS.union (D.values inputs |> SVS.of_list)
      |> SVS.union (D.values outputs |> SVS.of_list)
      |> SVS.union (
        List.concat (List.map D.values locals) |> SVS.of_list
      )
    else
      (roots_of_contract ~with_sofar_var:true contract)
  in
  Some vars


(* Slice nodes to abstraction or implementation as indicated in
   [abstraction_map] *)
let slice_to_abstraction
  ?(preserve_sig = false) reduce_to_coi analysis subsystem
=
  let roots =
    if reduce_to_coi then (fun _ _ -> None) else no_slice
  in
  slice_to_abstraction'
    ~preserve_sig analysis roots subsystem

(* The internal nodes, among the callees in [nodes], whose outputs are read
   by an equation, a node call, an assertion, a property or a contract kept
   in the calling node, or are outputs of a calling node whose outputs are
   demanded, as [outputs_demanded] says. The top node, at the head of
   [nodes], has no demanded outputs. *)
let internal_nodes_read outputs_demanded nodes =
  let top = match nodes with { N.node_id } :: _ -> Some node_id | [] -> None in
  List.fold_left
    (fun acc
      { N.node_id; N.outputs; N.equations; N.calls; N.asserts; N.props;
        N.contract } ->
      let reads =
        List.fold_left add_roots_of_equation [] equations
        |> (fun roots -> List.fold_left add_roots_of_node_call roots calls)
        |> SVS.of_list
        |> add_roots_of_asserts asserts
        |> SVS.union (roots_of_props props)
        |> SVS.union (roots_of_contract contract)
        |> SVS.union
          (if Some node_id = top || not (outputs_demanded node_id)
           then SVS.empty
           else D.values outputs |> SVS.of_list)
      in
      List.fold_left
        (fun acc { N.call_node_id; N.call_outputs } ->
           if NI.is_internal call_node_id
           && D.exists (fun _ sv -> SVS.mem sv reads) call_outputs
           then NI.Set.add call_node_id acc
           else acc)
        acc calls)
    NI.Set.empty nodes

module IntSet = Set.Make (Int)

(* The identifiers of the calls in the cone of influence of the properties
   of the top node of [analysis], for each node of [subsystem]. These are
   the calls whose properties are lifted into the calling node with
   --check_subproperties relevant.

   They are the calls kept by the slicing of [subsystem] to the cone of
   influence, except for the calls kept only for the assumptions of their
   contracts, or of the calls inside them, which depend on the inputs of
   the call only, and for the calls inside an internal node kept only for
   its properties. The properties of an internal node are properties of the
   calling node, so their cone of influence counts, but not the cone of
   influence of the outputs of the internal node, unless something kept in
   the calling node reads them. Slicing is done node by node, not call by
   call, so the outputs of an internal node are demanded as soon as one of
   its calls has them read. Whether they are demanded depends on what the
   slicing keeps, which in turn depends on the internal nodes whose outputs
   are demanded: this is a least fixpoint, whose number of rounds is at most
   the depth at which internal nodes are nested. *)
let relevant_calls_of_subsystem analysis subsystem =
  let rec fix demanded =
    let outputs_demanded node_id =
      not (NI.is_internal node_id) || NI.Set.mem node_id demanded
    in
    let nodes =
      slice_to_abstraction' ~assumptions:false ~outputs_demanded analysis
        (fun _ _ -> None) subsystem
      |> N.nodes_of_subsystem
    in
    let demanded' =
      internal_nodes_read outputs_demanded nodes |> NI.Set.union demanded
    in
    if NI.Set.equal demanded demanded' then nodes else fix demanded'
  in
  fix NI.Set.empty
  |> List.fold_left
    (fun acc { N.node_id; N.calls } ->
       NI.Map.add node_id
         (List.fold_left
            (fun acc { N.call_id } -> IntSet.add call_id acc)
            IntSet.empty calls)
         acc)
    NI.Map.empty

(* The relevant calls last computed, with the subsystem, the top node and
   the abstraction of the analysis, which are all they depend on. A system
   is built several times for the same analysis (for each property that
   IC3IA checks, for instance), possibly in different domains, and the
   analyses run one after the other: keeping the last entry only is enough
   for these builds to share it, and bounds what the cache holds. *)
let relevant_calls_cache = ref None
let relevant_calls_lock = Mutex.create ()

(* [relevant_calls_of_subsystem], as a predicate on the identifier of the
   calling node and the identifier of the call in it *)
let relevant_calls analysis subsystem =
  let { A.top; A.abstraction_map } = A.info_of_param analysis in
  let same (subsystem', top', abstraction_map', _) =
    subsystem' == subsystem
    && Scope.equal top' top
    && Scope.Map.equal Bool.equal abstraction_map' abstraction_map
  in
  let relevant =
    match Mutex.protect relevant_calls_lock (fun () -> !relevant_calls_cache)
    with
    | Some ((_, _, _, relevant) as entry) when same entry -> relevant
    | _ ->
      let relevant = relevant_calls_of_subsystem analysis subsystem in
      Mutex.protect relevant_calls_lock (fun () ->
        relevant_calls_cache :=
          Some (subsystem, top, abstraction_map, relevant));
      relevant
  in
  fun node_id call_id ->
    match NI.Map.find_opt node_id relevant with
    | Some call_ids -> IntSet.mem call_id call_ids
    | None -> false

let slice_node_to_abstraction node =
  
  let nodes' =
    let roots = (fun _ _ -> None) in
    let preserve_sig = true in

    slice_nodes
      preserve_sig
      (fun _ -> assert false)
      [node]
      []
      [root_and_leaves_of_contracts None false roots node]
  in
  match nodes' with
  | [node] -> node
  | _ -> assert false


(* Slice nodes to abstraction or implementation as indicated in
   [abstraction_map] *)
let slice_to_abstraction_and_property
  ?(preserve_sig = false) analysis prop subsystem
=
  let roots =
    match prop.Property.prop_source with
    | Property.Instantiated _
    | Property.Assumption _ -> (fun _ _ -> None)
    | _ -> (
      let vars =
        Term.state_vars_of_term prop.Property.prop_term
      in
      fun { N.contract } is_impl -> (
        if is_impl then
          Some vars
        else
          (* Always include at least roots of contract *)
          Some (roots_of_contract_ass contract)
        )
    )
  in
  slice_to_abstraction'
    ~preserve_sig:preserve_sig ~property:prop analysis roots subsystem


  

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
