(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

module N = LustreNode
module E = LustreExpr
module D = LustreIndex
module NI = NodeId

module SVS = StateVar.StateVarSet
module SVM = StateVar.StateVarMap
module UFS = UfSymbol.UfSymbolSet

type def = UfSymbol.t * Var.t list * Term.t

type block = def list

(* What a defined function's system needs: the blocks of definitions its
   own depends on followed by its own, and the uninterpreted symbols they
   apply *)
type node_defs = {
  blocks : block list;
  ufs : UfSymbol.t list;
}

type t = node_defs NI.Map.t

let empty = NI.Map.empty

let enabled () =
  Flags.Smt.define_fun_rec ()
  &&
  (* Only the solvers that accept recursive function definitions *)
  (match Flags.Smt.solver () with
   | `cvc5_SMTLIB | `Z3_SMTLIB -> true
   | _ -> false)
  &&
  (* Only a logic inferred from the system, the default. A logic set with
     --smt_logic is sent to the solver as it was written, and both solvers
     refuse a recursive definition under most of the named logics (Z3 takes
     one in UFLIA but not in UFNIA); the definitions are left out rather
     than overriding what was asked for. It is also only an inferred logic
     that carries the [TermLib.RF] feature, which is how the solver drivers
     learn that the system defines recursive functions and pass the options
     they need to handle them. *)
  Flags.Smt.logic () = `detect

let is_defined t node_id = NI.Map.mem node_id t

let blocks_of_node t node_id =
  match NI.Map.find_opt node_id t with
  | Some { blocks } -> blocks
  | None -> []

let ufs_of_node t node_id =
  match NI.Map.find_opt node_id t with
  | Some { ufs } -> ufs
  | None -> []


(* ********************************************************************** *)
(* Termination conditions                                                 *)
(* ********************************************************************** *)

(* Lexicographic termination requires the measure to be bounded below, i.e.
   each component is non-negative. *)
let bounded_below ms =
  List.map (fun m -> Term.mk_leq [Term.mk_num Numeral.zero; m]) ms
  |> Term.mk_and

(* The measure strictly decreases in the lexicographic order: some component
   decreases while all earlier components stay equal. For a single component
   this reduces to the ordinary "callee < caller". When the two measures have
   different arities (possible for mutually recursive functions), their common
   prefix is compared. *)
let lex_lt callee caller =
  let rec lex cs ds =
    match cs, ds with
    | [c], [d] -> Term.mk_lt [c; d]
    | c :: cs', d :: ds' ->
      Term.mk_or [
        Term.mk_lt [c; d];
        Term.mk_and [Term.mk_eq [c; d]; lex cs' ds']
      ]
    | _ -> Term.t_true
  in
  let n = min (List.length callee) (List.length caller) in
  let take l = List.filteri (fun i _ -> i < n) l in
  lex (take callee) (take caller)


(* ********************************************************************** *)
(* Eligibility                                                            *)
(* ********************************************************************** *)

let func_info { N.comp_type } =
  match comp_type with
  | N.Function info -> Some info
  | N.Node -> None

let scc_of_node node =
  match func_info node with
  | Some { N.rec_info = Some (scc_id, _) } -> Some scc_id
  | _ -> None

let is_lemma node =
  match func_info node with
  | Some { N.is_lemma } -> is_lemma
  | None -> false

(* A recursive function is eligible for a definition if there is no contract
   to abstract its recursive calls with, or if it is transparent, i.e. its
   contract is never to be used in place of its body.

   A contract abstracts the function through its guarantees and modes, be
   they explicit or from a refinement type of an output. An assumption
   (explicit, or from a refinement or subrange type of an input) is an
   obligation of the callers instead, which the transition system keeps at
   every call: it does not stand in the way of a definition. *)
let eligible node =
  not (N.has_effective_contract node)
  || node.N.opacity = Opacity.Transparent

(* The equations and calls of a node, by the state variable they define *)
type svar_def =
  | Eq of E.t
  | Call of N.node_call

let defs_of_node { N.equations; N.calls } =
  let defs =
    List.fold_left
      (fun acc ((sv, _), e) -> SVM.add sv (Eq e) acc)
      SVM.empty
      equations
  in
  List.fold_left
    (fun acc ({ N.call_outputs } as call) ->
       D.fold (fun _ sv acc -> SVM.add sv (Call call) acc) call_outputs acc)
    defs
    calls

(* The state variables a definition depends on *)
let deps_of_def = function
  | Eq e -> E.state_vars_of_expr e
  | Call { N.call_inputs; N.call_context } ->
    let deps = D.values call_inputs |> SVS.of_list in
    match call_context with
    | Some sv -> SVS.add sv deps
    | None -> deps

let all_svars { N.inputs; N.outputs; N.locals } =
  D.values inputs
  @ D.values outputs
  @ List.concat_map D.values locals

(* Whether the body of a function is a total function of its inputs that a
   definition can be built from: no assertion, oracle or array; every output
   defined, through equations and calls only, from the inputs (and global
   constants); and every callee recursive, imported, or itself definable
   (memoized in [memo]; a function in progress is not definable, which only
   matters for a call cycle, and a call cycle is a recursive group) *)
let rec definable nodes memo node =
  let node_id = node.N.node_id in
  match NI.Map.find_opt node_id !memo with
  | Some b -> b
  | None ->
    memo := NI.Map.add node_id false !memo;
    let b = definable' nodes memo node in
    memo := NI.Map.add node_id b !memo;
    b

and definable' nodes memo ({ N.inputs; N.outputs; N.equations; N.calls } as node) =
  let no_array sv =
    not (Type.is_array (StateVar.type_of_state_var sv))
  in
  let callee_ok { N.call_node_id } =
    match N.node_of_node_id call_node_id nodes with
    | exception Not_found -> false
    | callee ->
      N.is_function callee
      && not (is_lemma callee)
      && (N.is_recursive callee
          || callee.N.is_extern
          || definable nodes memo callee)
  in
  (* A call may have a context (the branch of a conditional it is in):
     its constraints only hold under it, and the definition leaves its value
     undefined outside of it *)
  let call_ok ({ N.call_cond; N.call_defaults; N.call_oracles } as call) =
    call_cond = [] && call_defaults = None
    && call_oracles = [] && callee_ok call
  in
  let defs = defs_of_node node in
  let input_svars = D.values inputs |> SVS.of_list in
  (* Every output is defined from the inputs *)
  let rec defined visited sv =
    if SVS.mem sv visited || SVS.mem sv input_svars || StateVar.is_const sv
    then true, visited
    else
      match SVM.find_opt sv defs with
      | None -> false, visited
      | Some def ->
        SVS.fold
          (fun sv' (ok, visited) ->
             if ok then defined visited sv' else ok, visited)
          (deps_of_def def)
          (true, SVS.add sv visited)
  in
  N.is_function node
  && not (is_lemma node)
  && not node.N.is_extern
  && node.N.oracles = []
  && node.N.asserts = []
  && List.for_all (fun ((_, bounds), _) -> bounds = []) equations
  && List.for_all no_array (all_svars node)
  && List.for_all call_ok calls
  && (D.values outputs
      |> List.fold_left
        (fun (ok, visited) sv -> if ok then defined visited sv else ok, visited)
        (true, SVS.empty)
      |> fst)


(* ********************************************************************** *)
(* Definitions                                                            *)
(* ********************************************************************** *)

let var_of_svar sv = Var.mk_state_var_instance sv Numeral.zero

let term_of_svar sv = Term.mk_var (var_of_svar sv)

let term_of_expr e = E.base_term_of_expr Numeral.zero e

(* The symbol giving a recursive call its value when its termination checks
   fail *)
let undefined_call_symbol node_id inputs output =
  let type_of = StateVar.type_of_state_var in
  let name =
    Format.asprintf "%a.%s.%s"
      HString.pp_print_hstring (NI.get_internal_name node_id)
      (StateVar.name_of_state_var output)
      Lib.ReservedIds.undefined_call
  in
  UfSymbol.mk_uf_symbol
    name (List.map type_of (D.values inputs)) (type_of output)

(* Context of the construction of the bindings of a function's body *)
type ctx = {
  nodes : N.t list;
  (* The recursive group being defined *)
  scc_id : int;
  (* The measure of the function being defined, over its inputs *)
  caller_rf : E.expr list;
  (* Symbols giving the recursive calls of the group their value when their
     termination checks fail, by callee output *)
  undefined_calls : UfSymbol.t SVM.t;
}

(* The bindings of the state variables defined in the body of [node], in
   reverse dependency order (a binding follows the bindings it depends on),
   prepended to [acc] *)
let rec bindings_of_node ctx node acc =
  let defs = defs_of_node node in
  let input_svars = D.values node.N.inputs |> SVS.of_list in
  (* Visit the definitions in dependency order, each once ([visited] holds
     the state variables whose definition was emitted) *)
  let rec visit (visited, acc) sv =
    if SVS.mem sv visited || SVS.mem sv input_svars || StateVar.is_const sv
    then visited, acc
    else
      match SVM.find_opt sv defs with
      | None -> assert false (* Checked by [definable] *)
      | Some def ->
        let visited, acc =
          SVS.fold
            (fun sv' acc -> visit acc sv')
            (deps_of_def def)
            (visited, acc)
        in
        match def with
        | Eq e ->
          SVS.add sv visited,
          (var_of_svar sv, term_of_expr (E.init_expr e)) :: acc
        | Call ({ N.call_outputs } as call) ->
          D.fold (fun _ sv -> SVS.add sv) call_outputs visited,
          bindings_of_call ctx call acc
  in
  D.values node.N.outputs
  |> List.fold_left visit (SVS.empty, acc)
  |> snd

(* The bindings of the outputs of a call *)
and bindings_of_call
    ctx ({ N.call_node_id; N.call_inputs; N.call_outputs; N.call_context }) acc =
  let callee = N.node_of_node_id call_node_id ctx.nodes in
  let args = D.values call_inputs |> List.map term_of_svar in
  let uf_symbols =
    match func_info callee with
    | Some { N.uf_symbols } -> uf_symbols
    | None -> assert false (* Checked by [definable] *)
  in
  let bind_outputs term_of_output acc =
    D.fold2
      (fun _ callee_out call_out acc ->
         (var_of_svar call_out, term_of_output callee_out) :: acc)
      callee.N.outputs
      call_outputs
      acc
  in
  match scc_of_node callee with
  | Some scc_id when scc_id = ctx.scc_id ->
    (* A recursive call of the group: apply the symbol of the callee under
       the guard of the termination checks of the call (and of its context,
       if any), and leave the value of the call undefined otherwise. Whether
       or not the measure actually decreases, the recursion of the
       definitions is then well founded, so they have a model. *)
    let callee_rf =
      match func_info callee with
      | Some { N.rec_info = Some (_, rf) } -> rf
      | _ -> assert false
    in
    let termination_guard =
      (* An empty measure is an ADT measure, whose decrease is established
         statically (LustreCheckADTDecreases) *)
      if ctx.caller_rf = [] || callee_rf = [] then []
      else
        let caller_terms = List.map term_of_expr ctx.caller_rf in
        (* The measure of the callee at the arguments of the call *)
        let sigma =
          List.combine
            (D.values callee.N.inputs |> List.map var_of_svar)
            args
        in
        let callee_terms =
          List.map
            (fun e -> term_of_expr e |> Term.apply_subst sigma)
            callee_rf
        in
        [bounded_below caller_terms; lex_lt callee_terms caller_terms]
    in
    let context_guard =
      match call_context with
      | Some sv -> [term_of_svar sv]
      | None -> []
    in
    let guard =
      match context_guard @ termination_guard with
      | [] -> None
      | conjuncts -> Some (Term.mk_and conjuncts)
    in
    bind_outputs
      (fun callee_out ->
         let app = Term.mk_uf (SVM.find callee_out uf_symbols) args in
         match guard with
         | None -> app
         | Some guard ->
           Term.mk_ite guard app
             (Term.mk_uf (SVM.find callee_out ctx.undefined_calls) args))
      acc
  | Some _ ->
    (* A recursive function of another group: its functional symbol is
       defined by its own block, or uninterpreted (and tied to its instances
       by the transition system) *)
    bind_outputs
      (fun callee_out -> Term.mk_uf (SVM.find callee_out uf_symbols) args)
      acc
  | None when callee.N.is_extern ->
    (* An imported function: its functional symbol is uninterpreted, and
       tied to its instances by the transition system *)
    bind_outputs
      (fun callee_out -> Term.mk_uf (SVM.find callee_out uf_symbols) args)
      acc
  | None ->
    (* Any other function is inlined: bind its formal inputs to the
       arguments, then its body, then the outputs of the call to its
       outputs. A later inlining of the same function rebinds the same
       variables, which the nesting of the bindings keeps apart. *)
    let acc =
      D.fold2
        (fun _ formal arg acc -> (var_of_svar formal, term_of_svar arg) :: acc)
        callee.N.inputs
        call_inputs
        acc
    in
    let acc = bindings_of_node ctx callee acc in
    bind_outputs (fun callee_out -> term_of_svar callee_out) acc

(* The body of the definition of [output] from the bindings of the body of
   its function, in reverse dependency order: the bindings the output
   depends on, nested in dependency order, around the output variable *)
let body_of_output bindings output =
  let output_var = var_of_svar output in
  (* Keep the bindings the output depends on, going backwards *)
  let _, kept =
    List.fold_left
      (fun (needed, kept) ((v, t) as binding) ->
         if Var.VarSet.mem v needed then
           Var.VarSet.union needed (Term.vars_of_term t),
           binding :: kept
         else needed, kept)
      (Var.VarSet.singleton output_var, [])
      bindings
  in
  (* [kept] is in dependency order: nest the bindings from the innermost
     (last) one *)
  List.fold_right
    (fun binding body -> Term.mk_let [binding] body)
    kept
    (Term.mk_var output_var)

(* The uninterpreted function symbols applied by a term *)
let ufs_of_term term =
  let acc = ref UFS.empty in
  Term.map
    (fun _ t ->
       (match Term.node_of_term t with
        | Term.T.Node (s, _) when Symbol.is_uf s ->
          acc := UFS.add (Symbol.uf_of_symbol s) !acc
        | _ -> ());
       t)
    term
  |> ignore;
  !acc

(* The block of definitions of a recursive group *)
let block_of_scc nodes scc_id members =
  let undefined_calls =
    List.fold_left
      (fun acc ({ N.node_id; N.inputs; N.outputs }) ->
         D.fold
           (fun _ output acc ->
              SVM.add output (undefined_call_symbol node_id inputs output) acc)
           outputs
           acc)
      SVM.empty
      members
  in
  List.concat_map
    (fun node ->
       let caller_rf, uf_symbols =
         match func_info node with
         | Some { N.rec_info = Some (_, rf); N.uf_symbols } -> rf, uf_symbols
         | _ -> assert false
       in
       let ctx = { nodes; scc_id; caller_rf; undefined_calls } in
       let formals = D.values node.N.inputs |> List.map var_of_svar in
       let bindings = bindings_of_node ctx node [] in
       D.values node.N.outputs
       |> List.map (fun output ->
           SVM.find output uf_symbols,
           formals,
           body_of_output bindings output))
    members


(* ********************************************************************** *)
(* All definitions                                                        *)
(* ********************************************************************** *)

module IMap = Map.Make (Int)

let compute ~adt_junk_ufs nodes =

  if not (enabled ()) then empty else

    (* The recursive groups, by identifier *)
    let sccs =
      List.fold_left
        (fun acc node ->
           match scc_of_node node with
           | Some scc_id ->
             let members =
               match IMap.find_opt scc_id acc with
               | Some l -> l
               | None -> []
             in
             IMap.add scc_id (node :: members) acc
           | None -> acc)
        IMap.empty
        nodes
    in

    (* The groups to define: every function of the group must be eligible and
       definable *)
    let memo = ref NI.Map.empty in
    let defined_sccs =
      IMap.filter
        (fun _ members ->
           List.for_all
             (fun node -> eligible node && definable nodes memo node)
             members)
        sccs
    in

    if IMap.is_empty defined_sccs then empty else

      let blocks =
        IMap.mapi (fun scc_id members -> block_of_scc nodes scc_id members)
          defined_sccs
      in

      (* The symbols each block defines and applies *)
      let defined_of_block block =
        List.fold_left (fun acc (uf, _, _) -> UFS.add uf acc) UFS.empty block
      in
      let applied_of_block block =
        List.fold_left
          (fun acc (_, _, body) -> UFS.union acc (ufs_of_term body))
          UFS.empty
          block
      in
      let all_defined =
        IMap.fold
          (fun _ block acc -> UFS.union acc (defined_of_block block))
          blocks
          UFS.empty
      in

      (* The uninterpreted symbols a block may apply: the functional symbols
         of the functions that are not defined, the symbols of the
         undefined recursive calls, and the ADT junk symbols. Anything else
         (a constructor, a select) is declared elsewhere. *)
      let declarable =
        let function_ufs =
          List.concat_map
            (fun node ->
               match func_info node with
               | Some { N.uf_symbols } -> SVM.bindings uf_symbols |> List.map snd
               | None -> [])
            nodes
        in
        let undefined_calls =
          IMap.fold
            (fun _ members acc ->
               List.fold_left
                 (fun acc { N.node_id; N.inputs; N.outputs } ->
                    D.fold
                      (fun _ output acc ->
                         undefined_call_symbol node_id inputs output :: acc)
                      outputs
                      acc)
                 acc
                 members)
            defined_sccs
            []
        in
        function_ufs @ undefined_calls @ adt_junk_ufs
        |> List.filter (fun uf -> not (UFS.mem uf all_defined))
        |> UFS.of_list
      in

      (* Blocks in dependency order (a block after the ones defining the
         symbols it applies), each with the uninterpreted symbols it applies *)
      let block_info =
        IMap.map
          (fun block ->
             let applied = applied_of_block block in
             let deps =
               IMap.fold
                 (fun scc_id block' acc ->
                    if UFS.is_empty (UFS.inter applied (defined_of_block block'))
                    then acc
                    else scc_id :: acc)
                 blocks
                 []
             in
             block, deps, UFS.inter applied declarable)
          blocks
      in

      (* The blocks a group's own depends on, followed by its own, and the
         symbols they apply *)
      let rec closure (order, seen, ufs) scc_id =
        if List.mem scc_id seen then order, seen, ufs
        else
          let block, deps, applied = IMap.find scc_id block_info in
          let order, seen, ufs =
            List.fold_left closure (order, scc_id :: seen, ufs) deps
          in
          order @ [block], seen, UFS.union ufs applied
      in

      IMap.fold
        (fun scc_id members acc ->
           let blocks, _, ufs = closure ([], [], UFS.empty) scc_id in
           let node_defs = { blocks; ufs = UFS.elements ufs } in
           List.fold_left
             (fun acc { N.node_id } -> NI.Map.add node_id node_defs acc)
             acc
             members)
        defined_sccs
        NI.Map.empty
