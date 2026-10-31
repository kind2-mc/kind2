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

(* Realizability of a function contract with temporal operators.

   A function is applied pointwise: its outputs at each instant are a
   function [f] of its inputs at that instant. Its contract [C], which may
   have temporal operators, is realizable by a function if there is a
   function [f] such that, for every input stream [s], the streams [s] and
   [f(s)] satisfy [C]. This is stronger than the realizability of [C] by a
   reactive component, which the realizability check decides, since the
   output of such a component may depend on the past inputs: the contract
   [guarantee y = (0 -> pre x)] is realizable by a node, not by a function.
   Both coincide when the contract has no state.

   The check is counterexample-guided. It keeps a finite set [S] of input
   traces, and asks whether some function satisfies the contract on each
   of them: the outputs at each instant are an uninterpreted function [u]
   of the inputs at that instant, shared by all the traces and instants.

   - If not, no function satisfies the contract on every input stream, and
     the traces are a certificate that the contract is unrealizable by a
     function.
   - Otherwise, a total function [f] consistent with the traces is taken:
     the simplest instance of a sequence of templates (a term of the
     contract, a constant, a linear combination of the inputs, a piecewise
     linear function) whose unknowns the query is solved for, since the
     points of the traces are concrete; or, when no template fits, a
     decision list whose guards and leaves are taken from the contract and
     the points of a model of [u]. The contract system is checked with its
     outputs defined by [f]. If its guarantees hold, [f] realizes the
     contract; otherwise, the inputs of the counterexamples are added to
     [S], and the check is repeated.

   The answers are sound both ways, but the check is incomplete: the
   generalization may not find a function that realizes the contract, and
   a contract with infinitely many output values may be unrealizable by a
   function while every finite set of traces is satisfiable. *)

module TSys = TransSys
module ISys = InputSystem
module N = LustreNode
module C = LustreContract
module D = LustreIndex
module E = LustreExpr
module NI = NodeId
module A = Analysis
module SVS = StateVar.StateVarSet
module VS = Var.VarSet

type trace = (StateVar.t * Model.value list) list

type result =
  | Realizable of (StateVar.t * Term.t) list
  | Unrealizable of (int * trace) list
  | Unknown

exception Unsupported of string

(* ********************************************************************** *)
(* Applicability                                                          *)
(* ********************************************************************** *)

(* Whether the contract of the function [node] has state. A function is
   only given a variable for its assumptions so far when its contract has
   state (see [LustreNodeGen]): the guarantees of a contract without state
   only depend on the assumptions at the current instant. *)
let contract_has_state ({ N.contract } as node) =
  N.is_function node
  &&
  match contract with
  | Some { C.sofar_assump = Some _ } -> true
  | _ -> false

let applies in_sys param =
  let scope = (A.info_of_param param).A.top in
  match NI.get_node_type (ISys.get_node_id in_sys scope) with
  | NI.Component when not (ISys.is_lemma in_sys scope) -> (
    match ISys.get_lustre_node in_sys scope with
    | Some node -> contract_has_state node
    | None -> false
  )
  | _ -> false

(* ********************************************************************** *)
(* Contract system                                                        *)
(* ********************************************************************** *)

(* The info of an analysis of the contract of the function with its outputs
   left free. The function is imported, so its outputs are undefined when it
   is not abstract. *)
let concrete_info param =
  let info = A.info_of_param param in
  { info with
    A.uid = A.get_uid () ;
    A.abstraction_map = Scope.Map.add info.A.top false info.A.abstraction_map }

(* The system of the contract with the outputs of the function left free,
   the assumptions assumed, and the guarantees as properties. Its signature
   is preserved: an input the contract does not mention is still an argument
   of the function. *)
let contract_system in_sys param =
  let sys, _ =
    ISys.trans_sys_of_analysis
      ~preserve_sig:true ~add_functional_constraints:false
      in_sys (A.ContractCheck (concrete_info param))
  in
  sys

(* The system of the contract with the outputs left free, without the
   assumptions assumed, for the refutation queries (see
   [constraints_of_trace]). Its guarantees are its properties. It is not
   sliced, so that it keeps the variable for the assumptions so far, which
   no guarantee depends on. *)
let query_system in_sys param =
  let sys, _ =
    ISys.trans_sys_of_analysis
      ~preserve_sig:true ~slice_nodes:`Off ~add_functional_constraints:false
      in_sys (A.ContractMonitor (concrete_info param))
  in
  sys

(* A copy of the contract system [sys] for an analysis, and the parameter of
   the analysis. The system an analysis runs on stores the invariants it
   proves, and the systems made from it with [TSys.set_subsystem_equations]
   share them with it: an analysis of one candidate function must not reuse
   those of another. *)
let fresh_copy param sys =
  let sys = TSys.copy sys in
  TSys.clear_all_invariants sys ;
  A.ContractCheck (concrete_info param), sys

(* The engines the contract system is checked with *)
let modules = [`BMC; `IND; `IC3]

(* The guarantees of the contract system. Its other properties, such as
   the reachability of the modes, do not constrain the outputs. *)
let guarantees sys =
  TSys.get_real_properties sys
  |> List.filter (fun { Property.prop_kind } -> prop_kind = Property.Invariant)

(* Check the properties of [sys] with [analyze], and return the
   counterexamples of the falsified ones, or [None] if a property is left
   undecided *)
let check_properties analyze in_sys param sys =
  (* A copy of a system keeps the status of its properties *)
  TSys.get_real_properties sys
  |> List.iter (fun { Property.prop_name } -> TSys.set_prop_unknown sys prop_name) ;
  let old_log_level = Lib.get_log_level () in
  Lib.set_log_level L_off ;
  (try analyze false modules in_sys param sys
   with e -> Lib.set_log_level old_log_level ; raise e) ;
  Lib.set_log_level old_log_level ;
  guarantees sys
  |> List.fold_left (fun acc { Property.prop_status } ->
    match acc, prop_status with
    | None, _ -> None
    | Some cexs, Property.PropFalse cex -> Some (cex :: cexs)
    | Some cexs, Property.PropInvariant _ -> Some cexs
    | Some _, _ -> None)
    (Some [])

(* ********************************************************************** *)
(* Traces and points                                                      *)
(* ********************************************************************** *)

let term_of_value = function
  | Model.Term t -> t
  | Model.Lambda _ | Model.Map _ ->
    raise (Unsupported "an input of the function is not of a scalar type")

(* Evaluate a closed term to a constant *)
let eval t =
  Eval.eval_term [] (Var.VarHashtbl.create 0) t |> Eval.term_of_value

(* A trace with its length, which a function without inputs needs *)
type sized_trace = int * trace

(* The restriction of a counterexample to the environment variables *)
let trace_of_cex env cex : sized_trace =
  let length =
    match cex with
    | (_, values) :: _ -> List.length values
    | [] -> 0
  in
  length,
  env |> List.map (fun sv ->
    match List.find_opt (fun (sv', _) -> StateVar.equal_state_vars sv sv') cex with
    | Some (_, values) -> sv, values
    | None ->
      raise (Unsupported "a counterexample has no value for an input"))

let length_of_trace ((n, _) : sized_trace) = n

(* The values of the variables [svs] of [trace] at instant [i] *)
let values_at ((_, trace) : sized_trace) svs i =
  svs |> List.map (fun sv ->
    let _, values =
      List.find (fun (sv', _) -> StateVar.equal_state_vars sv sv') trace
    in
    List.nth values i |> term_of_value |> eval)

let input_vars inputs =
  List.map (fun sv -> Var.mk_state_var_instance sv Numeral.zero) inputs

(* The value of [t] at the point [x] of the inputs *)
let eval_at inputs t x =
  eval (Term.apply_subst (List.combine (input_vars inputs) x) t)

(* ********************************************************************** *)
(* Templates                                                              *)
(* ********************************************************************** *)

(* A template of a candidate function for an output: a term over the
   current inputs and unknown constants, with a constraint on the unknowns.
   The refutation query is strengthened with the equality of the output to
   the template at every point of the traces. The points are concrete, so
   the equalities are linear in the unknowns, and a model of the query gives
   their values; the template with those values is the candidate for the
   output. The templates of an output are tried from the simplest, and the
   first one the traces allow is taken: the candidate is the simplest
   function of the shapes below that is consistent with the traces, rather
   than a decision list that fits their points.

   [term_of fe cs] is the term for the unknowns [cs], with the features (the
   terms over the inputs the template combines) mapped by [fe]: the identity
   gives the candidate, and the evaluation at a point gives the equality
   asserted in the query. *)
type template = {
  unknown_types : Type.t list ;
  term_of : (Term.t -> Term.t) -> Term.t list -> Term.t ;
  constraint_of : Term.t list -> Term.t ;
  finite : bool ;
  (* Whether the unknowns range over finite sets: a refuted candidate of a
     finite template is one of finitely many, and the template may be tried
     again (see [check]) *)
}

(* A term of the contract, or an input, as a template without unknowns *)
let template_of_term e =
  { unknown_types = [] ;
    term_of = (fun fe _ -> fe e) ;
    constraint_of = (fun _ -> Term.t_true) ;
    finite = true }

(* The values an unknown may take *)
type range =
  | Set of Term.t list (* One of the constants *)
  | Bound of int (* An integer within [-n; n] *)
  | Free

let is_finite = function Set _ | Bound _ -> true | Free -> false

(* The constant [n] of the numeric type [ty] *)
let num ty n =
  if Type.is_real ty then Term.mk_dec (Decimal.of_int n)
  else Term.mk_num_of_int n

let in_range ty range c =
  match range with
  | Set ks -> Term.mk_or (List.map (fun k -> Term.mk_eq [c; k]) ks)
  | Bound n -> Term.mk_and [Term.mk_leq [num ty (-n); c]; Term.mk_leq [c; num ty n]]
  | Free -> Term.t_true

(* The numeric features of the inputs as terms of type [ty], int or real: a
   numeric input, cast when it is an integer and [ty] is real, and a Boolean
   input as 0 or 1. A real input is no feature of an integer type. *)
let features inputs ty =
  let real = Type.is_real ty in
  input_vars inputs |> List.filter_map (fun v ->
    let t = Term.mk_var v in
    let vty = Var.type_of_var v in
    if Type.is_bool vty then Some (Term.mk_ite t (num ty 1) (num ty 0))
    else if Type.is_int vty || Type.is_int_range vty then
      Some (if real then Term.mk_to_real t else t)
    else if Type.is_real vty && real then Some t
    else None)

(* Whether [t] is the constant [n] *)
let is_num n t =
  (Term.is_numeral t && Numeral.(equal (Term.numeral_of_term t) (of_int n)))
  || (Term.is_decimal t && Decimal.(equal (Term.decimal_of_term t) (of_int n)))

let neg_num t =
  if Term.is_numeral t then Term.mk_num (Numeral.neg (Term.numeral_of_term t))
  else if Term.is_decimal t then Term.mk_dec (Decimal.neg (Term.decimal_of_term t))
  else Term.mk_minus [t]

(* [c0 + c1 f1 + ... + cn fn], without the terms whose coefficient is the
   constant 0, and with [f] and [- f] for the coefficients 1 and -1: the
   candidates are printed, and the unknowns are constants in them *)
let combine ty c0 coefs feats =
  let pos, neg =
    List.fold_left2 (fun (pos, neg) c f ->
      if is_num 0 c then pos, neg
      else if is_num 1 c then f :: pos, neg
      else if is_num (-1) c then pos, f :: neg
      else Term.mk_times [c; f] :: pos, neg)
      ([], []) coefs feats
  in
  let pos = List.rev pos and neg = List.rev neg in
  let pos = if is_num 0 c0 && (pos <> [] || neg <> []) then pos else c0 :: pos in
  let base =
    match pos with
    | [] -> num ty 0
    | [t] -> t
    | ts -> Term.mk_plus ts
  in
  List.fold_left (fun acc f -> Term.mk_minus [acc; f]) base neg

(* A linear combination [c0 + c1 f1 + ... + cn fn] of the features [feats]
   of type [ty], with the coefficients in [coefs] and the constant in
   [const] *)
let linear ty feats ~coefs ~const =
  { unknown_types = List.init (List.length feats + 1) (fun _ -> ty) ;
    term_of = (fun fe cs ->
      match cs with
      | c0 :: cs -> combine ty c0 cs (List.map fe feats)
      | [] -> assert false) ;
    constraint_of = (fun cs ->
      match cs with
      | c0 :: cs ->
        Term.mk_and (in_range ty const c0 :: List.map (in_range ty coefs) cs)
      | [] -> assert false) ;
    finite = is_finite coefs && is_finite const }

(* A linear atom [a1 f1 + ... + an fn <= b] over the features [feats] of
   type [ty], with the coefficients in {-1, 0, 1} and the threshold [b] in
   [threshold]: a threshold on an input, a comparison of two inputs, or,
   with no feature, a constant *)
let atom ty feats ~threshold =
  { unknown_types = List.init (List.length feats + 1) (fun _ -> ty) ;
    term_of = (fun fe cs ->
      match cs with
      | b :: cs -> (
        let feats = List.map fe feats in
        (* A threshold on a single feature reads better as [f <= b] or
           [f >= -b] *)
        match
          List.filter (fun (a, _) -> not (is_num 0 a)) (List.combine cs feats)
        with
        | [a, f] when is_num 1 a -> Term.mk_leq [f; b]
        | [a, f] when is_num (-1) a -> Term.mk_geq [f; neg_num b]
        | _ -> Term.mk_leq [combine ty (num ty 0) cs feats; b])
      | [] -> assert false) ;
    constraint_of = (fun cs ->
      match cs with
      | b :: cs ->
        Term.mk_and
          (in_range ty threshold b
           :: List.map (in_range ty (Set (List.map (num ty) [-1; 0; 1]))) cs)
      | [] -> assert false) ;
    finite = is_finite threshold }

(* One of the Boolean [terms], selected by Boolean unknowns of which
   exactly one is true: a guard taken from the contract *)
let choice terms =
  { unknown_types = List.map (fun _ -> Type.t_bool) terms ;
    term_of = (fun fe sels ->
      match
        List.find_opt (fun (s, _) -> Term.equal s Term.t_true)
          (List.combine sels terms)
      with
      | Some (_, g) -> fe g
      | None ->
        Term.mk_or (List.map2 (fun s g -> Term.mk_and [s; fe g]) sels terms)) ;
    constraint_of = (fun sels ->
      let rec at_most_one = function
        | [] -> []
        | s :: rest ->
          List.map (fun s' -> Term.mk_not (Term.mk_and [s; s'])) rest
          @ at_most_one rest
      in
      Term.mk_and (Term.mk_or sels :: at_most_one sels)) ;
    finite = true }

(* [if g then t else e], with the unknowns of the three templates *)
let ite_template g t e =
  let ng = List.length g.unknown_types in
  let nt = List.length t.unknown_types in
  let split cs =
    let cg, cs = Lib.list_split ng cs in
    let ct, ce = Lib.list_split nt cs in
    cg, ct, ce
  in
  { unknown_types = g.unknown_types @ t.unknown_types @ e.unknown_types ;
    term_of = (fun fe cs ->
      let cg, ct, ce = split cs in
      Term.mk_ite (g.term_of fe cg) (t.term_of fe ct) (e.term_of fe ce)) ;
    constraint_of = (fun cs ->
      let cg, ct, ce = split cs in
      Term.mk_and [g.constraint_of cg; t.constraint_of ct; e.constraint_of ce]) ;
    finite = g.finite && t.finite && e.finite }

(* The subterms of [t] *)
let rec subterms acc t =
  let acc = t :: acc in
  match Term.destruct t with
  | Term.T.App (_, args) -> List.fold_left subterms acc args
  | Term.T.Var _ | Term.T.Const _ -> acc
  | exception _ -> acc

(* The numeric constants of the equations of [node], of type [ty], with
   the small constants: the constants of the templates. A constant of a
   candidate is most often one of the contract. *)
let constants node ty =
  let real = Type.is_real ty in
  let small =
    List.map (num ty) [-1; 0; 1; 2]
    @ (if real then [Term.mk_dec Decimal.(div one (of_int 2))] else [])
  in
  node.N.equations
  |> List.concat_map (fun (_, e) ->
    [ E.base_term_of_expr Numeral.zero (E.init_expr e) ;
      E.cur_term_of_expr Numeral.zero (E.step_expr e) ])
  |> List.fold_left subterms []
  |> List.filter (if real then Term.is_decimal else Term.is_numeral)
  |> List.append small
  |> List.sort_uniq Term.compare

(* The templates for the output [y], simplest first. A numeric output is a
   constant, a linear combination of the inputs with coefficients in
   {-1, 0, 1}, then larger, and a piecewise linear function with two, then
   three, then four pieces in a tree of depth two, selected by one of the
   Boolean [atoms] of the contract, or by a linear atom over the inputs. A
   Boolean output is a linear atom, then a conditional of atoms. The linear
   atoms are over the real features when an input is real, since a real
   input is no feature of an integer type.

   The constants are first those of the contract and small ones, so that
   the templates are finite and the first candidates simple; the templates
   with free constants come last. *)
let templates_of_output node atoms inputs y =
  let ty = StateVar.type_of_state_var y in
  let guard_ty =
    if List.exists
         (fun sv -> Type.is_real (StateVar.type_of_state_var sv)) inputs
    then Type.t_real else Type.t_int
  in
  let guard_feats = features inputs guard_ty in
  let guard_consts = constants node guard_ty in
  let guard () = atom guard_ty guard_feats ~threshold:(Set guard_consts) in
  let free_guard () = atom guard_ty guard_feats ~threshold:Free in
  (* Templates with a guard of the contract, when it has some *)
  let with_atoms f = if atoms = [] then [] else [f (fun () -> choice atoms)] in
  if Type.is_bool ty then
    [ guard () ]
    @ with_atoms (fun g -> ite_template (g ()) (guard ()) (guard ()))
    @ [ ite_template (guard ()) (guard ()) (guard ()) ;
        free_guard () ;
        ite_template (free_guard ()) (free_guard ()) (free_guard ()) ]
  else if Type.is_int ty || Type.is_int_range ty || Type.is_real ty then
    let ty = if Type.is_real ty then Type.t_real else Type.t_int in
    let feats = features inputs ty in
    let consts = constants node ty in
    let units = Set (List.map (num ty) [-1; 0; 1]) in
    let const = linear ty feats ~coefs:(Set [num ty 0]) ~const:(Set consts) in
    let lin = linear ty feats ~coefs:units ~const:(Set consts) in
    (* Larger coefficients: an integer in [-3; 3], or a constant of the
       contract *)
    let wide =
      linear ty feats
        ~coefs:(if Type.is_real ty then Set consts else Bound 3)
        ~const:(Set consts)
    in
    let free = linear ty feats ~coefs:Free ~const:Free in
    let pw2 g l = ite_template (g ()) (l ()) (l ()) in
    let pw3 g l = ite_template (g ()) (l ()) (ite_template (g ()) (l ()) (l ())) in
    (* A tree of depth two: the maximum of three inputs, for instance,
       needs a guard under each branch of the first *)
    let tree g l = ite_template (g ()) (pw2 g l) (pw2 g l) in
    [ const ; lin ]
    @ with_atoms (fun g -> pw2 g (fun () -> const))
    @ with_atoms (fun g -> pw2 g (fun () -> lin))
    @ [ wide ; pw2 guard (fun () -> lin) ]
    @ with_atoms (fun g -> pw3 g (fun () -> lin))
    @ [ pw3 guard (fun () -> lin) ; tree guard (fun () -> lin) ;
        free ; pw2 free_guard (fun () -> free) ; pw3 free_guard (fun () -> free) ]
  else []

(* ********************************************************************** *)
(* Refutation query                                                       *)
(* ********************************************************************** *)

(* The logic of the refutation query: that of the system, which is always
   inferred for a Lustre system, with uninterpreted functions for the
   outputs and linear arithmetic for the templates *)
let query_logic ~has_real = function
  | `Inferred l ->
    let l = List.fold_left (fun l f -> TermLib.FeatureSet.add f l) l
        TermLib.[UF; IA; LA] in
    `Inferred (if has_real then TermLib.FeatureSet.add TermLib.RA l else l)
  | `None | `SMTLogic _ -> assert false

(* The constraints of a trace starting at offset [base]: the system is
   unrolled along the trace, the environment has the values of the trace,
   the outputs are the uninterpreted functions [ufs] of the inputs, and the
   guarantees hold at each instant at which the assumptions [sofar] have
   held so far.

   The assumptions are not assumed by the system: they may depend on the
   previous values of the outputs, and a function that violates them on a
   trace is relieved of the guarantees from then on, rather than excluded.

   The contract does not depend on constant streams (see [check]). *)
let constraints_of_trace sys sofar env inputs ufs base trace =
  let n = length_of_trace trace in
  let at i = Numeral.of_int (base + i) in
  let var sv i = Term.mk_var (Var.mk_state_var_instance sv (at i)) in
  List.init n (fun i ->
    let unrolling =
      if i = 0 then TSys.init_of_bound None sys (at 0)
      else TSys.trans_of_bound None sys (at i)
    in
    let env_eqs =
      List.map2
        (fun sv v -> Term.mk_eq [var sv i; v])
        env (values_at trace env i)
    in
    let x = values_at trace inputs i in
    let out_eqs =
      List.map (fun (y, uf) -> Term.mk_eq [var y i; Term.mk_uf uf x]) ufs
    in
    let props =
      guarantees sys
      |> List.map (fun { Property.prop_term } ->
        Term.mk_implies [var sofar i; Term.bump_state (at i) prop_term])
    in
    unrolling :: env_eqs @ out_eqs @ props)
  |> List.flatten
  |> Term.mk_and

type query_result =
  | Points of
      (Term.t list * Term.t list) list
      * (StateVar.t * (Term.t * int option)) list
  (* The values of the outputs at the distinct inputs of the traces, and
     the candidates of the outputs a template fits, with the position of
     the template among those of the output (see [check]) *)
  | Refuted of sized_trace list
  (* A subset of the traces no function satisfies the contract on *)

(* Whether some function satisfies the contract of [sys] on each of the
   [traces] *)
let solve_query sys sofar env inputs outputs templates traces =
  let total = List.fold_left (fun acc t -> acc + length_of_trace t) 0 traces in
  let solver =
    SMTSolver.create_instance
      ~produce_models:true
      ~produce_unsat_assumptions:true
      (query_logic
         ~has_real:(List.exists
                      (fun sv -> Type.is_real (StateVar.type_of_state_var sv))
                      (inputs @ outputs))
         (TSys.get_logic sys))
      (Flags.Smt.solver ())
  in
  Fun.protect ~finally:(fun () -> SMTSolver.delete_instance solver) (fun () ->
    SMTSolver.trace_comment solver "Function realizability: refutation query" ;
    TSys.define_and_declare_of_bounds
      sys
      (SMTSolver.define_fun solver)
      ~define_rec:(SMTSolver.define_funs_rec solver)
      (SMTSolver.declare_fun solver)
      (SMTSolver.declare_sort solver)
      Numeral.zero (Numeral.of_int (max 0 (total - 1))) ;
    TSys.assert_global_constraints sys (SMTSolver.assert_term solver) ;
    let ufs =
      outputs |> List.map (fun y ->
        let uf =
          UfSymbol.mk_fresh_uf_symbol
            (List.map StateVar.type_of_state_var inputs)
            (StateVar.type_of_state_var y)
        in
        SMTSolver.declare_fun solver uf ;
        y, uf)
    in
    (* Each trace is asserted under an activation literal, so that the
       certificate can be minimized *)
    let actlits, _ =
      List.fold_left (fun (acc, base) trace ->
        let actlit = Actlit.fresh_actlit () in
        SMTSolver.declare_fun solver actlit ;
        let act = Actlit.term_of_actlit actlit in
        SMTSolver.assert_term solver
          (Term.mk_implies
             [act; constraints_of_trace sys sofar env inputs ufs base trace]) ;
        (act, trace) :: acc, base + length_of_trace trace)
        ([], 0) traces
    in
    let actlits = List.rev actlits in
    let points =
      traces
      |> List.concat_map (fun trace ->
        List.init (length_of_trace trace) (values_at trace inputs))
      |> List.sort_uniq (List.compare Term.compare)
    in
    let point_terms =
      points |> List.concat_map (fun x ->
        List.map (fun (_, uf) -> Term.mk_uf uf x) ufs)
    in
    let acts = List.map fst actlits in
    let is_sat lits =
      SMTSolver.check_sat_assuming solver (fun _ -> true) (fun _ -> false) lits
    in
    (* The values of the outputs in a model are arbitrary. Each output is
       made equal, at every point, to the first of its [templates] that the
       traces allow together with those chosen for the previous outputs, if
       any: the model then follows the template, whose unknowns it gives. *)
    let chosen =
      if not (is_sat acts) then []
      else
        List.fold_left (fun chosen (y, tmpls) ->
          let uf = List.assq y ufs in
          let kept = List.concat_map (fun (acts, _, _, _, _) -> acts) chosen in
          let allowed (idx, tmpl) =
            let cs =
              tmpl.unknown_types |> List.map (fun ty ->
                let c = UfSymbol.mk_fresh_uf_symbol [] ty in
                SMTSolver.declare_fun solver c ;
                Term.mk_uf c [])
            in
            let act = Actlit.fresh_actlit () in
            SMTSolver.declare_fun solver act ;
            let act = Actlit.term_of_actlit act in
            SMTSolver.assert_term solver
              (Term.mk_implies
                 [act;
                  Term.mk_and
                    (tmpl.constraint_of cs
                     :: (points |> List.map (fun x ->
                       Term.mk_eq
                         [Term.mk_uf uf x;
                          tmpl.term_of (fun f -> eval_at inputs f x) cs])))]) ;
            if is_sat (act :: kept @ acts) then (
              (* The simplest candidate of the template: as many of its
                 numeric unknowns as the traces allow are made zero, in
                 order, so that the candidate has few terms and the
                 candidates of a template are tried from the simplest *)
              let zeros =
                List.fold_left (fun zeros c ->
                  let ty = Term.type_of_term c in
                  if Type.is_bool ty then zeros
                  else
                    let z = Actlit.fresh_actlit () in
                    SMTSolver.declare_fun solver z ;
                    let z = Actlit.term_of_actlit z in
                    SMTSolver.assert_term solver
                      (Term.mk_implies [z; Term.mk_eq [c; num ty 0]]) ;
                    if is_sat (z :: zeros @ act :: kept @ acts) then z :: zeros
                    else zeros)
                  [] cs
              in
              Some (act :: zeros, y, cs, tmpl, idx))
            else None
          in
          match List.find_map allowed tmpls with
          | Some c -> c :: chosen
          | None -> chosen)
          [] templates
    in
    let unknowns = List.concat_map (fun (_, _, cs, _, _) -> cs) chosen in
    let sat = SMTSolver.check_sat_assuming_and_get_term_values solver
      (fun _ values ->
        let value t = List.assoc t values |> eval in
        let points =
          points |> List.map (fun x ->
            x, List.map (fun (_, uf) -> value (Term.mk_uf uf x)) ufs)
        in
        let candidates =
          chosen |> List.map (fun (_, y, cs, tmpl, idx) ->
            y, (tmpl.term_of Fun.id (List.map value cs), idx))
        in
        Ok (points, candidates))
      (fun solver -> Error (SMTSolver.get_unsat_core_lits solver))
      (List.concat_map (fun (acts, _, _, _, _) -> acts) chosen @ acts)
      (point_terms @ unknowns)
    in
    match sat with
    | Ok (points, candidates) -> Points (points, candidates)
    | Error core_lits ->
      (* Remove the traces the refutation does not need, starting from those
         of the unsat core *)
      let actlits =
        match
          List.filter
            (fun (act, _) -> List.exists (Term.equal act) core_lits)
            actlits
        with
        | [] -> actlits
        | core -> core
      in
      let is_unsat = function
        | [] -> false (* Every function satisfies the contract on no trace *)
        | acts ->
          SMTSolver.check_sat_assuming solver
            (fun _ -> false) (fun _ -> true) (List.map fst acts)
      in
      let core =
        List.fold_left (fun kept a ->
          let without = List.filter (fun a' -> a' != a) kept in
          if is_unsat without then without else kept)
          actlits actlits
      in
      Refuted (List.map snd core)
  )

(* ********************************************************************** *)
(* Generalization                                                         *)
(* ********************************************************************** *)

(* The subterms of the equations of [node] whose only variables are the
   current values of [inputs], with the current instant at offset zero *)
let contract_terms node inputs =
  let is_input_var v =
    Var.is_state_var_instance v
    && Numeral.equal (Var.offset_of_state_var_instance v) Numeral.zero
    && List.exists
         (StateVar.equal_state_vars (Var.state_var_of_state_var_instance v))
         inputs
  in
  node.N.equations
  |> List.concat_map (fun (_, e) ->
    [ E.base_term_of_expr Numeral.zero (E.init_expr e) ;
      E.cur_term_of_expr Numeral.zero (E.step_expr e) ])
  |> List.fold_left subterms []
  |> List.filter (fun t ->
    let vars = Term.vars_of_term t in
    not (VS.is_empty vars) && VS.for_all is_input_var vars)
  |> List.sort_uniq Term.compare

(* The guards of the decision lists: the Boolean terms of the contract over
   the inputs and the Boolean inputs, with their negations, and, for each
   numeric input, a threshold at each value of the points *)
let guards_of terms inputs points =
  let inputs_vars = input_vars inputs in
  let atoms =
    List.filter (fun t -> Type.is_bool (Term.type_of_term t)) terms
    @ List.filter_map (fun v ->
      if Type.is_bool (Var.type_of_var v) then Some (Term.mk_var v) else None)
      inputs_vars
  in
  let thresholds =
    List.mapi (fun k v ->
      let ty = Var.type_of_var v in
      if Type.is_int ty || Type.is_int_range ty || Type.is_real ty then
        points
        |> List.map (fun (x, _) -> List.nth x k)
        |> List.sort_uniq Term.compare
        |> List.map (fun c -> Term.mk_leq [Term.mk_var v; c])
      else [])
      inputs_vars
    |> List.flatten
  in
  atoms @ List.map Term.mk_not atoms @ thresholds

(* The leaves of the decision list of an output of type [ty]: the inputs
   and the terms of the contract of that type, and the values of the output
   at the points *)
let leaves_of terms inputs ty values =
  let fits t = Type.check_type (Term.type_of_term t) ty in
  List.filter fits (List.map Term.mk_var (input_vars inputs))
  @ List.filter fits terms
  @ List.sort_uniq Term.compare values

(* A decision list [if g1 then e1 elif ... else en] that has the value [b]
   at each point [(a, b)] of [points]. A guard selects some of the points
   not selected yet, and its leaf has their values. The guard of a single
   point, the conjunction of the equalities of the inputs to its values,
   always selects it, so a decision list is always found. *)
let decision_list inputs guards leaves points =
  let inputs_vars = input_vars inputs in
  let fits e (a, b) = Term.equal (eval_at inputs e a) b in
  let holds g (a, _) = Term.equal (eval_at inputs g a) Term.t_true in
  let cube (a, _) =
    Term.mk_and
      (List.map2 (fun v c -> Term.mk_eq [Term.mk_var v; c]) inputs_vars a)
  in
  let rec loop remaining rules =
    match List.find_opt (fun e -> List.for_all (fits e) remaining) leaves with
    | Some e ->
      List.fold_left (fun f (g, e') -> Term.mk_ite g e' f) e rules
    | None ->
      let candidates =
        List.map (fun g -> g, List.filter (holds g) remaining) guards
        @ List.map (fun p -> cube p, [p]) remaining
      in
      let best =
        List.fold_left (fun best (g, selected) ->
          if selected = [] then best
          else
            match List.find_opt (fun e -> List.for_all (fits e) selected) leaves with
            | None -> best
            | Some e ->
              match best with
              | Some (_, _, n) when n >= List.length selected -> best
              | _ -> Some (g, e, List.length selected))
          None candidates
      in
      match best with
      | None -> assert false
      | Some (g, e, _) ->
        let remaining = List.filter (fun p -> not (holds g p)) remaining in
        loop remaining ((g, e) :: rules)
  in
  loop points []

(* A total function with the values of the outputs at the [points] *)
let generalize node inputs outputs points candidates =
  let terms = contract_terms node inputs in
  List.mapi (fun k y ->
    match List.assq_opt y candidates with
    | Some (f, idx) -> y, (f, idx)
    | None ->
      let points_y = List.map (fun (a, b) -> a, List.nth b k) points in
      let guards = guards_of terms inputs points_y in
      let leaves =
        leaves_of terms inputs (StateVar.type_of_state_var y) (List.map snd points_y)
      in
      y, (decision_list inputs guards leaves points_y, None))
    outputs

(* The contract system with the outputs defined by [witness], and, if
   [restrict] is given, the inputs restricted to its points *)
let with_outputs ?restrict inputs sys witness =
  let scope = TSys.scope_of_trans_sys sys in
  let at off t = Term.bump_state off t in
  let eqs off =
    witness
    |> List.map (fun (y, f) ->
      Term.mk_eq [Term.mk_var (Var.mk_state_var_instance y off); at off f])
  in
  let restriction off =
    match restrict with
    | None -> []
    | Some points ->
      [ points
        |> List.map (fun x ->
          Term.mk_and
            (List.map2
               (fun v c -> Term.mk_eq [Term.mk_var v; c])
               (input_vars inputs) x))
        |> Term.mk_or
        |> at off ]
  in
  let constraints off = Term.mk_and (eqs off @ restriction off) in
  let _, init, trans = TSys.init_trans_open sys in
  TSys.set_subsystem_equations sys scope
    (Term.mk_and [init; constraints TSys.init_base])
    (Term.mk_and [trans; constraints TSys.trans_base])

(* ********************************************************************** *)
(* Check                                                                  *)
(* ********************************************************************** *)

(* Whether the contract of [node] depends on constant streams: the initial
   values of unguarded [pre] operators, or global free constants. They would
   be shared by all the traces of a refutation query, which would then remain
   satisfiable with values of the constants that fit the previous candidate,
   and the check would make no progress. Handling them requires a copy of
   the oracles for each trace, and the global constants as arguments of the
   function, which may depend on them. *)
let depends_on_constants { N.oracles; N.equations } =
  oracles <> []
  || List.exists (fun (_, e) ->
    [ E.base_term_of_expr Numeral.zero (E.init_expr e) ;
      E.cur_term_of_expr Numeral.zero (E.step_expr e) ]
    |> List.exists (fun t ->
      VS.exists Var.is_const_state_var (Term.vars_of_term t)))
    equations

let check analyze in_sys param =
  let scope = (A.info_of_param param).A.top in
  let node =
    match ISys.get_lustre_node in_sys scope with
    | Some node -> node
    | None -> assert false
  in
  try
    if depends_on_constants node then
      raise (Unsupported "the contract depends on constant streams") ;
    (* The contract system, which is only analyzed through copies, and the
       system the refutation queries unroll *)
    let sys = contract_system in_sys param in
    let qsys = query_system in_sys param in
    let sofar =
      match node.N.contract with
      | Some { C.sofar_assump = Some sv } -> sv
      | _ -> assert false (* See [applies] *)
    in
    let in_sys_vars = SVS.of_list (TSys.state_vars sys) in
    let present svs = List.filter (fun sv -> SVS.mem sv in_sys_vars) svs in
    let inputs = present (D.values node.N.inputs) in
    let outputs = present (D.values node.N.outputs) in
    let env = inputs in
    if List.exists
         (fun sv -> Type.is_array (StateVar.type_of_state_var sv))
         (inputs @ outputs)
    then raise (Unsupported "an input or output is of an array type") ;
    let traces_of_cexs = List.map (trace_of_cex env) in
    (* The templates of each output, in the order they are tried: its
       previous candidate, if any, which is kept while the traces allow it;
       the leaves of the decision lists that do not depend on the points (the
       inputs and the terms of the contract); then the templates with
       unknowns, by position, except the ones that gave a refuted candidate.
       A candidate that is refuted is not allowed by the trace of its
       counterexample, so a previous candidate that is still allowed was not
       the cause of the refutation: it is kept. The template of a previous
       candidate that is not kept is given up when its unknowns are free:
       it would otherwise give another candidate that fits the traces at
       every iteration, such as a larger constant. A finite template has
       finitely many candidates, each refuted at most once. *)
    let terms = contract_terms node inputs in
    let atoms =
      List.filter (fun t -> Type.is_bool (Term.type_of_term t)) terms
      @ List.filter_map
          (fun v ->
             if Type.is_bool (Var.type_of_var v) then Some (Term.mk_var v)
             else None)
          (input_vars inputs)
    in
    let leaves =
      outputs |> List.map (fun y ->
        y,
        List.map (fun e -> None, template_of_term e)
          (leaves_of terms inputs (StateVar.type_of_state_var y) []))
    in
    let indexed =
      outputs |> List.map (fun y ->
        y, List.mapi (fun i t -> Some i, t) (templates_of_output node atoms inputs y))
    in
    let templates prevs failed =
      outputs |> List.map (fun y ->
        let prev = List.assq_opt y prevs in
        let failed = try List.assq y failed with Not_found -> [] in
        let failed =
          match prev with
          | Some (_, Some i)
            when not (List.assq y indexed |> List.assoc (Some i)).finite ->
            i :: failed
          | _ -> failed
        in
        y,
        (match prev with
         | Some (f, idx) -> [idx, template_of_term f]
         | None -> [])
        @ List.assq y leaves
        @ List.filter
            (fun (i, _) -> match i with Some i -> not (List.mem i failed) | None -> true)
            (List.assq y indexed))
    in
    let check_with_outputs ?restrict witness =
      let param', sys' = fresh_copy param sys in
      check_properties analyze in_sys param'
        (with_outputs ?restrict inputs sys' witness)
    in
    (* A candidate is checked first with the inputs restricted to the points
       of the traces. A counterexample then goes through points whose
       outputs other traces already constrain, and is more likely to
       conflict with them: the values a model checker picks for the inputs
       of a counterexample would otherwise seldom repeat. A candidate is
       only found to realize the contract by the check without the
       restriction. *)
    let check_candidate points witness =
      match
        if inputs = [] then Some []
        else check_with_outputs ~restrict:(List.map fst points) witness
      with
      | Some (_ :: _) as cexs -> cexs
      | Some [] | None -> check_with_outputs witness
    in
    let rec loop traces iter prevs failed =
      if iter > Flags.Contracts.function_realizability_iter () then Unknown
      else
        match
          solve_query qsys sofar env inputs outputs (templates prevs failed) traces
        with
        | Refuted traces -> Unrealizable traces
        | Points (points, candidates) ->
          let candidates = generalize node inputs outputs points candidates in
          let witness = List.map (fun (y, (f, _)) -> y, f) candidates in
          KEvent.log L_info "Function realizability: candidate %d:@ %a" iter
            (Lib.pp_print_list
               (fun fmt (y, f) ->
                 Format.fprintf fmt "%a = %a"
                   StateVar.pp_print_state_var y
                   (ISys.pp_print_term_as_expr in_sys sys) f)
               ";@ ")
            witness ;
          match check_candidate points witness with
          | None -> Unknown
          | Some [] -> Realizable witness
          | Some cexs ->
            (* The templates of the previous candidates that were not kept *)
            let failed =
              List.fold_left (fun failed (y, (f, _)) ->
                match List.assq_opt y prevs with
                | Some (f', Some i)
                  when not (Term.equal f f')
                    && not (List.assq y indexed |> List.assoc (Some i)).finite ->
                  let failed_y = try List.assq y failed with Not_found -> [] in
                  (y, i :: failed_y) :: List.remove_assq y failed
                | _ -> failed)
                failed candidates
            in
            loop (traces @ traces_of_cexs cexs) (iter + 1) candidates failed
    in
    (* The initial traces are the inputs of the counterexamples of the
       guarantees with the outputs left free *)
    match check_with_outputs [] with
    | None -> Unknown
    | Some [] -> Realizable []
    | Some cexs -> loop (traces_of_cexs cexs) 1 [] []
  with Unsupported msg ->
    KEvent.log L_note
      "Realizability by a function was not checked: %s." msg ;
    Unknown

let pp_print_witness in_sys sys fmt witness =
  Format.fprintf fmt "@[<v>%a@]"
    (Lib.pp_print_list
       (fun fmt (y, f) ->
         Format.fprintf fmt "@[<hov 2>%s =@ %a@]"
           (StateVar.name_of_state_var y)
           (ISys.pp_print_term_as_expr in_sys sys) f)
       "@,")
    witness

(* The values of an input of a certificate *)
let pp_print_values fmt (sv, values) =
  let as_type = StateVar.type_of_state_var sv in
  Lib.pp_print_list (Model.pp_print_value ~as_type) " " fmt values

let pp_print_certificate_pt fmt traces =
  Format.fprintf fmt
    "@[<hov>No function satisfies the contract on all of the following \
     input traces, since the outputs of a function only depend on its \
     current inputs.@]@.@." ;
  List.iteri (fun i (n, trace) ->
    Format.fprintf fmt "@[<v 2>Conflicting input trace %d (%d step%s):%a@]@.@."
      (i + 1) n (if n = 1 then "" else "s")
      (fun fmt -> List.iter (fun (sv, values) ->
         Format.fprintf fmt "@,%a: %a"
           (E.pp_print_lustre_var false) sv pp_print_values (sv, values)))
      trace)
    traces

let pp_print_certificate_json fmt traces =
  let pp_input fmt (sv, values) =
    let as_type = StateVar.type_of_state_var sv in
    Format.fprintf fmt "{\"name\" : \"%a\", \"values\" : [%a]}"
      (E.pp_print_lustre_var false) sv
      (Lib.pp_print_list (Model.pp_print_value_json ~as_type) ", ") values
  in
  Format.fprintf fmt "[@[<v 1>%a@]]"
    (Lib.pp_print_list
       (fun fmt (n, trace) ->
         Format.fprintf fmt "{\"length\" : %d, \"inputs\" : [%a]}"
           n (Lib.pp_print_list pp_input ", ") trace)
       ",@,")
    traces

let pp_print_certificate_xml fmt traces =
  List.iter (fun (n, trace) ->
    Format.fprintf fmt "@,@[<v 2><ConflictingInputTrace length=\"%d\">%a@]@,</ConflictingInputTrace>"
      n
      (fun fmt -> List.iter (fun (sv, values) ->
         let as_type = StateVar.type_of_state_var sv in
         Format.fprintf fmt "@,<Input name=\"%a\">%a</Input>"
           (E.pp_print_lustre_var false) sv
           (Lib.pp_print_list (Model.pp_print_value_xml ~as_type) " ") values))
      trace)
    traces
