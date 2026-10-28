(* This file is part of the Kind 2 model checker.

   Copyright (c) 2025 by the Board of Trustees of the University of Iowa

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

type error =
  | UnexpectedChar of Lib.position * char
  | SyntaxError of Lib.position
  | TypeError of MoxiTypeChecker.error
  | Unsupported of Lib.position * string

(* A well-sorted construct that kmoxi does not translate *)
exception Unsupported_feature of Lib.position * string

let pp_print_error ppf = function
  | UnexpectedChar (pos, c) ->
    Format.fprintf ppf "%a: error: unexpected character ‘%c’"
      Lib.pp_print_position pos c
  | SyntaxError pos ->
    Format.fprintf ppf "%a: syntax error" Lib.pp_print_position pos
  | TypeError (pos, kind) ->
    Format.fprintf ppf "%a: error: %s" Lib.pp_print_position pos
      (MoxiTypeChecker.error_message kind)
  | Unsupported (pos, msg) ->
    Format.fprintf ppf "%a: error: %s" Lib.pp_print_position pos msg

module A = MoxiAst
module ML = MoxiLexer
module MP = MoxiParser

module I = LustreIdent
module RI = Lib.ReservedIds

module SV = StateVar
module SVS = StateVar.StateVarSet
module SVM = StateVar.StateVarMap
module SVH = StateVar.StateVarHashtbl

module HS = HString
module HSS = HS.HStringSet
module HSM = HS.HStringMap

module TS = TransSys

let (let*) = Res.(>>=)

type system_variables =
{
  inputs: SV.t list;
  outputs: SV.t list;
  locals: SV.t list;
  internal: SV.t list
}

type system_check = TS.t SubSystem.t

type encoding =
{
  current_state: bool ;
  flags: bool
}

type check =
{
  systems: system_check list ;
  queries: (string * encoding) list
}

type input =
{
  systems: (TS.t * system_variables) HSM.t ;
  (* The definitions of the systems, by name *)
  system_defs: A.define_system_cmd HSM.t ;
  (* The checks, last first *)
  checks: check list ;
  (* The names of all the systems of the script, and the number of the next
     system of a check, for the names of the systems of the checks *)
  system_names: HSS.t ;
  next_check: int ;
  (* The logic set with set-logic, if any *)
  logic: string option ;
  (* Numerals denote reals, in a logic with reals and no integers *)
  real_numerals: bool ;
  (* The functions defined with define-fun: their symbols by name, and
     their definitions, last first *)
  funs: UfSymbol.t HSM.t ;
  fun_defs: TS.fun_def list ;
  (* The declared constants that the body of each function uses, directly
     or through the functions it applies, by the name of the function *)
  fun_constants: HSS.t HSM.t ;
  (* The enumeration sorts declared with declare-enum-sort, by name, and
     their values. An enumeration sort is a type of Kind 2 that stands for
     an integer range, one integer per value. *)
  enums: Type.t HSM.t ;
  enum_values: HSS.t ;
  (* The constants declared with declare-const, by name: each is a constant
     state variable, the same in every state and every system *)
  consts: SV.t HSM.t ;
  (* Their variables, and the ranges of those of an enumeration sort, last
     first *)
  const_vars: Var.t list ;
  const_constraints: Term.t list
}

let empty_input =
{
  systems = HSM.empty ;
  system_defs = HSM.empty ;
  checks = [] ;
  system_names = HSS.empty ;
  next_check = 0 ;
  logic = None ;
  real_numerals = false ;
  funs = HSM.empty ;
  fun_defs = [] ;
  fun_constants = HSM.empty ;
  enums = HSM.empty ;
  enum_values = HSS.empty ;
  consts = HSM.empty ;
  const_vars = [] ;
  const_constraints = []
}

(* The environment of the translation of a term *)
type term_env =
{
  scope: Scope.t ;
  (* The variables bound by the enclosing let binders, which shadow the
     state variables of the system *)
  lets: Var.t HSM.t ;
  (* The declarations and definitions read so far *)
  decls: input
}

(* The MoXI names of the functions defined with define-fun, by their
   symbols, which have fresh names (see [process_command]) *)
let moxi_names = UfSymbol.UfSymbolHashtbl.create 7

let moxi_name_of_uf uf = UfSymbol.UfSymbolHashtbl.find_opt moxi_names uf

(* The names of the subsystem calls, by the scope of the caller and the uid
   of the instance, since the instances of a transition system have none *)
let call_names : (Scope.t * int, string) Hashtbl.t = Hashtbl.create 7

(* Every call is named as it is built, so a missing name is a bug of kmoxi's
   rather than of the model: fail naming it, instead of with Not_found deep
   in whatever prints a response *)
let call_name caller inst =
  let scope = TS.scope_of_trans_sys caller in
  match Hashtbl.find_opt call_names (scope, inst.TS.uid) with
  | Some name -> name
  | None ->
    failwith
      (Format.asprintf "No name for the call %d of %a" inst.TS.uid
         Scope.pp_print_scope_internal scope)

let unsupported span msg =
  raise (Unsupported_feature (Lib.start_pos span, msg))

let parse_buffer lexbuf =
  try
    Ok (MP.script ML.token lexbuf)
  with
  | ML.Unexpected_Char c ->
    let pos = Lib.position_of_lexing lexbuf.lex_start_p in
    Error (UnexpectedChar (pos, c))
  | MP.Error ->
    let pos = Lib.position_of_lexing lexbuf.lex_start_p in
    Error (SyntaxError pos)

(* Parse and type check the script in a lexing buffer *)
let parse_and_check lexbuf =
  let* ast = parse_buffer lexbuf in
  match MoxiTypeChecker.check_script ast with
  | Ok () -> Ok ast
  | Error e -> Error (TypeError e)


let rec mk_subsystem map sys =
  let scope = TS.scope_of_trans_sys sys in
  let subsystems = TS.get_subsystems sys in
  let sub = {
    SubSystem.scope = scope;
    source = sys;
    opacity = Opacity.Transparent;
    has_contract = false;
    has_impl = true;
    rec_group = None;
    is_internal = false;
    has_modes = false;
    map;
    subsystems = subsystems |> List.map TS.scope_of_trans_sys;
  } in
  Scope.Hashtbl.add map scope sub;
  (* Assume no cycles between subsystems *)
  List.map (mk_subsystem map) subsystems |> ignore;
  sub

let hstring_of_symbol = snd
let string_of_symbol symbol = HString.string_of_hstring (snd symbol)

let rec type_of_sort enums A.{ id; parameters } =
  let _, symbol, indices = id in

  let name = string_of_symbol symbol in

  match HSM.find_opt (hstring_of_symbol symbol) enums with
  | Some ty -> ty
  | None ->
  if name = "Bool" then Type.t_bool
  else if name = "Int" then Type.t_int
  else if name = "Real" then Type.t_real
  else if name = "BitVec" then (
    match indices with
    | [NumericIndex (_, n)] -> Type.t_ubv (Numeral.to_int n)
    | _ -> failwith("Unexpected index for BitVec sort")
  )
  else if name = "Array" then (
    match parameters with
    | [idx_ty; elem_ty] ->
      Type.mk_array (type_of_sort enums elem_ty) (type_of_sort enums idx_ty)
    | _ -> failwith("Incorrect arity for Array sort")
  )
  else raise (Invalid_argument
    (Format.asprintf "Sort '%s' is not supported" name))

let mk_sys_scope ?(reserved=false) sys_name =
  if reserved then
    sys_name :: I.reserved_scope
  else
    sys_name :: I.user_scope

let mk_svar ?(reserved=false) enums sys_name is_input symbol sort =
  let name = string_of_symbol symbol in
  let scope = mk_sys_scope ~reserved sys_name in
  StateVar.mk_state_var
    ~is_input ~is_const:false ~for_inv_gen:true
    name scope (type_of_sort enums sort)

(* The engines bound the indices of an array by its index type, which must
   be a bit-vector type (see [bounds]). The elements are not constrained, so
   they cannot be of an enumeration sort, whose values are a range of the
   integers. *)
let rec check_array_indices span name ty =
  match Type.node_of_type ty with
  | Array (e, i) ->
    if not (Type.is_bitvector i || Type.is_ubitvector i) then
      unsupported span
        (Format.asprintf
           "kmoxi supports arrays indexed by bit-vectors only; %s has sort %a"
           name Type.pp_print_type ty);
    if Type.is_enum e then
      unsupported span
        (Format.sprintf
           "kmoxi does not support arrays of an enumeration sort, such as %s"
           name);
    check_array_indices span name e
  | _ -> ()

(* The constraint that a variable of an enumeration sort has one of its
   values *)
let enum_range ty v =
  let l, u = Type.bounds_of_enum ty in
  Term.mk_leq [Term.mk_num l; v; Term.mk_num u]

let mk_svars enums sys_name is_input sys_vars =
  match sys_vars with
  | None -> []
  | Some (_, sorted_vars) -> (
    List.fold_left 
      (fun acc (span, name, sort) ->
        let svar = mk_svar enums sys_name is_input name sort in
        check_array_indices span (string_of_symbol name)
          (SV.type_of_state_var svar);
        svar :: acc
      )
      []
      sorted_vars
  )

(* Widest bit-vector index for which an equality with a constant array is
   expanded (see [const_array_eq]): 2^8 conjuncts at most *)
let max_expanded_index_width = 8

(* The sort and value of a constant array term [((as const S) v)] *)
let const_array_of_ast = function
  | A.App (_, ((_, symbol, []), false, Some sort), [v]) -> (
    try
      let symb =
        GenericSMTLIBDriver.symbol_of_smtlib_atom (hstring_of_symbol symbol)
      in
      if Symbol.is_const_array symb then Some (sort, v) else None
    with Not_found -> None
  )
  | _ -> None

(* [const_array_eq a ty v] is the conjunction of [(select a i) = v] over every
   index [i] of the array type [ty], when its index sort is a bit-vector of at
   most [max_expanded_index_width] bits: it is equivalent to [a = ((as const
   ty) v)], by extensionality. Some solvers, such as Bitwuzla 0.9, do not
   support an equality over constant arrays under Boolean structure, which
   is where the engines put the initial-state constraint, and answer unknown;
   they support the expansion. *)
let const_array_eq a ty v =
  let width = Type.bitvectorsize (Type.index_type_of_array ty) in
  if width < 1 || width > max_expanded_index_width then None
  else
    let index i =
      Term.mk_ubv
        (Bitvector.num_to_ubv (Numeral.of_int width) (Numeral.of_int i))
    in
    List.init (1 lsl width) (fun i ->
      Term.mk_eq [Term.mk_select a (index i); v])
    |> Term.mk_and
    |> Option.some

(* The symbols that occur free in the term as variables, that is, not as
   function symbols, primed or indexed, and not bound by a let of the term,
   added to [acc] *)
let rec free_symbols bound acc = function
  | A.Constant _ -> acc
  | A.QualId ((_, s, []), false, _) ->
    let s = hstring_of_symbol s in
    if HSS.mem s bound then acc else HSS.add s acc
  | A.QualId _ -> acc
  | A.App (_, _, args) -> List.fold_left (free_symbols bound) acc args
  | A.Let (_, bindings, t) ->
    let acc =
      List.fold_left (fun acc (_, _, t) -> free_symbols bound acc t)
        acc bindings
    in
    let bound =
      List.fold_left (fun bound (_, s, _) -> HSS.add (hstring_of_symbol s) bound)
        bound bindings
    in
    free_symbols bound acc t

(* The declared constants that a term uses, directly or through the
   functions it applies, outside the symbols [bound] by lets or as
   parameters, added to [acc] *)
let rec constants_of_term decls bound acc = function
  | A.Constant _ -> acc
  | A.QualId ((_, s, _), _, _) ->
    let s = hstring_of_symbol s in
    if HSS.mem s bound then acc
    else if HSM.mem s decls.consts then HSS.add s acc
    else (
      match HSM.find_opt s decls.fun_constants with
      | Some consts -> HSS.union consts acc
      | None -> acc
    )
  | A.App (_, ((_, f, _), _, _), args) ->
    let acc =
      match HSM.find_opt (hstring_of_symbol f) decls.fun_constants with
      | Some consts -> HSS.union consts acc
      | None -> acc
    in
    List.fold_left (constants_of_term decls bound) acc args
  | A.Let (_, bindings, t) ->
    let acc =
      List.fold_left (fun acc (_, _, t) -> constants_of_term decls bound acc t)
        acc bindings
    in
    let bound =
      List.fold_left (fun bound (_, s, _) -> HSS.add (hstring_of_symbol s) bound)
        bound bindings
    in
    constants_of_term decls bound acc t

(* The bindings of the lets of a chain of directly nested lets, outermost
   first, and the term innermost *)
let rec let_chain acc = function
  | A.Let (_, bindings, t) ->
    let_chain (List.map (fun (_, s, t) -> s, t) bindings :: acc) t
  | t -> List.rev acc, t

(* The chain of lets [chain] (see [let_chain]) split into segments by
   dependency level, see [LetChain.segments] *)
let let_segments chain =
  LetChain.segments ~name:hstring_of_symbol
    ~free:(free_symbols HSS.empty HSS.empty) chain

(* Translate a term in the environment [env] *)
let rec kind2_term env = function
  | A.Constant c -> (
    match c with
    | True -> Term.mk_true ()
    | False -> Term.mk_false ()
    | Numeral (_, n) ->
      if env.decls.real_numerals then Term.mk_dec (Decimal.of_big_int (Numeral.to_big_int n))
      else Term.mk_num n
    | Decimal (_, d) -> Term.mk_dec d
    | Bitvector (_, b) -> Term.mk_ubv b
  )
  | A.QualId ((_, symbol, (_ :: _ as indices)), false, _)
    when MoxiTypeChecker.bv_literal (string_of_symbol symbol) indices <> None -> (
    (* A bit-vector constant [(_ bvN m)]: the type checker has checked that
       the value fits the width *)
    let value, width =
      Option.get (MoxiTypeChecker.bv_literal (string_of_symbol symbol) indices)
    in
    Term.mk_ubv (Bitvector.num_to_ubv width value)
  )
  | A.QualId ((_, symbol, []), false, _)
    when HSM.mem (hstring_of_symbol symbol) env.lets ->
    Term.mk_var (HSM.find (hstring_of_symbol symbol) env.lets)
  | A.QualId (id, is_prime, _) -> (
    let _, symbol, indices = id in
    let scope = env.scope in

    if indices <> [] then
      failwith("Unexpected indexed identifier") ;

    let name = string_of_symbol symbol in
    
    try
      let svar =  
        StateVar.state_var_of_string (name, scope)
      in
      let offset =
        if is_prime then TS.trans_base
        else TS.init_base
      in
      let var = 
        Var.mk_state_var_instance svar offset
      in
      Term.mk_var var
    with Not_found -> (
      try
        if is_prime then raise Not_found ;
        let s = hstring_of_symbol symbol in
        match HSM.find_opt s env.decls.consts with
        | Some sv -> Term.mk_var (Var.mk_const_state_var sv)
        | None when HSS.mem s env.decls.enum_values -> Term.mk_constr name
        | None ->
        match HSM.find_opt s env.decls.funs with
        | Some uf -> Term.mk_uf uf []
        | None -> Term.mk_uf (UfSymbol.uf_symbol_of_string name) []
      with Not_found -> (
        failwith(Format.sprintf "Invalid constant symbol '%s'" name)
      )
    )
  )
  | A.App (_, ((_, symbol, []), false, _), [x; y]) as t
    when string_of_symbol symbol = "="
      && (const_array_of_ast x <> None || const_array_of_ast y <> None) -> (
    (* An equality with a constant array: expand it if the index sort
       allows, otherwise translate it as any other application *)
    let a, (sort, v) =
      match const_array_of_ast x, const_array_of_ast y with
      | _, Some c -> x, c
      | Some c, _ -> y, c
      | None, None -> assert false
    in
    match
      const_array_eq (kind2_term env a) (type_of_sort env.decls.enums sort)
        (kind2_term env v)
    with
    | Some expanded -> expanded
    | None -> kind2_app env t
  )
  | A.App _ as t -> kind2_app env t
  | A.Let _ as t ->
    (* A chain of directly nested lets, as translators write a formula with
       shared subterms, is translated as a few lets of independent bindings
       (see [let_segments]), built at once with [Term.mk_let_chain]. Built
       one at a time, thousands of lets take a time that grows faster than
       the square of their number, since Kind 2 builds a let by traversing
       its body; and each subterm of a long chain of lets keeps the indexes
       of the bound variables it contains, a memory that grows with the
       square of the length of the chain *)
    let chain, body = let_chain [] t in
    kind2_let_segments env (let_segments chain) body

(* Translate the let segments [segments] (see [let_segments]) with the term
   [body] innermost. The bindings of a let are simultaneous: their terms
   are translated in the scope of the lets before it, and the variables
   they bind, free variables named after them, shadow state and let-bound
   variables of the same name in the lets after it and in [body]. The
   bindings of a segment are then bound by one let per level, the lowest
   outermost, so that a binding is in the scope of those it depends on,
   and the lets of all segments are built as one chain *)
and kind2_let_segments env segments body =
  let env, levels =
    List.fold_left (fun (env, levels) segment ->
      let env, bindings =
        List.fold_left (fun (env, acc) lets ->
          let bindings =
            lets |> List.map (fun (s, level, t) ->
              let term' = kind2_term env t in
              let var =
                Var.mk_free_var (hstring_of_symbol s) (Term.type_of_term term')
              in
              s, level, var, term'
            )
          in
          let lets =
            List.fold_left (fun lets (s, _, var, _) ->
              HSM.add (hstring_of_symbol s) var lets)
              env.lets bindings
          in
          { env with lets }, List.rev_append bindings acc
        ) (env, []) segment
      in
      (* The bindings of each level, in their order *)
      let depth = List.fold_left (fun d (_, l, _, _) -> max d l) 0 bindings in
      let at_level = Array.make depth [] in
      List.iter (fun (_, l, var, term') ->
        at_level.(l - 1) <- (var, term') :: at_level.(l - 1))
        bindings;
      let levels =
        Array.fold_left (fun levels b -> if b = [] then levels else b :: levels)
          levels at_level
      in
      env, levels
    ) (env, []) segments
  in
  Term.mk_let_chain (List.rev levels) (kind2_term env body)

(* The width of a bit-vector term *)
and bv_width t = Type.bitvectorsize (Term.type_of_term t)

(* The bits [i] to [j] of [t], both included *)
and bv_extract i j t =
  Term.mk_bvextract (Numeral.of_int i) (Numeral.of_int j) t

(* The bit-vector operators of SMT-LIB that Kind 2 has no symbol for,
   defined as in the FixedSizeBitVectors theory from the ones it has; the
   type checker has established the arities and the sorts. Each definition
   mentions its operands once, so that the terms stay linear in the size of
   the model: Kind 2 prints terms to the solvers without sharing *)
and kind2_bv_app name args =
  match name, args with
  | "bvnand", [a; b] -> Some (Term.mk_bvnot (Term.mk_bvand [a; b]))
  | "bvnor", [a; b] -> Some (Term.mk_bvnot (Term.mk_bvor [a; b]))
  | "bvxnor", [a; b] -> Some (Term.mk_bvnot (Term.mk_bvxor [a; b]))
  | "bvcomp", [a; b] ->
    Some (Term.mk_ite (Term.mk_eq [a; b])
      (Term.mk_ubv (Bitvector.one 1)) (Term.mk_ubv (Bitvector.zero 1)))
  | "bvsmod", [s; t] -> Some (Term.mk_bvsmod [s; t])
  | _ -> None

(* The indexed bit-vector operators of SMT-LIB, given their numeral
   indices; [extract], [sign_extend] and [zero_extend] are symbols of
   Kind 2, the others are defined from them and [concat] *)
and kind2_indexed_bv_app name indices args =
  match name, indices, args with
  | "extract", [i; j], [t] -> Some (bv_extract i j t)
  | "sign_extend", [i], [t] -> Some (Term.mk_bvsignext (Numeral.of_int i) t)
  | "zero_extend", [i], [t] -> Some (Term.mk_bvzeroext (Numeral.of_int i) t)
  | "repeat", [i], [t] ->
    (* [i] copies of [t], [i] being positive, by doubling: the term has
       log2 [i] concatenations, each of a term shared with itself, rather
       than [i] - 1 of ever wider terms *)
    let rec copies i =
      if i = 1 then t
      else
        let half = copies (i / 2) in
        let even = Term.mk_bvconcat half half in
        if i mod 2 = 0 then even else Term.mk_bvconcat even t
    in
    Some (copies i)
  | ("rotate_left" | "rotate_right"), [i], [t] ->
    (* Rotating by the width is the identity; a rotation to the left by [k]
       bits moves the [m - k] low bits up, and the [k] high bits down *)
    let m = bv_width t in
    let k = if name = "rotate_left" then i mod m else (m - i mod m) mod m in
    if k = 0 then Some t
    else Some (Term.mk_bvconcat (bv_extract (m - k - 1) 0 t)
                 (bv_extract (m - 1) (m - k) t))
  | _ -> None

(* Translate a function application *)
and kind2_app env = function
  | A.App (span, (id, is_prime, sort), args) -> (
    let args = List.map (kind2_term env) args in

    let _, symbol, indices = id in

    let numeral_index = function
      | A.NumericIndex (_, n) -> Numeral.to_int n
      | A.SymbolicIndex _ -> raise Not_found
    in

    try
      if is_prime then raise Not_found ;
      match indices with
      | [] when HSM.mem (hstring_of_symbol symbol) env.decls.funs ->
        (* A defined function, which the solvers are given the definition
           of *)
        Term.mk_uf (HSM.find (hstring_of_symbol symbol) env.decls.funs) args
      | [] when string_of_symbol symbol = "!=" ->
        (* The disequality of MoXI *)
        Term.mk_not (Term.mk_eq args)
      | [] -> (
        match kind2_bv_app (string_of_symbol symbol) args with
        | Some t -> t
        | None ->
          let symb =
            GenericSMTLIBDriver.symbol_of_smtlib_atom (hstring_of_symbol symbol)
          in
          if Symbol.is_const_array symb then (
            match sort with
            | Some sort -> (
              match args with
              | [v] ->
                Term.mk_const_array (type_of_sort env.decls.enums sort) v
              | _ -> failwith("Incorrect number of arguments for const function")
            )
            | None -> failwith("Couldn't determine sort for const function")
          )
          else
            Term.mk_app symb args
      )
      | _ -> (
        match
          kind2_indexed_bv_app (string_of_symbol symbol)
            (List.map numeral_index indices) args
        with
        | Some t -> t
        | None -> raise Not_found
      )
    with Not_found -> (
      (* The type checker has accepted the symbol: it is one of the theories
         that kmoxi does not translate *)
      raise (Unsupported_feature (Lib.start_pos span,
        Format.sprintf "kmoxi does not support the function symbol '%s'"
          (MoxiTypeChecker.string_of_indexed_id (string_of_symbol symbol)
             indices)))
    )
  )
  | A.Constant _ | A.QualId _ | A.Let _ -> assert false

let mk_subsystem_calls enums local_map sys_name init_flag systems subsys =
  let process_subsys_attr
    (subsystems, acc_svars, formulas, uid)
    A.{ loc; instance_name; system_name; variables } =
    
    let sub_name = hstring_of_symbol system_name in
    let sub, { inputs; outputs; locals; internal } =
      match HSM.find_opt sub_name systems with
      | Some s -> s
      | None -> assert false
    in
    let lifted_locals, save_locals =
      match HSM.find_opt sub_name local_map with
      | Some map -> 
        map |> List.map (fun (_, symb, sort) ->
          let name = string_of_symbol symb in
          let scope = mk_sys_scope sys_name in
          StateVar.mk_state_var
            ~is_input:false ~is_const:false ~for_inv_gen:true
            name scope (type_of_sort enums sort)
        ), false
      | None -> (
        locals |> List.map (fun sv ->
          let name = SV.name_of_state_var sv in
          let orig_scope = List.tl (SV.scope_of_state_var sv) in
          let instance_name = string_of_symbol instance_name in
          let scope = sys_name :: "ins" :: instance_name :: orig_scope in
          StateVar.mk_state_var
            ~is_input:false ~is_const:false ~for_inv_gen:true
            name scope (SV.type_of_state_var sv)
        ), true
      )
    in
    let lifted_internals =
      internal |> List.map (fun sv ->
        let name = SV.name_of_state_var sv in
        let orig_scope = List.tl (SV.scope_of_state_var sv) in
        let instance_name = string_of_symbol instance_name in
        let scope = sys_name :: "ins" :: instance_name :: orig_scope in
        StateVar.mk_state_var
          ~is_input:false ~is_const:false ~for_inv_gen:true
          name scope (SV.type_of_state_var sv)
      )
    in
    let lifted_svars =
      lifted_locals @ lifted_internals
    in
    let map_up, map_down =
      List.fold_left2 
        (fun (map_down, map_up) sv sv'->
          SVM.add sv' sv map_down,
          SVM.add sv sv' map_up
        )
        (SVM.empty, SVM.empty)
        (locals @ internal)
        (lifted_svars)
    in
    let io_svars =
      variables |> List.map (fun symb ->
        let scope = mk_sys_scope sys_name in
        try
          SV.state_var_of_string (string_of_symbol symb, scope)
        with
        | Not_found ->
          failwith (Format.sprintf "State variable not found!")
      )
    in
    let map_up, map_down =
      List.fold_left2
        (fun (map_down, map_up) sv sv' ->
          
          SVM.add sv' sv map_down,
          SVM.add sv sv' map_up
        )
        (map_down, map_up)
        io_svars
        (inputs @ outputs)
    in
    (* The subsystem's init flag is the caller's init flag: unlike a Lustre
       node call, a subsystem instance has no flag of its own, so every
       instance of a system maps the caller's flag down to the same callee
       flag. Code that picks one instance by the state variables of a
       property, like [TS.map_cex_prop_to_subsystem], must not be given a
       property that mentions the flag; MoXI properties never do. *)
    let sub_init_flag = TS.init_flag_state_var sub in
    let map_up = SVM.add sub_init_flag init_flag map_up in
    let map_down = SVM.add init_flag sub_init_flag map_down in
    Hashtbl.replace call_names ([sys_name], uid)
      (string_of_symbol instance_name) ;
    let inst =
      TS.{
        uid ;
        pos = Lib.start_pos loc;
        map_down ;
        map_up ;
        guard_clock = (fun _ t -> t);
        active = (fun _ -> Term.t_true);
        assumes = None
      }
    in
    let subsystems =
      subsystems |> HSM.update sub_name (function
        | Some (sub, instances) -> Some (sub, inst :: instances)
        | None -> Some (sub, [inst])
      )
    in
    (* Actual parameters, in the order of the subsystem's state variables:
       init flag first, then inputs, outputs, locals and internals *)
    let svars =
      init_flag :: io_svars @ lifted_svars
      |> List.map (fun sv ->
        let v = Var.mk_state_var_instance sv TS.init_base in
        Term.mk_var v
      )
    in
    let p_svars =
      List.map (fun t -> Term.bump_state Numeral.one t) svars
    in
    let init_f =
      Term.mk_uf (TS.init_uf_symbol sub) svars
    in
    let trans_f =
      Term.mk_uf (TS.trans_uf_symbol sub) (p_svars @ svars)
    in
    let init_fs, trans_fs = formulas in
    let formulas = (init_f :: init_fs, trans_f :: trans_fs) in
    let acc_svars =
      if save_locals then lifted_svars @ acc_svars
      else lifted_internals @ acc_svars
    in
    subsystems, acc_svars, formulas, uid+1
  in 
  let subsystems, lifted_svars, formulas, _ =
    List.fold_left process_subsys_attr (HSM.empty, [], ([],[]), 0) subsys
  in
  let subsystems =
    HSM.bindings subsystems |> List.map snd
  in
  subsystems, lifted_svars, formulas

(* The definitions, among [fun_defs] (last first), that [terms] apply,
   directly or through the bodies of other definitions, in definition
   order. A body applies only the functions defined before it, so one pass
   from the last definition to the first collects them all. *)
let applied_fun_defs fun_defs terms =
  let module UFS = UfSymbol.UfSymbolSet in
  let used =
    List.fold_left (fun acc t -> UFS.union (Term.uf_symbols_of_term t) acc)
      UFS.empty terms
  in
  List.fold_left
    (fun (used, acc) ((uf, _, body) as def) ->
       if UFS.mem uf used then
         UFS.union (Term.uf_symbols_of_term body) used, def :: acc
       else used, acc)
    (used, []) fun_defs
  |> snd

let rec bounds ty =
  let fixed_bound ty' =
    match Type.node_of_type ty' with
    | UBV s
    | BV s -> LustreExpr.mk_int_expr (Lib.power_of_two s |> Numeral.of_int)
    | _ -> failwith("Only arrays with a Bitvector index type are currently supported")
  in
  match Type.node_of_type ty with
  | Bool | Int | IntRange _ | Enum _ | Real | UBV _ | BV _ | Abstr _ -> []
  | Array (e, i) -> LustreExpr.Fixed (fixed_bound i) :: bounds e
  | Datatype _ | DatatypeRef _ -> failwith "MoXI input does not support algebraic datatypes"

(* The system of a definition. A system of a check has variables of kmoxi's
   own as well, [defs], each with the initial value it may have and its
   value in a transition, given the environment of the translation of the
   terms of the system. *)
let mk_system ?(defs=fun _ -> []) ?(local_map=HSM.empty) (input : input)
    (sys_def: A.define_system_cmd) =

  let sys_name_hs = hstring_of_symbol sys_def.A.name in
  let sys_name = HString.string_of_hstring sys_name_hs in

  let scope = [sys_name] in
  let init_flag = StateVar.mk_init_flag scope in

  let enums = input.enums in
  let input_svars = mk_svars enums sys_name true sys_def.A.input in
  let output_svars = mk_svars enums sys_name false sys_def.A.output in
  let local_svars = mk_svars enums sys_name false sys_def.A.local in

  let sys_scope = mk_sys_scope sys_name in
  let env = { scope = sys_scope; lets = HSM.empty; decls = input } in

  let def_svars, init_defs, trans_defs =
    List.fold_left
      (fun (def_svars, init_defs, trans_defs) (svar, (init, trans)) ->
        let init_defs =
          match init with
          | None -> init_defs
          | Some init -> (
            let var = Var.mk_state_var_instance svar TS.init_base in
            let eq = Term.mk_eq [Term.mk_var var; init] in
            eq :: init_defs
          )
        in
        let var' = Var.mk_state_var_instance svar TS.trans_base in
        let eq' = Term.mk_eq [Term.mk_var var'; trans] in
        svar :: def_svars, init_defs, eq' :: trans_defs
      )
      ([], [], [])
      (defs env)
  in

  let subsystems, subsys_svars, (subsys_init, subsys_trans) =
    mk_subsystem_calls enums local_map sys_name init_flag input.systems
      sys_def.A.subsys
  in

  let internal_svars =
    subsys_svars
    |> List.rev_append def_svars
  in

  (* The init flag is a state variable of the system: it must be declared
     to the solvers together with the other state variables, and it is the
     first formal parameter of the init and trans predicates *)
  let state_vars =
    internal_svars
    |> List.rev_append local_svars
    |> List.rev_append output_svars
    |> List.rev_append input_svars
    |> List.cons init_flag
  in

  (* The declared constants, which every system has, rather than passes to
     its subsystems *)
  let global_consts = List.rev input.const_vars in

  let global_constraints = List.rev input.const_constraints in

  (* The variables of an enumeration sort have one of its values, in every
     state; those of the subsystems are constrained by the subsystems *)
  let enum_ranges offset =
    List.rev_append input_svars (List.rev_append output_svars local_svars)
    |> List.filter (fun sv -> Type.is_enum (SV.type_of_state_var sv))
    |> List.map (fun sv ->
      enum_range (SV.type_of_state_var sv)
        (Term.mk_var (Var.mk_state_var_instance sv offset)))
  in

  let ufs = [] in (* TODO *)

  let init_formals =
    List.map (fun sv ->
      Var.mk_state_var_instance sv TS.init_base
    )
    state_vars
  in

  let init_uf_symbol =
    UfSymbol.mk_uf_symbol
      (Format.sprintf "%s_%s" RI.init_uf_string sys_name)
      (List.map Var.type_of_var init_formals)
      Type.t_bool
  in

  (* Init flag is true in the initial state *)
  let init_flag_init =
    Var.mk_state_var_instance init_flag TS.init_base |> Term.mk_var
  in
  let init_conj =
    init_flag_init :: enum_ranges TS.init_base @ init_defs @ subsys_init
  in
  let init_conj =
    if (sys_def.inv = A.Constant True) then init_conj
    else (kind2_term env sys_def.inv) :: init_conj
  in
  let init_conj =
    if (sys_def.init = A.Constant True) then init_conj
    else (kind2_term env sys_def.init) :: init_conj
  in
  let init_term = Term.mk_and init_conj in

  let trans_formals =
    List.map (fun sv ->
      Var.mk_state_var_instance sv TS.trans_base
    )
    state_vars
    @
    List.map (fun sv ->
      Var.mk_state_var_instance
        sv (TS.trans_base |> Numeral.pred)
    )
    (List.filter
      (fun sv -> not (StateVar.is_const sv)) state_vars)
  in

  let trans_uf_symbol =
    UfSymbol.mk_uf_symbol
      (Format.sprintf "%s_%s" RI.trans_uf_string sys_name)
      (List.map Var.type_of_var trans_formals)
      Type.t_bool
  in

  (* Init flag becomes and stays false after the initial state *)
  let init_flag_trans =
    Var.mk_state_var_instance init_flag TS.trans_base
    |> Term.mk_var |> Term.mk_not
  in
  let trans_conj =
    init_flag_trans :: enum_ranges TS.trans_base @ trans_defs @ subsys_trans
  in
  let trans_conj =
    if (sys_def.inv = A.Constant True) then trans_conj
    else
      let inv' = Term.bump_state Numeral.one (kind2_term env sys_def.inv) in
      inv' :: trans_conj
  in
  let trans_conj =
    if (sys_def.trans = A.Constant True) then trans_conj
    else (kind2_term env sys_def.trans) :: trans_conj
  in
  let trans_term = Term.mk_and trans_conj in

  let state_var_bounds = SVH.create 7 in

  (* The engines read the bounds of every array, the constants' included *)
  state_vars
  @ List.map Var.state_var_of_state_var_instance global_consts
  |> List.iter (fun sv ->
    SVH.add state_var_bounds sv (bounds (SV.type_of_state_var sv))
  );

  let sys, _ =
    TS.mk_trans_sys
      ~fun_defs:(applied_fun_defs input.fun_defs [init_term; trans_term])
      scope
      None (* instance_state_var *)
      init_flag
      state_vars
      SVS.empty (* unconstrained_inputs *)
      state_var_bounds
      global_consts
      global_constraints
      ufs
      init_uf_symbol
      init_formals
      init_term
      trans_uf_symbol
      trans_formals
      trans_term
      subsystems
      [] (* properties *)
      (None, []) (* mode_requires *)
      (Invs.empty ()) (* node_assumptions *)
      (* visible *)
      true 
  in

  let sys_vars = {
    inputs = List.rev input_svars;
    outputs = List.rev output_svars;
    locals = List.rev local_svars;
    internal = internal_svars;
  }
  in
  sys_name_hs, sys, sys_vars

let extract_vars = function
| None -> []
| Some (_, l) ->
  List.map (fun (_, s, _) -> s) l

let sort_of_name name =
  let sort_name = HString.mk_hstring name in
  let id =
    (Lib.dummy_span, (Lib.dummy_span, sort_name), [])
  in
  A.{
    id ;
    parameters = [] ;
  }

let bool_sort = sort_of_name "Bool"

let rec current_state_term = function
  | A.Constant _ -> true
  | QualId (_, is_prime, _) -> not is_prime
  | App (_, (_, is_prime, _), args) ->
    not is_prime &&
    List.for_all current_state_term args
  | Let (_, bindings, t) ->
    List.for_all (fun (_, _, t') -> current_state_term t') bindings &&
    current_state_term t

(* Copies of the system [name] and of the systems it calls, directly or not,
   without their initial conditions, added to [copies] by the names of the
   systems they copy: the systems a query with a :current condition checks,
   which replaces the initial condition of every system (MoXI paper, SPIN
   2024, Sect. 3.2). The invariants of the systems hold in the first state
   still. The copy of a system [S] is named [prefix_S], after a name that
   is the prefix of no system of the script. *)
let rec init_free_systems decls prefix copies name =
  if HSM.mem name copies then copies
  else
    let def = HSM.find name decls.system_defs in
    let copies =
      List.fold_left (fun copies sub ->
        init_free_systems decls prefix copies
          (hstring_of_symbol sub.A.system_name)
      ) copies def.A.subsys
    in
    let copy_name =
      Format.sprintf "%s_%s" prefix (HString.string_of_hstring name)
    in
    let def =
      { def with
        A.name = (fst def.A.name, HString.mk_hstring copy_name) ;
        init = A.Constant A.True }
    in
    let _, sys, svars = mk_system { decls with systems = copies } def in
    HSM.add name (sys, svars) copies

(* The declared constants that the system [name] and the systems it calls,
   directly or not, use *)
let rec system_constants decls name =
  let def = HSM.find name decls.system_defs in
  List.fold_left (fun acc sub ->
    HSS.union (system_constants decls (hstring_of_symbol sub.A.system_name))
      acc
  ) HSS.empty def.A.subsys
  |> fun acc ->
  List.fold_left (constants_of_term decls HSS.empty) acc
    [def.A.init; def.A.trans; def.A.inv]

(* The variable of kmoxi's own that records whether a :reachable condition
   of a query with several has held, in the system [sys_name]. Its scope is
   not that of the variable that encodes the condition of a query with only
   that one, which is named after the condition too. *)
let flag_svar sys_name symb =
  StateVar.mk_state_var ~is_input:false ~is_const:false ~for_inv_gen:true
    (string_of_symbol symb) (sys_name :: "held" :: I.reserved_scope)
    Type.t_bool

(* The elements of a list of conditions, or of symbols, with the first
   occurrence of each name only *)
let first_occurrences name l =
  List.fold_left (fun acc x ->
    if List.exists (fun y -> HS.equal (name y) (name x)) acc then acc
    else x :: acc
  ) [] l
  |> List.rev

let condition_name (_, ((_, s), _)) = s

(* The systems of a check-system, one per group of its queries with the
   same assumptions and the same initiality condition, with how each query
   is encoded, in the order of the script. A query is a property of the
   system of its group: the assumptions constrain the transitions of the
   system, and the initiality condition, or the initial condition of the
   checked system if there is none, its initial states. The system of a
   group is named [fresh_name ()], and so are the copies of the systems
   (see [init_free_systems]) for the groups with an initiality condition. *)
let mk_check decls fresh_name (check_cmd: A.check_system_cmd) =
  (* What the type checker accepts of a check-system but kmoxi does not
     translate *)
  let unsupported_cmd = unsupported check_cmd.A.loc in
  let conditions =
    check_cmd.A.attrs |> List.filter_map (function
      | A.FormulaAttr f -> Some f
      | A.QueryAttr _ | A.QueriesAttr _ -> None
    )
  in
  let condition s =
    List.find (fun c -> HS.equal (condition_name c) s) conditions
  in
  (* The queries of a :queries attribute are satisfied by the same values
     of the declared constants; as separate properties, each would have
     values of its own. They are separate queries if neither the checked
     system nor their conditions use a constant. *)
  check_cmd.A.attrs |> List.iter (function
    | A.QueriesAttr (span, (_ :: _ :: _ as qs)) ->
      let constants =
        List.concat_map snd qs
        |> List.fold_left (fun acc (_, s) ->
          let (_, (_, term)) = condition s in
          constants_of_term decls HSS.empty acc term
        ) (system_constants decls (hstring_of_symbol check_cmd.A.system_id))
      in
      if not (HSS.is_empty constants) then
        unsupported span
          "kmoxi does not support a :queries attribute with several \
           queries that use declared constants"
    | A.QueriesAttr _ | A.QueryAttr _ | A.FormulaAttr _ -> ()
  ) ;
  let queries = A.queries_of_attrs check_cmd.A.attrs in
  if queries = [] then
    unsupported_cmd "kmoxi requires a :query in every check-system" ;
  (* Each query, with its initiality condition, if any, its assumptions,
     and its reachability conditions *)
  let queries =
    queries |> List.map (fun (q, names) ->
      let named =
        first_occurrences snd names |> List.map (fun (_, s) -> condition s)
      in
      named |> List.iter (fun (ty, ((span, _), _)) ->
        if ty = A.Fairness then
          unsupported span
            "kmoxi does not support :fairness conditions (liveness queries)"
      ) ;
      let of_type ty =
        List.filter_map (fun (ty', c) -> if ty' = ty then Some c else None)
          named
      in
      let current = List.nth_opt (of_type A.Current) 0 in
      let assumptions =
        of_type A.Assumption
        |> List.sort (fun ((_, s), _) ((_, s'), _) -> HS.compare s s')
      in
      match of_type A.Reachable with
      | [] ->
        unsupported_cmd "kmoxi requires a query to name a :reachable condition"
      | reachables -> current, assumptions, (q, reachables)
    )
  in
  (* The groups of queries, in the order of their first queries *)
  let groups =
    let same_names = List.equal (fun ((_, s), _) ((_, s'), _) -> HS.equal s s') in
    List.fold_left (fun groups (current, assumptions, query) ->
      let same_group (current', assumptions', _) =
        same_names (Option.to_list current) (Option.to_list current')
        && same_names assumptions assumptions'
      in
      if List.exists same_group groups then
        List.map (fun ((c, a, qs) as group) ->
          if same_group group then c, a, query :: qs else group
        ) groups
      else (current, assumptions, [query]) :: groups
    ) [] queries
    |> List.rev_map (fun (c, a, qs) -> c, a, List.rev qs)
  in
  (* One set of copies for every group with an initiality condition *)
  let init_free_decls =
    lazy (
      let systems =
        init_free_systems decls (fresh_name ()) HSM.empty
          (hstring_of_symbol check_cmd.A.system_id)
      in
      { decls with systems }
    )
  in
  let mk_group_system (current, assumptions, queries) =
    let sys_name = fresh_name () in
    let decls =
      match current with
      | None -> decls
      | Some _ -> Lazy.force init_free_decls
    in
    let reserved_svar symb =
      mk_svar ~reserved:true decls.enums sys_name false symb bool_sort
    in
    let assumption_svars =
      List.map (fun (symb, _) -> reserved_svar symb) assumptions
    in
    (* The conditions of the queries with one, and of the queries with
       several, each once *)
    let single =
      queries
      |> List.filter_map (function (_, [c]) -> Some c | _ -> None)
      |> first_occurrences (fun ((_, s), _) -> s)
    in
    let flagged =
      queries
      |> List.concat_map (function (_, [_]) -> [] | (_, cs) -> cs)
      |> first_occurrences (fun ((_, s), _) -> s)
    in
    (* The variable of an assumption is its value in a transition. The
       variable of the condition of a query with only that one is its
       negation, in the transition to a state, and true in the initial
       state: the property of the query. A flag is whether its condition
       has held in a transition up to the state, false in the initial
       state. A condition over the current state holds in a transition if
       it holds in the state the transition is from: as Sect. 3.2 of the
       MoXI paper requires, the witness has a transition out of that state,
       in which the assumptions hold. *)
    let defs env =
      List.map2 (fun sv (_, term) -> sv, (None, kind2_term env term))
        assumption_svars assumptions
      @ List.map (fun (symb, term) ->
        reserved_svar symb,
        (Some Term.t_true, Term.mk_not (kind2_term env term))
      ) single
      @ List.map (fun (symb, term) ->
        let flag = flag_svar sys_name symb in
        let held = Term.mk_var (Var.mk_state_var_instance flag TS.init_base) in
        flag, (Some Term.t_false, Term.mk_or [held; kind2_term env term])
      ) flagged
    in
    let prop_var sv =
      Term.mk_var (Var.mk_state_var_instance sv TS.prop_base)
    in
    let props, encodings =
      queries |> List.map (fun (q, reachables) ->
        let prop_name = string_of_symbol q in
        let span, prop_term =
          match reachables with
          | [(symb, _)] -> fst symb, prop_var (reserved_svar symb)
          | _ ->
            fst q,
            reachables
            |> List.map (fun (symb, _) -> prop_var (flag_svar sys_name symb))
            |> Term.mk_and |> Term.mk_not
        in
        let encoding = {
          current_state =
            List.for_all (fun (_, term) -> current_state_term term) reachables ;
          flags = List.length reachables > 1
        }
        in
        Property.{
          prop_name ;
          prop_source = PropAnnot (Lib.start_pos span) ;
          prop_kind = Reachable None ;
          prop_term ;
          prop_status = PropUnknown ;
          prop_expr = None ;
        },
        (prop_name, encoding)
      )
      |> List.split
    in
    let loc = check_cmd.A.loc in
    let name =
      (Lib.dummy_span, HString.mk_hstring sys_name)
    in
    let input = check_cmd.A.input in
    let output = check_cmd.A.output in
    let local = check_cmd.A.local in
    let variables =
      let input_lst = extract_vars input in
      let output_lst = extract_vars output in
      input_lst @ output_lst
    in
    let local_map =
      let map =
        match check_cmd.local with
        | Some (_, l) -> l
        | None -> []
      in
      HSM.singleton
          (hstring_of_symbol check_cmd.system_id)
          map
    in
    let subsys =
      let instance_name =
        Lib.dummy_span, hstring_of_symbol check_cmd.system_id
      in
      [A.{
        loc = Lib.dummy_span;
        instance_name ;
        system_name = check_cmd.system_id ;
        variables ;
      }]
    in
    let init =
      match current with
      | None -> A.Constant True
      | Some (_, term) -> term
    in
    let trans = A.Constant True in
    let inv = A.Constant True in
    let sys_def = A.{
      loc ; name ; input ; output ; local ;
      subsys ; init ; trans ; inv ;
    }
    in
    let _, sys, _ =
      mk_system ~defs ~local_map decls sys_def
    in
    let sys_scope = TS.scope_of_trans_sys sys in
    let sys =
      let (_, init_eq, trans_eq) = TS.init_trans_open sys in
      let trans_ass =
        List.map (fun sv ->
          Term.mk_var (Var.mk_state_var_instance sv TS.trans_base)
        ) assumption_svars
        |> Term.mk_and
      in
      let trans_eq = Term.mk_and [trans_ass; trans_eq] in
      TS.set_subsystem_equations sys sys_scope init_eq trans_eq
    in
    let sys =
      TS.set_subsystem_properties sys sys_scope props
    in
    mk_subsystem (Scope.Hashtbl.create 7) sys, encodings
  in
  let systems, encodings = List.map mk_group_system groups |> List.split in
  let encodings = List.concat encodings in
  {
    systems ;
    queries =
      List.map (fun (_, _, (q, _)) ->
        let name = string_of_symbol q in
        name, List.assoc name encodings
      ) queries
  }

let process_command (input : input) = function
  | A.SetLogicCmd (_, logic) ->
    let logic = HString.string_of_hstring logic in
    { input with
      logic = Some logic ;
      real_numerals = MoxiTypeChecker.numerals_are_real logic }
  | A.DefineFunCmd def -> (
    (* The parameters are instances at offset zero of state variables in a
       scope of the function's own, as the formals of the predicates of a
       system are: that is the form the solvers are given formals in. The
       body refers to them as to let-bound variables, which shadow
       everything else, and may apply the functions defined before. *)
    let name = hstring_of_symbol def.A.name in
    (* The solvers are given the function under a fresh name, which no
       other symbol has and is a simple SMT-LIB symbol: the MoXI name may
       need quoting, or be the name of an internal symbol of Kind 2 *)
    let fresh_name =
      Format.sprintf "__kmoxi_fun_%d_%s" (List.length input.fun_defs)
        (String.map
           (fun c ->
              match c with
              | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> c
              | _ -> '_')
           (HString.string_of_hstring name))
    in
    (* The reserved scope of the fresh name, which the scope of no state
       variable of a system can be *)
    let fun_scope = mk_sys_scope ~reserved:true fresh_name in
    let params =
      List.map (fun (_, s, sort) ->
        let sv =
          StateVar.mk_state_var ~is_input:true ~is_const:false
            ~for_inv_gen:false (string_of_symbol s) fun_scope
            (type_of_sort input.enums sort)
        in
        hstring_of_symbol s, Var.mk_state_var_instance sv Numeral.zero
      ) def.A.params
    in
    let env = {
      scope = [];
      lets = List.fold_left (fun m (s, v) -> HSM.add s v m) HSM.empty params;
      decls = input;
    }
    in
    let body = kind2_term env def.A.body in
    let vars = List.map snd params in
    let uf =
      UfSymbol.mk_uf_symbol fresh_name
        (List.map Var.type_of_var vars) (type_of_sort input.enums def.A.sort)
    in
    UfSymbol.UfSymbolHashtbl.replace moxi_names uf
      (HString.string_of_hstring name) ;
    let constants =
      let params =
        List.fold_left (fun acc (s, _) -> HSS.add s acc) HSS.empty params
      in
      constants_of_term input params HSS.empty def.A.body
    in
    { input with
      funs = HSM.add name uf input.funs;
      fun_defs = (uf, vars, body) :: input.fun_defs;
      fun_constants = HSM.add name constants input.fun_constants }
  )
  | A.DeclareEnumSortCmd decl ->
    let values = List.map string_of_symbol decl.A.values in
    let ty = Type.mk_enum (string_of_symbol decl.A.name) values in
    { input with
      enums = HSM.add (hstring_of_symbol decl.A.name) ty input.enums ;
      enum_values =
        List.fold_left (fun acc (_, v) -> HSS.add v acc) input.enum_values
          decl.A.values }
  | A.DeclareConstCmd decl -> (
    let name = string_of_symbol decl.A.name in
    let ty = type_of_sort input.enums decl.A.sort in
    check_array_indices (fst decl.A.name) name ty;
    (* In a reserved scope of its own, which the scope of no system can be *)
    let sv =
      StateVar.mk_state_var ~is_input:false ~is_const:true ~for_inv_gen:true
        name (mk_sys_scope ~reserved:true "const") ty
    in
    let var = Var.mk_const_state_var sv in
    let constraints =
      if Type.is_enum ty then [enum_range ty (Term.mk_var var)] else []
    in
    { input with
      consts = HSM.add (hstring_of_symbol decl.A.name) sv input.consts ;
      const_vars = var :: input.const_vars ;
      const_constraints = List.rev_append constraints input.const_constraints }
  )
  | A.DefineSystemCmd sys_def -> (
    let name, sys, svars = mk_system input sys_def in
    { input with
      systems = HSM.add name (sys, svars) input.systems ;
      system_defs = HSM.add name sys_def input.system_defs }
  )
  | A.CheckSystemCmd check_cmd ->
    (* Each system of the check has a name of its own, which no other
       system of a check and no system of the script has, and is the prefix
       of the name of no system of the script, as it is of those of the
       copies of systems it checks: its scope, those of its variables, and
       the names of its predicates are its own *)
    let next = ref input.next_check in
    let rec fresh_name () =
      let name = Format.sprintf "__kmoxi_check_%d" !next in
      incr next ;
      let taken =
        HSS.exists (fun s ->
          let s = HString.string_of_hstring s in
          s = name || String.starts_with ~prefix:(name ^ "_") s
        ) input.system_names
      in
      if taken then fresh_name () else name
    in
    let check = mk_check input fresh_name check_cmd in
    { input with checks = check :: input.checks ; next_check = !next }

let process_ast ast =
  let system_names =
    List.fold_left (fun acc -> function
      | A.DefineSystemCmd sys -> HSS.add (hstring_of_symbol sys.A.name) acc
      | _ -> acc
    ) HSS.empty ast
  in
  List.fold_left process_command { empty_input with system_names } ast

(* Open a file and apply [f] to its parsed and type checked script; the
   channel is closed on every path, an error or exception included *)
let with_file filename f =
  let in_ch =
    match filename with
    | "" -> stdin
    | _ -> open_in filename
  in
  Fun.protect ~finally:(fun () -> close_in_noerr in_ch) (fun () ->
    try
      let lexbuf = Lexing.from_channel in_ch in
      Lib.set_lexer_filename lexbuf filename ;
      let* ast = parse_and_check lexbuf in
      Ok (f ast)
    with Unsupported_feature (pos, msg) -> Error (Unsupported (pos, msg))
  )

let check_file filename = with_file filename ignore

let of_file filename =
  with_file filename (fun ast ->
    let input = process_ast ast in
    (* In the order of the script, which the responses follow *)
    List.rev input.checks, input.logic)

let subsystems_of_checks checks =
  List.concat_map (fun (check : check) -> check.systems) checks
   
