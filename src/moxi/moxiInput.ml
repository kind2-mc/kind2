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

type input =
{
  systems: (TS.t * system_variables) HSM.t ;
  checks: (system_check * string list) list ;
  (* Numerals denote reals, in a logic with reals and no integers *)
  real_numerals: bool ;
  (* The functions defined with define-fun: their symbols by name, and
     their definitions, last first *)
  funs: UfSymbol.t HSM.t ;
  fun_defs: TS.fun_def list ;
  (* The enumeration sorts declared with declare-enum-sort, by name, and
     their values. An enumeration sort is a type of Kind 2 that stands for
     an integer range, one integer per value. *)
  enums: Type.t HSM.t ;
  enum_values: HSS.t ;
  (* The constants declared with declare-const, by name: each is a constant
     state variable, the same in every state and every system *)
  consts: SV.t HSM.t ;
  (* Their variables, in declaration order, and the ranges of those of an
     enumeration sort *)
  const_vars: Var.t list ;
  const_constraints: Term.t list
}

let empty_input =
{
  systems = HSM.empty ;
  checks = [] ;
  real_numerals = false ;
  funs = HSM.empty ;
  fun_defs = [] ;
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

  if HSM.mem (hstring_of_symbol symbol) enums then
    HSM.find (hstring_of_symbol symbol) enums
  else if name = "Bool" then Type.t_bool
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
  | A.Let (_, var_bindings, term) -> (
    (* The bindings are simultaneous: the bound terms are translated in the
       enclosing scope, and the variables they bind, free variables named
       after them, are in scope in the body only, where they shadow state
       and let-bound variables of the same name *)
    let bindings =
      var_bindings |> List.map (fun (_, s, t) ->
        let term' = kind2_term env t in
        let var = Var.mk_free_var (hstring_of_symbol s) (Term.type_of_term term') in
        s, var, term'
      )
    in
    let lets =
      List.fold_left (fun lets (s, var, _) -> HSM.add (hstring_of_symbol s) var lets)
        env.lets bindings
    in
    Term.mk_let (List.map (fun (_, var, term') -> var, term') bindings)
      (kind2_term { env with lets } term)
  )

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

let mk_system ?(defs=[]) ?(local_map=HSM.empty) (input : input)
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
      (fun (def_svars, init_defs, trans_defs) ((symb, sort), (init, trans)) ->
        let svar = mk_svar ~reserved:true enums sys_name false symb sort in
        let init_defs =
          match init with
          | None -> init_defs
          | Some init -> (
            let var = Var.mk_state_var_instance svar TS.init_base in
            let eq = Term.mk_eq [Term.mk_var var; kind2_term env init] in
            eq :: init_defs
          )
        in
        let var' = Var.mk_state_var_instance svar TS.trans_base in
        let eq' = Term.mk_eq [Term.mk_var var'; kind2_term env trans] in
        svar :: def_svars, init_defs, eq' :: trans_defs
      )
      ([], [], [])
      defs
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
  let global_consts = input.const_vars in

  let global_constraints = input.const_constraints in

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

  state_vars |> List.iter (fun sv ->
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

let negate term =
  let symb = (Lib.dummy_span, HString.mk_hstring "not") in
  let id = (Lib.dummy_span, symb, []) in
  A.App (Lib.dummy_span, (id, false, None), [term])

let mk_check decls (check_cmd: A.check_system_cmd) =
  let queries, formulas =
    List.partition A.is_query_attr check_cmd.A.attrs
  in
  (* What the type checker accepts of a check-system but kmoxi does not
     translate *)
  let unsupported = unsupported check_cmd.A.loc in
  match queries with
  | [] -> unsupported "kmoxi requires a :query in every check-system"
  | [q] -> (
    let query_name, query_symbols =
      match q with
      | A.QueryAttr (q_symb, symb_lst) -> (
        q_symb, List.fold_left
          (fun acc (_, symb_hs) -> HSS.add symb_hs acc)
          HSS.empty
          symb_lst
      )
      | _ -> assert false
    in
    let assumption_fs, reachable_fs =
      formulas |> List.filter_map (function
        | A.FormulaAttr attr ->
          let (_, ((_, s), _)) = attr in
          if HSS.mem s query_symbols then Some attr else None
        | _ -> None
      )
      |> List.partition (fun (ty, _) ->
        match ty with
        | A.Assumption -> true
        | A.Reachable -> false
      )
    in
    let loc = check_cmd.A.loc in
    let sys_name = "query" in
    let name =
      (Lib.dummy_span, HString.mk_hstring sys_name)
    in
    let defs, assumption_vars =
      List.fold_left
        (fun (defs, vars) (_, (symb, term)) ->
          let v =
            let svar =
              mk_svar ~reserved:true decls.enums sys_name false symb bool_sort
            in
            Var.mk_state_var_instance svar TS.trans_base
          in
          ((symb, bool_sort), (None, term)) :: defs, v :: vars
        )
        ([], [])
        assumption_fs
    in
    let defs, props, curr_state_props =
      match reachable_fs with
      | [] -> unsupported "kmoxi requires a query to name a :reachable condition"
      | [(_, (symb, term))] -> (
        let v =
          let svar =
            mk_svar ~reserved:true decls.enums sys_name false symb bool_sort
          in
          Var.mk_state_var_instance svar TS.prop_base
        in
        let p =
          Property.{
            prop_name = string_of_symbol query_name;
            prop_source = PropAnnot (Lib.start_pos (fst symb)) ;
            prop_kind = Reachable None;
            prop_term = Term.mk_var v;
            prop_status = PropUnknown ; 
            prop_expr = None ;
          }
        in
        let curr_state_props =
          if current_state_term term then [p.Property.prop_name]
          else []
        in
        ((symb, bool_sort), (Some (A.Constant A.True), negate term)) :: defs,
        [p], curr_state_props
      )
      | _ -> unsupported "kmoxi supports one :reachable condition per query"
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
    let init = A.Constant True in
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
        List.map Term.mk_var assumption_vars |> Term.mk_and
      in
      let trans_eq = Term.mk_and [trans_ass; trans_eq] in
      TS.set_subsystem_equations sys sys_scope init_eq trans_eq
    in
    let sys =
      TS.set_subsystem_properties sys sys_scope props
    in
    mk_subsystem (Scope.Hashtbl.create 7) sys, curr_state_props
  )
  | _ -> unsupported "kmoxi supports one :query per check-system"

let process_command (input : input) = function
  | A.SetLogicCmd (_, logic) ->
    { input with
      real_numerals =
        MoxiTypeChecker.numerals_are_real (HString.string_of_hstring logic) }
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
    { input with
      funs = HSM.add name uf input.funs;
      fun_defs = (uf, vars, body) :: input.fun_defs }
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
      const_vars = input.const_vars @ [var] ;
      const_constraints = input.const_constraints @ constraints }
  )
  | A.DefineSystemCmd sys_def -> (
    let name, sys, svars = mk_system input sys_def in
    { input with systems = HSM.add name (sys, svars) input.systems }
  )
  | A.CheckSystemCmd check_cmd ->
    let check = mk_check input check_cmd in
    { input with checks = check :: input.checks }

let process_ast ast =
  List.fold_left process_command empty_input ast

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
  with_file filename (fun ast -> (process_ast ast).checks)
   
