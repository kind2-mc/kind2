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

module A = MoxiAst
module HS = HString
module HSM = HS.HStringMap

(* ********************************************************************** *)
(* Sorts                                                                  *)
(* ********************************************************************** *)

type sort =
  | Bool
  | Int
  | Real
  | BitVec of int
  | Array of sort * sort

let rec pp_print_sort ppf = function
  | Bool -> Format.pp_print_string ppf "Bool"
  | Int -> Format.pp_print_string ppf "Int"
  | Real -> Format.pp_print_string ppf "Real"
  | BitVec n -> Format.fprintf ppf "(_ BitVec %d)" n
  | Array (i, e) ->
    Format.fprintf ppf "(Array %a %a)" pp_print_sort i pp_print_sort e

let string_of_sort = Format.asprintf "%a" pp_print_sort

let is_arith = function Int | Real -> true | _ -> false

let is_bitvec = function BitVec _ -> true | _ -> false

(* ********************************************************************** *)
(* Errors                                                                 *)
(* ********************************************************************** *)

type error_kind =
  | UnknownLogic of string
  | LogicAlreadySet
  | LogicAfterDefinition
  | UnknownSort of string
  | MalformedSort of string * string
  | SortNotInLogic of sort * string
  | NumeralNotInLogic of string
  | DecimalNotInLogic of string
  | BitvectorNotInLogic of string
  | BitvectorOutOfRange of string * int
  | SymbolNotInLogic of string * string
  | NonlinearTerm of string * string
  | UnboundVariable of string
  | UnknownFunction of string
  | UnknownIndexedIdentifier of string
  | PrimedLetVariable of string
  | PrimedNonVariable of string
  | PrimeNotAllowed of string * string
  | PrimedNonInput of string * string
  | Arity of string * string * int
  | ArgumentSort of string * int * sort * string
  | ExpectedBool of string * sort
  | AscriptionMismatch of sort * sort
  | ConstArrayWithoutSort
  | ConstArrayNotArraySort of sort
  | DuplicateLetBinding of string
  | SystemRedefined of string
  | UnknownSystem of string
  | SelfInstantiation of string
  | DuplicateInstance of string
  | DuplicateVariable of string
  | SubsystemArity of string * string * int * int
  | SubsystemArgumentSort of string * string * sort * string * sort
  | SubsystemOutputToInput of string * string * string
  | RenamingArity of string * string * int * int
  | RenamingSort of string * sort * string * sort
  | DuplicateFormula of string
  | DuplicateQuery of string
  | UnknownFormula of string * string

type error = Lib.position * error_kind

let plural n word = if n = 1 then word else word ^ "s"

let error_message = function
  | UnknownLogic l ->
    Format.sprintf "unknown or unsupported logic '%s'" l
  | LogicAlreadySet ->
    "the logic is already set; set-logic may occur only once"
  | LogicAfterDefinition ->
    "set-logic must precede every define-system and check-system command"
  | UnknownSort s ->
    Format.sprintf "unknown sort '%s'" s
  | MalformedSort (s, why) ->
    Format.sprintf "malformed sort '%s': %s" s why
  | SortNotInLogic (s, l) ->
    Format.sprintf "sort %s is not in logic %s" (string_of_sort s) l
  | NumeralNotInLogic l ->
    Format.sprintf "numerals are not in logic %s" l
  | DecimalNotInLogic l ->
    Format.sprintf "decimals are not in logic %s" l
  | BitvectorNotInLogic l ->
    Format.sprintf "bit-vector literals are not in logic %s" l
  | BitvectorOutOfRange (id, width) ->
    Format.sprintf "bit-vector literal %s does not fit in %d bits" id width
  | SymbolNotInLogic (f, l) ->
    Format.sprintf "symbol '%s' is not in logic %s" f l
  | NonlinearTerm (f, l) ->
    Format.sprintf
      "nonlinear application of '%s' in logic %s: at most one operand of a \
       multiplication, and the divisor of a division, may be non-constant" f l
  | UnboundVariable v ->
    Format.sprintf "unbound variable '%s'" v
  | UnknownFunction f ->
    Format.sprintf "unknown function symbol '%s'" f
  | UnknownIndexedIdentifier id ->
    Format.sprintf "unknown indexed identifier '%s'" id
  | PrimedLetVariable v ->
    Format.sprintf
      "'%s' is bound by a let and cannot be primed; only the state variables \
       of the system can" v
  | PrimedNonVariable f ->
    Format.sprintf
      "'%s' cannot be primed; only the state variables of the system can" f
  | PrimeNotAllowed (v, ctx) ->
    Format.sprintf
      "next-state variable %s' in %s, which must be a one-state formula over \
       the unprimed variables" v ctx
  | PrimedNonInput (v, ctx) ->
    Format.sprintf
      "next-state variable %s' in %s, where only input variables may be \
       primed" v ctx
  | Arity (f, expected, got) ->
    Format.sprintf "'%s' expects %s but is applied to %d %s"
      f expected got (plural got "argument")
  | ArgumentSort (f, i, actual, expected) ->
    Format.sprintf "argument %d of '%s' has sort %s; expected %s"
      i f (string_of_sort actual) expected
  | ExpectedBool (what, actual) ->
    Format.sprintf "%s has sort %s; expected Bool" what (string_of_sort actual)
  | AscriptionMismatch (actual, ascribed) ->
    Format.sprintf "term of sort %s is ascribed the sort %s"
      (string_of_sort actual) (string_of_sort ascribed)
  | ConstArrayWithoutSort ->
    "'const' must be qualified with the sort of the array, as in \
     ((as const (Array Int Bool)) true)"
  | ConstArrayNotArraySort s ->
    Format.sprintf "'const' is qualified with the sort %s, which is not an \
                    array sort" (string_of_sort s)
  | DuplicateLetBinding v ->
    Format.sprintf "variable '%s' is bound twice by the same let" v
  | SystemRedefined s ->
    Format.sprintf "system '%s' is already defined" s
  | UnknownSystem s ->
    Format.sprintf "unknown system '%s'" s
  | SelfInstantiation s ->
    Format.sprintf "system '%s' cannot have itself as a subsystem" s
  | DuplicateInstance n ->
    Format.sprintf "duplicate subsystem instance name '%s'" n
  | DuplicateVariable v ->
    Format.sprintf "duplicate variable '%s'" v
  | SubsystemArity (inst, sys, expected, got) ->
    Format.sprintf
      "subsystem %s: system %s has %d input and output %s but %d %s given"
      inst sys expected (plural expected "variable") got
      (if got = 1 then "is" else "are")
  | SubsystemArgumentSort (inst, actual, actual_sort, formal, formal_sort) ->
    Format.sprintf
      "subsystem %s: variable %s of sort %s is bound to %s, which has sort %s"
      inst actual (string_of_sort actual_sort) formal
      (string_of_sort formal_sort)
  | SubsystemOutputToInput (inst, actual, formal) ->
    Format.sprintf
      "subsystem %s: input variable %s is bound to the output %s; an output \
       of a subsystem must be bound to an output or local variable" inst
      actual formal
  | RenamingArity (kind, sys, declared, expected) ->
    Format.sprintf "%d %s %s declared but system %s has %d" declared kind
      (plural declared "variable") sys expected
  | RenamingSort (v, s, orig, orig_sort) ->
    Format.sprintf "variable %s has sort %s but renames %s, which has sort %s"
      v (string_of_sort s) orig (string_of_sort orig_sort)
  | DuplicateFormula f ->
    Format.sprintf "duplicate condition name '%s'" f
  | DuplicateQuery q ->
    Format.sprintf "duplicate query name '%s'" q
  | UnknownFormula (q, f) ->
    Format.sprintf "query %s refers to '%s', which names no condition of \
                    this check-system" q f

exception Type_error of error

let fail pos kind = raise (Type_error (pos, kind))

let fail_span span kind = fail (Lib.start_pos span) kind

(* ********************************************************************** *)
(* Logics                                                                 *)
(* ********************************************************************** *)

(* The theories and restrictions a logic name stands for *)
type logic = {
  name : string;
  arrays : bool;
  bitvectors : bool;
  ints : bool;
  reals : bool;
  linear : bool;
}

let logic_all = {
  name = "ALL";
  arrays = true; bitvectors = true; ints = true; reals = true; linear = false;
}

(* The logic a name stands for, following the structure of SMT-LIB logic
   names: an optional QF_ prefix, then A (arrays), UF, BV and DT in that
   order, then an arithmetic fragment *)
let logic_of_name name =
  let strip prefix s =
    if String.starts_with ~prefix s then
      Some (String.sub s (String.length prefix)
              (String.length s - String.length prefix))
    else None
  in
  let strip_opt prefix (s, l) f =
    match strip prefix s with Some r -> r, f l | None -> s, l
  in
  if name = "ALL" then Some logic_all
  else
    let none = {
      name; arrays = false; bitvectors = false; ints = false; reals = false;
      linear = true }
    in
    let rest = match strip "QF_" name with Some r -> r | None -> name in
    if rest = "AX" then Some { none with arrays = true }
    else
      let rest, l = strip_opt "A" (rest, none) (fun l -> { l with arrays = true }) in
      let rest, l = strip_opt "UF" (rest, l) Fun.id in
      let rest, l = strip_opt "BV" (rest, l) (fun l -> { l with bitvectors = true }) in
      let rest, l = strip_opt "DT" (rest, l) Fun.id in
      match rest with
      | "" -> Some l
      | "LIA" | "IDL" -> Some { l with ints = true }
      | "LRA" | "RDL" -> Some { l with reals = true }
      | "LIRA" -> Some { l with ints = true; reals = true }
      | "NIA" -> Some { l with ints = true; linear = false }
      | "NRA" -> Some { l with reals = true; linear = false }
      | "NIRA" -> Some { l with ints = true; reals = true; linear = false }
      | _ -> None

(* Numerals denote reals in a logic with reals and no integers *)
let numerals_are_real name =
  match logic_of_name name with
  | Some logic -> logic.reals && not logic.ints
  | None -> false

(* ********************************************************************** *)
(* Environment                                                            *)
(* ********************************************************************** *)

type var_kind = Input | Output | Local

(* Which state variables may be primed in the formula being checked *)
type priming =
  | NoPrime of string      (* None; the name of the formula, for errors *)
  | PrimeInputs of string  (* Inputs only *)
  | PrimeAll

type system = {
  inputs : (HS.t * sort) list;
  outputs : (HS.t * sort) list;
  locals : (HS.t * sort) list;
}

type env = {
  logic : logic;
  systems : system HSM.t;
  (* State variables of the current system or check *)
  vars : (var_kind * sort) HSM.t;
  (* Let-bound variables, with whether they are bound to a constant term *)
  lets : (sort * bool) HSM.t;
  priming : priming;
}

let str = HS.string_of_hstring

(* ********************************************************************** *)
(* Sorts                                                                  *)
(* ********************************************************************** *)

(* An identifier with its indices, as written: [(_ f i j)], or [f] with no
   indices *)
let string_of_indexed_id name indices =
  match indices with
  | [] -> name
  | _ ->
    Format.sprintf "(_ %s %s)" name
      (String.concat " " (List.map (function
         | A.NumericIndex (_, n) -> Numeral.string_of_numeral n
         | A.SymbolicIndex (_, s) -> str s) indices))

let rec string_of_ast_sort A.{ id = (_, (_, s), indices); parameters } =
  let name = string_of_indexed_id (str s) indices in
  match parameters with
  | [] -> name
  | _ ->
    Format.sprintf "(%s %s)" name
      (String.concat " " (List.map string_of_ast_sort parameters))

let check_sort_in_logic pos logic sort =
  let rec check = function
    | Bool -> ()
    | Int -> if not logic.ints then fail pos (SortNotInLogic (Int, logic.name))
    | Real -> if not logic.reals then fail pos (SortNotInLogic (Real, logic.name))
    | BitVec _ as s ->
      if not logic.bitvectors then fail pos (SortNotInLogic (s, logic.name))
    | Array (i, e) as s ->
      if not logic.arrays then fail pos (SortNotInLogic (s, logic.name));
      check i; check e
  in
  check sort

let rec sort_of_ast logic (A.{ id = (span, (_, s), indices); parameters } as ast) =
  let pos = Lib.start_pos span in
  let malformed why = fail pos (MalformedSort (string_of_ast_sort ast, why)) in
  let simple sort =
    if indices <> [] then malformed "the sort takes no indices"
    else if parameters <> [] then malformed "the sort takes no parameters"
    else sort
  in
  let sort =
    match str s with
    | "Bool" -> simple Bool
    | "Int" -> simple Int
    | "Real" -> simple Real
    | "BitVec" -> (
      if parameters <> [] then malformed "BitVec takes no parameters";
      match indices with
      | [A.NumericIndex (_, n)] ->
        if Numeral.(n <= zero) then malformed "the width must be positive"
        else if Numeral.(n > of_int max_int) then
          malformed "the width is too large"
        else BitVec (Numeral.to_int n)
      | _ -> malformed "BitVec takes one numeral index, the width"
    )
    | "Array" -> (
      if indices <> [] then malformed "Array takes no indices";
      match parameters with
      | [i; e] -> Array (sort_of_ast logic i, sort_of_ast logic e)
      | _ -> malformed "Array takes two sort parameters, index and element"
    )
    | _ -> fail pos (UnknownSort (string_of_ast_sort ast))
  in
  check_sort_in_logic pos logic sort;
  sort

(* ********************************************************************** *)
(* Terms                                                                  *)
(* ********************************************************************** *)

(* The sort of a term, and whether it is a constant term, one with no state
   variables, for the linearity restriction of the logic *)

let not_in_logic pos env f =
  fail pos (SymbolNotInLogic (f, env.logic.name))

(* The value and width of a bit-vector literal [(_ bvN m)], if the indexed
   identifier is one: a symbol [bv] followed by digits, with one numeral
   index, the width. The value may exceed the width: [bv_constant] checks it *)
let bv_literal name indices =
  match indices with
  | [A.NumericIndex (_, width)] when String.starts_with ~prefix:"bv" name ->
    let digits = String.sub name 2 (String.length name - 2) in
    if digits <> "" && String.for_all (fun c -> c >= '0' && c <= '9') digits
    then Some (Numeral.of_string digits, width)
    else None
  | _ -> None

(* Interpret a bit-vector constant [(_ bvN m)] *)
let bv_constant pos env name indices =
  let id = string_of_indexed_id name indices in
  match bv_literal name indices with
  | Some (value, width) when Numeral.(width > zero) ->
    if not env.logic.bitvectors then
      fail pos (BitvectorNotInLogic env.logic.name);
    if Numeral.(width > of_int max_int) then
      fail pos (UnknownIndexedIdentifier id);
    let width = Numeral.to_int width in
    let bound = Numeral.of_big_int (Big_int.power_int_positive_int 2 width) in
    if Numeral.(value >= bound) then fail pos (BitvectorOutOfRange (id, width));
    BitVec width
  | _ -> fail pos (UnknownIndexedIdentifier id)

(* The indices of an indexed identifier [id] as integers, all of which must
   be numerals *)
let numeric_indices pos id indices =
  List.map (function
    | A.NumericIndex (_, n) ->
      if Numeral.(n > of_int max_int) then
        fail pos (UnknownIndexedIdentifier id);
      Numeral.to_int n
    | A.SymbolicIndex _ -> fail pos (UnknownIndexedIdentifier id)
  ) indices

(* What an argument is expected to be: a description, or a sort with the
   role it has, such as the sort of another argument *)
type expected = Descr of string | SortAs of sort * string

let rec check_term env = function
  | A.Constant c -> (
    match c with
    | A.True | A.False -> Bool, true
    | A.Numeral ((span, _)) ->
      (* In a logic with integers numerals are integers; in one with reals
         only, they are reals *)
      if env.logic.ints then Int, true
      else if env.logic.reals then Real, true
      else fail_span span (NumeralNotInLogic env.logic.name)
    | A.Decimal ((span, _)) ->
      if env.logic.reals then Real, true
      else fail_span span (DecimalNotInLogic env.logic.name)
    | A.Bitvector ((span, b)) ->
      if env.logic.bitvectors then BitVec (Bitvector.length_of_bitvector b), true
      else fail_span span (BitvectorNotInLogic env.logic.name)
  )

  | A.QualId ((span, (_, s), indices), is_prime, ascription) -> (
    let pos = Lib.start_pos span in
    let name = str s in
    let sort, const =
      match indices with
      | _ :: _ ->
        if is_prime then fail pos (PrimedNonVariable name);
        bv_constant pos env name indices, true
      | [] -> (
        match HSM.find_opt s env.lets with
        | Some (sort, const) ->
          if is_prime then fail pos (PrimedLetVariable name);
          sort, const
        | None -> (
          match HSM.find_opt s env.vars with
          | Some (kind, sort) ->
            if is_prime then (
              match env.priming with
              | NoPrime ctx -> fail pos (PrimeNotAllowed (name, ctx))
              | PrimeInputs ctx when kind <> Input ->
                fail pos (PrimedNonInput (name, ctx))
              | PrimeInputs _ | PrimeAll -> ()
            );
            sort, false
          | None -> fail pos (UnboundVariable name)
        )
      )
    in
    check_ascription env pos sort ascription;
    sort, const
  )

  | A.App (span, ((id_span, (_, s), indices), is_prime, ascription), args) -> (
    let pos = Lib.start_pos span in
    let name = str s in
    if is_prime then fail (Lib.start_pos id_span) (PrimedNonVariable name);
    let args = List.map (check_term env) args in
    let const = List.for_all snd args in
    let sort =
      match indices with
      | [] -> (
        match name, ascription with
        | "const", Some sort -> (
          let sort = sort_of_ast env.logic sort in
          if not env.logic.arrays then not_in_logic pos env name;
          match sort with
          | Array (_, e) ->
            if List.length args <> 1 then
              fail pos (Arity (name, "1 argument", List.length args));
            check_args pos name [e] (List.map fst args);
            sort
          | _ -> fail pos (ConstArrayNotArraySort sort)
        )
        | "const", None -> fail pos ConstArrayWithoutSort
        | _ ->
          let sort = check_app pos env name args in
          check_ascription env pos sort ascription;
          sort
      )
      | _ ->
        let sort = check_indexed_app pos env name indices (List.map fst args) in
        check_ascription env pos sort ascription;
        sort
    in
    sort, const
  )

  | A.Let (_, bindings, body) -> (
    (* The bindings are simultaneous: each term is checked in the outer
       scope *)
    let lets =
      List.fold_left (fun lets (span, (_, s), term) ->
        if HSM.mem s lets then fail_span span (DuplicateLetBinding (str s));
        HSM.add s (check_term env term) lets
      ) HSM.empty bindings
    in
    let lets = HSM.union (fun _ _ inner -> Some inner) env.lets lets in
    check_term { env with lets } body
  )

and check_ascription env pos sort = function
  | None -> ()
  | Some ascribed ->
    let ascribed = sort_of_ast env.logic ascribed in
    if ascribed <> sort then fail pos (AscriptionMismatch (sort, ascribed))

(* Check the sorts of the arguments against a list of expected sorts; the
   arity must have been checked *)
and check_args pos f expected args =
  List.iteri (fun i (arg, sort) ->
    if arg <> sort then
      fail pos (ArgumentSort (f, i + 1, arg, string_of_sort sort))
  ) (List.combine args expected)

(* What an argument was expected to be, described only in an error *)
and describe = function
  | Descr d -> d
  | SortAs (s, role) -> Format.sprintf "%s, %s" (string_of_sort s) role

(* Check an application of a non-indexed function symbol to arguments given
   with their sorts and constant flags, and return its sort *)
and check_app pos env f args =
  let logic = env.logic in
  let consts = List.map snd args in
  let args = List.map fst args in
  let n = List.length args in
  let arity expected ok =
    if not ok then fail pos (Arity (f, expected, n))
  in
  let exactly k = arity (Format.sprintf "%d %s" k (plural k "argument")) (n = k) in
  let at_least k =
    arity (Format.sprintf "at least %d %s" k (plural k "argument")) (n >= k)
  in
  let arg_sort i expected pred =
    let s = List.nth args (i - 1) in
    if not (pred s) then fail pos (ArgumentSort (f, i, s, describe expected));
    s
  in
  (* All arguments have the sort of the first one, which satisfies [pred] *)
  let homogeneous descr pred =
    let s = arg_sort 1 descr pred in
    List.iteri (fun i arg ->
      if arg <> s then
        fail pos (ArgumentSort (f, i + 1, arg,
          Format.sprintf "%s, the sort of the first argument"
            (string_of_sort s)))
    ) args;
    s
  in
  let arith = Descr "Int or Real" in
  let bitvec = Descr "a bit-vector sort" in
  let any = Descr "any sort" in
  let array = Descr "an array sort" in
  let require ok = if not ok then not_in_logic pos env f in
  let require_arith () = require (logic.ints || logic.reals) in
  let require_bv () = require logic.bitvectors in
  let require_arrays () = require logic.arrays in
  let linear_if ok =
    if logic.linear && not ok then fail pos (NonlinearTerm (f, logic.name))
  in
  (* Every argument but the first is constant *)
  let constant_divisors () = List.for_all Fun.id (List.tl consts) in
  match f with
  (* Core *)
  | "not" -> exactly 1; check_args pos f [Bool] args; Bool
  | "=>" | "and" | "or" | "xor" ->
    at_least 2; ignore (homogeneous (Descr "Bool") (( = ) Bool)); Bool
  | "=" | "distinct" ->
    at_least 2; ignore (homogeneous any (fun _ -> true)); Bool
  | "!=" -> exactly 2; ignore (homogeneous any (fun _ -> true)); Bool
  | "ite" ->
    exactly 3;
    ignore (arg_sort 1 (Descr "Bool") (( = ) Bool));
    let s = arg_sort 2 any (fun _ -> true) in
    ignore (arg_sort 3 (SortAs (s, "the sort of the second argument")) (( = ) s));
    s

  (* Ints, Reals and Reals_Ints *)
  | "+" -> require_arith (); at_least 2; homogeneous arith is_arith
  | "-" -> require_arith (); at_least 1; homogeneous arith is_arith
  | "*" ->
    require_arith (); at_least 2;
    let s = homogeneous arith is_arith in
    linear_if (List.length (List.filter not consts) <= 1);
    s
  | "/" ->
    require logic.reals; at_least 2;
    ignore (homogeneous (Descr "Real") (( = ) Real));
    linear_if (constant_divisors ());
    Real
  | "div" ->
    require logic.ints; at_least 2;
    ignore (homogeneous (Descr "Int") (( = ) Int));
    linear_if (constant_divisors ());
    Int
  | "mod" ->
    require logic.ints; exactly 2;
    ignore (homogeneous (Descr "Int") (( = ) Int));
    linear_if (constant_divisors ());
    Int
  | "abs" ->
    require logic.ints; exactly 1; check_args pos f [Int] args; Int
  | "<=" | "<" | ">=" | ">" ->
    require_arith (); at_least 2; ignore (homogeneous arith is_arith); Bool
  | "to_real" ->
    require (logic.ints && logic.reals); exactly 1;
    check_args pos f [Int] args; Real
  | "to_int" ->
    require (logic.ints && logic.reals); exactly 1;
    check_args pos f [Real] args; Int
  | "is_int" ->
    require (logic.ints && logic.reals); exactly 1;
    check_args pos f [Real] args; Bool

  (* FixedSizeBitVectors *)
  | "concat" -> (
    require_bv (); exactly 2;
    match arg_sort 1 bitvec is_bitvec, arg_sort 2 bitvec is_bitvec with
    | BitVec m, BitVec n -> BitVec (m + n)
    | _ -> assert false
  )
  | "bvnot" | "bvneg" -> require_bv (); exactly 1; homogeneous bitvec is_bitvec
  | "bvand" | "bvor" | "bvxor" | "bvadd" | "bvmul" ->
    require_bv (); at_least 2; homogeneous bitvec is_bitvec
  | "bvnand" | "bvnor" | "bvxnor" | "bvsub" | "bvudiv" | "bvurem" | "bvsdiv"
  | "bvsrem" | "bvsmod" | "bvshl" | "bvlshr" | "bvashr" ->
    require_bv (); exactly 2; homogeneous bitvec is_bitvec
  | "bvcomp" ->
    require_bv (); exactly 2; ignore (homogeneous bitvec is_bitvec); BitVec 1
  | "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt"
  | "bvsge" ->
    require_bv (); exactly 2; ignore (homogeneous bitvec is_bitvec); Bool
  | "bv2nat" ->
    require (logic.bitvectors && logic.ints); exactly 1;
    ignore (arg_sort 1 bitvec is_bitvec); Int

  (* ArraysEx *)
  | "select" -> (
    require_arrays (); exactly 2;
    match arg_sort 1 array (function Array _ -> true | _ -> false) with
    | Array (i, e) ->
      ignore (arg_sort 2 (SortAs (i, "the index sort of the array")) (( = ) i));
      e
    | _ -> assert false
  )
  | "store" -> (
    require_arrays (); exactly 3;
    match arg_sort 1 array (function Array _ -> true | _ -> false) with
    | Array (i, e) as a ->
      ignore (arg_sort 2 (SortAs (i, "the index sort of the array")) (( = ) i));
      ignore (arg_sort 3 (SortAs (e, "the element sort of the array")) (( = ) e));
      a
    | _ -> assert false
  )

  | _ -> fail pos (UnknownFunction f)

(* Check an application of an indexed function symbol and return its sort *)
and check_indexed_app pos env f indices args =
  let n = List.length args in
  let name = string_of_indexed_id f indices in
  let unknown () = fail pos (UnknownIndexedIdentifier name) in
  let indices = numeric_indices pos name indices in
  let exactly k =
    if n <> k then
      fail pos (Arity (name, Format.sprintf "%d %s" k (plural k "argument"), n))
  in
  let require ok = if not ok then not_in_logic pos env name in
  let bv_arg () =
    match args with
    | [BitVec m] -> m
    | [s] -> fail pos (ArgumentSort (name, 1, s, "a bit-vector sort"))
    | _ -> assert false
  in
  match f, indices with
  | "extract", [i; j] ->
    require env.logic.bitvectors; exactly 1;
    let m = bv_arg () in
    if not (m > i && i >= j && j >= 0) then
      fail pos (ArgumentSort (name, 1, BitVec m,
        Format.sprintf "a bit-vector sort of more than %d bits" i));
    BitVec (i - j + 1)
  | "repeat", [i] ->
    require env.logic.bitvectors; exactly 1;
    if i < 1 then unknown ();
    BitVec (i * bv_arg ())
  | "zero_extend", [i] | "sign_extend", [i] ->
    require env.logic.bitvectors; exactly 1;
    if i < 0 then unknown ();
    BitVec (bv_arg () + i)
  | "rotate_left", [i] | "rotate_right", [i] ->
    require env.logic.bitvectors; exactly 1;
    if i < 0 then unknown ();
    BitVec (bv_arg ())
  | "int2bv", [m] ->
    require (env.logic.bitvectors && env.logic.ints); exactly 1;
    if m < 1 then unknown ();
    check_args pos name [Int] args;
    BitVec m
  | _ -> unknown ()

(* Check a formula: a term of sort Bool. [what] names it in errors *)
let check_formula env what term =
  match check_term env term with
  | Bool, _ -> ()
  | sort, _ ->
    let span =
      match term with
      | A.Constant (A.Numeral (span, _) | A.Decimal (span, _)
                    | A.Bitvector (span, _)) -> span
      | A.Constant (A.True | A.False) -> assert false
      | A.QualId ((span, _, _), _, _) -> span
      | A.App (span, _, _) -> span
      | A.Let (span, _, _) -> span
    in
    fail_span span (ExpectedBool (what, sort))

(* ********************************************************************** *)
(* Systems                                                                *)
(* ********************************************************************** *)

(* The sorted variables of a [:input], [:output] or [:local] attribute *)
let sorted_vars logic = function
  | None -> []
  | Some (_, vars) ->
    List.map (fun (span, (_, s), sort) ->
      span, s, sort_of_ast logic sort
    ) vars

(* The state variables of a system or check as an environment, failing on a
   duplicate name *)
let vars_of kinds =
  List.fold_left (fun vars (kind, l) ->
    List.fold_left (fun vars (span, s, sort) ->
      if HSM.mem s vars then fail_span span (DuplicateVariable (str s));
      HSM.add s (kind, sort) vars
    ) vars l
  ) HSM.empty kinds

let signature inputs outputs locals =
  let strip = List.map (fun (_, s, sort) -> s, sort) in
  { inputs = strip inputs; outputs = strip outputs; locals = strip locals }

let check_subsystems env sys_name sys_name_hs subsys =
  List.fold_left (fun instances
    A.{ loc; instance_name = (inst_span, inst); system_name = (sub_span, sub);
        variables } ->
    let inst_name = str inst in
    if List.exists (HS.equal inst) instances then
      fail_span inst_span (DuplicateInstance inst_name);
    if HS.equal sub sys_name_hs then
      fail_span sub_span (SelfInstantiation sys_name);
    let sub_sig =
      match HSM.find_opt sub env.systems with
      | Some s -> s
      | None -> fail_span sub_span (UnknownSystem (str sub))
    in
    let formals =
      List.map (fun v -> Input, v) sub_sig.inputs
      @ List.map (fun v -> Output, v) sub_sig.outputs
    in
    let expected = List.length formals and got = List.length variables in
    if expected <> got then
      fail_span loc (SubsystemArity (inst_name, str sub, expected, got));
    List.iter2 (fun (formal_kind, (formal, formal_sort)) (var_span, v) ->
      let kind, sort =
        match HSM.find_opt v env.vars with
        | Some vs -> vs
        | None -> fail_span var_span (UnboundVariable (str v))
      in
      if sort <> formal_sort then
        fail_span var_span (SubsystemArgumentSort
          (inst_name, str v, sort, str formal, formal_sort));
      if formal_kind = Output && kind = Input then
        fail_span var_span (SubsystemOutputToInput (inst_name, str v, str formal))
    ) formals variables;
    inst :: instances
  ) [] subsys
  |> ignore

let check_define_system env (sys : A.define_system_cmd) =
  let name_span, name_hs = sys.name in
  let name = str name_hs in
  if HSM.mem name_hs env.systems then fail_span name_span (SystemRedefined name);
  let inputs = sorted_vars env.logic sys.input in
  let outputs = sorted_vars env.logic sys.output in
  let locals = sorted_vars env.logic sys.local in
  let vars = vars_of [Input, inputs; Output, outputs; Local, locals] in
  let env = { env with vars; lets = HSM.empty } in
  (* The parser lists the subsystems last first *)
  check_subsystems env name name_hs (List.rev sys.subsys);
  let what attr = Format.sprintf "the %s condition of system %s" attr name in
  check_formula { env with priming = NoPrime (what ":init") } (what ":init")
    sys.init;
  check_formula { env with priming = PrimeAll } (what ":trans") sys.trans;
  check_formula { env with priming = NoPrime (what ":inv") } (what ":inv")
    sys.inv;
  { env with
    systems = HSM.add name_hs (signature inputs outputs locals) env.systems }

let check_check_system env (check : A.check_system_cmd) =
  let sys_span, sys_hs = check.system_id in
  let sys_name = str sys_hs in
  let sys_sig =
    match HSM.find_opt sys_hs env.systems with
    | Some s -> s
    | None -> fail_span sys_span (UnknownSystem sys_name)
  in
  (* The variables of the check rename those of the system, in order *)
  let renaming kind attr formals =
    let span =
      match attr with Some (span, _) -> span | None -> check.loc
    in
    let vars = sorted_vars env.logic attr in
    let declared = List.length vars and expected = List.length formals in
    if declared <> expected then
      fail_span span (RenamingArity (kind, sys_name, declared, expected));
    List.iter2 (fun (span, v, sort) (orig, orig_sort) ->
      if sort <> orig_sort then
        fail_span span (RenamingSort (str v, sort, str orig, orig_sort))
    ) vars formals;
    vars
  in
  let inputs = renaming "input" check.input sys_sig.inputs in
  let outputs = renaming "output" check.output sys_sig.outputs in
  let locals = renaming "local" check.local sys_sig.locals in
  let vars = vars_of [Input, inputs; Output, outputs; Local, locals] in
  let env = { env with vars; lets = HSM.empty } in
  (* Conditions: assumptions may prime inputs only, reachability conditions
     any variable *)
  let conditions =
    List.fold_left (fun conditions -> function
      | A.FormulaAttr (ty, ((span, f), term)) ->
        let name = str f in
        if List.exists (HS.equal f) conditions then
          fail_span span (DuplicateFormula name);
        let what attr = Format.sprintf "the %s condition %s" attr name in
        (match ty with
         | A.Assumption ->
           check_formula
             { env with priming = PrimeInputs (what ":assumption") }
             (what ":assumption") term
         | A.Reachable ->
           check_formula { env with priming = PrimeAll } (what ":reachable")
             term);
        f :: conditions
      | A.QueryAttr _ -> conditions
    ) [] check.attrs
  in
  (* Queries name declared conditions *)
  List.fold_left (fun queries -> function
    | A.QueryAttr ((span, q), names) ->
      if List.exists (HS.equal q) queries then
        fail_span span (DuplicateQuery (str q));
      List.iter (fun (span, f) ->
        if not (List.exists (HS.equal f) conditions) then
          fail_span span (UnknownFormula (str q, str f))
      ) names;
      q :: queries
    | A.FormulaAttr _ -> queries
  ) [] check.attrs
  |> ignore;
  env

(* ********************************************************************** *)
(* Scripts                                                                *)
(* ********************************************************************** *)

let check_script script =
  let empty_env = {
    logic = logic_all;
    systems = HSM.empty;
    vars = HSM.empty;
    lets = HSM.empty;
    priming = PrimeAll;
  }
  in
  try
    (* The logic, when set, is set once and before any definition *)
    List.fold_left (fun (env, logic_set, defined) -> function
      | A.SetLogicCmd (span, l) ->
        if logic_set then fail_span span LogicAlreadySet;
        if defined then fail_span span LogicAfterDefinition;
        let logic =
          match logic_of_name (str l) with
          | Some logic -> logic
          | None -> fail_span span (UnknownLogic (str l))
        in
        { env with logic }, true, defined
      | A.DefineSystemCmd sys -> check_define_system env sys, logic_set, true
      | A.CheckSystemCmd check -> check_check_system env check, logic_set, true
    ) (empty_env, false, false) script
    |> ignore;
    Ok ()
  with Type_error e -> Error e
