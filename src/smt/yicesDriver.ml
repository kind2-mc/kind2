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


(* Configuration for Yices *)
let cmd_line 
    logic
    produce_assignments
    produce_proofs
    produce_cores
    produce_interpolants = 

  (* Path and name of Yices executable *)
  let yices_bin = Flags.Smt.yices_bin () in

  [| yices_bin |]



(* Command to limit check-sat to run for the given numer of ms at most *)
let check_sat_limited_cmd ms =
  failwith "Yices.check_sat_limited_cmd"


(* Indicates whether the solver supports the check-sat-assuming
   command. *)
let check_sat_assuming_supported () = true


let check_sat_assuming_cmd _ =
  failwith "Yices: check_sat_assuming not applicable"


let headers () = []

let prelude =
  [
    (* Define functions for int / real conversions *)
    "(define to_int::(-> x::real (subtype (y::int) (and (<= y x) (< x (+ y 1))))))";
    "(define to_real::(-> x::int (subtype (y::real) (= y x))))";
    (* Define xor operator *)
    "(define xor :: (-> bool bool bool) (lambda (x::bool y::bool) (and (or x y) (not (and x y)) )))";
  ]
  
let trace_extension = "ys"


let comment_delims = ";;", ""


(* Pretty-print a type *)
let rec pp_print_type ppf t =
  pp_print_type_node ppf (Type.node_of_type t)

and pp_print_type_node ppf = function 

    | Type.Bool -> Format.pp_print_string ppf "bool"

    | Type.Int -> Format.pp_print_string ppf "int"

    | Type.UBV i ->
      begin match i with
      | 8 -> Format.pp_print_string ppf "uint8"
      | 16 -> Format.pp_print_string ppf "uint16"
      | 32 -> Format.pp_print_string ppf "uint32"
      | 64 -> Format.pp_print_string ppf "uint64"
      | _ -> raise 
      (Invalid_argument "pp_print_type_node: BV size not allowed")
      end

    | Type.BV i ->
      begin match i with
      | 8 -> Format.pp_print_string ppf "int8"
      | 16 -> Format.pp_print_string ppf "int16"
      | 32 -> Format.pp_print_string ppf "int32"
      | 64 -> Format.pp_print_string ppf "int64"
      | _ -> raise 
      (Invalid_argument "pp_print_type_node: BV size not allowed")
      end

    | Type.IntRange (i, j, _) ->
      Format.fprintf ppf "(subrange %a %a)"
        Numeral.pp_print_numeral i Numeral.pp_print_numeral j

    | Type.Real -> Format.pp_print_string ppf "real"
    | Type.Abstr s -> Format.pp_print_string ppf s
(*
  | Type.BV i -> 

    Format.fprintf
      ppf 
      "(bitvector %d)" 
      i 
*)
    | Type.Array (te, ti) -> 
      Format.fprintf
        ppf 
        "(-> %a %a)" 
        pp_print_type ti
        pp_print_type te

(* Pretty-print a hashconsed variable *)


(* Pretty-print a logic identifier *)
let pp_print_logic ppf l =  failwith "no logic selection in yices"


let rec interpr_type t = match Type.node_of_type t with
  | Type.IntRange _ (* -> Type.mk_int () *)
  | Type.Bool | Type.Int | Type.UBV 8 | Type.UBV 16 
  | Type.UBV 32 | Type.UBV 64 | Type.BV 8 | Type.BV 16 
  | Type.BV 32 | Type.BV 64 | Type.Real | Type.Abstr _  -> t
  | Type.UBV _ | Type.BV _ -> raise 
      (Invalid_argument "rec_interpr_type: BV size not allowed")
  | Type.Array (te, ti) ->
    let ti', te' = interpr_type ti, interpr_type te in
    if Type.equal_types ti ti' && Type.equal_types te te' then t
    else Type.mk_array te' ti'
  (* | _ -> failwith ((Type.string_of_type t)^" not supported") *)


let pp_print_sort ppf t = pp_print_type ppf (interpr_type t)

let string_of_sort = string_of_t pp_print_sort
let pp_print_sort = pp_print_type



(* Convert a logic to a string *)
let string_of_logic _ = failwith "no logic selection in yices"

(* Static hashconsed strings *)
let s_int = HString.mk_hstring "int"
let s_real = HString.mk_hstring "real"
let s_bool = HString.mk_hstring "bool"
let s_subrange = HString.mk_hstring "subrange"


(* Convert an S-expression to a sort *)
let type_of_string_sexpr = function 

  | HStringSExpr.Atom s when s == s_int -> Type.t_int

  | HStringSExpr.Atom s when s == s_real -> Type.t_real

  | HStringSExpr.Atom s when s == s_bool -> Type.t_bool 

  | HStringSExpr.List [HStringSExpr.Atom s;
                       HStringSExpr.Atom i; HStringSExpr.Atom j]
    when s == s_subrange ->
    Type.mk_int_range (Numeral.of_string (HString.string_of_hstring i))
      (Numeral.of_string (HString.string_of_hstring j))
                                                
  | HStringSExpr.Atom _
  | HStringSExpr.List _ as s ->

    raise
      (Invalid_argument 
         (Format.asprintf
            "Sort %a not supported" 
            HStringSExpr.pp_print_sexpr s))



(* Association list of strings to function symbols *) 
let string_symbol_list =
  [("not", Symbol.mk_symbol `NOT);
   ("=>", Symbol.mk_symbol `IMPLIES);
   ("and", Symbol.mk_symbol `AND);
   ("or", Symbol.mk_symbol `OR);
   (* ("xor", Symbol.mk_symbol `XOR); *)
   ("=", Symbol.mk_symbol `EQ);
   (* ("distinct", Symbol.mk_symbol `DISTINCT); *)
   ("ite", Symbol.mk_symbol `ITE);
   ("-", Symbol.mk_symbol `MINUS);
   ("+", Symbol.mk_symbol `PLUS);
   ("*", Symbol.mk_symbol `TIMES);
   ("/", Symbol.mk_symbol `DIV);
   ("div", Symbol.mk_symbol `INTDIV);
   ("mod", Symbol.mk_symbol `MOD);
   (* ("abs", Symbol.mk_symbol `ABS); *)
   ("<=", Symbol.mk_symbol `LEQ);
   ("<", Symbol.mk_symbol `LT);
   (">=", Symbol.mk_symbol `GEQ);
   (">", Symbol.mk_symbol `GT);
   ("to_real", Symbol.mk_symbol `TO_REAL);
   ("to_int", Symbol.mk_symbol `TO_INT);
   ("(_ int2bv 8)", Symbol.mk_symbol `TO_UINT8);
   ("(_ int2bv 16)", Symbol.mk_symbol `TO_UINT16);
   ("(_ int2bv 32)", Symbol.mk_symbol `TO_UINT32);
   ("(_ int2bv 64)", Symbol.mk_symbol `TO_UINT64);
   (* ("is_int", Symbol.mk_symbol `IS_INT); *)

   ("bv-not", Symbol.mk_symbol `BVNOT);
   ("bv-neg", Symbol.mk_symbol `BVNEG);
   ("bv-and", Symbol.mk_symbol `BVAND);
   ("bv-or", Symbol.mk_symbol `BVOR);
   ("bv-add", Symbol.mk_symbol `BVADD);
   ("bv-sub", Symbol.mk_symbol `BVSUB);
   ("bv-mul", Symbol.mk_symbol `BVMUL);
   ("bv-div", Symbol.mk_symbol `BVUDIV);
   ("bv-sdiv", Symbol.mk_symbol `BVSDIV);
   ("bv-rem", Symbol.mk_symbol `BVUREM);
   ("bv-shift-left0", Symbol.mk_symbol `BVSHL);
   ("bv-shift-right0", Symbol.mk_symbol `BVLSHR);
   ("bv-ashift-right", Symbol.mk_symbol `BVASHR);
   ("bv-lt", Symbol.mk_symbol `BVULT);
   ("bv-le", Symbol.mk_symbol `BVULE);
   ("bv-gt", Symbol.mk_symbol `BVUGT);
   ("bv-ge", Symbol.mk_symbol `BVUGE);
   ("bv-slt", Symbol.mk_symbol `BVSLT);
   ("bv-sle", Symbol.mk_symbol `BVSLE);
   ("bv-sgt", Symbol.mk_symbol `BVSGT);
   ("bv-sge", Symbol.mk_symbol `BVSGE);
   ("bv-concat", Symbol.mk_symbol `BVCONCAT);
   (* ("select", Symbol.mk_symbol `SELECT); *)

   ("update", Symbol.mk_symbol `STORE)

  ]

(* TODO add support for arrays by keeping info on which function symbols are
   in fact arrays *)

(* Reserved words that we don't support *)
let reserved_word_list = 
  List.map 
    HString.mk_hstring 
    [ "maxsat"; "mk-tuple"; "tuple"; "record" ]



(* Pretty-print a symbol *)
let rec pp_print_symbol_node ?arity ppf = function 

  | `TRUE -> Format.pp_print_string ppf "true"
  | `FALSE -> Format.pp_print_string ppf "false"
  | `NOT -> Format.pp_print_string ppf "not"
  | `IMPLIES -> Format.pp_print_string ppf "=>"
  | `AND  -> Format.pp_print_string ppf "and"
  | `OR -> Format.pp_print_string ppf "or"
  | `XOR -> Format.pp_print_string ppf "xor"

  | `EQ -> Format.pp_print_string ppf "="
  | `DISTINCT -> failwith "distinct not implemented for yices"
  | `ITE -> Format.pp_print_string ppf "ite" 

  | `NUMERAL i -> Numeral.pp_print_numeral ppf i
  | `DECIMAL f -> Decimal.pp_print_decimal ppf f

  | `UBV b -> Bitvector.pp_yices_print_bitvector_b ppf b
  | `BV b -> Bitvector.pp_yices_print_bitvector_b ppf b

  (* Special case for unary minus : print -a as (- 0 a) *)
  | `MINUS when arity = Some 1 -> Format.pp_print_string ppf "- 0"

  | `MINUS -> Format.pp_print_string ppf "-"
  | `PLUS -> Format.pp_print_string ppf "+"
  | `TIMES -> Format.pp_print_string ppf "*"
  | `DIV -> Format.pp_print_string ppf "/"
  | `INTDIV -> Format.pp_print_string ppf "div"
  | `MOD -> Format.pp_print_string ppf "mod"
  | `ABS -> failwith "abs not implemented for yices"

  | `LEQ -> Format.pp_print_string ppf "<="
  | `LT -> Format.pp_print_string ppf "<"
  | `GEQ -> Format.pp_print_string ppf ">="
  | `GT -> Format.pp_print_string ppf ">"

  | `TO_REAL -> Format.pp_print_string ppf "to_real"
  | `TO_INT -> Format.pp_print_string ppf "to_int"
  | `TO_UINT8 -> Format.pp_print_string ppf "(_ int2bv 8)"
  | `TO_UINT16 -> Format.pp_print_string ppf "(_ int2bv 16)"
  | `TO_UINT32 -> Format.pp_print_string ppf "(_ int2bv 32)"
  | `TO_UINT64 -> Format.pp_print_string ppf "(_ int2bv 64)"
  | `TO_INT8 -> Format.pp_print_string ppf "(_ int2bv 8)"
  | `TO_INT16 -> Format.pp_print_string ppf "(_ int2bv 16)"
  | `TO_INT32 -> Format.pp_print_string ppf "(_ int2bv 32)"
  | `TO_INT64 -> Format.pp_print_string ppf "(_ int2bv 64)"
  | `BV2NAT -> Format.pp_print_string ppf "bv2nat"
  | `IS_INT -> failwith "is_int not implemented for yices"

  | `DIVISIBLE n ->
    failwith "divisible not implemented for yices"

  | `BVNOT -> Format.pp_print_string ppf "bv-not"
  | `BVNEG -> Format.pp_print_string ppf "bv-neg"
  | `BVAND -> Format.pp_print_string ppf "bv-and"
  | `BVOR -> Format.pp_print_string ppf "bv-or"
  | `BVADD -> Format.pp_print_string ppf "bv-add"
  | `BVSUB -> Format.pp_print_string ppf "bv-sub"
  | `BVMUL -> Format.pp_print_string ppf "bv-mul"
  | `BVUDIV -> Format.pp_print_string ppf "bv-div"
  | `BVSDIV -> Format.pp_print_string ppf "bv-sdiv"
  | `BVUREM -> Format.pp_print_string ppf "bv-rem"
  | `BVSHL -> Format.pp_print_string ppf "bv-shift-left0"
  | `BVLSHR -> Format.pp_print_string ppf "bv-shift-right0"
  | `BVASHR -> Format.pp_print_string ppf "bv-ashift-right"
  | `BVULT -> Format.pp_print_string ppf "bv-lt"
  | `BVULE -> Format.pp_print_string ppf "bv-le"
  | `BVUGT -> Format.pp_print_string ppf "bv-gt"
  | `BVUGE -> Format.pp_print_string ppf "bv-ge"
  | `BVSLT -> Format.pp_print_string ppf "bv-slt"
  | `BVSLE -> Format.pp_print_string ppf "bv-sle"
  | `BVSGT -> Format.pp_print_string ppf "bv-sgt"
  | `BVSGE -> Format.pp_print_string ppf "bv-sge"
  | `BVCONCAT -> Format.pp_print_string ppf "bv-concat"
  | `BVEXTRACT (i, j) -> 
      Format.fprintf 
        ppf 
        "bv-extract %a %a" 
        Numeral.pp_print_numeral j
        Numeral.pp_print_numeral i
  | `BVSIGNEXT i ->
      Format.fprintf
        ppf
        "bv-sign-extend %a"
        Numeral.pp_print_numeral i
        
  | `SELECT _ -> Format.pp_print_string ppf ""

  | `STORE -> Format.pp_print_string ppf "update"

  | `UF u -> UfSymbol.pp_print_uf_symbol ppf u


(* Pretty-print a hashconsed symbol *)
and pp_print_symbol ?arity ppf s =
  pp_print_symbol_node ?arity ppf (Symbol.node_of_symbol s)


(* Return a string representation of a hashconsed symbol *)
let string_of_symbol ?arity s = string_of_t (pp_print_symbol ?arity) s


(* Pretty-print a list of typed variables *)
let rec pp_print_typed_var_list db ppf = function 
  (* Print nothing for the empty list *)
  | [] -> ()
  (* Print the first typed variable *)
  | s :: tl -> 
    (* Increment variable index *)
    let db' = succ db in
    (* Print variable as (Xn t) *)
    Format.fprintf ppf "@[<hv 1>X%i::%a@]" db' pp_print_type s;
    (* Add space and recurse if more bindings follow *)
    if not (tl = []) then 
      (Format.pp_print_space ppf (); 
       pp_print_typed_var_list db' ppf tl)


(* Pretty-print at a given De Bruijn index *)
let rec pp_print_term' db ppf t = match Term.T.node_of_t t with
  (* Delegate printing of free variables to function in input module *)
  | Term.T.FreeVar v -> Var.pp_print_var ppf v

  (* Print bound variable with its de Bruijn index *)
  | Term.T.BoundVar dbv -> Format.fprintf ppf "X%i" (db - dbv + 1)

  (* Delegate printing of leaf to function in input module *)
  | Term.T.Leaf s -> pp_print_symbol ?arity:(Some 0) ppf s

  (* Print array store *)
  | Term.T.Node (s, [a; i; v]) when s == Symbol.s_store ->

    Format.fprintf ppf 
      "@[<hv 1>(%a@ %a (%a)@ %a)@]" 
      (pp_print_symbol ?arity:(Some 3)) s
      (pp_print_term' db) a
      (pp_print_term' db) i
      (pp_print_term' db) v

  (* Print a function application as S-expression *)
  | Term.T.Node (s, a) -> 

    Format.fprintf ppf 
      "@[<hv 1>(%a@ %a)@]" 
      (pp_print_symbol ?arity:(Some (List.length a))) s
      (pp_print_list (pp_print_term' db) "@ ") a

  (* Print a let binding *)
  | Term.T.Let (l, b) ->
    let Term.T.L (x, t) = Term.T.node_of_lambda l in
    Format.fprintf ppf
      "@[<hv 1>(let@ @[<hv 1>(%a)@]@ %a)@]"
      (pp_print_let_bindings 0 db) (b, x)
      (pp_print_term' (db + List.length b)) t

  (* Print a universal quantification *)
  | (Term.T.Forall l | Term.T.Exists l) as nt ->
    let Term.T.L (x, t) = Term.T.node_of_lambda l in
    let quant = match nt with
      | Term.T.Forall _ -> "forall"
      | Term.T.Exists _ -> "exists"
      | _ -> assert false
    in
    Format.fprintf ppf
      "@[<hv 1>(%s@ @[<hv 1>(%a)@ %a@])@]"
      quant
      (pp_print_typed_var_list db) x
      (pp_print_term' (db + List.length x)) t

  | _ -> Term.T.pp_print_term_w pp_print_symbol
           Var.pp_print_var pp_print_sort ~db ppf t


(* Pretty-print a list of variable term bindings *)
and pp_print_let_bindings i db ppf = function 
  (* Print nothing for the empty list *)
  | [], [] -> ()
  (* Print the first binding *)
  | t :: tl, s :: sl -> 
    (* Increment variable index *)
    let db' = succ db in
    (* Print as binding as (Xn t) *)
    Format.fprintf 
      ppf 
      "@[<hv 1>(X%i::%a@ %a)@]" 
      db'
      pp_print_type s
      (pp_print_term' (db - i)) t;

    (* Add space and recurse if more bindings follow *)
    if not (tl = []) then 
      (Format.pp_print_space ppf (); 
       pp_print_let_bindings (succ i) db' ppf (tl, sl))
      
  | _ -> assert false


(* Pretty-print a term *)
let pp_print_term = pp_print_term' 0


(* Pretty-print an expression *)
let pp_print_expr = pp_print_term


(* Pretty-print an expression to the standard formatter *)
let print_expr = pp_print_expr Format.std_formatter


(* Return a string representation of an expression *)
let string_of_expr t = string_of_t pp_print_expr t



