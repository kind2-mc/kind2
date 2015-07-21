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

(* Symbols are hashconsed so that we can rely on physical equality for
   comparison, as of now there are no useful properties to be stored
   alongside symbols. In particular the `NUMERAL i, `DECIMAL f and
   `SYM (s, t) symbols need to be hashconsed for physical equality. *)


(* ********************************************************************* *)
(* Types and hash-consing                                                *)
(* ********************************************************************* *)


(* The symbols at leaves of terms without the attribute symbol 

   Keep the attribute symbol and others of different types out of this
   type for easy pattern matching when converting from an expression
   returned by the SMT solver *)
type interpreted_symbol = 
  [ `TRUE                 (* Boolean true value (nullary) *)
  | `FALSE                (* Boolean false value (nullary) *)
  | `NOT                  (* Boolean negation (unary) *)
  | `IMPLIES              (* Boolean implication (right-associative) *)
  | `AND                  (* Boolean conjunction (left-associative) *)
  | `OR                   (* Boolean disjunction (left-associative) *)
  | `XOR                  (* Boolean exclusive disjunction (left-associative) *)

  | `EQ                   (* Equality between terms (chainable) *)
  | `DISTINCT             (* Pairwise distinct predicate (chainable) *)
  | `ITE                  (* If-then-else (ternary) *) 

  | `NUMERAL of Numeral.t   (* Infinite precision integer numeral (nullary) *)
  | `DECIMAL of Decimal.t 
                       (* Infinite precision floating-point decimal (nullary) *)
(*
  | `BV of bitvector      (* Constant bitvector *)
*)
  | `MINUS                (* Difference or unary negation (left-associative) *)
  | `PLUS                 (* Sum (left-associative) *)
  | `TIMES                (* Product (left-associative) *)
  | `DIV                  (* Real quotient (left-associative) *)
  | `INTDIV               (* Integer quotient (left-associative) *)
  | `MOD                  (* Modulus (binary) *)
  | `ABS                  (* Absolute value (unary) *)
  | `LEQ                  (* Less than or equal relation (chainable) *)
  | `LT                   (* Less than relation (chainable) *)
  | `GEQ                  (* Greater than or equal relation (chainable) *)
  | `GT                   (* Greater than relation (chainable) *)
  | `TO_REAL              (* Conversion to a floating-point decimal (unary) *)
  | `TO_INT               (* Conversion to an integer numeral (unary) *)
  | `IS_INT               (* Real is an integer (unary) *)

  | `DIVISIBLE of Numeral.t 
                          (* Divisible by [n] (unary) *)
(*
  | `CONCAT               (* Concatenation of bitvectors (binary) *)
  | `EXTRACT of Numeral.t * Numeral.t 
                          (* Extract subsequence from bitvector (unary) *)
  | `BVNOT                (* Bit-wise negation (unary) *)
  | `BVNEG                (* Arithmetic negation (unary) *)
  | `BVAND                (* Bit-wise conjunction (binary) *)
  | `BVOR                 (* Bit-wise disjunction (binary) *)
  | `BVADD                (* Arithmetic sum (binary) *)
  | `BVMUL                (* Arithmetic multiplication (binary) *)
  | `BVDIV                (* Arithmetic integer division (binary) *)
  | `BVUREM               (* Arithmetic remainder (binary) *)
  | `BVSHL                (* Logical shift left (unary) *)
  | `BVLSHR               (* Logical shift right (unary) *)
  | `BVULT                (* Arithmetic comparision (binary) *)
*)

  | `SELECT               (* Selection from array (binary) *)
(*
  | `STORE                (* Update of an array (ternary) *)
*)
  ]


(* Symbol to be hashconsed *)
type symbol = 
  [ interpreted_symbol
  | `UF of UfSymbol.t     (* Uninterpreted symbol (variadic) *)
  ]


(* A private type that cannot be constructed outside this module

   This is necessary to ensure the invariant that all subterms of a
   term are hashconsed. We can construct and thus pattern match on the
   {!symbol} type, but not on the {!symbol_node} type *)
type symbol_node = symbol


(* Properties of a symbol

   Only keep essential properties here that are shared by all
   modules. For local properties use a hashtable in the respective
   module.

   No properties for now. *)
type symbol_prop = unit 


(* Hashconsed symbol *)
type t = (symbol_node, symbol_prop) Hashcons.hash_consed


(* Hashing and equality on symbols *)
module Symbol_node = struct

  (* The type of a symbol *)
  type t = symbol

  (* Properties of a symbol

     No properties for now *)
  type prop = symbol_prop

  (* Equality of two symbols *)
  let equal s1 s2 = match s1, s2 with 

    (* Parametric symbols *)
    | `NUMERAL n1, `NUMERAL n2 -> Numeral.equal n1 n2
    | `DECIMAL d1, `DECIMAL d2 -> Decimal.equal d1 d2
    | `DIVISIBLE n1, `DIVISIBLE n2 -> Numeral.equal n1 n2
(*
    | `EXTRACT (i1, j1), `EXTRACT (i2, j2) -> Numeral.equal i1 i2 && Numeral.equal j1 j2
    | `BV i, `BV j -> i = j
*)
    | `UF u1, `UF u2 -> UfSymbol.equal_uf_symbols u1 u2

    | `NUMERAL _, _
    | `DECIMAL _, _
    | `DIVISIBLE _, _
(*
    | `EXTRACT _, _
    | `BV _, _
*)
    | `UF _, _  -> false

    (* Non-parametric symbols *)
    | `TRUE, `TRUE
    | `FALSE, `FALSE
    | `NOT, `NOT
    | `IMPLIES, `IMPLIES
    | `AND, `AND
    | `OR, `OR
    | `XOR, `XOR
    | `EQ, `EQ
    | `DISTINCT, `DISTINCT
    | `ITE, `ITE
    | `MINUS, `MINUS
    | `PLUS, `PLUS
    | `TIMES, `TIMES
    | `DIV, `DIV
    | `INTDIV, `INTDIV
    | `MOD, `MOD
    | `ABS, `ABS
    | `LEQ, `LEQ
    | `LT, `LT
    | `GEQ, `GEQ
    | `GT, `GT
    | `TO_REAL, `TO_REAL
    | `TO_INT, `TO_INT
    | `IS_INT, `IS_INT
    | `SELECT, `SELECT -> true
(*
    | `STORE, `STORE -> true
*)

(*
    | `CONCAT, `CONCAT
    | `BVNOT, `BVNOT 
    | `BVNEG, `BVNEG
    | `BVAND, `BVAND
    | `BVOR, `BVOR
    | `BVADD, `BVADD
    | `BVMUL, `BVMUL
    | `BVDIV, `BVDIV
    | `BVUREM, `BVUREM
    | `BVSHL, `BVSHL
    | `BVLSHR, `BVLSHR
    | `BVULT, `BVULT
*)

    | `TRUE, _
    | `FALSE, _
    | `NOT, _
    | `IMPLIES, _
    | `AND, _
    | `OR, _
    | `XOR, _
    | `EQ, _
    | `DISTINCT, _
    | `ITE, _
    | `MINUS, _
    | `PLUS, _
    | `TIMES, _
    | `DIV, _
    | `INTDIV, _
    | `MOD, _
    | `ABS, _
    | `LEQ, _
    | `LT, _
    | `GEQ, _
    | `GT, _
    | `TO_REAL, _
    | `TO_INT, _
    | `IS_INT, _
    | `SELECT, _ -> false

(*
    | `STORE, _ -> false
*)
(*
    | `CONCAT, _
    | `BVNOT, _ 
    | `BVNEG, _
    | `BVAND, _
    | `BVOR, _
    | `BVADD, _
    | `BVMUL, _
    | `BVDIV, _
    | `BVUREM, _
    | `BVSHL, _
    | `BVLSHR, _
    | `BVULT, _
*)


  (* Return hash of a symbol *)
  let hash = Hashtbl.hash

end


(* Hashconsed symbols *)
module Hsymbol = Hashcons.Make (Symbol_node)


(* Storage for hashconsed symbols *)
let ht = Hsymbol.create 251


let stats () = Hsymbol.stats ht


(* Return the node of a symbol *)
let node_of_symbol = function { Hashcons.node = t } -> t 


(* ********************************************************************* *)
(* Hashtables, maps and sets                                             *)
(* ********************************************************************* *)


(* Comparison function on symbols *)
let compare_symbols = Hashcons.compare

(* Equality function on symbols *)
let equal_symbols = Hashcons.equal 

(* Hashing function on symbols *)
let hash_symbol = Hashcons.hash 


(* Module as input to functors *)
module HashedSymbol = struct 

  (* Dummy type to prevent writing [type t = t] which is cyclic *)
  type z = t
  type t = z

  (* Compare tags of hashconsed symbols for equality *)
  let equal = equal_symbols
    
  (* Use hash of symbol *)
  let hash = hash_symbol

end

(* Module as input to functors *)
module OrderedSymbol = struct 

  (* Dummy type to prevent writing [type t = t] which is cyclic *)
  type z = t
  type t = z

  (* Compare tags of hashconsed symbols *)
  let compare = compare_symbols

end

(* Hashtable of symbols *)
module SymbolHashtbl = Hashtbl.Make (HashedSymbol)

(* Set of symbols

   Try to turn this into a patricia set with Hset for another small
   gain in efficiency. *)
module SymbolSet = Set.Make (OrderedSymbol)


(* Map of symbols

   Try to turn this into a patricia set with Hset for another small
   gain in efficiency. *)
module SymbolMap = Map.Make (OrderedSymbol)


(* ********************************************************************* *)
(* Pretty-printing                                                       *)
(* ********************************************************************* *)

(* Print in SMTlib syntax by default *)

(* Pretty-print a symbol *)
let rec pp_print_symbol_node ppf = function 

  | `TRUE -> Format.pp_print_string ppf "true"
  | `FALSE -> Format.pp_print_string ppf "false"
  | `NOT -> Format.pp_print_string ppf "not"
  | `IMPLIES -> Format.pp_print_string ppf "=>"
  | `AND  -> Format.pp_print_string ppf "and"
  | `OR -> Format.pp_print_string ppf "or"
  | `XOR -> Format.pp_print_string ppf "xor"

  | `EQ -> Format.pp_print_string ppf "="
  | `DISTINCT -> Format.pp_print_string ppf "distinct"
  | `ITE -> Format.pp_print_string ppf "ite" 

  | `NUMERAL i -> Numeral.pp_print_numeral ppf i
  | `DECIMAL f -> Decimal.pp_print_decimal_sexpr ppf f
  | `BV b -> pp_smtlib_print_bitvector_b ppf b

  | `MINUS -> Format.pp_print_string ppf "-"
  | `PLUS -> Format.pp_print_string ppf "+"
  | `TIMES -> Format.pp_print_string ppf "*"
  | `DIV -> Format.pp_print_string ppf "/"
  | `INTDIV -> Format.pp_print_string ppf "div"
  | `MOD -> Format.pp_print_string ppf "mod"
  | `ABS -> Format.pp_print_string ppf "abs"

  | `LEQ -> Format.pp_print_string ppf "<="
  | `LT -> Format.pp_print_string ppf "<"
  | `GEQ -> Format.pp_print_string ppf ">="
  | `GT -> Format.pp_print_string ppf ">"

  | `TO_REAL -> Format.pp_print_string ppf "to_real"
  | `TO_INT -> Format.pp_print_string ppf "to_int"
  | `IS_INT -> Format.pp_print_string ppf "is_int"

  | `DIVISIBLE n -> 
    Format.pp_print_string ppf "divisible";
    Format.pp_print_space ppf ();
    Numeral.pp_print_numeral ppf n
(*
  | `CONCAT -> Format.pp_print_string ppf "concat"
  | `EXTRACT (i, j) -> 
    Format.fprintf 
      ppf 
      "(_ extract %a %a)" 
      Numeral.pp_print_numeral i
      Numeral.pp_print_numeral j

  | `BVNOT -> Format.pp_print_string ppf "bvnot"
  | `BVNEG -> Format.pp_print_string ppf "bvneg"
  | `BVAND -> Format.pp_print_string ppf "bvand"
  | `BVOR -> Format.pp_print_string ppf "bvor"
  | `BVADD -> Format.pp_print_string ppf "bvadd"
  | `BVMUL -> Format.pp_print_string ppf "bvmul"
  | `BVDIV -> Format.pp_print_string ppf "bvdiv"
  | `BVUREM -> Format.pp_print_string ppf "bvurem"
  | `BVSHL -> Format.pp_print_string ppf "bvshl"
  | `BVLSHR -> Format.pp_print_string ppf "bvlshr"
  | `BVULT -> Format.pp_print_string ppf "bvult"
*)

  | `SELECT -> Format.pp_print_string ppf "select"
(*
  | `STORE -> Format.pp_print_string ppf "store"
*)
  | `UF u -> UfSymbol.pp_print_uf_symbol ppf u

(* Pretty-print a hashconsed symbol *)
and pp_print_symbol ppf { Hashcons.node = n } =
  pp_print_symbol_node ppf n


(* Return a string representation of a hashconsed symbol *)
let string_of_symbol s = string_of_t pp_print_symbol s


(* Return a string representation of a symbol *)
let string_of_symbol_node s = string_of_t pp_print_symbol_node s



(* Return true if the symbol is a numeral *)
let is_numeral = function 
  | { Hashcons.node = `NUMERAL _ } -> true 
  | _ -> false

(* Return true if the symbol is a decimal *)
let is_decimal = function 
  | { Hashcons.node = `DECIMAL _ } -> true 
  | _ -> false
(*
(* Return true if the symbol is a bitvector *)
let is_bitvector = function 
  | { Hashcons.node = `BV _ } -> true 
  | _ -> false
*)
(* Return true if the symbol is [`TRUE] or [`FALSE] *)
let is_bool = function 
  | { Hashcons.node = `TRUE } 
  | { Hashcons.node = `FALSE } -> true 
  | _ -> false

(* Return the numeral in a `NUMERAL symbol  *)
let numeral_of_symbol = function 
  | { Hashcons.node = `NUMERAL n } -> n 
  | _ -> raise (Invalid_argument "numeral_of_symbol")

(* Return the decimal in a `DECIMAL symbol  *)
let decimal_of_symbol = function 
  | { Hashcons.node = `DECIMAL n } -> n 
  | _ -> raise (Invalid_argument "decimal_of_symbol")
(*
(* Return the bitvector in a `BV symbol  *)
let bitvector_of_symbol = function 
  | { Hashcons.node = `BV n } -> n 
  | _ -> raise (Invalid_argument "bitvector_of_symbol")
*)
(* Return [true] for the [`TRUE] symbol and [false] for the [`FALSE]
    symbol *)
let bool_of_symbol = function 
  | { Hashcons.node = `TRUE } -> true
  | { Hashcons.node = `FALSE } -> false 
  | _ -> raise (Invalid_argument "bool_of_symbol")

(* Return true if the symbol is uninterpreted *)
let is_uf = function 
  | { Hashcons.node = `UF _ } -> true 
  | _ -> false

(* Return the uninterpreted symbol of a symbol *)
let uf_of_symbol = function 
  | { Hashcons.node = `UF u } -> u
  | _ -> raise (Invalid_argument "uf_of_symbol")


(* ********************************************************************* *)
(* Constructors                                                          *)
(* ********************************************************************* *)


(* Return a hashconsed symbol *)
let mk_symbol sym = 
  Hsymbol.hashcons ht sym ()
    

(* Import symbol from a different instance into this hashcons table *)
let import = function 
  | { Hashcons.node = `UF u } -> mk_symbol (`UF (UfSymbol.import u))
  | { Hashcons.node = s } -> mk_symbol s


(* Constant propositional value *)
let s_true = mk_symbol `TRUE

(* Constant propositional value *)
let s_false = mk_symbol `FALSE

(* Constant negation symbol *)
let s_not = mk_symbol `NOT

(* Constant conjunction symbol *)
let s_and = mk_symbol `AND

(* Constant conjunction symbol *)
let s_or = mk_symbol `OR

(* Constant conjunction symbol *)
let s_implies = mk_symbol `IMPLIES

(* Constant conjunction symbol *)
let s_eq = mk_symbol `EQ

(* Constant conjunction symbol *)
let s_geq = mk_symbol `GEQ

(* Constant conjunction symbol *)
let s_leq = mk_symbol `LEQ

(* Constant conjunction symbol *)
let s_gt = mk_symbol `GEQ

(* Constant conjunction symbol *)
let s_lt = mk_symbol `LEQ

(* Constant modulus operator symbol *)
let s_mod = mk_symbol `MOD

(* Constant plus operator *)
let s_plus = mk_symbol `PLUS

(* Constant minus operator *)
let s_minus = mk_symbol `MINUS

(* Constant times operator *)
let s_times = mk_symbol `TIMES

(* Constant division operator *)
let s_div = mk_symbol `DIV

(* Array read operator *)
let s_select = mk_symbol `SELECT




(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
