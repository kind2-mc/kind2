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

  | `UBV of Bitvector.t   (* Constant unsigned bitvector *)
  | `BV of Bitvector.t    (* Constant bitvector *)

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
  | `UINT8_TO_INT         (* Conversion from an unsigned integer 8 numeral to an integer *)
  | `UINT16_TO_INT        (* Conversion from an unsigned integer 16 numeral to an integer *)
  | `UINT32_TO_INT        (* Conversion from an unsigned integer 32 numeral to an integer *)
  | `UINT64_TO_INT        (* Conversion from an unsigned integer 64 numeral to an integer *)
  | `INT8_TO_INT          (* Conversion from a signed integer 8 numeral to an integer *)
  | `INT16_TO_INT         (* Conversion from a signed integer 16 numeral to an integer *)
  | `INT32_TO_INT         (* Conversion from a signed integer 32 numeral to an integer *)
  | `INT64_TO_INT         (* Conversion from a signed integer 64 numeral to an integer *)
  | `TO_UINT8             (* Conversion to an unsigned integer8 numeral (unary) *)  
  | `TO_UINT16            (* Conversion to an unsigned integer16 numeral (unary) *)  
  | `TO_UINT32            (* Conversion to an unsigned integer32 numeral (unary) *)  
  | `TO_UINT64            (* Conversion to an unsigned integer64 numeral (unary) *)
  | `TO_INT8              (* Conversion to an integer8 numeral (unary) *)  
  | `TO_INT16             (* Conversion to an integer16 numeral (unary) *)  
  | `TO_INT32             (* Conversion to an integer32 numeral (unary) *)  
  | `TO_INT64             (* Conversion to an integer64 numeral (unary) *)  
  | `BV2NAT               (* Conversion from bitvector to natural number *)
  | `IS_INT               (* Real is an integer (unary) *)

  | `DIVISIBLE of Numeral.t 
                          (* Divisible by [n] (unary) *)

  | `BVNOT                (* Bit-wise negation (unary) *)
  | `BVNEG                (* Arithmetic negation (unary) *)
  | `BVAND                (* Bit-wise conjunction (binary) *)
  | `BVOR                 (* Bit-wise disjunction (binary) *)
  | `BVADD                (* Signed bitvector sum (binary) *)
  | `BVSUB                (* Signed bitvector difference (binary) *)
  | `BVMUL                (* Arithmetic multiplication (binary) *)
  | `BVUDIV               (* Arithmetic integer division (binary) *)
  | `BVSDIV               (* Arithmetic integer signed division (binary) *)
  | `BVUREM               (* Arithmetic remainder (binary) *)
  | `BVSREM               (* Arithmetic signed remainder (binary) *)
  | `BVSHL                (* Logical shift left (binary) *)
  | `BVLSHR               (* Logical shift right (binary) *)
  | `BVASHR               (* Arithmetic right shift (binary) *)
  | `BVULT                (* Arithmetic comparision less than (unsigned binary) *)
  | `BVULE                (* Arithmetic comparision less than or equal to (unsigned binary) *)
  | `BVUGT                (* Arithmetic comparision greater than (unsigned binary) *)
  | `BVUGE                (* Arithmetic comparision greater than or equal to (unsigned binary) *)
  | `BVSLT                (* Arithmetic comparision less than (signed binary) *)
  | `BVSLE                (* Arithmetic comparision less than or equal to (signed binary) *)
  | `BVSGT                (* Arithmetic comparision greater than (signed binary) *)
  | `BVSGE                (* Arithmetic comparision greater than or equal to (signed binary) *)
  | `BVEXTRACT of Numeral.t * Numeral.t 
                          (* Extract subsequence from bitvector (unary) *)
  | `BVCONCAT             (* Concatenation of bitvectors (binary) *)
  | `BVSIGNEXT of Numeral.t
                          (* Sign extension of bitvector (unary) *)

  (* Selection from array (binary) *)
  | `SELECT of Type.t
  | `STORE                (* Update of an array (ternary) *)
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

    | `UBV i, `UBV j -> i = j
    | `BV i, `BV j -> i = j

    | `UF u1, `UF u2 -> UfSymbol.equal_uf_symbols u1 u2

    | `NUMERAL _, _
    | `DECIMAL _, _
    | `DIVISIBLE _, _

    | `UBV _, _
    | `BV _, _

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
    | `UINT8_TO_INT, `UINT8_TO_INT
    | `UINT16_TO_INT, `UINT16_TO_INT
    | `UINT32_TO_INT, `UINT32_TO_INT
    | `UINT64_TO_INT, `UINT64_TO_INT
    | `INT8_TO_INT, `INT8_TO_INT
    | `INT16_TO_INT, `INT16_TO_INT
    | `INT32_TO_INT, `INT32_TO_INT
    | `INT64_TO_INT, `INT64_TO_INT
    | `TO_UINT8, `TO_UINT8
    | `TO_UINT16, `TO_UINT16
    | `TO_UINT32, `TO_UINT32
    | `TO_UINT64, `TO_UINT64
    | `TO_INT8, `TO_INT8
    | `TO_INT16, `TO_INT16
    | `TO_INT32, `TO_INT32
    | `TO_INT64, `TO_INT64
    | `BV2NAT, `BV2NAT
    | `IS_INT, `IS_INT -> true

  
    | `SELECT a1, `SELECT a2 ->
      (* Same symbol if there are on arrays of the same type *)
      Type.equal_types a1 a2

    | `STORE, `STORE -> true

    | `BVEXTRACT (i1, j1), `BVEXTRACT (i2, j2) -> Numeral.equal i1 i2 && Numeral.equal j1 j2
    | `BVSIGNEXT i1, `BVSIGNEXT i2 -> Numeral.equal i1 i2
    | `BVNOT, `BVNOT 
    | `BVNEG, `BVNEG
    | `BVAND, `BVAND
    | `BVOR, `BVOR
    | `BVADD, `BVADD
    | `BVSUB, `BVSUB
    | `BVMUL, `BVMUL
    | `BVUDIV, `BVUDIV
    | `BVSDIV, `BVSDIV
    | `BVUREM, `BVUREM
    | `BVSREM, `BVSREM
    | `BVSHL, `BVSHL
    | `BVLSHR, `BVLSHR
    | `BVASHR, `BVASHR
    | `BVULT, `BVULT
    | `BVULE, `BVULE
    | `BVUGT, `BVUGT
    | `BVUGE, `BVUGE
    | `BVSLT, `BVSLT
    | `BVSLE, `BVSLE
    | `BVSGT, `BVSGT
    | `BVSGE, `BVSGE
    | `BVCONCAT, `BVCONCAT

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
    | `UINT8_TO_INT, _
    | `UINT16_TO_INT, _
    | `UINT32_TO_INT, _
    | `UINT64_TO_INT, _
    | `INT8_TO_INT, _
    | `INT16_TO_INT, _
    | `INT32_TO_INT, _
    | `INT64_TO_INT, _
    | `TO_UINT8, _    
    | `TO_UINT16, _ 
    | `TO_UINT32, _ 
    | `TO_UINT64, _
    | `TO_INT8, _    
    | `TO_INT16, _ 
    | `TO_INT32, _ 
    | `TO_INT64, _ 
    | `BV2NAT, _
    | `IS_INT, _
    | `SELECT _, _
    | `STORE, _ 
    | `BVEXTRACT _, _
    | `BVCONCAT, _
    | `BVSIGNEXT _, _

    | `BVNOT, _ 
    | `BVNEG, _
    | `BVAND, _
    | `BVOR, _
    | `BVADD, _
    | `BVSUB, _
    | `BVMUL, _
    | `BVUDIV, _
    | `BVSDIV, _
    | `BVUREM, _
    | `BVSREM, _
    | `BVSHL, _
    | `BVLSHR, _
    | `BVASHR, _
    | `BVULT, _ 
    | `BVULE, _
    | `BVUGT, _
    | `BVUGE, _
    | `BVSLT, _ 
    | `BVSLE, _
    | `BVSGT, _
    | `BVSGE, _ -> false


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
  | `UBV b -> Bitvector.pp_smtlib_print_bitvector_b ppf b
  | `BV b -> Bitvector.pp_smtlib_print_bitvector_b ppf b

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
  | `UINT8_TO_INT -> Format.pp_print_string ppf "bv2nat"
  | `UINT16_TO_INT -> Format.pp_print_string ppf "bv2nat"
  | `UINT32_TO_INT -> Format.pp_print_string ppf "bv2nat"
  | `UINT64_TO_INT -> Format.pp_print_string ppf "bv2nat"
  | `INT8_TO_INT -> Format.pp_print_string ppf "int8_to_int"
  | `INT16_TO_INT -> Format.pp_print_string ppf "int16_to_int"
  | `INT32_TO_INT -> Format.pp_print_string ppf "int32_to_int"
  | `INT64_TO_INT -> Format.pp_print_string ppf "int64_to_int"
  | `TO_UINT8 -> Format.pp_print_string ppf "(_ int2bv 8)"
  | `TO_UINT16 -> Format.pp_print_string ppf "(_ int2bv 16)"
  | `TO_UINT32 -> Format.pp_print_string ppf "(_ int2bv 32)"
  | `TO_UINT64 -> Format.pp_print_string ppf "(_ int2bv 64)"
  | `TO_INT8 -> Format.pp_print_string ppf "(_ int2bv 8)"
  | `TO_INT16 -> Format.pp_print_string ppf "(_ int2bv 16)"
  | `TO_INT32 -> Format.pp_print_string ppf "(_ int2bv 32)"
  | `TO_INT64 -> Format.pp_print_string ppf "(_ int2bv 64)"
  | `BV2NAT -> Format.pp_print_string ppf "bv2nat"
  | `IS_INT -> Format.pp_print_string ppf "is_int"

  | `DIVISIBLE n -> 
    Format.pp_print_string ppf "divisible";
    Format.pp_print_space ppf ();
    Numeral.pp_print_numeral ppf n

  | `BVNOT -> Format.pp_print_string ppf "bvnot"
  | `BVNEG -> Format.pp_print_string ppf "bvneg"
  | `BVAND -> Format.pp_print_string ppf "bvand"
  | `BVOR -> Format.pp_print_string ppf "bvor"
  | `BVADD -> Format.pp_print_string ppf "bvadd"
  | `BVSUB -> Format.pp_print_string ppf "bvsub"
  | `BVMUL -> Format.pp_print_string ppf "bvmul"
  | `BVUDIV -> Format.pp_print_string ppf "bvudiv"
  | `BVSDIV -> Format.pp_print_string ppf "bvsdiv"
  | `BVUREM -> Format.pp_print_string ppf "bvurem"
  | `BVSREM -> Format.pp_print_string ppf "bvsrem"
  | `BVSHL -> Format.pp_print_string ppf "bvshl"
  | `BVLSHR -> Format.pp_print_string ppf "bvlshr"
  | `BVASHR -> Format.pp_print_string ppf "bvashr"
  | `BVULT -> Format.pp_print_string ppf "bvult"
  | `BVULE -> Format.pp_print_string ppf "bvule"
  | `BVUGT -> Format.pp_print_string ppf "bvugt"
  | `BVUGE -> Format.pp_print_string ppf "bvuge"
  | `BVSLT -> Format.pp_print_string ppf "bvslt"
  | `BVSLE -> Format.pp_print_string ppf "bvsle"
  | `BVSGT -> Format.pp_print_string ppf "bvsgt"
  | `BVSGE -> Format.pp_print_string ppf "bvsge"
  | `BVCONCAT -> Format.pp_print_string ppf "concat"
  | `BVEXTRACT (i, j) -> 
      Format.fprintf 
      ppf 
      "(_ extract %a %a)" 
      Numeral.pp_print_numeral i
      Numeral.pp_print_numeral j
  | `BVSIGNEXT i ->
      Format.fprintf
      ppf
      "(_ sign_extend %a)"
      Numeral.pp_print_numeral i

  | `SELECT _ -> Format.pp_print_string ppf "select"
  | `STORE -> Format.pp_print_string ppf "store"
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

(* Return true if the symbol is a bitvector *)
let is_bitvector = function 
  | { Hashcons.node = `BV _ } -> true 
  | _ -> false

(* Return true if the symbol is an unsigned bitvector *)
let is_ubitvector = function
  | { Hashcons.node = `UBV _ } -> true
  | _ -> false

(* Return true if the symbol is an unsigned bitvector of size 8 *)
let is_ubv8 = function
  | { Hashcons.node = `UBV n } -> 
      if (Bitvector.length_of_bitvector n = 8) then true else false
  | _ -> false

(* Return true if the symbol is an unsigned bitvector of size 16 *)
let is_ubv16 = function
  | { Hashcons.node = `UBV n } -> 
      if (Bitvector.length_of_bitvector n = 16) then true else false
  | _ -> false

(* Return true if the symbol is an unsigned bitvector of size 32 *)
let is_ubv32 = function
  | { Hashcons.node = `UBV n } -> 
      if (Bitvector.length_of_bitvector n = 32) then true else false
  | _ -> false

(* Return true if the symbol is an unsigned bitvector of size 64 *)
let is_ubv64 = function
  | { Hashcons.node = `UBV n } -> 
      if (Bitvector.length_of_bitvector n = 64) then true else false
  | _ -> false

(* Return true if the symbol is a bitvector of size 8 *)
let is_bv8 = function
  | { Hashcons.node = `BV n } -> 
      if (Bitvector.length_of_bitvector n = 8) then true else false
  | _ -> false

(* Return true if the symbol is a bitvector of size 16 *)
let is_bv16 = function
  | { Hashcons.node = `BV n } -> 
      if (Bitvector.length_of_bitvector n = 16) then true else false
  | _ -> false

(* Return true if the symbol is a bitvector of size 32 *)
let is_bv32 = function
  | { Hashcons.node = `BV n } -> 
      if (Bitvector.length_of_bitvector n = 32) then true else false
  | _ -> false

(* Return true if the symbol is a bitvector of size 64 *)
let is_bv64 = function
  | { Hashcons.node = `BV n } -> 
      if (Bitvector.length_of_bitvector n = 64) then true else false
  | _ -> false

(* Return true if the symbol is a to_uint8 *)
let is_to_uint8 = function
  | { Hashcons.node = `TO_UINT8 } -> true
  | _ -> false

(* Return true if the symbol is a to_uint16 *)
let is_to_uint16 = function
  | { Hashcons.node = `TO_UINT16 } -> true
  | _ -> false

(* Return true if the symbol is a to_uint32 *)
let is_to_uint32 = function
  | { Hashcons.node = `TO_UINT32 } -> true
  | _ -> false

(* Return true if the symbol is a to_uint64 *)
let is_to_uint64 = function
  | { Hashcons.node = `TO_UINT64 } -> true
  | _ -> false

(* Return true if the symbol is a to_int8 *)
let is_to_int8 = function
  | { Hashcons.node = `TO_INT8 } -> true
  | _ -> false

(* Return true if the symbol is a to_int16 *)
let is_to_int16 = function
  | { Hashcons.node = `TO_INT16 } -> true
  | _ -> false

(* Return true if the symbol is a to_int32 *)
let is_to_int32 = function
  | { Hashcons.node = `TO_INT32 } -> true
  | _ -> false

(* Return true if the symbol is a to_int64 *)
let is_to_int64 = function
  | { Hashcons.node = `TO_INT64 } -> true
  | _ -> false

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

(* Return the bitvector in a `BV symbol  *)
let bitvector_of_symbol =  function 
  | { Hashcons.node = `BV b } -> b 
  | _ -> raise (Invalid_argument "bitvector_of_symbol")

(* Return the unsigned bitvector in a `UBV symbol *)
let ubitvector_of_symbol = function
  | { Hashcons.node = `UBV b } -> b
  | _ -> raise (Invalid_argument "ubitvector_of_symbol")

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

(* Return true if the symbol is [`ITE] *)
let is_ite = function
  | { Hashcons.node = `ITE } -> true
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

(* Constant ite symbol *)
let s_ite = mk_symbol `ITE

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

let s_to_int = mk_symbol `TO_INT

let s_to_real = mk_symbol `TO_REAL

(* Array read operator *)
let s_select ta = mk_symbol (`SELECT ta)

let is_select = function 
  | { Hashcons.node = `SELECT _ } -> true
  | { Hashcons.node = `UF u } ->
    let s = UfSymbol.string_of_uf_symbol u in
    (try Scanf.sscanf s "_select%s" (fun _ -> true)
     with Scanf.Scan_failure _ -> false)
  | _ -> false

let is_divisible = function
  | { Hashcons.node = `DIVISIBLE _ } -> true
  | _ -> false

let s_store = mk_symbol `STORE

(* Constant integer -> machine integer operators *)
let s_to_uint8 = mk_symbol `TO_UINT8

let s_to_uint16 = mk_symbol `TO_UINT16

let s_to_uint32 = mk_symbol `TO_UINT32

let s_to_uint64 = mk_symbol `TO_UINT64

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
