open Lib

(*--------------------------- Dummy values ------------------------------*)

let config () =  [|  |]

let check_sat_limited_cmd ms = failwith "Not implemented"

let check_sat_assuming_supported () = failwith "Not implemented"

(*-------------------------- Default values ------------------------------*)

let headers () = []

let trace_extension = "smt2"

let comment_delims = ";;", ""


(* Convert a logic to a string *)
let string_of_logic = function
  | `AUFLIA -> "AUFLIA"
  | `AUFLIRA -> "AUFLIRA"
  | `AUFNIRA -> "AUFNIRA"
  | `LRA -> "LRA"
  | `LIA -> "LIA"
  | `QF_ABV -> "QF_ABV"
  | `QF_AUFBV -> "QF_AUFBV"
  | `QF_AUFLIA -> "QF_AUFLIA"
  | `QF_AX -> "QF_AX"
  | `QF_BV -> "QF_BV"
  | `QF_IDL -> "QF_IDL"
  | `QF_LIA -> "QF_LIA"
  | `QF_LRA -> "QF_LRA"
  | `QF_NIA -> "QF_NIA"
  | `QF_NRA -> "QF_NRA"
  | `QF_RDL -> "QF_RDL"
  | `QF_UF -> "QF_UF"
  | `QF_UFBV -> "QF_UFBV"
  | `QF_UFIDL -> "QF_UFIDL"
  | `QF_UFLIA -> "QF_UFLIA"
  | `QF_UFLRA -> "QF_UFLRA"
  | `QF_UFNRA -> "QF_UFNRA"
  | `UFLIA -> "UFLIA"
  | `UFLRA -> "UFLRA"
  | `UFNIA -> "UFNIA"
  | _ -> raise (Invalid_argument "Unsupported logic")


(* Pretty-print a logic identifier *)
let pp_print_logic ppf l = 
  Format.pp_print_string ppf (string_of_logic l) 


let interpr_type t = match Type.node_of_type t with
  | Type.IntRange _ -> Type.mk_int ()
  | Type.Bool | Type.Int | Type.Real -> t
  | _ -> failwith ((Type.string_of_type t)^" not supported")


let pp_print_sort ppf t =
  Type.pp_print_type ppf (interpr_type t)


let string_of_sort = string_of_t pp_print_sort


(* Static hashconsed strings *)
let s_int = HString.mk_hstring "Int"
let s_real = HString.mk_hstring "Real"
let s_bool = HString.mk_hstring "Bool"


(* Convert an S-expression to a sort *)
let type_of_string_sexpr = function 

  | HStringSExpr.Atom s when s == s_int -> Type.t_int

  | HStringSExpr.Atom s when s == s_real -> Type.t_real

  | HStringSExpr.Atom s when s == s_bool -> Type.t_bool 

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
   ("xor", Symbol.mk_symbol `XOR);
   ("=", Symbol.mk_symbol `EQ);
   ("distinct", Symbol.mk_symbol `DISTINCT);
   ("ite", Symbol.mk_symbol `ITE);
   ("-", Symbol.mk_symbol `MINUS);
   ("+", Symbol.mk_symbol `PLUS);
   ("*", Symbol.mk_symbol `TIMES);
   ("/", Symbol.mk_symbol `DIV);
   ("div", Symbol.mk_symbol `INTDIV);
   ("mod", Symbol.mk_symbol `MOD);
   ("abs", Symbol.mk_symbol `ABS);
   ("<=", Symbol.mk_symbol `LEQ);
   ("<", Symbol.mk_symbol `LT);
   (">=", Symbol.mk_symbol `GEQ);
   (">", Symbol.mk_symbol `GT);
   ("to_real", Symbol.mk_symbol `TO_REAL);
   ("to_int", Symbol.mk_symbol `TO_INT);
   ("is_int", Symbol.mk_symbol `IS_INT);
   ("concat", Symbol.mk_symbol `CONCAT);
   ("bvnot", Symbol.mk_symbol `BVNOT);
   ("bvneg", Symbol.mk_symbol `BVNEG);
   ("bvand", Symbol.mk_symbol `BVAND);
   ("bvor", Symbol.mk_symbol `BVOR);
   ("bvadd", Symbol.mk_symbol `BVADD);
   ("bvmul", Symbol.mk_symbol `BVMUL);
   ("bvdiv", Symbol.mk_symbol `BVDIV);
   ("bvurem", Symbol.mk_symbol `BVUREM);
   ("bvshl", Symbol.mk_symbol `BVSHL);
   ("bvlshr", Symbol.mk_symbol `BVLSHR);
   ("bvult", Symbol.mk_symbol `BVULT);
   ("select", Symbol.mk_symbol `SELECT);
   ("store", Symbol.mk_symbol `STORE)]


(* Reserved words that we don't support *)
let reserved_word_list = 
  List.map 
    HString.mk_hstring 
    ["par"; "_"; "!"; "as" ]



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
  | `DISTINCT -> Format.pp_print_string ppf "distinct"
  | `ITE -> Format.pp_print_string ppf "ite" 

  | `NUMERAL i -> Numeral.pp_print_numeral_sexpr ppf i
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

  | `SELECT -> Format.pp_print_string ppf "select"
  | `STORE -> Format.pp_print_string ppf "store"

  | `UF u -> UfSymbol.pp_print_uf_symbol ppf u

(* Pretty-print a hashconsed symbol *)
and pp_print_symbol ?arity ppf s =
  pp_print_symbol_node ?arity ppf (Symbol.node_of_symbol s)


(* Return a string representation of a hashconsed symbol *)
let string_of_symbol ?arity s = string_of_t (pp_print_symbol ?arity) s



