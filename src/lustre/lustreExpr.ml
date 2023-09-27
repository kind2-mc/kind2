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

(* Abbreviations *)
module I = LustreIdent

module SVS = StateVar.StateVarSet
module VS = Var.VarSet

(* Exceptions *)
exception Type_mismatch

(* A Lustre expression is a term *)
type expr = Term.t

(* Lift of [Term.is_true]. *)
let is_true_expr e = e = Term.t_true

(* A Lustre type is a type *)
(* type lustre_type = Type.t *)

(* A typed Lustre expression *)
type t = { 
  
  (* Lustre expression for the initial state *)
  expr_init: expr;

  (* Lustre expression after initial state *)
  expr_step: expr;
  
  (* Type of expression

     Keep the type here instead of reading from expr_init or
     expr_step, otherwise we need to get both types and merge *)
  expr_type: Type.t 

}

(* Bound for index variable, or fixed value for index variable *)
type 'a bound_or_fixed = 
  | Bound of 'a  (* Upper bound for index variable *)
  | Fixed of 'a  (* Fixed value for index variable *)
  | Unbound of 'a  (* unbounded index variable *)

type num = 
  | Number of Numeral.t 
  | Inf
  | NegInf
  | Nothing

let compare_expr = Term.compare

(* Total order on expressions *)
let compare
    { expr_init = init1; expr_step = step1 } 
    { expr_init = init2; expr_step = step2 } =

  (* Lexicographic comparision of initial value, step value *)
  let c_init = compare_expr init1 init2 in 
  if c_init = 0 then compare_expr step1 step2 else c_init


(* Equality on expressions *)
let equal
    { expr_init = init1; expr_step = step1 } 
    { expr_init = init2; expr_step = step2 } = 

  Term.equal init1 init2 && Term.equal step1 step2


(* Hashing of expressions *)
let hash { expr_init; expr_step } =
  Hashtbl.hash
    (Term.hash expr_init, Term.hash expr_step)


(* Map on expression

   We want to use the constructors of this module instead of the
   functions of the term module to get type checking and
   simplification. Therefore the function [f] gets values of type [t],
   not of type [expr].

   A Lustre expression of type [t] has the [->] only at the top with
   the [expr_init] as the left operand and [expr_step] as the
   right. We apply Term.map separately to [expr_init] and [expr_step],
   which are of type [expr = Term.t] and construct a new Lustre
   expression from the result.

   When mapping [expr_init], we know that we are on the left side of a
   [->] operator. If the result of [f] is [l -> r] we always take [l],
   because [(l -> r) -> t = (l -> t)]. Same for [expr_step], because
   [t -> (l -> r) = t -> r].
*)
let map f { expr_init; expr_step } = 

  (* Create a Lustre expression from a term and return a term, if
     [init] is true considering [expr_init] only, otherwise [expr_step]
     only. *)
  let f' init i term = 

    (* Construct Lustre expression from term, using the term for both
       the initial state and the step state *)
    let expr = 
      { expr_init = term; 
        expr_step = term;
        expr_type = Term.type_of_term term }
    in

    (* Which of Init or step? *)
    if init then 
      
      (* Return term for initial state *)
      (f i expr).expr_init

    else

      (* Return term for step state *)
      (f i expr).expr_step

  in

  (* Apply function separately to init and step expression and
     rebuild *)
  let expr_init = Term.map (f' true) expr_init in
  let expr_step = Term.map (f' false) expr_step in
  let expr_type = Term.type_of_term expr_init in
      
  { expr_init; expr_step; expr_type }


let map_vars_expr = Term.map_vars 
  
let map_vars f { expr_init = i; expr_step = s; expr_type = t } = {
  expr_init = map_vars_expr f i;
  expr_step = map_vars_expr f s;
  expr_type = t
}

(*

let rec map_top' f term = match Term.T.node_of_t term with 

  | Term.T.FreeVar _ -> f term 

  | Term.T.Node (s, _) when Symbol.equal_symbols s Symbol.s_select -> f term

  | Term.T.BoundVar _ -> term 

  | Term.T.Leaf _ -> term 

  | Term.T.Node (s, l) -> Term.T.mk_app s (List.map (map_array_var' f) l)

  | Term.T.Let (l, t)  -> 
    Term.T.mk_let_of_lambda (map_array_var'' f l) (List.map (map_array_var' f) t)

  | Term.T.Exists l  -> 
    Term.T.mk_exists_of_lambda (map_array_var'' f l)

  | Term.T.Forall l  -> 
    Term.T.mk_forall_of_lambda (map_array_var'' f l)

  | Term.T.Annot (t, a) -> Term.T.mk_annot (map_array_var' f t) a

and map_array_var'' f lambda = match Term.T.node_of_lambda lambda with

  | Term.T.L (l, t) -> Term.T.mk_lambda_of_term l (map_array_var' f t)


let map_array_var f ({ expr_init; expr_step } as expr) =

  { expr with
      expr_init = map_array_var' f' expr_init;
      expr_step = map_array_var' f' expr_step }
      
*)


(* Return the type of the expression *)
let type_of_lustre_expr { expr_type } = expr_type


let type_of_expr e = Term.type_of_term e


(* Hash table over Lustre expressions *)
module LustreExprHashtbl = Hashtbl.Make
    (struct
      type z = t
      type t = z (* avoid cyclic type abbreviation *)
      let equal = equal
      let hash = hash
    end)


(* Equality on expressions *)
let equal_expr = Term.equal


(* These offsets are different from the offsets in the transition system,
   because here we want to know if the initial and the step
   expressions are equal without bumping offsets. *)

(* Offset of state variable at first instant *)
let base_offset = Numeral.zero

(* Offset of state variable at first instant *)
let pre_base_offset = Numeral.(pred base_offset)

(* Offset of state variable at current instant *)
let cur_offset = base_offset

(* Offset of state variable at previous instant *)
let pre_offset = Numeral.(pred cur_offset)




(* ********************************************************************** *)
(* Pretty-printing                                                        *)
(* ********************************************************************** *)

(* Pretty-print a type as a Lustre type *)
let rec pp_print_lustre_type safe ppf t = match Type.node_of_type t with

  | Type.Bool -> Format.pp_print_string ppf "bool"

  | Type.Int -> Format.pp_print_string ppf "int"

  | Type.IntRange (i, j) -> 
    Format.fprintf
      ppf 
      "subrange [%a, %a] of int" 
      pp_print_bound_opt i 
      pp_print_bound_opt j

  | Type.Real -> Format.pp_print_string ppf "real"

  | Type.Abstr s -> Format.pp_print_string ppf s

  | Type.Enum (_, _) -> 
     let cs = Type.constructors_of_enum t in
     Format.fprintf ppf "enum {%a}"
       (pp_print_list Format.pp_print_string ", ") cs

  | Type.UBV i -> 
     begin match i with
     | 8 -> Format.pp_print_string ppf "uint8"
     | 16 -> Format.pp_print_string ppf "uint16"
     | 32 -> Format.pp_print_string ppf "uint32"
     | 64 -> Format.pp_print_string ppf "uint64"
     | _ -> raise 
      (Invalid_argument "pp_print_lustre_type: UBV size not allowed")
     end

  | Type.BV i -> 
     begin match i with
     | 8 -> Format.pp_print_string ppf "int8"
     | 16 -> Format.pp_print_string ppf "int16"
     | 32 -> Format.pp_print_string ppf "int32"
     | 64 -> Format.pp_print_string ppf "int64"
     | _ -> raise 
      (Invalid_argument "pp_print_lustre_type: BV size not allowed")
     end

  | Type.Array (s, _) ->

    Format.fprintf ppf "array of %a" (pp_print_lustre_type safe) s


(* String representation of a symbol in Lustre *)
let string_of_symbol = function
  | `TRUE -> "true"
  | `FALSE -> "false"
  | `NOT -> "not"
  | `IMPLIES -> "=>"
  | `AND -> "and"
  | `OR -> "or"
  | `EQ -> "="
  | `NUMERAL n -> Numeral.string_of_numeral n
  | `DECIMAL d -> Decimal.string_of_decimal_lustre d
  | `XOR -> "xor"
  | `UBV b ->
          (match Bitvector.length_of_bitvector b with
          | 8 -> "(uint8 " ^ (Numeral.string_of_numeral (Bitvector.ubv8_to_num b)) ^ ")"
          | 16 -> "(uint16 " ^ (Numeral.string_of_numeral (Bitvector.ubv16_to_num b)) ^ ")"
          | 32 -> "(uint32 " ^ (Numeral.string_of_numeral (Bitvector.ubv32_to_num b)) ^ ")"
          | 64 -> "(uint64 " ^ (Numeral.string_of_numeral (Bitvector.ubv64_to_num b)) ^ ")"
          | _ -> raise Type_mismatch)
  | `BV b -> 
          (match Bitvector.length_of_bitvector b with
          | 8 -> "(int8 " ^ (Numeral.string_of_numeral (Bitvector.bv8_to_num b)) ^ ")"
          | 16 -> "(int16 " ^ (Numeral.string_of_numeral (Bitvector.bv16_to_num b)) ^ ")"
          | 32 -> "(int32 " ^ (Numeral.string_of_numeral (Bitvector.bv32_to_num b)) ^ ")"
          | 64 -> "(int64 " ^ (Numeral.string_of_numeral (Bitvector.bv64_to_num b)) ^ ")"
          | _ -> raise Type_mismatch)
  | `MINUS -> "-"
  | `PLUS -> "+"
  | `TIMES -> "*"
  | `DIV -> "/"
  | `INTDIV ->"div"
  | `MOD -> "mod"
  | `ABS -> "abs"
  | `LEQ -> "<="
  | `LT -> "<"
  | `GEQ -> ">="
  | `GT -> ">"
  | `TO_REAL -> "real"
  | `TO_INT -> "int"
  | `TO_UINT8 -> "uint8"
  | `TO_UINT16 -> "uint16"
  | `TO_UINT32 -> "uint32"
  | `TO_UINT64 -> "uint64"
  | `TO_INT8 -> "int8"
  | `TO_INT16 -> "int16"
  | `TO_INT32 -> "int32"
  | `TO_INT64 -> "int64"
  | `BVAND -> "&&"
  | `BVOR -> "||"
  | `BVNOT -> "!"
  | `BVNEG -> "-"
  | `BVADD -> "+"
  | `BVSUB -> "-"
  | `BVMUL -> "*"
  | `BVUDIV -> "div"
  | `BVSDIV -> "div"
  | `BVUREM -> "mod"
  | `BVSREM -> "mod"
  | `BVULT -> "<"
  | `BVULE -> "<="
  | `BVUGT -> ">"
  | `BVUGE -> ">="
  | `BVSLT -> "<"
  | `BVSLE -> "<="
  | `BVSGT -> ">"
  | `BVSGE -> ">="
  | `BVSHL -> "lshift"
  | `BVLSHR -> "rshift"
  | `BVASHR -> "arshift"
  | `BVEXTRACT (i,j) -> "(_ extract " ^ (Numeral.string_of_numeral i) ^ " " ^ (Numeral.string_of_numeral j) ^ ")"
  | `BVCONCAT -> "concat"
  | `BVSIGNEXT i -> "(_ sign_extend " ^ (Numeral.string_of_numeral i) ^ ")" 
  | _ -> failwith "string_of_symbol"



(* Pretty-print a symbol with a given type *)
let pp_print_symbol_as_type as_type ppf s =
  match as_type, s with
  | Some ty, `NUMERAL n when Type.is_enum ty ->
     Type.get_constr_of_num n
     |> Format.pp_print_string ppf
  | _ ->
     Format.pp_print_string ppf (string_of_symbol s) 
    
(* Pretty-print a symbol as is *)
let pp_print_symbol ppf s =
  Format.pp_print_string ppf (string_of_symbol s) 
    

(* Pretty-print a variable *)
let pp_print_lustre_var _ ppf state_var = 
  Format.fprintf ppf "%s" (StateVar.name_of_state_var state_var)


(* Pretty-printa variable with its type *)
let pp_print_lustre_var_typed safe ppf state_var = 

  Format.fprintf ppf
    "%t%a: %a"
    (function ppf -> 
      if StateVar.is_const state_var then Format.fprintf ppf "const ")
    (pp_print_lustre_var safe) state_var
    (pp_print_lustre_type safe) (StateVar.type_of_state_var state_var)
  


(* Pretty-print a variable under [depth] pre operators *)
let rec pp_print_var pvar ppf var =

  (* Variable is at an instant *)
  if Var.is_state_var_instance var then 

    (* Get state variable of variable *)
    let state_var = Var.state_var_of_state_var_instance var in
    
    (* Function to pretty-print a variable with or without pre *)
    let pp = 
      
      (* Variable at current offset *)
      if Numeral.equal (Var.offset_of_state_var_instance var) cur_offset then 
        
        Format.fprintf ppf
          "@[<hv 2>%a@]"
          pvar
          
      (* Variable at previous offset *)
      else if Numeral.equal (Var.offset_of_state_var_instance var) pre_offset then 

      Format.fprintf ppf
        "@[<hv 2>(pre %a)@]"
        pvar

      (* Fail on other offsets *)
      else

        function _ -> raise  (Invalid_argument "pp_print_var")

    in

    (* Pretty-print state variable with or without pre *)
    pp state_var
    
  (* Variable is constant *)
  else if Var.is_const_state_var var then

    (* Get state variable of variable *)
    let state_var = Var.state_var_of_state_var_instance var in
    
    Format.fprintf ppf
      "@[<hv 2>%a@]"
      pvar
      state_var    
    
  (* Fail on other types of variables *)
  else

    (* free variable *)
    Format.fprintf ppf "%s" (Var.string_of_var var)


(* Pretty-print a term *)
and pp_print_term_node ?as_type safe pvar ppf t = match Term.T.destruct t with
    
  | Term.T.Var var -> pp_print_var pvar ppf var
      
  | Term.T.Const s -> 
    
    pp_print_symbol_as_type as_type ppf (Symbol.node_of_symbol s)
      
  | Term.T.App (s, l) -> 

    pp_print_app ?as_type safe pvar ppf (Symbol.node_of_symbol s) l

  (* | Term.T.Attr (t, _) -> 
    
    pp_print_term_node ?as_type safe pvar ppf t *)

  | exception Invalid_argument ex -> (

    match Term.T.node_of_t t with
    | Term.T.Forall l -> (match Term.T.node_of_lambda l with
      Term.T.L (_,t) -> (Format.fprintf ppf
        "@[<hv 1>forall@ @[<hv 1>(...)@ %a@]@]"
          (pp_print_term_node ?as_type safe pvar) t))

    | Term.T.Exists l -> (match Term.T.node_of_lambda l with
      Term.T.L (_,t) -> (Format.fprintf ppf
        "@[<hv 1>exists@ @[<hv 1>(...)@ %a@]@]"
          (pp_print_term_node ?as_type safe pvar) t))

    | Term.T.BoundVar _ -> Term.T.pp_print_term ppf t

    | _ -> raise (Invalid_argument ex)

  )

(* Pretty-print the second and following arguments of a
   left-associative function application *)
and pp_print_app_left' safe pvar s ppf = function

  | h :: tl -> 

    Format.fprintf ppf 
      " %a@ %a%t" 
      pp_print_symbol s 
      (pp_print_term_node safe pvar) h
      (function ppf -> pp_print_app_left' safe pvar s ppf tl)

  | [] -> ()


(* Pretty-print a left-associative function application

   Print (+ a b c) as (a + b + c) *)
and pp_print_app_left safe pvar s ppf = function

  (* Function application must have arguments, is a constant
     otherwise *)
  | [] -> assert false

  (* Print first argument *)
  | h :: tl -> 

    Format.fprintf ppf
      "@[<hv 2>(%a%t)@]" 
      (pp_print_term_node safe pvar) h
      (function ppf -> pp_print_app_left' safe pvar s ppf tl)


(* Pretty-print arguments of a right-associative function application *)
and pp_print_app_right' safe pvar s arity ppf = function

  (* Function application must have arguments, is a constant
     otherwise *)
  | [] -> assert false 

  (* Last or only argument *)
  | [h] -> 

    (* Print closing parentheses for all arguments *)
    let rec aux ppf = function 
      | 0 -> ()
      | i -> 
        Format.fprintf ppf
          "%t)@]"
          (function ppf -> aux ppf (pred i))
    in

    (* Print last argument and close all parentheses *)
    Format.fprintf ppf
      "%a%t" 
      (pp_print_term_node safe pvar) h
      (function ppf -> aux ppf arity)

  (* Second last or earlier argument *)
  | h :: tl -> 

    (* Open parenthesis and print argument *)
    Format.fprintf ppf 
      "@[<hv 2>(%a %a@ %t" 
      (pp_print_term_node safe pvar) h
      pp_print_symbol s 
      (function ppf -> pp_print_app_right' safe pvar s arity ppf tl)


(* Pretty-print a right-associative function application 

   Print (=> a b c) as (a => (b => c)) *)
and pp_print_app_right safe pvar s ppf l =
  pp_print_app_right' safe pvar s (List.length l - 1) ppf l


(* Pretty-print a chaining function application 

   Print (= a b c) as (a = b) and (b = c) *)
and pp_print_app_chain safe pvar s ppf = function

  (* Chaining function application must have more than one argument *)
  | []
  | [_] -> assert false 

  (* Last or only pair of arguments *)
  | [l; r] -> 

    Format.fprintf ppf 
      "@[<hv 2>(%a %a@ %a)@]" 
      (pp_print_term_node safe pvar) l
      pp_print_symbol s
      (pp_print_term_node safe pvar) r

  (* Print function application of first pair, conjunction and continue *)
  | l :: r :: tl -> 

    Format.fprintf ppf 
      "@[<hv 2>(%a %a@ %a) and %a@]" 
      (pp_print_term_node safe pvar) l
      pp_print_symbol s
      (pp_print_term_node safe pvar) r
      (pp_print_app_chain safe pvar s) (r :: tl)


(* Pretty-print a function application *)
and pp_print_app ?as_type safe pvar ppf = function

  (* Function application must have arguments, cannot have nullary
     symbols here *)
  | `TRUE
  | `FALSE
  | `NUMERAL _
  | `DECIMAL _
  | `UBV _
  | `BV _ 
  | `BV2NAT -> (function _ -> assert false)

  (* Unary symbols *) 
  | `NOT
  | `BVNOT
  | `BVNEG
  | `TO_REAL
  | `TO_INT
  | `UINT8_TO_INT
  | `UINT16_TO_INT
  | `UINT32_TO_INT
  | `UINT64_TO_INT
  | `INT8_TO_INT
  | `INT16_TO_INT
  | `INT32_TO_INT
  | `INT64_TO_INT
  | `TO_UINT8
  | `TO_UINT16
  | `TO_UINT32
  | `TO_UINT64
  | `TO_INT8
  | `TO_INT16
  | `TO_INT32
  | `TO_INT64
  | `BVEXTRACT _
  | `BVSIGNEXT _
  | `ABS as s -> 

    (function [a] -> 
      Format.fprintf ppf
        "@[<hv 2>(%a@ %a)@]" 
        pp_print_symbol s 
        (pp_print_term_node safe pvar) a

      | _ -> assert false)
  
  (* Unary and left-associative binary symbols *)
  | `MINUS as s ->
      
      (function 
        | [] -> assert false 
        | [a] ->

          Format.fprintf ppf
            "%a%a" 
            pp_print_symbol s 
            (pp_print_term_node safe pvar) a

        | _ as l -> pp_print_app_left safe pvar s ppf l)
        
    (* Binary left-associative symbols with two or more arguments *)
    | `AND
    | `OR
    | `XOR
    | `BVAND
    | `BVOR
    | `BVADD
    | `BVSUB
    | `BVMUL
    | `BVUDIV
    | `BVSDIV
    | `BVUREM
    | `BVSREM
    | `PLUS
    | `TIMES
    | `DIV
    | `INTDIV as s ->
      
      (function 
        | [] 
        | [_] -> assert false
        | _ as l -> pp_print_app_left safe pvar s ppf l)
            
    (* Binary right-associative symbols *)
    | `IMPLIES as s -> pp_print_app_right safe pvar s ppf
        
    (* Chainable binary symbols *)
    | `EQ
    | `BVULT
    | `BVULE
    | `BVUGT
    | `BVUGE
    | `BVSLT
    | `BVSLE
    | `BVSGT
    | `BVSGE
    | `LEQ
    | `LT
    | `GEQ
    | `GT as s -> pp_print_app_chain safe pvar s ppf

    (* Binary non-associative symbols *)
    | `BVSHL 
    | `BVLSHR 
    | `BVASHR as s -> 
  
      (function 
        | [a;b] -> 

          Format.fprintf ppf
            "@[<hv 2>(%a %a@ %a)@]" 
            (pp_print_term_node safe pvar) a
            pp_print_symbol s 
            (pp_print_term_node safe pvar) b

        | _ -> assert false)
              
    (* if-then-else *)
    | `ITE ->
      
      (function [p; l; r] ->

        Format.fprintf ppf
          "(if %a then %a else %a)"
          (pp_print_term_node safe pvar) p
          (pp_print_term_node ?as_type safe pvar) l
          (pp_print_term_node ?as_type safe pvar) r
          
        | _ -> assert false)
        
    (* Binary symbols *)
    | `MOD as s ->
      
      (function [l; r] ->

        Format.fprintf ppf 
          "@[<hv 2>(%a %a@ %a)@]" 
          (pp_print_term_node safe pvar) l
          pp_print_symbol s
          (pp_print_term_node safe pvar) r
        
        | _ -> assert false)
        
    (* Divisibility *) 
    | `DIVISIBLE n -> 
      
      (function [a] -> 
        
        (* a divisble n becomes a mod n = 0 *)
        pp_print_app 
          safe
          pvar
          ppf
          `EQ
          [Term.T.mk_app 
             (Symbol.mk_symbol `MOD) 
             [a; Term.T.mk_const (Symbol.mk_symbol (`NUMERAL n))];
           Term.T.mk_const (Symbol.mk_symbol (`NUMERAL Numeral.zero))]
          
        | _ -> assert false)

    | `SELECT _ -> 

      (function 
        | [a; i] ->

          Format.fprintf ppf 
            "@[<hv 2>%a[%a]@]" 
            (pp_print_term_node safe pvar) a
            (pp_print_term_node safe pvar) i
            
        | _ -> assert false)

    | `STORE ->
      
      (function 
        | [a; i; v] ->
        
          Format.fprintf ppf 
            "@[<hv 2>(%a with [%a] = %a)@]" 
            (pp_print_term_node safe pvar) a
            (pp_print_term_node safe pvar) i
            (pp_print_term_node safe pvar) v
            
        | _ -> assert false)
        
    | `UF sym as s when Symbol.is_select (Symbol.mk_symbol s) ->
      pp_print_app ?as_type safe pvar ppf (`SELECT (UfSymbol.res_type_of_uf_symbol sym))
        
    (* Unsupported functions symbols *)
    | `BVCONCAT
    | `DISTINCT
    | `IS_INT
    | `UF _ -> (function _ -> assert false)
      

(* Pretty-print a hashconsed term *)
let pp_print_expr_pvar ?as_type safe pvar ppf expr =
  pp_print_term_node ?as_type safe pvar ppf expr

let pp_print_expr ?as_type safe ppf expr =
  pp_print_expr_pvar ?as_type safe (pp_print_lustre_var safe) ppf expr

let pp_print_lustre_expr_pvar safe pvar ppf = function

  (* Same expression for initial state and following states *)
  | { expr_init; expr_step; expr_type }
       when Term.equal expr_init expr_step -> 

    pp_print_expr_pvar ~as_type:expr_type safe pvar ppf expr_step

  (* Print expression of initial state followed by expression for
     following states *)
  | { expr_init; expr_step; expr_type } -> 

    Format.fprintf ppf 
      "@[<hv 1>(%a@ ->@ %a)@]" 
      (pp_print_expr_pvar ~as_type:expr_type safe pvar) expr_init
      (pp_print_expr_pvar ~as_type:expr_type safe pvar) expr_step

(* Pretty-print a term as an expr. *)
let pp_print_term_as_expr = pp_print_expr

let pp_print_term_as_expr_pvar = pp_print_expr_pvar

let pp_print_term_as_expr_mvar ?as_type safe map ppf expr =
  pp_print_term_as_expr_pvar
    ?as_type safe
    (fun fmt sv ->
     Format.fprintf fmt "%s"
       (try
         StateVar.StateVarMap.find sv map
       with Not_found ->
         StateVar.name_of_state_var sv)
    )
    ppf expr

(*
(* Pretty-print a hashconsed term to the standard formatter *)
let print_expr ?as_type safe =
  pp_print_expr ?as_type safe Format.std_formatter
*)

(* Pretty-print a typed Lustre expression *)
let pp_print_lustre_expr safe ppf = function

  (* Same expression for initial state and following states *)
  | { expr_init; expr_step; expr_type }
       when Term.equal expr_init expr_step ->

    pp_print_expr ~as_type:expr_type safe ppf expr_step

  (* Print expression of initial state followed by expression for
     following states *)
  | { expr_init; expr_step; expr_type } ->

    Format.fprintf ppf
      "@[<hv 1>(%a@ ->@ %a)@]" 
      (pp_print_expr ~as_type:expr_type safe) expr_init
      (pp_print_expr ~as_type:expr_type safe) expr_step

(** Pretty-print a bound or fixed annotation *)
let pp_print_bound_or_fixed ppf = function
  | Bound x -> Format.fprintf ppf "@[<hv 1>(Bound %a)@]" (pp_print_expr true) x
  | Fixed x -> Format.fprintf ppf "@[<hv 1>(Fixed %a)@]" (pp_print_expr true) x
  | Unbound x -> Format.fprintf ppf "@[<hv 1>(Unbound %a)@]" (pp_print_expr true) x

(* ********************************************************************** *)
(* Predicates                                                             *)
(* ********************************************************************** *)


(* Return true if expression is a previous state variable *)
let has_pre_var zero_offset { expr_step } = 

  (* Previous state variables have negative offset *)
  match Term.var_offsets_of_term expr_step with 
    | Some n, _ when Numeral.(n <= zero_offset + pre_offset) -> true
    | _ -> false


(* Return true if there is an unguarded pre operator in the expression *)
let pre_is_unguarded { expr_init } = 

  (* Check if there is a pre operator in the init expression *)
  match Term.var_offsets_of_term expr_init with 
    | None, _ -> false
    | Some c, _ -> Numeral.(c < base_offset)


(* Return true if expression is a current state variable *)
let is_var_at_offset { expr_init; expr_step } (init_offset, step_offset) = 

  (* Term must be a free variable *)
  Term.is_free_var expr_init && 

  (* Get free variable of term *)
  let var_init = Term.free_var_of_term expr_init in 

  (* Variable must be an instance of a state variable *)
  Var.is_state_var_instance var_init && 

  (* Variable must be at instant zero *)
  Numeral.(Var.offset_of_state_var_instance var_init = init_offset) &&

  (* Term must be a free variable *)
  Term.is_free_var expr_step && 

  (* Get free variable of term *)
  let var_step = Term.free_var_of_term expr_step in 

  (* Variable must be an instance of a state variable *)
  Var.is_state_var_instance var_step && 

  (* Variable must be at instant zero *)
  Numeral.(Var.offset_of_state_var_instance var_step = step_offset)(*  && *)

  (* StateVar.equal_state_vars *)
  (*   (Var.state_var_of_state_var_instance var_step) *)
  (*   (Var.state_var_of_state_var_instance var_step) *)



(* Return true if expression is a current state variable *)
let is_var expr = is_var_at_offset expr (base_offset, cur_offset)

(* Return true if expression is a constant state variable *)
let is_const_var { expr_init; expr_step } = 
  Term.is_free_var expr_init && Term.is_free_var expr_step
  && Var.is_const_state_var (Term.free_var_of_term expr_init)
  && Var.is_const_state_var (Term.free_var_of_term expr_step)

                          
(* Return true if expression is a previous state variable *)
let is_pre_var expr = is_var_at_offset expr (pre_base_offset, pre_offset)

let is_const_expr expr = 
  VS.for_all Var.is_const_state_var (Term.vars_of_term expr)
  
(* Return true if the expression is constant *)
let is_const { expr_init; expr_step } = 
  is_const_expr expr_init && is_const_expr expr_step &&
    Term.equal expr_init expr_step
    

(* ********************************************************************** *)
(* Conversion to terms                                                    *)
(* ********************************************************************** *)

(* Instance of state variable at instant zero *)
let pre_base_var_of_state_var zero_offset state_var = 
  Var.mk_state_var_instance 
    state_var
    Numeral.(zero_offset |> pred)


(* Instance of state variable at instant zero *)
let base_var_of_state_var zero_offset state_var = 
  Var.mk_state_var_instance
    state_var
    zero_offset


(* Instance of state variable at current instant *)
let cur_var_of_state_var zero_offset state_var = 
  Var.mk_state_var_instance
    state_var
    zero_offset


(* Instance of state variable at previous instant *)
let pre_var_of_state_var zero_offset state_var = 
  Var.mk_state_var_instance 
    state_var
    Numeral.(zero_offset |> pred)

(*    
(* Term of instance of state variable at previous instant *)
let pre_base_term_of_state_var zero_offset state_var = 
  pre_base_var_of_state_var zero_offset state_var
  |> Term.mk_var
*)

(* Term of instance of state variable at previous instant *)
let base_term_of_state_var zero_offset state_var = 
  base_var_of_state_var zero_offset state_var
  |> Term.mk_var


(* Term of instance of state variable at current instant *)
let cur_term_of_state_var zero_offset state_var = 
  cur_var_of_state_var zero_offset state_var
  |> Term.mk_var


(* Term of instance of state variable at previous instant *)
let pre_term_of_state_var zero_offset state_var = 
  pre_var_of_state_var zero_offset state_var
  |> Term.mk_var


(* Term at instant zero *)
let base_term_of_expr zero_offset expr = 
  Term.bump_state Numeral.(zero_offset - base_offset) expr


(* Term at current instant *)
let cur_term_of_expr zero_offset expr =
  Term.bump_state Numeral.(zero_offset - cur_offset) expr


(* Term at previous instant *)
let pre_term_of_expr zero_offset expr = 
  Term.bump_state Numeral.(zero_offset - cur_offset |> pred) expr


(* Term at instant zero *)
let base_term_of_t zero_offset { expr_init } = 
  base_term_of_expr zero_offset expr_init


(* Term at current instant *)
let cur_term_of_t zero_offset { expr_step } =
  cur_term_of_expr zero_offset expr_step


(* Term at previous instant *)
let pre_term_of_t zero_offset { expr_step } = 
  pre_term_of_expr zero_offset expr_step


(* Return the state variable of a variable *)
let state_var_of_expr ({ expr_init } as expr) = 

  (* Initial value and step value must be identical *)
  if is_var expr || is_pre_var expr then

    try 
      
      (* Get free variable of term *)
      let var = Term.free_var_of_term expr_init in 
      
      (* Get instance of state variable *)
      Var.state_var_of_state_var_instance var
        
    (* Fail if any of the above fails *)
    with Invalid_argument _ -> raise (Invalid_argument "state_var_of_expr")

  else

    (* Fail if initial value is different from step value *)
    raise (Invalid_argument "state_var_of_expr")

(*
(* Return the free variable of a variable *)
let var_of_expr { expr_init } = 
  try
    Term.free_var_of_term expr_init
  (* Fail if any of the above fails *)
  with Invalid_argument _ -> raise (Invalid_argument "var_of_expr")
*)

(* Return the free variable of a variable *)
let var_of_expr { expr_init } = 
  try
    Term.free_var_of_term expr_init
  (* Fail if any of the above fails *)
  with Invalid_argument _ -> raise (Invalid_argument "var_of_expr")

let var_of_init_expr { expr_init } = 
  try
    Term.free_var_of_term expr_init
  (* Fail if any of the above fails *)
  with Invalid_argument _ -> raise (Invalid_argument "var_of_init_expr")

(* Return all state variables *)
let state_vars_of_expr { expr_init; expr_step } = 

  (* State variables in initial state expression *)
  let state_vars_init = Term.state_vars_of_term expr_init in

  (* State variables in step state expression *)
  let state_vars_step = Term.state_vars_of_term expr_step in

  (* Join sets of state variables *)
  SVS.union state_vars_init state_vars_step

            
(* Return all state variables *)
let vars_of_expr { expr_init; expr_step } = 

  (* State variables in initial state expression *)
  let vars_init = Term.vars_of_term expr_init in

  (* State variables in step state expression *)
  let vars_step = Term.vars_of_term expr_step in

  (* Join sets of state variables *)
  Var.VarSet.union vars_init vars_step


(* Return all state variables at the current instant in the initial
   state expression *)
let base_state_vars_of_init_expr { expr_init } = 

  Term.state_vars_at_offset_of_term
    base_offset
    (base_term_of_expr base_offset expr_init)


(* Return all state variables at the current instant in the initial
   state expression *)
let cur_state_vars_of_step_expr { expr_step } = 

  Term.state_vars_at_offset_of_term
    cur_offset
    (cur_term_of_expr cur_offset expr_step)


let indexes_of_state_vars_in_init sv { expr_init } =
  Term.indexes_of_state_var sv expr_init

let indexes_of_state_vars_in_step sv { expr_step } =
  Term.indexes_of_state_var sv expr_step


(* Split a list of Lustre expressions into a list of pairs of
   expressions for the initial step and the transition steps,
   respectively *)
let split_expr_list list = 

  List.fold_left
    (fun (accum_init, accum_step) { expr_init; expr_step } -> 
       ((if expr_init == Term.t_true then 
           accum_init 
         else
           expr_init :: accum_init), 
        (if expr_step == Term.t_true then 
           accum_step
         else
           expr_step :: accum_step)))
    ([], [])
    list      


let init_expr { expr_init } = expr_init

let step_expr { expr_step } = expr_step 


(* ********************************************************************** *)
(* Generic constructors                                                   *)
(* ********************************************************************** *)

(* These constructors take as arguments functions [eval] and [type_of]
   whose arity matches the arity of the constructors, where [eval]
   applies the operator and simplifies the expression, and [type_of]
   returns the type of the resulting expression or fails with
   {!Type_mismatch}. *)

(* Construct a unary expression *)
let mk_unary eval type_of expr = 

  let res_type = type_of expr.expr_type in

  { expr_init = eval expr.expr_init;
    expr_step = eval expr.expr_step;
    expr_type = res_type } 


(* Construct a binary expression *)
let mk_binary eval type_of expr1 expr2 = 

  let res_type = 
    type_of expr1.expr_type expr2.expr_type 
  in

  { expr_init = eval expr1.expr_init expr2.expr_init;
    expr_step = eval expr1.expr_step expr2.expr_step;
    expr_type = res_type } 


(* Construct a binary expression *)
let mk_ternary eval type_of expr1 expr2 expr3 = 

  let res_type = 
    type_of expr1.expr_type expr2.expr_type expr3.expr_type 
  in

  { expr_init = eval expr1.expr_init expr2.expr_init expr3.expr_init;
    expr_step = eval expr1.expr_step expr2.expr_step expr3.expr_step;
    expr_type = res_type } 


(* ********************************************************************** *)
(* Constant constructors                                                  *)
(* ********************************************************************** *)
  

(* Boolean constant true *)
let t_true = 

  let expr = Term.t_true in

  { expr_init = expr; 
    expr_step = expr; 
    expr_type = Type.t_bool } 


(* Boolean constant false *)
let t_false =  

  let expr = Term.t_false in

  { expr_init = expr; 
    expr_step = expr; 
    expr_type = Type.t_bool } 


let mk_constr c t =  

  let expr = Term.mk_constr c in

  { expr_init = expr; 
    expr_step = expr; 
    expr_type = t } 

(* Integer constant *)
let mk_int d =  

  let expr = Term.mk_num d in

  { expr_init = expr; 
    expr_step = expr; 
    expr_type = Type.mk_int_range (Some d) (Some d) } 

(* Unsigned integer8 constant *)
let mk_uint8 d =

  let expr = Term.mk_num d in

  { expr_init = expr;
    expr_step = expr;
    expr_type = Type.t_ubv 8 }

(* Unsigned integer16 constant *)
let mk_uint16 d =

  let expr = Term.mk_num d in

  { expr_init = expr;
    expr_step = expr;
    expr_type = Type.t_ubv 16 }

(* Unsigned integer32 constant *)
let mk_uint32 d =

  let expr = Term.mk_num d in

  { expr_init = expr;
    expr_step = expr;
    expr_type = Type.t_ubv 32 }

(* Unsigned integer64 constant *)
let mk_uint64 d =

  let expr = Term.mk_num d in

  { expr_init = expr;
    expr_step = expr;
    expr_type = Type.t_ubv 64 }

(* Integer8 constant *)
let mk_int8 d =

  let expr = Term.mk_num d in

  { expr_init = expr;
    expr_step = expr;
    expr_type = Type.t_bv 8 }

(* Integer16 constant *)
let mk_int16 d =

  let expr = Term.mk_num d in

  { expr_init = expr;
    expr_step = expr;
    expr_type = Type.t_bv 16 }

(* Integer32 constant *)
let mk_int32 d =

  let expr = Term.mk_num d in

  { expr_init = expr;
    expr_step = expr;
    expr_type = Type.t_bv 32 }

(* Integer64 constant *)
let mk_int64 d =

  let expr = Term.mk_num d in

  { expr_init = expr;
    expr_step = expr;
    expr_type = Type.t_bv 64 }

(* Real constant *)
let mk_real f =  

  let expr = Term.mk_dec f in

  { expr_init = expr; 
    expr_step = expr; 
    expr_type = Type.t_real } 


(* Current state variable of state variable *)
let mk_var state_var = 

  { expr_init = base_term_of_state_var base_offset state_var;
    expr_step = cur_term_of_state_var cur_offset state_var;
    expr_type = StateVar.type_of_state_var state_var } 


let mk_free_var v =
  let t = Term.mk_var v in
  { expr_init = t;
    expr_step = t;
    expr_type = Var.type_of_var v } 
  

(* i-th index variable *)
let mk_index_var i = 

  let v =
    Var.mk_free_var
      (String.concat "."
         (((I.push_index I.index_ident i) |> I.string_of_ident true)
          :: I.reserved_scope)
       |> HString.mk_hstring)
      Type.t_int
    |> Term.mk_var
  in

  (* create lustre expression for free variable*)
  { expr_init = v;
    expr_step = v;
    expr_type = Type.t_int } 

let int_of_index_var { expr_init = t } =
  if not (Term.is_free_var t) then raise (Invalid_argument "int_of_index_var");
  let v = Term.free_var_of_term t in
  let s = Var.hstring_of_free_var v |> HString.string_of_hstring in
  try Scanf.sscanf s ("__index_%d%_s") (fun i -> i)
  with Scanf.Scan_failure _ -> raise (Invalid_argument "int_of_index_var")
          

let has_q_index_expr e =
  let vs = Term.vars_of_term e in
  Var.VarSet.exists (fun v ->
      Var.is_free_var v &&
      let s = Var.hstring_of_free_var v |> HString.string_of_hstring in
      try Scanf.sscanf s ("__index_%_d%_s") true
      with Scanf.Scan_failure _ -> false
    ) vs

let has_indexes { expr_init; expr_step } =
  has_q_index_expr expr_init || has_q_index_expr expr_step


(* ********************************************************************** *)
(* Type checking constructors                                             *)
(* ********************************************************************** *)

(* Generic type checking functions that fail with [Type_mismatch] or
   return a resulting type if the expressions match the required types. *)

(* Type check for bool -> bool *)
let type_of_bool_bool = function 
  | t when Type.is_bool t -> Type.t_bool
  | _ -> raise Type_mismatch


(* Type check for bool -> bool -> bool *)
let type_of_bool_bool_bool = function 
  | t when Type.is_bool t -> 
    (function 
      | t when Type.is_bool t -> Type.t_bool 
      | _ -> raise Type_mismatch)
  | _ -> raise Type_mismatch

(*
(* Type check for int -> int -> int *)
let type_of_int_int_int = function 

  | t when Type.is_int t || Type.is_int_range t -> 
    (function 
      | t when Type.is_int t || Type.is_int_range t -> Type.t_int 
      | _ -> raise Type_mismatch)
  | _ -> raise Type_mismatch


(* Type check for real -> real -> real *)
let type_of_real_real_real = function 

  | t when Type.is_real t -> 
    (function 
      | t when Type.is_real t -> Type.t_real
      | _ -> raise Type_mismatch)
    
  | _ -> raise Type_mismatch
*)

let sub_opt x y = match x, y with 
  | Number x, Number y -> Number (Numeral.sub x y) 
  | Number _, Inf -> NegInf
  | Inf, Number _ -> Inf
  | Inf, Inf -> Nothing
  | Number _, NegInf -> Inf
  | NegInf, Number _ -> NegInf 
  | NegInf, NegInf -> Nothing
  | Inf, NegInf -> Inf 
  | NegInf, Inf -> NegInf
  | Nothing, _ -> assert false 
  | _, Nothing -> assert false

let add_opt x y = match x, y with 
  | Number x, Number y -> Number (Numeral.add x y) 
  | Number _, Inf -> Inf
  | Inf, Number _ -> Inf
  | Inf, Inf -> Inf
  | Number _, NegInf -> NegInf
  | NegInf, Number _ -> NegInf 
  | NegInf, NegInf -> NegInf
  | Inf, NegInf -> Nothing 
  | NegInf, Inf -> Nothing
  | Nothing, _ -> assert false 
  | _, Nothing -> assert false

let mult_opt x y = match x, y with 
  | Number x, Number y -> Number (Numeral.mult x y) 
  | Number x, _ when x = Numeral.zero -> Number Numeral.zero
  | _, Number y  when y = Numeral.zero -> Number Numeral.zero
  | Number x, Inf when Numeral.gt x Numeral.zero -> Inf
  | Number x, Inf when Numeral.lt x Numeral.zero -> NegInf
  | Inf, Number y when Numeral.gt y Numeral.zero -> Inf
  | Inf, Number y when Numeral.lt y Numeral.zero -> NegInf
  | Number x, NegInf when Numeral.gt x Numeral.zero -> NegInf
  | Number x, NegInf when Numeral.lt x Numeral.zero -> Inf
  | NegInf, Number y when  Numeral.gt y Numeral.zero -> NegInf 
  | NegInf, Number y when  Numeral.lt y Numeral.zero -> Inf 
  | Inf, Inf -> Inf
  | NegInf, NegInf -> Inf
  | Inf, NegInf -> NegInf 
  | NegInf, Inf -> NegInf
  | Nothing, _ -> assert false 
  | _, Nothing -> assert false
  | _ -> assert false
  
let div_opt x y = match x, y with 
  | Number x, Number y -> Number (Numeral.div x y) 
  | Number _, Inf -> Nothing
  | Inf, Number y when Numeral.gt y Numeral.zero -> Inf
  | Inf, Number y when Numeral.lt y Numeral.zero -> NegInf
  | Inf, Inf -> Nothing
  | Number _, NegInf -> Nothing
  | NegInf, Number y when Numeral.gt y Numeral.zero -> NegInf 
  | NegInf, Number y when Numeral.lt y Numeral.zero -> Inf 
  | NegInf, NegInf -> Nothing
  | Inf, NegInf -> Nothing 
  | NegInf, Inf -> Nothing
  | Nothing, _ -> assert false 
  | _, Nothing -> assert false
  | _ -> assert false

let min_opt = List.fold_left (fun num1 num2 -> match num1, num2 with 
    | Number x, Number y -> Number (Numeral.min x y)
    | NegInf, _ -> NegInf 
    | _, NegInf -> NegInf
    | Inf, num -> num 
    | num, Inf -> num
    | Nothing, _ -> Nothing
    | _, Nothing -> Nothing
  ) Nothing

let max_opt = List.fold_left (fun num1 num2 -> match num1, num2 with 
    | Number x, Number y -> Number (Numeral.max x y)
    | NegInf, num -> num 
    | num, NegInf -> num
    | Inf, _ -> Inf 
    | _, Inf -> Inf
    | Nothing, _ -> Nothing
    | _, Nothing -> Nothing
  ) Nothing

let num_to_numeral_opt = function 
  | Number n -> Some n 
  | _ -> None

let numeral_opts_to_nums lo hi = match lo, hi with 
  | Some lo, Some hi -> Number lo, Number hi 
  | Some lo, None -> Number lo, Inf 
  | None, Some hi -> NegInf, Number hi 
  | None, None -> NegInf, Inf

(* Best int subrange for some operator. *)
let best_int_range is_div op t t' =
  match Type.bounds_of_int_range t' with
  
  | Some lo', Some hi' when (
    is_div &&
    Numeral.(equal lo' zero) &&
    Numeral.(equal hi' zero)
  ) -> raise Division_by_zero
  
  | Some lo', _ when (
    is_div && Numeral.(equal lo' zero)
  ) -> Type.t_int
  | _, Some hi' when (
    is_div && Numeral.(equal hi' zero)
  )-> Type.t_int

  | lo', hi' ->
    let lo, hi = Type.bounds_of_int_range t in
    let 
      (lo', hi'), (lo, hi) = numeral_opts_to_nums lo' hi', numeral_opts_to_nums lo hi
    in
    let bounds =
      [ op lo lo' ;
        op hi lo' ;
        op lo hi' ;
        op hi hi' ]
    in
    let lower = min_opt bounds in 
    let upper = max_opt bounds in 
    match lower, upper with 
      | Nothing, _ | _, Nothing -> Type.t_int 
      | _ -> Type.mk_int_range
              (num_to_numeral_opt lower)
              (num_to_numeral_opt upper)


(* Type check for int -> int -> int, real -> real -> real *)
(*let type_of_num_num_num ?(is_div = false) op t t' =
  try best_int_range is_div op t t' with
  | Invalid_argument _ -> (
    match t with
    | t when Type.is_int t || Type.is_int_range t -> (
      match t' with
      | t when Type.is_int t || Type.is_int_range t -> Type.t_int 
      | _ -> raise Type_mismatch
    )

    | t when Type.is_real t -> (
      match t' with
      | t when Type.is_real t -> Type.t_real
      | _ -> raise Type_mismatch
    )
      
    | _ -> raise Type_mismatch
  )
*)

(* Type check for int -> int -> int, real -> real -> real, 
abv -> abv -> abv *)
let type_of_numOrBV_numOrBV_numOrBV ?(is_div = false) op t t' =
  try best_int_range is_div op t t' with
  | Invalid_argument _ -> (
    match t with
    | t when Type.is_int t || Type.is_int_range t -> (
      match t' with
      | t when Type.is_int t || Type.is_int_range t -> Type.t_int
      | _ -> raise Type_mismatch
    )

    | t when Type.is_uint8 t -> (
      match t' with
      | t when Type.is_uint8 t -> Type.t_ubv 8
      | _ -> raise Type_mismatch)
    | t when Type.is_uint16 t -> (
      match t' with
      | t when Type.is_uint16 t -> Type.t_ubv 16
      | _ -> raise Type_mismatch)
    | t when Type.is_uint32 t -> (
      match t' with
      | t when Type.is_uint32 t -> Type.t_ubv 32
      | _ -> raise Type_mismatch)
    | t when Type.is_uint64 t -> (
      match t' with
      | t when Type.is_uint64 t -> Type.t_ubv 64
      | _ -> raise Type_mismatch)

    | t when Type.is_int8 t -> (
      match t' with
      | t when Type.is_int8 t -> Type.t_bv 8
      | _ -> raise Type_mismatch)
    | t when Type.is_int16 t -> (
      match t' with
      | t when Type.is_int16 t -> Type.t_bv 16
      | _ -> raise Type_mismatch)
    | t when Type.is_int32 t -> (
      match t' with
      | t when Type.is_int32 t -> Type.t_bv 32
      | _ -> raise Type_mismatch)
    | t when Type.is_int64 t -> (
      match t' with
      | t when Type.is_int64 t -> Type.t_bv 64
      | _ -> raise Type_mismatch)
    | t when Type.is_real t -> (
      match t' with
      | t when Type.is_real t -> Type.t_real
      | _ -> raise Type_mismatch)
    | _ -> raise Type_mismatch)
  

(* Type check for int -> int -> int, real -> real -> real, 
bv -> bv -> bv *)
let type_of_numOrSBV_numOrSBV_numOrSBV ?(is_div = false) op t t' =
  try best_int_range is_div op t t' with
  | Invalid_argument _ -> (
    match t with
    | t when Type.is_int t || Type.is_int_range t -> (
      match t' with
      | t when Type.is_int t || Type.is_int_range t -> Type.t_int
      | _ -> raise Type_mismatch
    )

    | t when Type.is_int8 t -> (
      match t' with
      | t when Type.is_int8 t -> Type.t_bv 8
      | _ -> raise Type_mismatch)
    | t when Type.is_int16 t -> (
      match t' with
      | t when Type.is_int16 t -> Type.t_bv 16
      | _ -> raise Type_mismatch)
    | t when Type.is_int32 t -> (
      match t' with
      | t when Type.is_int32 t -> Type.t_bv 32
      | _ -> raise Type_mismatch)
    | t when Type.is_int64 t -> (
      match t' with
      | t when Type.is_int64 t -> Type.t_bv 64
      | _ -> raise Type_mismatch)
    | t when Type.is_real t -> (
      match t' with
      | t when Type.is_real t -> Type.t_real
      | _ -> raise Type_mismatch)
    | _ -> raise Type_mismatch)


(* Type check for 'a -> 'a -> 'a *)
let type_of_a_a_a type1 type2 = 

  (* If first type is subtype of second, choose second type *)
  if Type.check_type type1 type2 then type2 

  (* If second type is subtype of first, choose first type *)
  else if Type.check_type type2 type1 then type1 

  (* Extend integer ranges if one is not a subtype of the other *)
  else if Type.is_int_range type1 && Type.is_int_range type2 then Type.t_int 

  (* Fail if types are incompatible *)
  else raise Type_mismatch


(* Type check for bv -> bv -> bv or ubv -> ubv -> ubv *)
let type_of_abv_abv_abv t t' =
  match t, t' with
  | t, t' when Type.is_uint8 t && Type.is_uint8 t' -> Type.t_ubv 8
  | t, t' when Type.is_uint16 t && Type.is_uint16 t' -> Type.t_ubv 16
  | t, t' when Type.is_uint32 t && Type.is_uint32 t' -> Type.t_ubv 32
  | t, t' when Type.is_uint64 t && Type.is_uint64 t' -> Type.t_ubv 64
  | t, t' when Type.is_int8 t && Type.is_int8 t' -> Type.t_bv 8
  | t, t' when Type.is_int16 t && Type.is_int16 t' -> Type.t_bv 16
  | t, t' when Type.is_int32 t && Type.is_int32 t' -> Type.t_bv 32
  | t, t' when Type.is_int64 t && Type.is_int64 t' -> Type.t_bv 64
  | _, _ -> raise Type_mismatch


(* Type check for bv -> ubv -> bv or ubv -> ubv -> ubv *)
let type_of_abv_ubv_abv t t' =
match t, t' with
  | t, t' when Type.is_uint8 t && Type.is_uint8 t' -> Type.t_ubv 8
  | t, t' when Type.is_uint16 t && Type.is_uint16 t' -> Type.t_ubv 16
  | t, t' when Type.is_uint32 t && Type.is_uint32 t' -> Type.t_ubv 32
  | t, t' when Type.is_uint64 t && Type.is_uint64 t' -> Type.t_ubv 64
  | t, t' when Type.is_int8 t && Type.is_uint8 t' -> Type.t_bv 8
  | t, t' when Type.is_int16 t && Type.is_uint16 t' -> Type.t_bv 16
  | t, t' when Type.is_int32 t && Type.is_uint32 t' -> Type.t_bv 32
  | t, t' when Type.is_int64 t && Type.is_uint64 t' -> Type.t_bv 64
  | _, _ -> raise Type_mismatch

(*
(* Type check for ubv -> ubv -> ubv *)
let type_of_ubv_ubv_ubv t t' =
  match t, t' with 
  | t, t' when Type.is_uint8 t && Type.is_uint8 t' -> Type.t_ubv 8
  | t, t' when Type.is_uint16 t && Type.is_uint16 t' -> Type.t_ubv 16
  | t, t' when Type.is_uint32 t && Type.is_uint32 t' -> Type.t_ubv 32
  | t, t' when Type.is_uint64 t && Type.is_uint64 t' -> Type.t_ubv 64
  | _, _ -> raise Type_mismatch
*)

(*
(* Type check for bv -> bv -> bv *)
let type_of_bv_bv_bv t t' =
  match t, t' with 
  | t, t' when Type.is_int8 t && Type.is_int8 t' -> Type.t_bv 8
  | t, t' when Type.is_int16 t && Type.is_int16 t' -> Type.t_bv 16
  | t, t' when Type.is_int32 t && Type.is_int32 t' -> Type.t_bv 32
  | t, t' when Type.is_int64 t && Type.is_int64 t' -> Type.t_bv 64
  | _, _ -> raise Type_mismatch
*)

(* Type check for 'a -> 'a -> bool *)
let type_of_a_a_bool type1 type2 = 

  if 

    (* One type must be subtype of the other *)
    Type.check_type type1 type2
    || Type.check_type type2 type1

    (* Extend integer ranges if one is not a subtype of the other *)
    || (Type.is_int_range type1 && Type.is_int_range type2) 

  then 

    (* Resulting type is Boolean *)
    Type.t_bool 

  (* Fail if types are incompatible *)
  else 

    raise Type_mismatch


(* Type check for int -> int -> bool, real -> real -> bool,
  bv -> bv -> bool, ubv -> ubv -> bool *)
let type_of_num_num_bool = function

  | t when Type.is_int t || Type.is_int_range t -> 
    (function 
      | t when Type.is_int t || Type.is_int_range t -> Type.t_bool 
      | _ -> raise Type_mismatch)

  | t when Type.is_real t -> 
    (function 
      | t when Type.is_real t -> Type.t_bool
      | _ -> raise Type_mismatch)

  | t when Type.is_ubitvector t ->
    (function 
      | t' when Type.is_ubitvector t' -> 
        let s1 = Type.bitvectorsize t in
          let s2 = Type.bitvectorsize t' in
            (match s1, s2 with
            | 8,8 -> Type.t_bool
            | 16,16 -> Type.t_bool
            | 32,32 -> Type.t_bool
            | 64,64 -> Type.t_bool
            | _, _ -> raise Type_mismatch)
      | _ -> raise Type_mismatch)

  | t when Type.is_bitvector t ->
    (function 
      | t' when Type.is_bitvector t' -> 
        let s1 = Type.bitvectorsize t in
          let s2 = Type.bitvectorsize t' in
            (match s1, s2 with
            | 8,8 -> Type.t_bool
            | 16,16 -> Type.t_bool
            | 32,32 -> Type.t_bool
            | 64,64 -> Type.t_bool
            | _, _ -> raise Type_mismatch)
      | _ -> raise Type_mismatch)

  | _ -> raise Type_mismatch


(* ********************************************************************** *)


(* Evaluate unary negation

   not true -> false
   not false -> true
*)
let eval_not = function 
  | t when t == Term.t_true -> Term.t_false
  | t when t == Term.t_false -> Term.t_true
  | expr -> Term.mk_not expr


(* Type of unary negation 

   not: bool -> bool 
*)
let type_of_not = type_of_bool_bool


(* Unary negation of expression *)
let mk_not expr = mk_unary eval_not type_of_not expr


(* ********************************************************************** *)


(* Evaluate unary minus

   -(c) -> (-c)
   -(-x) -> x
*)
let eval_uminus expr = match Term.destruct expr with 

  | Term.T.Const s when Symbol.is_numeral s -> 
    Term.mk_num Numeral.(- Symbol.numeral_of_symbol s)

  | Term.T.Const s when Symbol.is_decimal s -> 
    Term.mk_dec Decimal.(- Symbol.decimal_of_symbol s)

  | Term.T.App (s, [e]) when s == Symbol.s_minus -> e

  | _ -> if (Type.is_bitvector (Term.type_of_term expr) ||
             Type.is_ubitvector (Term.type_of_term expr)) then
            Term.mk_bvneg expr
         else
            Term.mk_minus [expr]

  | exception Invalid_argument _ -> Term.mk_minus [expr]


(* Type of unary minus 

   -: int -> int 
   -: int_range(l, u) -> int_range(-u, -l)
   -: real -> real 
*)
let type_of_uminus = function
  | t when Type.is_int t -> Type.t_int
  | t when Type.is_real t -> Type.t_real
  | t when Type.is_int_range t -> (
    match Type.bounds_of_int_range t with
      | Some lbound, Some ubound -> Type.mk_int_range (Some Numeral.(- ubound)) (Some Numeral.(- lbound))
      | Some lbound, None -> Type.mk_int_range None (Some Numeral.(- lbound))
      | None, Some ubound -> Type.mk_int_range (Some Numeral.(- ubound)) None
      | None, None -> Type.mk_int_range None None
    )
  | t when Type.is_int8 t -> Type.t_bv 8
  | t when Type.is_int16 t -> Type.t_bv 16
  | t when Type.is_int32 t -> Type.t_bv 32
  | t when Type.is_int64 t -> Type.t_bv 64
  | t when Type.is_uint8 t -> Type.t_ubv 8
  | t when Type.is_uint16 t -> Type.t_ubv 16
  | t when Type.is_uint32 t -> Type.t_ubv 32
  | t when Type.is_uint64 t -> Type.t_ubv 64
  | _ -> raise Type_mismatch


(* Unary negation of expression *)
let mk_uminus expr = mk_unary eval_uminus type_of_uminus expr


(* ********************************************************************** *)


(* Evaluate bitwise negation*)
let eval_bvnot expr = Term.mk_bvnot expr


(* Type of bitwise negation *)
let type_of_bvnot = function
  | t when Type.is_ubitvector t -> 
      let s = Type.bitvectorsize t in
        (match s with
        | 8 -> Type.t_ubv 8
        | 16 -> Type.t_ubv 16
        | 32 -> Type.t_ubv 32
        | 64 -> Type.t_ubv 64
        | _ -> raise Type_mismatch)
  | t when Type.is_bitvector t -> 
      let s = Type.bitvectorsize t in
        (match s with
        | 8 -> Type.t_bv 8
        | 16 -> Type.t_bv 16
        | 32 -> Type.t_bv 32
        | 64 -> Type.t_bv 64
        | _ -> raise Type_mismatch)
  | _ -> raise Type_mismatch


(* Unary negation of expression *)
let mk_bvnot expr = mk_unary eval_bvnot type_of_bvnot expr


(* ********************************************************************** *)


(* Evaluate conversion to integer *)
let eval_to_int expr =
  let tt = Term.type_of_term expr in
  if Type.is_int tt || Type.is_int_range tt then
    expr
  else
    match Term.destruct expr with
    | Term.T.Const s when Symbol.is_decimal s ->
      Term.mk_num
        (Numeral.of_big_int
           (Decimal.to_big_int
              (Symbol.decimal_of_symbol s)))
    | Term.T.Const s when Symbol.is_ubv8 s ->
      Term.mk_num
        (Bitvector.ubv8_to_num
          (Symbol.ubitvector_of_symbol s))
    | Term.T.Const s when Symbol.is_ubv16 s ->
      Term.mk_num
        (Bitvector.ubv16_to_num
          (Symbol.ubitvector_of_symbol s))
    | Term.T.Const s when Symbol.is_ubv32 s ->
      Term.mk_num
        (Bitvector.ubv32_to_num
          (Symbol.ubitvector_of_symbol s))
    | Term.T.Const s when Symbol.is_ubv64 s ->
      Term.mk_num
        (Bitvector.ubv64_to_num
          (Symbol.ubitvector_of_symbol s))
    | Term.T.Const s when Symbol.is_bv8 s ->
      Term.mk_num
        (Bitvector.bv8_to_num
          (Symbol.bitvector_of_symbol s))
    | Term.T.Const s when Symbol.is_bv16 s ->
      Term.mk_num
        (Bitvector.bv16_to_num
          (Symbol.ubitvector_of_symbol s))
    | Term.T.Const s when Symbol.is_bv32 s ->
      Term.mk_num
        (Bitvector.bv32_to_num
          (Symbol.ubitvector_of_symbol s))
    | Term.T.Const s when Symbol.is_bv64 s ->
      Term.mk_num
        (Bitvector.bv64_to_num
          (Symbol.ubitvector_of_symbol s))
    | x when Type.is_uint8 (Term.type_of_term (Term.construct x)) -> Term.mk_uint8_to_int expr
    | x when Type.is_uint16 (Term.type_of_term (Term.construct x)) -> Term.mk_uint16_to_int expr
    | x when Type.is_uint32 (Term.type_of_term (Term.construct x)) ->  Term.mk_uint32_to_int expr
    | x when Type.is_uint64 (Term.type_of_term (Term.construct x)) ->  Term.mk_uint64_to_int expr
    | x when Type.is_int8 (Term.type_of_term (Term.construct x)) ->  Term.mk_int8_to_int expr
    | x when Type.is_int16 (Term.type_of_term (Term.construct x)) ->  Term.mk_int16_to_int expr
    | x when Type.is_int32 (Term.type_of_term (Term.construct x)) ->  Term.mk_int32_to_int expr
    | x when Type.is_int64 (Term.type_of_term (Term.construct x)) ->  Term.mk_int64_to_int expr
    | _ -> Term.mk_to_int expr
    | exception Invalid_argument _ -> 
      if Type.is_uint8 (Term.type_of_term expr) then
        Term.mk_uint8_to_int expr
      else if Type.is_uint16 (Term.type_of_term expr) then
        Term.mk_uint16_to_int expr
      else if Type.is_uint32 (Term.type_of_term expr) then
        Term.mk_uint32_to_int expr
      else if Type.is_uint64 (Term.type_of_term expr) then
        Term.mk_uint64_to_int expr
      else if Type.is_int8 (Term.type_of_term expr) then
        Term.mk_int8_to_int expr
      else if Type.is_int16 (Term.type_of_term expr) then
        Term.mk_int16_to_int expr
      else if Type.is_int32 (Term.type_of_term expr) then
        Term.mk_int32_to_int expr
      else if Type.is_int64 (Term.type_of_term expr) then
        Term.mk_int64_to_int expr
      else
        Term.mk_to_int expr


(* Type of conversion to integer  

   int: real -> int 
*)
let type_of_to_int = function
  | t when Type.is_real t -> Type.t_int
  | t when Type.is_int t || Type.is_int_range t -> Type.t_int
  | t when Type.is_uint8 t || Type.is_uint16 t || Type.is_uint32 t || Type.is_uint64 t -> Type.t_int
  | t when Type.is_int8 t || Type.is_int16 t || Type.is_int32 t || Type.is_int64 t -> Type.t_int
  | _ -> raise Type_mismatch


(* Conversion to integer *)
let mk_to_int expr = mk_unary eval_to_int type_of_to_int expr 


(* ********************************************************************** *)


(* Evaluate conversion to unsigned integer8 *)
let eval_to_uint8 expr =

  match Term.destruct expr with

    | Term.T.Const c when Symbol.is_numeral c ->

      Term.mk_ubv (Bitvector.num_to_ubv8 (Symbol.numeral_of_symbol c))

    | Term.T.App (_, [ sub_expr ])
      when Term.is_negative_numeral expr ->
        Term.mk_ubv
          (Bitvector.num_to_ubv8 (Numeral.neg (Term.numeral_of_term sub_expr)))

    | _ -> let tt = Term.type_of_term expr in
            if (Type.is_int tt) then
              Term.mk_to_uint8 expr
            else if (Type.is_ubitvector tt) then
              if (Type.is_uint8 tt) then 
                expr
              else
                Term.mk_bvextract (Numeral.of_int 7) (Numeral.of_int 0) expr
            else 
              raise Type_mismatch

 
(* Type of conversion to unsigned integer8  

   int: real -> uint8 
*)
let type_of_to_uint8 = function
  | t when Type.is_real t -> Type.t_int
  | t when Type.is_uint8 t || Type.is_int t || Type.is_int_range t -> Type.t_ubv 8
  | t when Type.is_uint16 t || Type.is_uint32 t || Type.is_uint64 t -> Type.t_ubv 8
  | _ -> raise Type_mismatch


(* Conversion to unsigned integer8 *)
let mk_to_uint8 expr = mk_unary eval_to_uint8 type_of_to_uint8 expr


(* ********************************************************************** *)


(* Evaluate conversion to unsigned integer16 *)
let eval_to_uint16 expr =
  
  match Term.destruct expr with

    | Term.T.Const c when Symbol.is_numeral c ->

      Term.mk_ubv (Bitvector.num_to_ubv16 (Symbol.numeral_of_symbol c))

    | Term.T.App (_, [ sub_expr ])
      when Term.is_negative_numeral expr ->
        Term.mk_ubv
          (Bitvector.num_to_ubv16 (Numeral.neg (Term.numeral_of_term sub_expr)))

    | _ -> let tt = Term.type_of_term expr in
                      if (Type.is_int tt) then
                        Term.mk_to_uint16 expr
                      else if (Type.is_ubitvector tt) then
                        if (Type.is_uint16 tt) then
                          expr
                        else if (Type.is_uint8 tt) then
                          Term.mk_bvconcat (Term.mk_ubv (Bitvector.zero 8)) expr
                        else
                          Term.mk_bvextract (Numeral.of_int 15) (Numeral.of_int 0) expr
                      else
                        raise Type_mismatch


(* Type of conversion to unsigned integer16  

   int: real -> uint16 
*)
let type_of_to_uint16 = function
  | t when Type.is_real t -> Type.t_int
  | t when Type.is_uint16 t || Type.is_int t || Type.is_int_range t -> Type.t_ubv 16
  | t when Type.is_uint8 t || Type.is_uint32 t || Type.is_uint64 t -> Type.t_ubv 16
  | _ -> raise Type_mismatch


(* Conversion to unsigned integer16 *)
let mk_to_uint16 expr = mk_unary eval_to_uint16 type_of_to_uint16 expr


(* ********************************************************************** *)

(* Evaluate conversion to unsigned integer32 *)
let eval_to_uint32 expr =
  
  match Term.destruct expr with

    | Term.T.Const c when Symbol.is_numeral c ->

      Term.mk_ubv (Bitvector.num_to_ubv32 (Symbol.numeral_of_symbol c))

    | Term.T.App (_, [ sub_expr ])
      when Term.is_negative_numeral expr ->
        Term.mk_ubv
          (Bitvector.num_to_ubv32 (Numeral.neg (Term.numeral_of_term sub_expr)))

    | _ -> let tt = Term.type_of_term expr in
            if (Type.is_int tt) then
              Term.mk_to_uint32 expr
            else if (Type.is_ubitvector tt) then
              if (Type.is_uint32 tt) then
                expr
              else if (Type.is_uint8 tt) then
                Term.mk_bvconcat (Term.mk_ubv (Bitvector.zero 24)) expr
              else if (Type.is_uint16 tt) then
                Term.mk_bvconcat (Term.mk_ubv (Bitvector.zero 16)) expr
              else
                Term.mk_bvextract (Numeral.of_int 31) (Numeral.of_int 0) expr
                (*let n = Term.mk_bv2nat expr in
                Term.mk_to_uint32 n*)
            else
              raise Type_mismatch


(* Type of conversion to unsigned integer32  

   int: real -> uint32 
*)
let type_of_to_uint32 = function
  | t when Type.is_real t -> Type.t_int
  | t when Type.is_uint32 t || Type.is_int t || Type.is_int_range t -> Type.t_ubv 32 
  | t when Type.is_uint8 t || Type.is_uint16 t || Type.is_uint64 t -> Type.t_ubv 32
  | _ -> raise Type_mismatch


(* Conversion to unsigned integer32 *)
let mk_to_uint32 expr = mk_unary eval_to_uint32 type_of_to_uint32 expr


(* ********************************************************************** *)

(* Evaluate conversion to unsigned integer64 *)
let eval_to_uint64 expr =
  
  match Term.destruct expr with

    | Term.T.Const c when Symbol.is_numeral c ->

      Term.mk_ubv (Bitvector.num_to_ubv64 (Symbol.numeral_of_symbol c))

    | Term.T.App (_, [ sub_expr ])
      when Term.is_negative_numeral expr ->
        Term.mk_ubv
          (Bitvector.num_to_ubv64 (Numeral.neg (Term.numeral_of_term sub_expr)))

    | _ -> let tt = Term.type_of_term expr in
            if (Type.is_int tt) then
              Term.mk_to_uint64 expr
            else if (Type.is_ubitvector tt) then
              if (Type.is_uint64 tt) then
                expr
              else if (Type.is_uint32 tt) then
                Term.mk_bvconcat (Term.mk_ubv (Bitvector.zero 32)) expr
              else if (Type.is_uint16 tt) then
                Term.mk_bvconcat (Term.mk_ubv (Bitvector.zero 48)) expr
              else
                Term.mk_bvconcat (Term.mk_ubv (Bitvector.zero 56)) expr
            else
              raise Type_mismatch


(* Type of conversion to unsigned integer64  

   int: real -> int64 
*)
let type_of_to_uint64 = function
  | t when Type.is_real t -> Type.t_int
  | t when Type.is_uint64 t || Type.is_int t || Type.is_int_range t -> Type.t_ubv 64 
  | t when Type.is_uint8 t || Type.is_uint16 t || Type.is_uint32 t -> Type.t_ubv 64
  | _ -> raise Type_mismatch


(* Conversion to unsigned integer64 *)
let mk_to_uint64 expr = mk_unary eval_to_uint64 type_of_to_uint64 expr


(* ********************************************************************** *)

(* Evaluate conversion to integer8 *)
let eval_to_int8 expr =
  
  match Term.destruct expr with

    | Term.T.Const c when Symbol.is_numeral c ->

      Term.mk_bv (Bitvector.num_to_bv8 (Symbol.numeral_of_symbol c))

    | Term.T.App (_, [ sub_expr ])
      when Term.is_negative_numeral expr ->
        Term.mk_bv
          (Bitvector.num_to_bv8 (Numeral.neg (Term.numeral_of_term sub_expr)))

    | _ -> let tt = Term.type_of_term expr in
            if (Type.is_int tt) then
              Term.mk_to_int8 expr
            else if (Type.is_bitvector tt) then
              if (Type.is_int8 tt) then 
                expr
              else
                Term.mk_bvextract (Numeral.of_int 7) (Numeral.of_int 0) expr
            else 
              raise Type_mismatch


(* Type of conversion to integer8  

   int: real -> int8 
*)
let type_of_to_int8 = function
  | t when Type.is_real t -> Type.t_int
  | t when Type.is_int8 t || Type.is_int t || Type.is_int_range t -> Type.t_bv 8
  | t when Type.is_int16 t || Type.is_int32 t || Type.is_int64 t -> Type.t_bv 8
  | _ -> raise Type_mismatch


(* Conversion to integer8 *)
let mk_to_int8 expr = mk_unary eval_to_int8 type_of_to_int8 expr


(* ********************************************************************** *)


(* Evaluate conversion to integer16 *)
let eval_to_int16 expr =
  
  match Term.destruct expr with

    | Term.T.Const c when Symbol.is_numeral c ->

      Term.mk_bv (Bitvector.num_to_bv16 (Symbol.numeral_of_symbol c))

    | Term.T.App (_, [ sub_expr ])
      when Term.is_negative_numeral expr ->
        Term.mk_bv
          (Bitvector.num_to_bv16 (Numeral.neg (Term.numeral_of_term sub_expr)))

    | _ -> let tt = Term.type_of_term expr in
            if (Type.is_int tt) then
              Term.mk_to_int16 expr
            else if (Type.is_bitvector tt) then
              if (Type.is_int16 tt) then 
                expr
              else if (Type.is_int8 tt) then
                Term.mk_bvsignext (Numeral.of_int 8) expr
              else
                Term.mk_bvextract (Numeral.of_int 15) (Numeral.of_int 0) expr
            else 
              raise Type_mismatch


(* Type of conversion to integer16  

   int: real -> int16 
*)
let type_of_to_int16 = function
  | t when Type.is_real t -> Type.t_int
  | t when Type.is_int16 t || Type.is_int t || Type.is_int_range t -> Type.t_bv 16
  | t when Type.is_int8 t || Type.is_int32 t || Type.is_int64 t -> Type.t_bv 16
  | _ -> raise Type_mismatch


(* Conversion to integer16 *)
let mk_to_int16 expr = mk_unary eval_to_int16 type_of_to_int16 expr


(* ********************************************************************** *)

(* Evaluate conversion to integer32 *)
let eval_to_int32 expr =
  
  match Term.destruct expr with

    | Term.T.Const c when Symbol.is_numeral c ->

      Term.mk_bv (Bitvector.num_to_bv32 (Symbol.numeral_of_symbol c))

    | Term.T.App (_, [ sub_expr ])
      when Term.is_negative_numeral expr ->
        Term.mk_bv
          (Bitvector.num_to_bv32 (Numeral.neg (Term.numeral_of_term sub_expr)))

    | _ -> let tt = Term.type_of_term expr in
            if (Type.is_int tt) then
              Term.mk_to_int32 expr
            else if (Type.is_bitvector tt) then
              if (Type.is_int32 tt) then 
                expr
              else if (Type.is_int64 tt) then
                Term.mk_bvextract (Numeral.of_int 31) (Numeral.of_int 0) expr
              else if (Type.is_int8 tt) then
                Term.mk_bvsignext (Numeral.of_int 24) expr
              else
                Term.mk_bvsignext (Numeral.of_int 16) expr
            else 
              raise Type_mismatch


(* Type of conversion to integer32  

   int: real -> int32 
*)
let type_of_to_int32 = function
  | t when Type.is_real t -> Type.t_int
  | t when Type.is_int32 t || Type.is_int t || Type.is_int_range t -> Type.t_bv 32
  | t when Type.is_int8 t || Type.is_int16 t || Type.is_int64 t -> Type.t_bv 32
  | _ -> raise Type_mismatch


(* Conversion to integer32 *)
let mk_to_int32 expr = mk_unary eval_to_int32 type_of_to_int32 expr


(* ********************************************************************** *)

(* Evaluate conversion to integer64 *)
let eval_to_int64 expr =
  
  match Term.destruct expr with

    | Term.T.Const c when Symbol.is_numeral c ->

      Term.mk_bv (Bitvector.num_to_bv64 (Symbol.numeral_of_symbol c))

    | Term.T.App (_, [ sub_expr ])
      when Term.is_negative_numeral expr ->
        Term.mk_bv
          (Bitvector.num_to_bv64 (Numeral.neg (Term.numeral_of_term sub_expr)))

    | _ -> let tt = Term.type_of_term expr in
            if (Type.is_int tt) then
              Term.mk_to_int64 expr
            else if (Type.is_bitvector tt) then
              if (Type.is_int64 tt) then 
                expr
              else if (Type.is_int8 tt) then
                Term.mk_bvsignext (Numeral.of_int 56) expr
              else if (Type.is_int16 tt) then
                Term.mk_bvsignext (Numeral.of_int 48) expr
              else
                Term.mk_bvsignext (Numeral.of_int 32) expr
            else 
              raise Type_mismatch


(* Type of conversion to integer64  

   int: real -> int64 
*)
let type_of_to_int64 = function
  | t when Type.is_real t -> Type.t_int
  | t when Type.is_int64 t || Type.is_int t || Type.is_int_range t -> Type.t_bv 64
  | t when Type.is_int8 t || Type.is_int16 t || Type.is_int32 t -> Type.t_bv 64
  | _ -> raise Type_mismatch


(* Conversion to integer64 *)
let mk_to_int64 expr = mk_unary eval_to_int64 type_of_to_int64 expr


(* ********************************************************************** *)

(* Evaluate conversion to real *)
let eval_to_real expr =
  let tt = Term.type_of_term expr in
  if Type.is_real tt then
    expr
  else
    match Term.destruct expr with
    | Term.T.Const s when Symbol.is_numeral s ->
      Term.mk_dec
        (Decimal.of_big_int
           (Numeral.to_big_int
              (Symbol.numeral_of_symbol s)))

    | _ -> Term.mk_to_real expr
    | exception Invalid_argument _ -> Term.mk_to_real expr

(* Type of conversion to real  

   real: int -> real 
*)
let type_of_to_real = function
  | t when Type.is_int t || Type.is_int_range t -> Type.t_real
  | t when Type.is_real t -> Type.t_real
  | _ -> raise Type_mismatch


(* Conversion to integer *)
let mk_to_real expr = mk_unary eval_to_real type_of_to_real expr 


(* ********************************************************************** *)


(* Evaluate Boolean conjunction

   true and e2 -> e2 
   false and e2 -> false
   e1 and true -> e1
   e1 and false -> false *)
let eval_and = function 
  | t when t == Term.t_true -> (function expr2 -> expr2)
  | t when t == Term.t_false -> (function _ -> Term.t_false)
  | expr1 -> 
    (function 
      | t when t == Term.t_true -> expr1
      | t when t == Term.t_false -> Term.t_false
      | expr2 -> Term.mk_and [expr1; expr2])


(* Type of Boolean conjunction 

   and: bool -> bool -> bool *)
let type_of_and = type_of_bool_bool_bool


(* Boolean conjunction *)
let mk_and expr1 expr2 = mk_binary eval_and type_of_and expr1 expr2 

(* n-ary Boolean conjunction *)
let mk_and_n = function
  | [] -> t_true
  | h :: [] -> h
  | h :: tl -> List.fold_left mk_and h tl
                 

(* ********************************************************************** *)


(* Evaluate Boolean disjunction

   true or e2 -> true
   false or e2 -> e2
   e1 or true -> true
   e1 or false -> e1 *)
let eval_or = function 
  | t when t == Term.t_true -> (function _ -> Term.t_true)
  | t when t == Term.t_false -> (function expr2 -> expr2)
  | expr1 -> 
    (function 
      | t when t == Term.t_true -> Term.t_true
      | t when t == Term.t_false -> expr1
      | expr2 -> Term.mk_or [expr1; expr2])


(* Type of Boolean disjunction 

   or: bool -> bool -> bool *)
let type_of_or = type_of_bool_bool_bool


(* Boolean disjunction *)
let mk_or expr1 expr2 = mk_binary eval_or type_of_or expr1 expr2 

(* n-ary Boolean disjunction *)
let mk_or_n = function
  | [] -> t_true
  | h :: [] -> h
  | h :: tl -> List.fold_left mk_or h tl
                 

(* ********************************************************************** *)


(* Evaluate Boolean exclusive disjunction

   true xor e2 -> not e2
   false xor e2 -> e2
   e1 xor true -> not e1
   e1 xor false -> e1 *)
let eval_xor = function 
  | t when t == Term.t_true -> (function expr2 -> eval_not expr2)
  | t when t == Term.t_false -> (function expr2 -> expr2)
  | expr1 -> 
    (function 
      | t when t == Term.t_true -> eval_not expr1
      | t when t == Term.t_false -> expr1
      | expr2 -> Term.mk_xor [expr1; expr2])


(* Type of Boolean exclusive disjunction 

   xor: bool -> bool -> bool *)
let type_of_xor = type_of_bool_bool_bool


(* Boolean exclusive disjunction *)
let mk_xor expr1 expr2 = mk_binary eval_xor type_of_xor expr1 expr2 


(* ********************************************************************** *)


(* Evaluate Boolean implication

   true => e2 -> e2
   false => e2 -> true
   e1 => true -> true
   e1 => false -> not e1 *)
let eval_impl = function 
  | t when t == Term.t_true -> (function expr2 -> expr2)
  | t when t == Term.t_false -> (function _ -> Term.t_true)
  | expr1 -> 
    (function 
      | t when t == Term.t_true -> Term.t_true
      | t when t == Term.t_false -> eval_not expr1
      | expr2 -> Term.mk_implies [expr1; expr2])


(* Type of Boolean implication 

   =>: bool -> bool -> bool *)
let type_of_impl = type_of_bool_bool_bool


(* Boolean implication *)
let mk_impl expr1 expr2 = mk_binary eval_impl type_of_impl expr1 expr2 

(* ********************************************************************** *)

let mk_let bindings expr =
  {
    expr_init = Term.mk_let bindings expr.expr_init;
    expr_step = Term.mk_let bindings expr.expr_step;
    expr_type = expr.expr_type;
  }

(* ********************************************************************** *)

let apply_subst sigma expr =
  {
    expr_init = Term.apply_subst sigma expr.expr_init;
    expr_step = Term.apply_subst sigma expr.expr_step;
    expr_type = expr.expr_type;
  }

(* ********************************************************************** *)

(* Evaluate universal quantification *)
let eval_forall vars t = match vars, t with
  | [], _ -> Term.t_true
  | _, t when t == Term.t_true -> Term.t_true
  | _, t when t == Term.t_false -> Term.t_false
  | _ -> Term.mk_forall vars t 

let type_of_forall = type_of_bool_bool

(* Universal quantification*)
let mk_forall vars expr =
  mk_unary (eval_forall vars) type_of_forall expr


(* ********************************************************************** *)

(* Evaluate existential quantification *)
let eval_exists vars t = match vars, t with
  | [], _ -> Term.t_false
  | _, t when t == Term.t_true -> Term.t_true
  | _, t when t == Term.t_false -> Term.t_false
  | _ -> Term.mk_exists vars t 

let type_of_exists = type_of_bool_bool

(* Existential quantification*)
let mk_exists vars expr = mk_unary (eval_exists vars) type_of_exists expr


(* ********************************************************************** *)


(* Evaluate integer modulus *)
let eval_mod expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && Symbol.is_numeral c2 -> 

      Term.mk_num 
        Numeral.(Symbol.numeral_of_symbol c1 mod 
                 Symbol.numeral_of_symbol c2) 
    
    | _ -> (if Type.is_ubitvector (Term.type_of_term expr1) then 
              Term.mk_bvurem [expr1; expr2]
            else if Type.is_bitvector (Term.type_of_term expr1) then
              Term.mk_bvsrem [expr1; expr2]
            else 
              Term.mk_mod expr1 expr2)
    
    | exception Invalid_argument _ -> Term.mk_mod expr1 expr2


(* Type of integer modulus 

   If j is bounded by [l, u], then the result of i mod j is bounded by
   [0, (max(|l|, |u|) - 1)].

   mod: int -> int -> int *)
let type_of_mod = function 
  | t when Type.is_int t || Type.is_int_range t -> 
    (function 
      | t when Type.is_int t -> Type.t_int 
      | t when Type.is_int_range t -> (
        match Type.bounds_of_int_range t with 
          | Some l, Some u -> Type.mk_int_range (Some Numeral.zero) (Some Numeral.(pred (max (abs l) (abs u))))
          | _ -> Type.mk_int_range (Some Numeral.zero) None
        )
      | _ -> raise Type_mismatch)
  | t1 when Type.is_ubitvector t1 -> 
    (function 
      | t2 when Type.is_ubitvector t2 -> 
        let s1 = Type.bitvectorsize t1 in
          let s2 = Type.bitvectorsize t2 in 
            if s1 != s2 then
              raise Type_mismatch
            else
              (match s1,s2 with
              | 8, 8 -> Type.t_ubv 8
              | 16, 16 -> Type.t_ubv 16
              | 32, 32 -> Type.t_ubv 32
              | 64, 64 -> Type.t_ubv 64
              | _, _ -> raise Type_mismatch)
      | _ -> raise Type_mismatch)
  | t1 when Type.is_bitvector t1 -> 
    (function 
      | t2 when Type.is_bitvector t2 -> 
        let s1 = Type.bitvectorsize t1 in
          let s2 = Type.bitvectorsize t2 in 
            if s1 != s2 then
              raise Type_mismatch
            else
              (match s1,s2 with
              | 8, 8 -> Type.t_bv 8
              | 16, 16 -> Type.t_bv 16
              | 32, 32 -> Type.t_bv 32
              | 64, 64 -> Type.t_bv 64
              | _, _ -> raise Type_mismatch)
      | _ -> raise Type_mismatch)
  | _ -> raise Type_mismatch

(* Integer modulus *)
let mk_mod expr1 expr2 = mk_binary eval_mod type_of_mod expr1 expr2 


(* ********************************************************************** *)


(* Evaluate subtraction *)
let eval_minus expr1 expr2 = 
  
  match Term.destruct expr1, Term.destruct expr2 with
    
    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && Symbol.is_numeral c2 -> 
      
      Term.mk_num 
        Numeral.(Symbol.numeral_of_symbol c1 -
                 Symbol.numeral_of_symbol c2) 
        
    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_decimal c1 && Symbol.is_decimal c2 -> 
      
      Term.mk_dec
        Decimal.(Symbol.decimal_of_symbol c1 -
                 Symbol.decimal_of_symbol c2) 

    | _ -> (if ((Type.is_bitvector (Term.type_of_term expr1)) 
            || (Type.is_ubitvector (Term.type_of_term expr1))) then
              Term.mk_bvsub [expr1; expr2]
            else 
              Term.mk_minus [expr1; expr2])
        
    | exception Invalid_argument _ -> Term.mk_minus [expr1; expr2]

(* Type of subtraction 

   If both arguments are bounded, the difference is bounded by the
   difference of the lower bound of the first argument and the upper
   bound of the second argument and the difference of the upper bound
   of the first argument and the lower bound of the second argument.

   -: int -> int -> int
      real -> real -> real *)
let type_of_minus = function 
  | t when Type.is_int_range t -> 
    (function 
      | s when Type.is_int_range s -> 
        let l1, u1 = Type.bounds_of_int_range t in
        let l2, u2 = Type.bounds_of_int_range s in
        let lower = (
        match l1, u2 with 
          | Some l1, Some u2 -> (Some Numeral.(l1 - u2))
          | _ -> None
        ) in 
        let upper = (
        match l2, u1 with 
          | Some l2, Some u1 -> (Some Numeral.(u1 - l2))
          | _ -> None
        ) in 
        Type.mk_int_range lower upper 
      | s -> type_of_numOrSBV_numOrSBV_numOrSBV sub_opt t s)
  | t -> type_of_numOrBV_numOrBV_numOrBV sub_opt t


(* Subtraction *)
let mk_minus expr1 expr2 = mk_binary eval_minus type_of_minus expr1 expr2 


(* ********************************************************************** *)


(* Evaluate addition *)
let eval_plus expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && Symbol.is_numeral c2 -> 

      Term.mk_num 
        Numeral.(Symbol.numeral_of_symbol c1 +
                 Symbol.numeral_of_symbol c2) 

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_decimal c1 && Symbol.is_decimal c2 -> 

      Term.mk_dec
        Decimal.(Symbol.decimal_of_symbol c1 +
                 Symbol.decimal_of_symbol c2) 
  
    | _ -> (if (((Type.is_bitvector (Term.type_of_term expr1)) 
                  && (Type.is_bitvector (Term.type_of_term expr2)))
                  ||
                ((Type.is_ubitvector (Term.type_of_term expr1)) 
                  && (Type.is_ubitvector (Term.type_of_term expr1)))) then
              Term.mk_bvadd [expr1; expr2]
            else 
              Term.mk_plus [expr1; expr2])

  | exception Invalid_argument _ -> Term.mk_plus [expr1; expr2]


(* Type of addition 
   
   If both summands are bounded, the sum is bounded by the sum of the
   lower bound and the sum of the upper bounds.

   +: int -> int -> int
      real -> real -> real *)
let type_of_plus = function 
  | t when Type.is_int_range t -> 
    (function 
      | s when Type.is_int_range s -> 
        let l1, u1 = Type.bounds_of_int_range t in
        let l2, u2 = Type.bounds_of_int_range s in
        let lower = match l1, l2 with 
          | Some l1, Some l2 -> Some Numeral.(l1 + l2)
          | _ -> None
        in let upper = match u1, u2 with 
          | Some u1, Some u2 -> Some Numeral.(u1 + u2)
          | _ -> None
        in
        Type.mk_int_range lower upper
      | s -> type_of_numOrBV_numOrBV_numOrBV add_opt t s)
  | t -> type_of_numOrBV_numOrBV_numOrBV add_opt t


(* Addition *)
let mk_plus expr1 expr2 = mk_binary eval_plus type_of_plus expr1 expr2


(* ********************************************************************** *)


(* Evaluate real division *)
let eval_div expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

  | Term.T.Const c1, Term.T.Const c2 ->

    if Symbol.is_decimal c1 && Symbol.is_decimal c2 then

      Term.mk_dec
        Decimal.(Symbol.decimal_of_symbol c1 /
                 Symbol.decimal_of_symbol c2)

    else (

      assert (Symbol.is_numeral c1 && Symbol.is_numeral c2);

      Term.mk_num
        Numeral.(Symbol.numeral_of_symbol c1 /
                 Symbol.numeral_of_symbol c2)
    )

  | _ ->

    let tt = Term.type_of_term expr1 in

    if Type.is_real tt then (
      Term.mk_div [expr1; expr2]
    )
    else if Type.is_ubitvector (Term.type_of_term expr1) then (
      Term.mk_bvudiv [expr1; expr2]
    )
    else if Type.is_bitvector (Term.type_of_term expr1) then (
      Term.mk_bvsdiv [expr1; expr2]
    ) 
    else (
      Term.mk_intdiv [expr1; expr2]
    )

  | exception Invalid_argument _ -> Term.mk_div [expr1; expr2]


(* Type of real division

   /: real -> real -> real

   When the operator is applied to integer and machine integer arguments,
   its semantics is the same as integer division (div)
*)
let type_of_div = type_of_numOrBV_numOrBV_numOrBV ~is_div:true div_opt


(* Real division *)
let mk_div expr1 expr2 = mk_binary eval_div type_of_div expr1 expr2 


(* ********************************************************************** *)


(* Evaluate multiplication *)
let eval_times expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && Symbol.is_numeral c2 -> 

      Term.mk_num 
        Numeral.(Symbol.numeral_of_symbol c1 *
                 Symbol.numeral_of_symbol c2) 

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_decimal c1 && Symbol.is_decimal c2 -> 

      Term.mk_dec
        Decimal.(Symbol.decimal_of_symbol c1 *
                 Symbol.decimal_of_symbol c2) 

    | _ -> (if (Type.is_bitvector (Term.type_of_term expr1) ||
                Type.is_ubitvector (Term.type_of_term expr1)) then 
              Term.mk_bvmul [expr1; expr2]
            else 
              Term.mk_times [expr1; expr2])

  | exception Invalid_argument _ -> Term.mk_times [expr1; expr2]


(* Type of multiplication

   *: int -> int -> int
      real -> real -> real *)
let type_of_times = type_of_numOrBV_numOrBV_numOrBV mult_opt


(* Multiplication *)
let mk_times expr1 expr2 = mk_binary eval_times type_of_times expr1 expr2 


(* ********************************************************************** *)


(* Evaluate integer division *)
let eval_intdiv expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && Symbol.is_numeral c2 -> 

      Term.mk_num
        Numeral.(Symbol.numeral_of_symbol c1 /
                 Symbol.numeral_of_symbol c2)                 

    | _ -> (if Type.is_ubitvector (Term.type_of_term expr1) then 
              Term.mk_bvudiv [expr1; expr2]
            else if Type.is_bitvector (Term.type_of_term expr1) then
              Term.mk_bvsdiv [expr1; expr2]
            else 
              Term.mk_intdiv [expr1; expr2])

  | exception Invalid_argument _ -> Term.mk_intdiv [expr1; expr2]


(* Type of integer division

   div: int -> int -> int *)
let type_of_intdiv t t' =
  try best_int_range true div_opt t t' with
  | Invalid_argument _ -> (
    match t with
    | t when Type.is_int t || Type.is_int_range t -> (
      match t' with
      | t when Type.is_int t || Type.is_int_range t -> Type.t_int
      | _ -> raise Type_mismatch
    )
    | t when Type.is_ubitvector t -> (
      match t' with
      | t' when Type.is_ubitvector t' -> 
        let s1 = Type.bitvectorsize t in
          let s2 = Type.bitvectorsize t' in 
            if s1 != s2 then
              raise Type_mismatch
            else
              (match s1,s2 with
              | 8, 8 -> Type.t_ubv 8
              | 16, 16 -> Type.t_ubv 16
              | 32, 32 -> Type.t_ubv 32
              | 64, 64 -> Type.t_ubv 64
              | _, _ -> raise Type_mismatch)
      | _ -> raise Type_mismatch)
    | t when Type.is_bitvector t -> (
      match t' with
      | t' when Type.is_bitvector t' ->
        let s1 = Type.bitvectorsize t in
          let s2 = Type.bitvectorsize t' in 
            if s1 != s2 then
              raise Type_mismatch
            else
              (match s1,s2 with
              | 8, 8 -> Type.t_bv 8
              | 16, 16 -> Type.t_bv 16
              | 32, 32 -> Type.t_bv 32
              | 64, 64 -> Type.t_bv 64
              | _, _ -> raise Type_mismatch)
      | _ -> raise Type_mismatch)
    | _ -> raise Type_mismatch
    )
  


(* Integer division *)
let mk_intdiv expr1 expr2 = mk_binary eval_intdiv type_of_intdiv expr1 expr2 


(* ********************************************************************** *)


(* Evaluate bitvector conjunction *)
let eval_bvand expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with              
    
  | _ -> Term.mk_bvand [expr1; expr2]
  | exception Invalid_argument _ -> Term.mk_bvand [expr1; expr2]


(* Type of bitvector conjunction*)
let type_of_bvand = type_of_abv_abv_abv


(* Bitvector conjunction *)
let mk_bvand expr1 expr2 = mk_binary eval_bvand type_of_bvand expr1 expr2 


(* ********************************************************************** *)


(* Evaluate bitvector disjunction *)
let eval_bvor expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with
  | _ -> Term.mk_bvor [expr1; expr2]
  | exception Invalid_argument _ -> Term.mk_bvor [expr1; expr2]


(* Type of bitvector disjunction *)
let type_of_bvor = type_of_abv_abv_abv


(* Bitvector disjunction *)
let mk_bvor expr1 expr2 = mk_binary eval_bvor type_of_bvor expr1 expr2 


(* ********************************************************************** *)


(* Evaluate bitvector left shift *)
let eval_bvshl expr1 expr2 = Term.mk_bvshl [expr1; expr2]


(* Type of bitvector left shift *)
let type_of_bvshl = type_of_abv_ubv_abv


(* Bitvector left shift *)
let mk_bvshl expr1 expr2 = mk_binary eval_bvshl type_of_bvshl expr1 expr2 


(* ********************************************************************** *)


(* Evaluate bitvector (logical or arithmetic) right shift *)
let eval_bvshr expr1 expr2 =
  if (Type.is_bitvector (Term.type_of_term expr1)) then
    Term.mk_bvashr [expr1; expr2]
  else
    Term.mk_bvlshr [expr1; expr2]


(* Type of bitvector logical right shift *)
let type_of_bvshr = type_of_abv_ubv_abv


(* Bitvector logical right shift *)
let mk_bvshr expr1 expr2 = mk_binary eval_bvshr type_of_bvshr expr1 expr2 


(* ********************************************************************** *)


let has_pre_vars t =
  Term.state_vars_at_offset_of_term (Numeral.of_int (-1)) t
  |> StateVar.StateVarSet.is_empty
  |> not


(* Evaluate equality *)
let eval_eq expr1 expr2 = match expr1, expr2 with

  (* true = e2 -> e2 *)
  | t, _ when t == Term.t_true -> expr2

  (* false = e2 -> not e2 *)
  | t, _ when t == Term.t_false -> eval_not expr2

  (* e1 = true -> e1 *)
  | _, t when t == Term.t_true -> expr1

  (* e1 = false -> not e1 *)
  | _, t when t == Term.t_false -> eval_not expr1

  (* e = e -> true and e has no pre *)
  | _ when Term.equal expr1 expr2
           && not (has_pre_vars expr1) && not (has_pre_vars expr2) ->
     Term.t_true

  | _ -> 

    match Term.destruct expr1, Term.destruct expr2 with
      
      | Term.T.Const c1, Term.T.Const c2 when
          Symbol.is_numeral c1 && 
          Symbol.is_numeral c2 -> 
    
        if Numeral.(Symbol.numeral_of_symbol c1 =
                    Symbol.numeral_of_symbol c2) then 

          Term.t_true

        else

          Term.t_false

      | Term.T.Const c1, Term.T.Const c2 when
          Symbol.is_decimal c1 && 
          Symbol.is_decimal c2 -> 
    
        if Decimal.(Symbol.decimal_of_symbol c1 =
                    Symbol.decimal_of_symbol c2) then 

          Term.t_true

        else

          Term.t_false

      
      | _ -> Term.mk_eq [expr1; expr2]
               
      | exception Invalid_argument _ -> Term.mk_eq [expr1; expr2]


(* Type of equality

   =: 'a -> 'a -> bool *)
let type_of_eq = type_of_a_a_bool


(* Equality *)
let mk_eq expr1 expr2 = mk_binary eval_eq type_of_eq expr1 expr2


(* ********************************************************************** *)

(* Evaluate disequality *)
let eval_neq expr1 expr2 = eval_not (eval_eq expr1 expr2)

(* Type of disequality

   <>: 'a -> 'a -> bool *)
let type_of_neq = type_of_a_a_bool


(* Disequality *)
let mk_neq expr1 expr2 = mk_binary eval_neq type_of_neq expr1 expr2 


(* ********************************************************************** *)


(* Evaluate inequality *)
let eval_lte expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && 
        Symbol.is_numeral c2 -> 

      if Numeral.(Symbol.numeral_of_symbol c1 <=
                  Symbol.numeral_of_symbol c2) then 

        Term.t_true

      else

        Term.t_false

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_decimal c1 && 
        Symbol.is_decimal c2 -> 

      if Decimal.(Symbol.decimal_of_symbol c1 <=
                  Symbol.decimal_of_symbol c2) then 

        Term.t_true

      else

        Term.t_false
    
    | _ ->
        (* Bitvector comparisons are simplified in the simplify module *) 
        (if (Type.is_ubitvector (Term.type_of_term expr1)) then 
          Term.mk_bvule [expr1; expr2]
        else if (Type.is_bitvector (Term.type_of_term expr1)) then
          Term.mk_bvsle [expr1; expr2]
        else
          Term.mk_leq [expr1; expr2])

    | exception Invalid_argument _ -> Term.mk_leq [expr1; expr2]


(* Type of inequality

   <=: int -> int -> bool
       real -> real -> bool *)
let type_of_lte = type_of_num_num_bool


(* Disequality *)
let mk_lte expr1 expr2 = mk_binary eval_lte type_of_lte expr1 expr2


(* ********************************************************************** *)


(* Evaluate inequality *)
let eval_lt expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && 
        Symbol.is_numeral c2 -> 

      if Numeral.(Symbol.numeral_of_symbol c1 <
                  Symbol.numeral_of_symbol c2) then 

        Term.t_true

      else

        Term.t_false

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_decimal c1 && 
        Symbol.is_decimal c2 -> 

      if Decimal.(Symbol.decimal_of_symbol c1 <
                  Symbol.decimal_of_symbol c2) then 

        Term.t_true

      else

        Term.t_false

    | _ ->
        (* Bitvector comparisons are simplified in the simplify module *) 
        (if (Type.is_ubitvector (Term.type_of_term expr1)) then 
          Term.mk_bvult [expr1; expr2]
        else if (Type.is_bitvector (Term.type_of_term expr1)) then
          Term.mk_bvslt [expr1; expr2]
        else 
          Term.mk_lt [expr1; expr2])

    | exception Invalid_argument _ -> Term.mk_lt [expr1; expr2]


(* Type of inequality

   <: int -> int -> bool
      real -> real -> bool *)
let type_of_lt = type_of_num_num_bool


(* Disequality *)
let mk_lt expr1 expr2 = mk_binary eval_lt type_of_lt expr1 expr2 


(* ********************************************************************** *)


(* Evaluate inequality *)
let eval_gte expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && 
        Symbol.is_numeral c2 -> 

      if Numeral.(Symbol.numeral_of_symbol c1 >=
                  Symbol.numeral_of_symbol c2) then 

        Term.t_true

      else

        Term.t_false

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_decimal c1 && 
        Symbol.is_decimal c2 -> 

      if Decimal.(Symbol.decimal_of_symbol c1 >=
                  Symbol.decimal_of_symbol c2) then 

        Term.t_true

      else

        Term.t_false

    | _ ->
        (* Bitvector comparisons are simplified in the simplify module *) 
        (if (Type.is_ubitvector (Term.type_of_term expr1)) then 
          Term.mk_bvuge [expr1; expr2]
        else if (Type.is_bitvector (Term.type_of_term expr1)) then
          Term.mk_bvsge [expr1; expr2]
        else 
          Term.mk_geq [expr1; expr2])

    | exception Invalid_argument _ -> Term.mk_geq [expr1; expr2]


(* Type of inequality

   >=: int -> int -> bool
       real -> real -> bool *)
let type_of_gte = type_of_num_num_bool


(* Disequality *)
let mk_gte expr1 expr2 = mk_binary eval_gte type_of_gte expr1 expr2 


(* ********************************************************************** *)


(* Evaluate inequality *)
let eval_gt expr1 expr2 = 

  match Term.destruct expr1, Term.destruct expr2 with

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_numeral c1 && 
        Symbol.is_numeral c2 -> 

      if Numeral.(Symbol.numeral_of_symbol c1 >
                  Symbol.numeral_of_symbol c2) then 

        Term.t_true

      else

        Term.t_false

    | Term.T.Const c1, Term.T.Const c2 when
        Symbol.is_decimal c1 && 
        Symbol.is_decimal c2 -> 

      if Decimal.(Symbol.decimal_of_symbol c1 >
                  Symbol.decimal_of_symbol c2) then 

        Term.t_true

      else

        Term.t_false

    | _ ->
        (* Bitvector comparisons are simplified in the simplify module *) 
        (if (Type.is_ubitvector (Term.type_of_term expr1)) then 
          (*if (Bitvector.ugt (Term.bitvector_of_term expr1) (Term.bitvector_of_term expr2)) then
            Term.t_true
          else
            Term.t_false*)
          Term.mk_bvugt [expr1; expr2]
        else if (Type.is_bitvector (Term.type_of_term expr1)) then
          (*if (Bitvector.gt (Term.bitvector_of_term expr1) (Term.bitvector_of_term expr2)) then
            Term.t_true
           else 
            Term.t_false*)
          Term.mk_bvsgt [expr1; expr2]
        else 
          Term.mk_gt [expr1; expr2])

    | exception Invalid_argument _ -> Term.mk_gt [expr1; expr2]


(* Type of inequality

   >=: int -> int -> bool
       real -> real -> bool *)
let type_of_gt = type_of_num_num_bool


(* Disequality *)
let mk_gt expr1 expr2 = mk_binary eval_gt type_of_gt expr1 expr2


(* ********************************************************************** *)


(* Evaluate if-then-else *)
let eval_ite = function 
  | t when t == Term.t_true -> (function expr2 -> (function _ -> expr2))
  | t when t == Term.t_false -> (function _ -> (function expr3 -> expr3))
  | expr1 -> 
    (function expr2 -> 
      (function expr3 -> 
        if Term.equal expr2 expr3 then 
          expr2 
        else
          (Term.mk_ite expr1 expr2 expr3))) 


(* Type of if-then-else

   If both the second and the third argument are bounded, the result
   is bounded by the smaller of the two lower bound and the greater of
   the upper bounds.

   ite: bool -> 'a -> 'a -> 'a *)
let type_of_ite = function 
  | t when t = Type.t_bool -> 

    (function type2 -> function type3 ->

       (* If first type is subtype of second, choose second type *)
       if Type.check_type type2 type3 then type3 else 

         (* If second type is subtype of first, choose first type *)
       if Type.check_type type3 type2 then type2 else 

         (* Extend integer ranges if one is not a subtype of the other *)
         (match type2, type3 with 
            | s, t when (Type.is_int_range s && Type.is_int t) ||
                  (Type.is_int s && Type.is_int_range t) -> Type.t_int

            | s, t when (Type.is_int_range s && Type.is_int_range t) -> 
              let l1, u1 = Type.bounds_of_int_range s in
              let l2, u2 = Type.bounds_of_int_range t in
              let lower = match l1, l2 with 
                | Some l1, Some l2 -> Some Numeral.(min l1 l2) 
                | _ -> None 
              in
              let upper = match u1, u2 with 
                | Some u1, Some u2 -> Some Numeral.(max u1 u2)
                | _ -> None
              in
             
             Type.mk_int_range lower upper 

            | _ -> raise Type_mismatch))

  | _ -> (function _ -> function _ -> raise Type_mismatch)


(* If-then-else *)
let mk_ite expr1 expr2 expr3 = 
  mk_ternary eval_ite type_of_ite expr1 expr2 expr3


(* ********************************************************************** *)


(* Type of ->

   If both the arguments are bounded, the result is bounded by the
   smaller of the two lower bound and the greater of the upper bounds.

   ->: 'a -> 'a -> 'a *)
let type_of_arrow type1 type2 =

  (* Extend integer ranges if one is not a subtype of the other *)
  (match type1, type2 with 
    | s, t 
      when (Type.is_int_range s && Type.is_int_range t) -> 
      
      let l1, u1 = Type.bounds_of_int_range s in
      let l2, u2 = Type.bounds_of_int_range t in
      let lower = match l1, l2 with 
        | Some l1, Some l2 -> Some Numeral.(min l1 l2) 
        | _ -> None 
      in
      let upper = match u1, u2 with 
        | Some u1, Some u2 -> Some Numeral.(max u1 u2)
        | _ -> None
      in
      
      Type.mk_int_range lower upper 

    | _ -> type_of_a_a_a type1 type2)


(* Followed by expression *)
let mk_arrow expr1 expr2 = 

  (* Types of expressions must be compatible *)
  let res_type = 
    type_of_arrow expr1.expr_type expr2.expr_type 
  in

  { expr_init = expr1.expr_init;
    expr_step = expr2.expr_step;
    expr_type = res_type } 
    

(* ********************************************************************** *)


(* Pre expression *)
(* We don't need to abstract the RHS because the AST normalization pass 
  already has. *)
let mk_pre ({ expr_init; expr_step } as expr) =
  if Term.equal expr_init expr_step then
    match expr_init with
    (* Expression is a constant not part of an unguarded pre expression *)
    | t when (t == Term.t_true
      || t == Term.t_false
      || (Term.is_free_var t && Term.free_var_of_term t |> Var.is_const_state_var)
      || (match Term.destruct t with
        | Term.T.Const c1 when Symbol.is_numeral c1 || Symbol.is_decimal c1 -> true
        | _ -> false))
      -> expr
    (* Expression is a variable at the current instant not part of an unguarded
      pre expression *)
    | t when Term.is_free_var t
      && Term.free_var_of_term t |> Var.is_state_var_instance
      && Numeral.(Var.offset_of_state_var_instance (Term.free_var_of_term t) = base_offset) ->
      let pt = Term.bump_state Numeral.(- one) t in
      { expr with expr_init = pt; expr_step = pt }
    (* Expression is not a variable at the current instant or a constant:
      abstract *)
    (* AST Normalization makes this situation impossible *)
    | _ -> assert false
  (* Stream is of the form: a -> b, abstract*)
  (* AST Normalization makes this situation impossible *)
  else assert false


let mk_pre_with_context mk_abs_for_expr mk_lhs_term ctx unguarded
    ({ expr_init; expr_step; expr_type } as expr) = 

  (* When simplifications fails, simply abstract with a new state variable,
      i.e., create an internal new memory. *)
  let abs_pre () =
    let expr_type = Type.generalize expr_type in
    let expr = { expr with expr_type } in
    (* Fresh state variable for identifier *)
    let abs, ctx = mk_abs_for_expr ctx expr in
    (* Abstraction at previous instant *)
    let abs_t = mk_lhs_term abs in
    { expr_init = abs_t;
      expr_step = abs_t;
      expr_type }, ctx
  in

  (* Stream is the same in the initial state and step (e -> e) *)
  if not unguarded &&
      Term.equal expr_init expr_step then
    match expr_init with
    (* Expression is a constant not part of an unguarded pre expression *)
    | t when
        (t == Term.t_true ||
          t == Term.t_false ||
          (Term.is_free_var t &&
          Term.free_var_of_term t |> Var.is_const_state_var) ||
            (match Term.destruct t with
            | Term.T.Const c1 when
                    Symbol.is_numeral c1 || Symbol.is_decimal c1 -> true
            | _ -> false)) ->
        
        expr, ctx
      
    (* Expression is a variable at the current instant not part of an unguarded
        pre expression *)
    | t when Term.is_free_var t &&
        Term.free_var_of_term t |> Var.is_state_var_instance &&
        Numeral.(Var.offset_of_state_var_instance (Term.free_var_of_term t) =
                    base_offset) ->

        let pt = Term.bump_state Numeral.(- one) t in
        { expr with expr_init = pt; expr_step = pt }, ctx
        
    (* Expression is not a variable at the current instant or a constant:
        abstract *)
    | _ -> abs_pre ()

  else (* Stream is of the form: a -> b, abstract*)

    abs_pre ()


(* ********************************************************************** *)


(* Evaluate select from array 

   Nothing to simplify here *)
let eval_select = Term.mk_select 


(* Type of A[k]

   A[k]: array 'a 'b -> 'a -> 'b *)
let type_of_select = function 

  (* First argument must be an array type *)
  | s when Type.is_array s -> 

    (function t -> 

      if (Type.is_int t || Type.is_int_range t) then

        (* Return type of array elements *)
        Type.elem_type_of_array s

      else

        (* Type of indexes do not match*)
        raise Type_mismatch)

  (* Not an array type *)
  | _ -> raise Type_mismatch


(* Select from an array *)
let mk_select expr1 expr2 =
  (* Types of expressions must be compatible *)
  mk_binary eval_select type_of_select expr1 expr2


let mk_array expr1 expr2 =
  (* Types of expressions must be compatible *)
  let type_of_array t1 t2 = Type.mk_array t1 t2 in
  mk_binary (fun x _ -> x) type_of_array expr1 expr2



(* ********************************************************************** *)

(* Evaluate store from array 

   Nothing to simplify here *)
let eval_store = Term.mk_store 


let type_of_store = function 

  (* First argument must be an array type *)
  | s when Type.is_array s -> 

    (fun i v -> 

       if (Type.is_int i || Type.is_int_range i) &&
          Type.check_type (Type.elem_type_of_array s) v
       then 

        (* Return type of array *)
        s

      else

        (* Type of indexes do not match*)
        raise Type_mismatch)

  (* Not an array type *)
  | _ ->
    raise Type_mismatch


(* Store from an array *)
let mk_store expr1 expr2 expr3 =
  (* Format.eprintf "mk_store  %a:%a [%a, %a]  %a:%a  %a:%a@." *)
  (*   (pp_print_lustre_expr false) expr1 *)
  (*   Type.pp_print_type (type_of_lustre_expr expr1) *)
  (*   Type.pp_print_type (Type.index_type_of_array (type_of_lustre_expr expr1)) *)
  (*   Type.pp_print_type (Type.elem_type_of_array (type_of_lustre_expr expr1)) *)
  (*   (pp_print_lustre_expr false) expr2 *)
  (*   Type.pp_print_type (type_of_lustre_expr expr2) *)
  (*   (pp_print_lustre_expr false) expr3 *)
  (*   Type.pp_print_type (type_of_lustre_expr expr3); *)
  (* Types of expressions must be compatible *)
  mk_ternary eval_store type_of_store expr1 expr2 expr3
    

let is_store e = Term.is_store e.expr_init && Term.is_store e.expr_step

let is_select e = Term.is_select e.expr_init && Term.is_select e.expr_step

let is_select_array_var e =
  is_select e &&
  try
    ignore (Term.indexes_and_var_of_select e.expr_init);
    ignore (Term.indexes_and_var_of_select e.expr_step);
    true
  with Invalid_argument _ -> false


let var_of_array_select e =
  let v1, _ = Term.indexes_and_var_of_select e.expr_init in
  let v2, _ = Term.indexes_and_var_of_select e.expr_step in
  if not (Var.equal_vars v1 v2) then invalid_arg ("var_of_array_select");
  v1

(* For an array select expression, get variable and list of indexes.
 * XXX: We could implement var_of_array_select in terms of this, but this
 * is stricter than var_of_array_select and will fail on different
 * indexes in init vs step. Maybe that should be the case anyway? *)
let indexes_and_var_of_array_select e =
  let v1, ixes1 = Term.indexes_and_var_of_select e.expr_init in
  let v2, ixes2 = Term.indexes_and_var_of_select e.expr_step in
  if not (Var.equal_vars v1 v2) then
    invalid_arg ("indexes_and_var_of_array_select.var");
  if not (List.for_all2 Term.equal ixes1 ixes2) then
    invalid_arg ("indexes_and_var_of_array_select.indexes");
  (v1, ixes1)

(* ********************************************************************** *)

(* Apply let binding for state variable at current instant to
   expression *)
let mk_let_cur substs ({ expr_init; expr_step } as expr) = 

  (* Split substitutions for initial state and step state *)
  let substs_init, substs_step = 
    let i, s = 
      List.fold_left
        (fun (substs_init, substs_step) (sv, { expr_init; expr_step }) -> 
           ((base_var_of_state_var base_offset sv, expr_init) :: substs_init, 
            (cur_var_of_state_var cur_offset sv, expr_step) :: substs_step))
        ([], [])
        substs
    in
    List.rev i, List.rev s
  in
  
  (* Apply substitutions separately *)
  { expr with 
      expr_init = Term.mk_let substs_init expr_init; 
      expr_step = Term.mk_let substs_step expr_step }


(* Apply let binding for state variable at previous instant to
   expression *)
let mk_let_pre substs ({ expr_init; expr_step } as expr) = 

  (* Split substitutions for initial state and step state *)
  let substs_init, substs_step = 
    let i, s = 
      List.fold_left
        (fun (substs_init, substs_step) (sv, { expr_init; expr_step }) -> 
           ((pre_base_var_of_state_var base_offset sv, expr_init) :: substs_init, 
            (pre_var_of_state_var cur_offset sv, expr_step) :: substs_step))
        ([], [])
        substs
    in
    List.rev i, List.rev s
  in

  let subst_has_arrays =
    List.exists (fun (v, _) -> Var.type_of_var v |> Type.is_array) in

  let expr_init =
    if subst_has_arrays substs_init then Term.apply_subst substs_init expr_init
    else Term.mk_let substs_init expr_init in

  let expr_step =
    if subst_has_arrays substs_step then Term.apply_subst substs_step expr_step
    else Term.mk_let substs_step expr_step in
  
  (* Apply substitutions separately *)
  { expr with expr_init; expr_step}

(* ********************************************************************** *)

(* Return expression of a numeral *)
let mk_int_expr n = Term.mk_num n


let mk_of_expr ?as_type expr = 

  let expr_type = match as_type with
    | Some ty -> ty
    | None -> Term.type_of_term expr
  in
  
  { expr_init = expr; 
    expr_step = expr; 
    expr_type } 


let is_numeral = Term.is_numeral

let numeral_of_expr = Term.numeral_of_term


let unsafe_term_of_expr e = (e : Term.t)
let unsafe_expr_of_term t = t

let push_select { expr_init; expr_step; expr_type } =
  let expr_init' = Term.push_select expr_init in
  let expr_step' = Term.push_select expr_step in
  { expr_init = expr_init';
    expr_step = expr_step';
    expr_type
  }

let mk_select_and_push e1 e2 =
  mk_select e1 e2 |> push_select

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
