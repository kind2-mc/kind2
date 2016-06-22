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
open Kind1.Types
open Kind1.Exceptions
open Kind1.Channels
open Format 

(* Pretty-print a Lustre type *)
let rec pp_print_lustre_type ppf = function   

  | L_INT -> pp_print_string ppf "L_INT"

  | L_REAL -> pp_print_string ppf "L_REAL"

  | L_BOOL -> pp_print_string ppf "L_BOOL"

  | L_INT_RANGE (l, u) -> fprintf ppf "@[<hv 12>L_INT_RANGE(%d,@,%d)@]" l u

  | L_TUPLE t ->
    
    fprintf ppf "@[<hv 8>L_TUPLE(%a)@]" pp_print_lustre_type_list t

  | L_RECORD r ->

    fprintf ppf "@[<hv 9>L_RECORD(%a)@]" pp_print_lustre_type_record_list r

  | L_TYPEDEF s -> 

    fprintf ppf "@[<hv 10>L_TYPEDEF(%s)@]" s
      
  | L_UNDET -> pp_print_string ppf "L_UNDET"

  | M_BOOL -> pp_print_string ppf "M_BOOL"

  | M_NAT-> pp_print_string ppf "M_NAT"

  | M_FUNC t -> 

    fprintf ppf "@[<hv 7>M_FUNC(%a)@]" pp_print_lustre_type_list t


and pp_print_lustre_type_list ppf = function 

  | [] -> ()

  | t :: [] -> pp_print_lustre_type ppf t

  | t :: tl -> 

    pp_print_lustre_type ppf t;
    pp_print_string ppf ",";
    pp_print_cut ppf ();
    pp_print_lustre_type_list ppf tl

and pp_print_lustre_type_record_list ppf = function 

  | [] -> ()

  | (f, t) :: [] -> fprintf ppf "@[<hv 1>(%s,%a)@]" f pp_print_lustre_type t

  | (f, t) :: tl -> 

    fprintf ppf "@[<hv 1>(%s,%a)@]" f pp_print_lustre_type t;
    pp_print_string ppf ",";
    pp_print_cut ppf ();
    pp_print_lustre_type_record_list ppf tl


(* Return a string representation of a Lustre type *)
let lustre_type_to_string e = 

  (* Create a buffer to print into *)
  let buf = Buffer.create 100 in
  
  (* Create a pretty-printer into the buffer *)
  let ppf = Format.formatter_of_buffer buf in
  
  (* Print the formula into the buffer *)
  pp_print_lustre_type ppf e;
  pp_print_flush ppf ();

  (* Return the contents of the buffer *)
  Buffer.contents buf

    
(* Pretty-print a relation in an IL formula *)
let pp_print_il_relation ppf = function 
  | EQ -> pp_print_string ppf "EQ"
  | LT -> pp_print_string ppf "LT"
  | GT -> pp_print_string ppf "GT"
  | LTE -> pp_print_string ppf "LTE"
  | GTE -> pp_print_string ppf "GTE"
  | NEQ -> pp_print_string ppf "NEQ"


(* Exploit associativity of B_AND and flatten nesting into a list *)
let rec flatten_b_and accum = function 

  | B_AND (f, g) :: tl -> 
    flatten_b_and accum (f :: g :: tl)
      
  | f :: tl -> 
    flatten_b_and (f :: accum) tl
      
  | [] -> List.rev accum

(* Exploit associativity of B_OR and flatten nesting into a list *)
let rec flatten_b_or accum = function 

  | B_OR (f, g) :: tl -> 
    flatten_b_or accum (f :: g :: tl)
      
  | f :: tl -> 
    flatten_b_or (f :: accum) tl
      
  | [] -> List.rev accum


(* Exploit associativity of F_AND and flatten nesting into a list *)
let rec flatten_f_and accum = function 

  | F_AND (f, g) :: tl -> 
    flatten_f_and accum (g :: f :: tl)
      
  | f :: tl -> 
    flatten_f_and (f :: accum) tl
      
  | [] -> List.rev accum

(* Exploit associativity of F_OR and flatten nesting into a list *)
let rec flatten_f_or accum = function 

  | F_OR (f, g) :: tl -> 
    flatten_f_or accum (f :: g :: tl)
      
  | f :: tl -> 
    flatten_f_or (f :: accum) tl
      
  | [] -> List.rev accum


let rec pp_print_il_expression ppf = function 

  (* This is a Boolean, the integer zero is INT_CONST (NUM 0) *)
  | ZERO -> pp_print_string ppf "ZERO"
    
  (* This is a Boolean, the integer one is INT_CONST (NUM 1) *)
  | ONE -> pp_print_string ppf "ONE"
    
  (* The constant for the base case of the induction, i.e. 0 *)
  | STEP_BASE -> pp_print_string ppf "STEP_BASE"
    
  (* The variable for the current position *)
  | POSITION_VAR s -> fprintf ppf "POSITION_VAR(%s)" s
    
  (* An integer constant *)
  | INT_CONST e -> 

    fprintf ppf "@[<hv 10>INT_CONST(%a)@]" pp_print_il_expression e

  (* TODO: what is the purpose of f? *)
  | REAL_CONST (e, _) -> 

    fprintf ppf "@[<hv 11>REAL_CONST(%a)@]" pp_print_il_expression e

  (* A string *)
  | STRING s -> fprintf ppf "STRING(%s)" s

  (* An integer *)
  | NUM i -> fprintf ppf "@[<hv 4>NUM(%d)@]" i
  
  (* A float *)
  | FLOAT f -> fprintf ppf "@[<hv 6>FLOAT(%f)@]" f
      
  (* An addition *)
  | PLUS (e, f) -> 

    fprintf 
      ppf 
      "@[<hv 5>PLUS(%a,@,%a)@]" 
      pp_print_il_expression e 
      pp_print_il_expression f

  (* A subtraction *)
  | MINUS (e, f) -> 

    fprintf 
      ppf 
      "@[<hv 6>MINUS(%a,@,%a)@]" 
      pp_print_il_expression e 
      pp_print_il_expression f

  (* A multiplication *)
  | MULT (e, f) ->

    fprintf 
      ppf 
      "@[<hv 5>MULT(%a,@,%a)@]" 
      pp_print_il_expression e 
      pp_print_il_expression f

  (* A division *)
  | DIV (e, f) ->

    fprintf 
      ppf 
      "@[<hv 4>DIV(%a,@,%a)@]" 
      pp_print_il_expression e 
      pp_print_il_expression f

  (* An integer division *)
  | INTDIV (e, f) ->

    fprintf 
      ppf 
      "@[<hv 7>INTDIV(%a,@,%a)@]" 
      pp_print_il_expression e 
      pp_print_il_expression f
      
  (* A modulo operation *)
  | MOD (e, f) ->

    fprintf 
      ppf 
      "@[<hv 4>MOD(%a,@,%a)@]" 
      pp_print_il_expression e 
      pp_print_il_expression f
      
  (* A unary minus *)
  | UMINUS e -> 

    fprintf 
      ppf 
      "@[<hv 7>UMINUS(%a)@]" 
      pp_print_il_expression e 

  (* A relation *)
  | REL (r, e, f) ->

    fprintf 
      ppf 
      "@[<hv 4>REL(%a,@,%a,@,%a)@]" 
      pp_print_il_relation r 
      pp_print_il_expression e
      pp_print_il_expression f 
      
  (* An if-then-else *)
  | ITE (p, e, f) ->
    
    fprintf 
      ppf 
      "@[<hv 4>ITE(%a,@,%a,@,%a)@]" 
      pp_print_il_expression p
      pp_print_il_expression e
      pp_print_il_expression f 
      
  (* An if-then-else on streams *)
  | STREAM_ITE (p, e, f) ->

    fprintf 
      ppf 
      "@[<hv 11>STREAM_ITE(%a,@,%a,@,%a)@]" 
      pp_print_il_expression p
      pp_print_il_expression e
      pp_print_il_expression f 
      
  (* A Boolean conjunction *)
  | B_AND _ as f ->

    (* Flatten nested B_AND terms and print as conjunction of n terms *)
    fprintf 
      ppf 
      "@[<hv 6>B_AND(%a)]" 
      pp_print_il_expression_list
      (flatten_b_and [] [f])

  (* A Boolean disjunction *)
  | B_OR _ as f ->

    (* Flatten nested B_OR terms and print as conjunction of n terms *)
    fprintf 
      ppf 
      "@[<hv 5>B_OR(%a)@]" 
      pp_print_il_expression_list
      (flatten_b_or [] [f])

  (* A Boolean equivalence *)
  | B_IFF (e, f) ->

    fprintf 
      ppf 
      "@[<hv 6>B_IFF(%a,@,%a)@]" 
      pp_print_il_expression e
      pp_print_il_expression f 

  (* A Boolean implication *)
  | B_IMPL (e, f) ->

    fprintf 
      ppf 
      "@[<hv 7>B_IMPL(%a,@,%a)@]" 
      pp_print_il_expression e
      pp_print_il_expression f 

  (* A Boolean negation *)
  | B_NOT e -> 

    fprintf 
      ppf 
      "@[<hv 6>B_NOT(%a)@]" 
      pp_print_il_expression e

  (* A stream variable with paramters symbol, depth, id, position *)
  | VAR_GET (s, d, ((NUM v) as i), p) -> 

    (* Get type for variable *)
    let (_, _, t, _) = Kind1.Tables.safe_find_varinfo v "yc_simplify_var" in

    fprintf 
      ppf 
      "@[<hv 8>VAR_GET(%s,@,%d,@,%a,@,%a,@,%a)@]" 
      s.s
      d
      pp_print_il_expression i
      pp_print_il_expression p
      pp_print_lustre_type t

  (* A stream variable with paramters symbol, depth, id, position *)
  | VAR_GET (s, d, v, p) -> 

    fprintf 
      ppf 
      "@[<hv 8>VAR_GET(%s,@,%d,@,%a,@,%a)@]" 
      s.s
      d
      pp_print_il_expression v
      pp_print_il_expression p

  (* (string * il_expression) list *)
  | RECORD_LIT l -> 
    
    fprintf 
      ppf 
      "@[<hv 11>RECORD_LIT(%a)@]" 
      pp_print_record_lit_list l

    (* il_expression * string *)
  | RECORDREF (e, s) -> 

    fprintf 
      ppf 
      "@[<hv 10>RECORDREF(%a,@,%s)@]" 
      pp_print_il_expression e
      s
      
  (* il_expression list *)
  | TUPLE_LIT l -> 

    fprintf 
      ppf 
      "@[<hv 10>TUPLE_LIT(%a)@]" 
      pp_print_il_expression_list l
      
  (* il_expression * int *)  
  | TUPLEREF (e, i) -> 

    fprintf 
      ppf 
      "@[<hv 9>TUPLEREF(%a,@,%d)@]" 
      pp_print_il_expression e
      i
      
  (* used when comparing symbolic positions

     string * il_expression list *)  
  | PRED (s, l)  -> 

    fprintf 
      ppf 
      "@[<hv 6>PRED(%s,@,%a)@]" 
      s
      pp_print_il_expression_list l
    

(* Print a list of IL expressions *)
and pp_print_il_expression_list ppf = function

  | [] -> ()
  
  | e :: [] -> 
    pp_print_il_expression ppf e

  | e :: tl -> 

    pp_print_il_expression ppf e;
    pp_print_string ppf ",";
    pp_print_cut ppf ();
    pp_print_il_expression_list ppf tl


(* Print a list of IL expressions *)
and pp_print_record_lit_list ppf = function

  | [] -> ()
  
  | (s, e) :: [] -> 
    fprintf ppf "@[<hv 1>(%s,@,%a)@]" s pp_print_il_expression e

  | (s,e) :: tl -> 

    fprintf ppf "@[<hv 1>(%s,@,%a)@]" s pp_print_il_expression e;
    pp_print_string ppf ",";
    pp_print_cut ppf ();
    pp_print_record_lit_list ppf tl


(* Print an IL formula *)    
let rec pp_print_il_formula ppf = function 

  (* The propositonal constant true *)
  | F_TRUE -> pp_print_string ppf "F_TRUE"
    
  (* The propositonal constant false *)
  | F_FALSE -> pp_print_string ppf "F_FALSE"

  (* A propositonal constant *)
  | F_STR s -> fprintf ppf "F_STR(%s)" s

  (* A negation *)
  | F_NOT f -> 
    
    fprintf 
      ppf 
      "@[<hv 6>F_NOT(%a)@]" 
      pp_print_il_formula f

  (* An equation of expressions *)
  | F_EQ (l, r, t) -> 

    fprintf 
      ppf 
      "@[<hv 5>F_EQ(%a,@,%a,@,%a)@]" 
      pp_print_il_expression l
      pp_print_il_expression r
      pp_print_lustre_type t

  (* A conjunction *)
  | F_AND _ as f -> 

    (* Flatten nested F_AND terms and print as conjunction of n terms *)
    fprintf 
      ppf 
      "@[<hv 6>F_AND(%a)@]" 
      pp_print_il_formula_list
      (flatten_f_and [] [f])

  (* A disjunction *)
  | F_OR _ as f  ->

    (* Flatten nested F_OR terms and print as disjunction of n terms *)
    fprintf 
      ppf 
      "@[<hv 5>F_OR(%a)@]" 
      pp_print_il_formula_list
      (flatten_f_or [] [f])

  (* An implication *)
  | F_IMPL (f, g) ->

    fprintf 
      ppf 
      "@[<hv 7>F_IMPL(%a,@,%a)@]" 
      pp_print_il_formula f
      pp_print_il_formula g

  (* A propositonal constant (nullary predicate) *)
  | F_PRED (p, []) -> fprintf ppf "@[<hv 7>F_PRED(%s)@]" p
    
  (* A predicate *)
  | F_PRED (p, l) -> 
    
    fprintf 
      ppf 
      "@[<hv 7>F_PRED(%s,@,%a)@]" 
      p
      pp_print_il_expression_list l
      
(* Print a list of IL formulas *)
and pp_print_il_formula_list ppf = function

  | [] -> ()
  
  | e :: [] -> 
    pp_print_il_formula ppf e

  | e :: tl -> 

    pp_print_il_formula ppf e;
    pp_print_string ppf ",";
    pp_print_cut ppf ();
    pp_print_il_formula_list ppf tl


let il_expression_to_string e = 

  (* Create a buffer to print into *)
  let buf = Buffer.create 100 in
  
  (* Create a pretty-printer into the buffer *)
  let ppf = Format.formatter_of_buffer buf in
  
  (* Print the formula into the buffer *)
  pp_print_il_expression ppf e;
  pp_print_flush ppf ();

  (* Return the contents of the buffer *)
  Buffer.contents buf


let il_formula_to_string init f = 

  (* Create a buffer to print into *)
  let buf = Buffer.create 100 in
  
  (* Create a pretty-printer into the buffer *)
  let ppf = Format.formatter_of_buffer buf in
  
  (* Print the formula into the buffer *)
  pp_print_il_formula ppf f;
  
  (* Return the contents of the buffer *)
  Buffer.contents buf


let type_mismatch_to_string expr t_is t_expected = 

  (* Create a buffer to print into *)
  let buf = Buffer.create 100 in
  
  (* Create a pretty-printer into the buffer *)
  let ppf = Format.formatter_of_buffer buf in
  
  (* Print the expression into the buffer *)
  fprintf 
    ppf
    "Type mismatch for %a: should be %a but is %a.@?"
    pp_print_il_expression expr
    pp_print_lustre_type t_expected
    pp_print_lustre_type t_is;
  
  (* Return the contents of the buffer *)
  Buffer.contents buf
  

let rec il_expression_to_term init = function 

  (* This is a Boolean, the integer zero is INT_CONST (NUM 0) *)
  | None, ZERO 
  | Some L_BOOL, ZERO -> Term.mk_false ()
      
  | Some t, ZERO -> failwith (type_mismatch_to_string ZERO t L_BOOL)
    
  (* This is a Boolean, the integer one is INT_CONST (NUM 1) *)
  | None, ONE
  | Some L_BOOL, ONE ->  Term.mk_true ()

  | Some t, ONE -> failwith (type_mismatch_to_string ONE t L_BOOL)

  (* The constant for the base case of the induction, i.e. 0 *)
  | None, STEP_BASE
  | Some L_INT, STEP_BASE -> assert false

  | Some t, STEP_BASE -> failwith (type_mismatch_to_string STEP_BASE t L_INT)

  (* The variable for the current position

     This will be eliminated *)
  | None, POSITION_VAR s
  | Some L_INT, POSITION_VAR s -> 

    if init then 

      (* Print as integer 0 in the initial state *)
      il_expression_to_term init (Some L_INT, INT_CONST (NUM 0))

    else 

      (* Print as integer 0 in the initial state *)
      il_expression_to_term init (Some L_INT, INT_CONST (STRING s))

  | Some t, (POSITION_VAR _ as e) -> 
    failwith (type_mismatch_to_string e t L_INT)

  (* An integer constant *)
  | None, INT_CONST e 
  | Some L_INT, INT_CONST e -> 

    il_expression_to_term init (Some L_INT, e)

  | Some t, (INT_CONST _ as e) -> 
    failwith (type_mismatch_to_string e t L_INT)

  (* TODO: what is the purpose of the second element in the pair? *)
  | None, REAL_CONST (e, _)
  | Some L_REAL, REAL_CONST (e, _) -> 

    il_expression_to_term init (Some L_REAL, e)

  | Some t, (REAL_CONST _ as e) -> 
    failwith (type_mismatch_to_string e t L_REAL)

  (* A string *)
  | Some L_INT, STRING s -> assert false

(*
    let u = UfSymbol.mk_uf_symbol s [Type.Int] Type.Int true in

    Term.mk_uf u [Term.mk_succ state_index] 
*)

  (* A string *)
  | Some L_REAL, STRING s -> assert false

(*
    let u = UfSymbol.mk_uf_symbol s [Type.Int] Type.Real true in

    Term.mk_uf u [Term.mk_succ state_index]
*)

  (* A string *)
  | Some L_BOOL, STRING s -> assert false

(*
    let u = UfSymbol.mk_uf_symbol s [Type.Int] Type.Bool true in

    Term.mk_uf u [Term.mk_succ state_index]
*)

  | Some t, STRING _ -> 
    failwith ("Unsupported type " ^ (lustre_type_to_string t) ^ " for STRING")

  | None, STRING _ -> failwith "No type information for STRING"

  (* An integer *)
  | Some L_INT, NUM i -> Term.mk_num_of_int i

  | Some L_REAL, NUM i -> Term.mk_dec (Decimal.of_int i)

  | Some t, (NUM _ as e) -> failwith (type_mismatch_to_string e t L_INT)

  | None, NUM _ -> failwith "No type information for NUM"
  
  (* A float *)
  | Some L_REAL, FLOAT f -> Term.mk_dec (Decimal.of_string (string_of_float f))

  | Some t, (FLOAT _ as e) -> failwith (type_mismatch_to_string e t L_REAL)

  | None, FLOAT _ -> failwith "No type information for FLOAT"

  (* An addition *)
  | t, PLUS (e, f) -> 

    (* Convert IL formulas to SMT expressions *)
    let e' = il_expression_to_term init (t, e) in
    let f' = il_expression_to_term init (t, f) in
    
    Term.mk_plus [e'; f']

  (* A subtraction *)
  | t, MINUS (e, f) -> 

    (* Convert IL formulas to SMT expressions *)
    let e' = il_expression_to_term init (t, e) in
    let f' = il_expression_to_term init (t, f) in
    
    Term.mk_minus [e'; f']

  (* A multiplication *)
  | t, MULT (e, f) ->

    (* Convert IL formulas to SMT expressions *)
    let e' = il_expression_to_term init (t, e) in
    let f' = il_expression_to_term init (t, f) in
    
    Term.mk_times [e'; f']

  (* A division *)
  | t, DIV (e, f) ->

    (* Convert IL formulas to SMT expressions *)
    let e' = il_expression_to_term init (t, e) in
    let f' = il_expression_to_term init (t, f) in
    
    Term.mk_div [e'; f']
    
  (* An integer division *)
  | None, INTDIV (e, f) 
  | Some L_INT, INTDIV (e, f) ->

    (* Convert IL formulas to SMT expressions *)
    let e' = il_expression_to_term init (Some L_INT, e) in
    let f' = il_expression_to_term init (Some L_INT, f) in
    
    Term.mk_intdiv [e'; f']

  | Some t, (INTDIV _ as e) -> failwith (type_mismatch_to_string e t L_INT)

  (* A modulo operation *)
  | None, MOD (e, f) 
  | Some L_INT, MOD (e, f) ->

    (* Convert IL formulas to SMT expressions *)
    let e' = il_expression_to_term init (Some L_INT, e) in
    let f' = il_expression_to_term init (Some L_INT, f) in
    
    Term.mk_mod e' f'

  | Some t, (MOD _ as e) -> failwith  (type_mismatch_to_string e t L_INT)

  (* A unary minus *)
  | t, UMINUS e -> 

    (* Convert IL formulas to SMT expressions *)
    let e' = il_expression_to_term init (t, e) in
    
    Term.mk_minus [e']

  (* A disequality *)
  | None, REL (NEQ, e, f) 
  | Some L_BOOL, REL (NEQ, e, f) 
  | Some M_BOOL, REL (NEQ, e, f) -> 

    (* Convert to not (= e f) 

       Alternative: (distinct e f) *)
    il_expression_to_term
      init 
      (Some L_BOOL, (B_NOT (REL (EQ, e, f))))

  | Some t, (REL (NEQ, _, _)) -> failwith "type mismatch for REL"

  (* A relation *)
  | None, REL (r, e, f) 
  | Some L_BOOL, REL (r, e, f) 
  | Some M_BOOL, REL (r, e, f) ->

    (* Convert IL formulas to SMT expressions *)
    let e' = il_expression_to_term init (None, e) in
    let f' = il_expression_to_term init (None, f) in
    
    let mk_rel = 
      match r with 
        | EQ -> Term.mk_eq
        | LT -> Term.mk_lt
        | GT -> Term.mk_gt
        | LTE -> Term.mk_leq
        | GTE -> Term.mk_geq
        | NEQ -> Term.mk_distinct
      in 

    mk_rel [e'; f']

  | Some t, REL _ -> failwith "type mismatch for REL"

  (* An if-then-else *)
  | t, ITE (p, e, f) ->
    
    (* Convert IL formulas to SMT expressions *)
    let p' = il_expression_to_term init (Some L_BOOL, p) in
    let e' = il_expression_to_term init (t, e) in
    let f' = il_expression_to_term init (t, f) in

    Term.mk_ite p' e' f'

  (* An if-then-else on streams dependent on whether a position
     variable is equal to the base *)
  | t, STREAM_ITE (REL(EQ, POSITION_VAR _, STEP_BASE), e, f) ->

    if init then 

      (* Print the base case *)
      il_expression_to_term init (t, e)

    else

      (* Print the base case *)
      il_expression_to_term init (t, f)

  (* An if-then-else on streams *)
  | t, STREAM_ITE (p, e, f) ->
    
    (* Print as normal if-then-else *)
    il_expression_to_term init (t, ITE (p, e, f))

  (* A Boolean conjunction *)
  | None, (B_AND _ as f)
  | Some L_BOOL, (B_AND _ as f)
  | Some M_BOOL, (B_AND _ as f) ->

    (* Create arguments in solver *)
    let f' = 
      il_expression_list_to_term_list 
        init 
        [] 
        (Some L_BOOL, flatten_b_and [] [f])
    in
    
    Term.mk_and f'

  | Some _, B_AND _ -> failwith "type mismatch for B_AND"

  (* A Boolean disjunction *)
  | None, (B_OR _ as f)
  | Some L_BOOL, (B_OR _ as f)
  | Some M_BOOL, (B_OR _ as f) ->

    (* Create arguments in solver *)
    let f' = 
      il_expression_list_to_term_list 
        init 
        [] 
        (Some L_BOOL, flatten_b_or [] [f])
    in
    
    Term.mk_or f'

  | Some _, B_OR _ -> failwith "type mismatch for B_OR"

  (* A Boolean equivalence *)
  | t, B_IFF (e, f) ->

    (* Convert IL formulas to SMT expressions *)
    let e' = il_expression_to_term init (Some L_BOOL, e) in
    let f' = il_expression_to_term init (Some L_BOOL, f) in

    Term.mk_eq [e'; f']

  (* A Boolean implication *)
  | None, B_IMPL (e, f)
  | Some L_BOOL, B_IMPL (e, f)
  | Some M_BOOL, B_IMPL (e, f) ->

    (* Convert IL formulas to SMT expressions *)
    let e' = il_expression_to_term init (Some L_BOOL, e) in
    let f' = il_expression_to_term init (Some L_BOOL, f) in
    
    Term.mk_implies [e'; f']

  | Some _, B_IMPL _ -> failwith "type mismatch for B_IMPL"

  (* A Boolean negation *)
  | None, B_NOT e
  | Some L_BOOL, B_NOT e
  | Some M_BOOL, B_NOT e -> 

    (* Convert IL formulas to SMT expressions *)
    let e' = il_expression_to_term init (Some L_BOOL, e) in
    
    Term.mk_not e'

  | Some _, B_NOT _ -> failwith "type mismatch for B_NOT"

  (* A stream variable with parameters symbol, depth, id, position *)
  | tt, (VAR_GET (s, d, (NUM id), p) as e) -> 

    (
      
      (* Get substituted variable from inlining if any *)
      let nk = Kind1.Tables.resolve_substitution id in
      
      (* Keep track of variables used and at what position *)
      Kind1.Tables.update_used_vars nk d e;
(*    
      (* Get depth of position *)
      let pos_depth = -(Lus_convert.simplify_position_depth p) in
*)
      try
        
        (* Get variable info for substituted variable *)
        let (_, v, t, c) = 
          Kind1.Tables.safe_find_varinfo nk "yc_simplify_var" 
        in

        let var_type = 

          (* Type check *)
          match tt, t with 
            | None, L_BOOL -> Type.t_bool
            | None, L_INT -> Type.t_int
            | None, L_INT_RANGE (l, u) -> 
              Type.mk_int_range (Numeral.of_int l) (Numeral.of_int u)
            | None, L_REAL -> Type.t_real
            | Some L_BOOL, L_BOOL -> Type.t_bool
            | Some L_INT, L_INT -> Type.t_int
            | Some (L_INT_RANGE (l, u)), L_INT_RANGE (l', u') 
              when l = l' && u = u' -> 
              Type.mk_int_range (Numeral.of_int l) (Numeral.of_int u)
            | Some L_REAL, L_REAL -> Type.t_real
            | None, t -> 
              failwith ("Unsupported type " ^ (lustre_type_to_string t))
            | Some tt', t when tt' = t -> 
              failwith ("Unsupported type " ^ (lustre_type_to_string t))
            | Some tt', t -> 
              failwith 
                ("Type mismatch for " ^ 
                    (il_expression_to_string e) ^ 
                    ": should be " ^ 
                    (lustre_type_to_string tt') ^ 
                    " but is " ^
                    (lustre_type_to_string t) ^ 
                    ".")
        in

        (* Set variable info for symbol *)
        s.s <- v;

        let state_var = 
          StateVar.mk_state_var 
            v 
            (not (Kind1.Tables.var_is_stateful nk))
            var_type 
        in

        let var' = 
          Var.mk_state_var_instance 
            state_var
            (match p with 
              | POSITION_VAR "M" -> 
                if init then Numeral.zero else Numeral.one
              | MINUS (POSITION_VAR "M", NUM 1) -> Numeral.zero
              | _ -> 
                failwith 
                  (Format.fprintf 
                     str_formatter
                     "VAR_GET for deeper state %a" 
                     pp_print_il_expression 
                     p;
                   flush_str_formatter ()))
        in

        Term.mk_var var'
          
      with Not_found -> raise (IdNotFound "??")

    )

  | _, VAR_GET _ -> 
    failwith "VAR_GET with non-NUM term"

  (* (string * il_expression) list *)
  | _, RECORD_LIT l -> 
    failwith "RECORD_LIT not implemented"

    (* il_expression * string *)
  | _, RECORDREF (e, s) -> 
    failwith "RECORDREF not implemented"
      
  (* il_expression list *)
  | _, TUPLE_LIT l -> 
    failwith "TUPLE_LIT not implemented"
      
  (* il_expression * int *)  
  | _, TUPLEREF (e, i) -> 
    failwith "TUPLEREF not implemented"
      
  (* used when comparing symbolic positions

     string * il_expression list *)  
  | _, PRED (s, l)  -> 
    failwith "PRED not implemented"
    



and il_expression_list_to_term_list init accum = function 

  | (_, []) -> accum

  | (t, e :: tl) -> 

    let e' = il_expression_to_term init (t, e) in

    il_expression_list_to_term_list init (e' :: accum) (t, tl)


let rec il_formula_to_term init = function 

  (* The propositonal constant true *)
  | F_TRUE -> Term.mk_true ()

  (* The propositonal constant false *)
  | F_FALSE -> Term.mk_false ()

  (* A propositonal constant *)
  | F_STR s -> assert false 

(*
    let u = UfSymbol.mk_uf_symbol s [Type.Int] Type.Bool in 
    Term.mk_uf u [Term.mk_succ state_index]
*)

  (* A negation *)
  | F_NOT f -> 

    (* Convert IL formula to SMT expression *)
    let f' = il_formula_to_term init f in

    Term.mk_not f'
      
  (* An equation of expressions *)
  | F_EQ (l, r, t) -> 

    (* Convert IL formulas to SMT expressions *)
    let l' = 
      (* The type from Lus_convert.convert_def_list is always L_INT *)
      (* il_expression_to_smt_expr solver init symbols (Some t, l) *)
      il_expression_to_term init (None, l) 
    in
    let r' = 
      (* The type from Lus_convert.convert_def_list is always L_INT *)
      (* il_expression_to_smt_expr solver init symbols' (Some t, r) *)
      il_expression_to_term init (None, r) 
    in

    Term.mk_eq [l'; r']


  (* A conjunction *)
  | F_AND _ as f -> 

    (* Create arguments in solver *)
    let f' = 
      il_formula_list_to_term_list 
        init 
        [] 
        (flatten_f_and [] [f])
    in
    
    Term.mk_and f'

  (* A disjunction *)
  | F_OR _ as f -> 

    (* Create arguments in solver *)
    let f' = 
      il_formula_list_to_term_list 
        init 
        [] 
        (flatten_f_or [] [f])
    in
    
    Term.mk_or f'

  (* An implication *)
  | F_IMPL (f, g) ->

    (* Convert IL formulas to SMT expressions *)
    let f' = il_formula_to_term init f in
    let g' = il_formula_to_term init g in
    
    Term.mk_implies [f'; g']

  (* A propositonal constant (nullary predicate) *)
  | F_PRED (p, []) -> assert false

(*
    let u = UfSymbol.mk_uf_symbol p [Type.Int] Type.Bool in
    Term.mk_uf u [Term.mk_succ state_index]
*)

  (* A predicate *)
  | F_PRED (p, l) -> 
    failwith "F_PRED not implemented"
    

and il_formula_list_to_term_list init accum = function 

  | [] -> accum

  | e :: tl -> 

    let e' = il_formula_to_term init e in

    il_formula_list_to_term_list init (e' :: accum) tl



(* Extract assignment from an equation *)
let assignment_of_il_equation init l r t =

  (* Extract state variable from left-hand side of equation *)
  let state_var = match l with 

    (* Left-hand side must be a stream variable at position zero *)
    | VAR_GET (s, d, (NUM id), POSITION_VAR "M") as e -> 

      (

        (* Get substituted variable from inlining if any *)
        let nk = Kind1.Tables.resolve_substitution id in

        (debug parse
           "VAR_GET: %d resolved to %d" id nk
         in

        (* Keep track of variables used and at what position *)
        Kind1.Tables.update_used_vars nk d e);

        try
          
          (* Get variable info for substituted variable *)
          let (_, v, t, c) = 
            Kind1.Tables.safe_find_varinfo nk "yc_simplify_var" 
          in

          (* Type of variable *)
          let var_type = match t with 
            | L_BOOL -> Type.t_bool
            | L_INT -> Type.t_int
            | L_INT_RANGE (l, u) -> 
              Type.mk_int_range (Numeral.of_int l) (Numeral.of_int u)
            | L_REAL -> Type.t_real
            | t -> 
              failwith ("Unsupported type " ^ (lustre_type_to_string t))
          in

          (* Set variable info for symbol *)
          s.s <- v;

          (* Create state variable *)
          StateVar.mk_state_var 
            v 
            (not (Kind1.Tables.var_is_stateful nk))
            var_type 

        with Not_found -> raise (IdNotFound "??")

      )

    | _ -> raise (Invalid_argument "Left-hand side of equation must be primed state variable")

  in
  
  (* Extract assigned term from right-hand side *)
  let term = il_expression_to_term init (None, r) in 

  (* Return pair of state variable and assigned term *)
  (state_var, term)


(* Extract a list of assignments of terms to state variables from a list IL formulas *)
let rec assignments_of_il_formulas init invariants assignments = function

  (* Extract assignments from each conjunct *)
  | F_AND (f, g) :: tl -> 

    assignments_of_il_formulas init invariants assignments (f :: g :: tl)

  (* Extract assignment from equation *)
  | F_EQ (VAR_GET (_, _, (NUM _), POSITION_VAR "M") as l, r, t) :: tl -> 

    assignments_of_il_formulas 
      init
      invariants 
      ((assignment_of_il_equation init l r t) :: assignments) 
      tl

  (* Treat other terms as invariants *)    
  | e :: tl -> 
    
    assignments_of_il_formulas 
      init
      ((il_formula_to_term init e) :: invariants)
      assignments
      tl

  (* Return at the end of the stack *)
  | [] -> (invariants, assignments)

    

let of_channel in_ch =   

  (* Must flatten pres *)
  Kind1.OldFlags.abstr_non_var_pre := true;

  (* Do not distribute pres over operations *)
  (* Flags.abstr_non_var_dist := false; *)

  (* Initialise buffer for lexing *)
  let lexbuf = Lexing.from_channel in_ch in

  (* Buffer for debug output *)
  let outdoc = Buffer.create 1000 in

  (* Create hash table to cache definitions *)
  let def_hash = Kind1.Deftable.get_defhash () in

  (* Flag *)
  let no_stateful = ref false in

  try
    
    (* Parse input file, first parameter is not used,
       - p is the property to prove, 
       - list_p is the list of properties to prove 
       - target_node is the top node *)
    let _, p, list_p, target_node = 
      Kind1.Lustre_parser.main Kind1.Lustre_lexer.token lexbuf 
    in
    
    let position = POSITION_VAR "M" in

    if

      (* Do abstraction? *)
      !Kind1.OldFlags.abstr_bool || 
        !Kind1.OldFlags.abstr_ite || 
        !Kind1.OldFlags.abstr_pre || 
        !Kind1.OldFlags.abstr_non_var_pre

    then 
      
      (* Flatten and abstract *)
      Kind1.Lus_flatten.flatten_all_node_defs ();

    (* Convert stream definitions into il_formula *)
    let fd = Kind1.Lus_convert.convert_def_list position target_node in
    
    (* Get meximum depth, i.e. nesting of pres *)
    let maxdepth = Kind1.Lus_convert.get_max_depth () in

    if 
      
      (* Nesting of pres is deeper than depth of followedbys *)
      maxdepth > Kind1.Lus_convert.get_max_adepth () 

    then
      
      (* Unguarded pre exists, fail *) 
      raise Unguarded_PRE;
    
    (* Formula with inlining *)
    let fd' =

      (* Do aggressive inlining? *)
      if !Kind1.OldFlags.aggressive_inlining > 0 then

        (* Inline formula, od not inline variables in property *)
        Kind1.Inlining.inlined_formula fd (Kind1.Coi.property_id_list p) 

      else

        (* Keep formula *)
        fd

    in
    
    (* Initialise cone of influence *)
    Kind1.Coi.examine_assignments fd';
    
    (* vrefs lists the initial set of variables: properties,
       basically *)
    let vrefs = Kind1.Coi.property_id_list p in

    (* State variables refined *)
    let vrefs' = 
      
      (* Refine state variables? *)
      if !Kind1.OldFlags.pre_refine_state_vars then

        (* Add refined state variables *)
        List.rev_append vrefs (Kind1.Lus_convert.state_vars_list())

      else
        
        (* Keep state variables *)
        vrefs

    in

    (* Calculate cone of influence based on state variables for depth
       between 0 and memory depth *)
    Kind1.Coi.calculate_all_dependencies vrefs' 0 maxdepth;

    (* The property *)
    let props, _ = 

      List.fold_left 
        
        (function (accum, i) -> 
          function id -> 
            
            (* Get substituted variable from inlining if any *)
            let nk = Kind1.Tables.resolve_substitution id in
            
            (* Get variable info for substituted variable *)
            let (_, v, t, _) = 
              Kind1.Tables.safe_find_varinfo nk "yc_simplify_var" 
            in
            
            let k = match t with 
              | Kind1.Types.L_BOOL -> Type.t_bool
              | Kind1.Types.L_INT -> Type.t_int
              | Kind1.Types.L_REAL -> Type.t_real
            in
(*
            (* Create list of current state variables and list of next
               state variables *)
            let u = UfSymbol.mk_uf_symbol v [Type.Int] k true in

            let p = Term.mk_uf u [state_index] in
*)
            let sv = StateVar.mk_state_var v true k in

            let p = 
              Term.mk_var 
                (Var.mk_state_var_instance sv Numeral.zero)
            in

            ((StateVar.original_name_of_state_var sv, p) :: accum, succ i)
        )
        
        ([], 0)
        vrefs'
        
    in

(*
    (* Convert internal representation to initial state constraint *)
    let init_term = 
      il_formula_to_term true fd'
    in

    (* Convert internal representation to formula for transition relation *)
    let trans_term = 
      il_formula_to_term false fd' 
    in
*)

    debug parse 
         ";; Transition relation@\n%a@\n"
         pp_print_il_formula 
         fd' 
     in
     

     (* Convert internal representation to assignments in initial state *)
     let invariants, init_assignments = 
       assignments_of_il_formulas true [] [] [fd'] 
     in
     
     (* Convert internal representation to assignments in transition *)
     let _, trans_assignments = 
       assignments_of_il_formulas false [] [] [fd'] 
     in

    (* Convert assertions to a formula *)
    let assert_term =

      (* Get assertions *)
      match Kind1.Lus_assertions.get_assertion_term () with

        (* No assertions *)
        | None -> Term.t_true

        (* Assertions present *)
        | Some a -> 
          
          debug parse 
              ";; Assertions@\n%a@\n"
              pp_print_il_expression a
          in
          
          (* Convert parsed expression to a term of Boolean type *)
          il_expression_to_term true (Some L_BOOL, a)

    in

    debug parse
      "@[<v>Invariants:@,%a@]"
      Lustre.pp_print_term assert_term
    in

    (* Invariants of transition system *)
    let invars = 

      (* Trivial assertions only? *)
      if assert_term == Term.t_true then 

        (* Invariants are only type invariants *)
        TransSys.invars_of_types () 

      else

        (* Invariants are assertions and type invariants *)
        assert_term :: TransSys.invars_of_types ()

    in

    (* Get declared variables 

       TODO: filter for proper state variables here, i.e. variables
       that occur under a pre *)
    let vars = StateVar.fold (fun v a -> v :: a) [] in

    (* Resulting transition system *)
    let res =
      { TransSys.init_assign = init_assignments;
        TransSys.init_constr = [];
        TransSys.constr_assign = StateVar.StateVarHashtbl.create (List.length trans_assignments);
        TransSys.constr_constr = [];
        TransSys.trans = [];
        TransSys.props = props;
        TransSys.invars = invars;
        TransSys.props_valid = [];
        TransSys.props_invalid = [];
        TransSys.constr_dep = StateVar.StateVarHashtbl.create (List.length trans_assignments) } 
    in

    (* Add definition to transition relation *)
    TransSys.constr_of_def_list res.TransSys.constr_assign trans_assignments;

    (* Return transition system *)
    res

  with 

    (* Type mismatch in parsing *)
    | TypeMismatch (s, x, y) ->

      Format.printf 
        "@\nType Mismatch %s:@\n%a@\n!=@\n%a@\n at line %d (col %d)@." 
        s
        pp_print_lustre_type x 
        pp_print_lustre_type y
        (!Kind1.Lus_convert.linenum) 
        ((Lexing.lexeme_start lexbuf) - !Kind1.Lus_convert.linepos);
      raise Lus_convert_error

    (* Error in parsing *)
    | Parsing.Parse_error ->
      Format.printf "@\nParse error at line %d (col %d): '%s'@." 
        (!Kind1.Lus_convert.linenum) 
        ((Lexing.lexeme_start lexbuf) - !Kind1.Lus_convert.linepos)
        (Lexing.lexeme lexbuf);
      raise Lus_convert_error


let of_file filename =

  (* Open the given file for reading *)
  let use_file = open_in filename in
  let in_ch = use_file in

  of_channel in_ch


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
