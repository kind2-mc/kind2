(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

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

(* Old code, see below for new code using Simplify module *)

(*
(* Value of an expression *)
type value =
  | ValBool of bool
  | ValInt of int
  | ValReal of float
  | ValTerm of Term.t


(* Extract the Boolean value from the value of an expression *)
let bool_of_value = function 
  | ValBool b -> b
  | ValTerm t -> 
    invalid_arg ("bool_of_value for term " ^ (string_of_t Term.pp_print_term t))
  | _ -> invalid_arg "bool_of_value"
    

(* Extract the integer value from the value of an expression *)
let int_of_value = function 
  | ValInt b -> b
  | ValTerm t -> 
    invalid_arg ("int_of_value for term " ^ (string_of_t Term.pp_print_term t))
  | _ -> invalid_arg "int_of_value"


(* Extract the float value from the value of an expression *)
let float_of_value = function 
  | ValReal b -> b
  | _ -> invalid_arg "float_of_value"


(* Check if the value is unknown *)
let value_is_unknown = function 
  | ValTerm _ -> true
  | _ -> false


(* Convert a value to a term *)
let term_of_value = function 
  | ValBool true -> Term.mk_true ()
  | ValBool false -> Term.mk_false ()
  | ValInt i -> Term.mk_num_of_int i
  | ValReal f -> Term.mk_dec_of_float f
  | ValTerm t -> t


(* Compute value of a term from values of its subterms 

   TODO: Evaluate distinct predicate, bitvector and array
   operators *)
let rec eval_term_node' sym args = match sym, args with

  (* Return constant true *)
  | `TRUE, [] -> ValBool true

  (* Must be nullary *)
  | `TRUE, _ -> assert false

  (* Return constant true *)
  | `FALSE, [] -> ValBool false

  (* Must be nullary *)
  | `FALSE, _ -> assert false

  (* Negate Boolean value of subterm *)
  | `NOT, [t] -> ValBool (not (bool_of_value t))

  (* Negation must be unary *)
  | `NOT, _ -> assert false

  (* Implication is a disjunction, empty implication is false *)
  | `IMPLIES, [] -> ValBool false

  (* An implication without premises is true if the conclusion is true *)
  | `IMPLIES, [t] -> t

  (* Evaluate binary implication as ~a | b *)
  | `IMPLIES, [t1; t2] -> 

    ValBool (not (bool_of_value t1) || (bool_of_value t2))

  (* Reduce higher arities to ~(a & b & ...) | c *)
  | `IMPLIES, (t1 :: t2 :: tl) -> 

    eval_term_node' 
      `IMPLIES 
      ((eval_term_node' `AND [t1; t2]) :: tl)

  (* Empty conjunction is true *)
  | `AND, [] -> ValBool true

  (* Unary conjunction is value of the argument *)
  | `AND, [t] -> t

  (* Binary conjunction *)
  | `AND, [t1; t2] ->       

    ValBool ((bool_of_value t1) && (bool_of_value t2))

  (* Left-associativity higher arities *)
  | `AND, (t1 :: t2 :: tl) -> 

    eval_term_node' 
      `AND 
      ((eval_term_node' `AND [t1; t2]) :: tl)

  (* Empty disjunction is false *)
  | `OR, [] -> ValBool false

  (* Unary disjunction is value of the argument *)
  | `OR, [t] -> t

  (* Binary disjunction *)
  | `OR, [t1; t2] ->       

    ValBool ((bool_of_value t1) || (bool_of_value t2))

  (* Left-associativity higher arities *)
  | `OR, (t1 :: t2 :: tl) -> 

    eval_term_node' 
      `OR 
      ((eval_term_node' `OR [t1; t2]) :: tl)

  (* Exclusive disjunction is at least binary *)
  | `XOR, []
  | `XOR, _ :: [] -> assert false

  (* Evaluate binary xor as (a & ~b) | (~a & b) *)
  | `XOR, [t1; t2] -> 

    ValBool 
      (((not (bool_of_value t1)) && (bool_of_value t2)) ||
       ((bool_of_value t1) && (not (bool_of_value t2))))

  (* Left-associativity for higher arities *)
  | `XOR, (t1 :: t2 :: tl) -> 

    eval_term_node' 
      `XOR 
      ((eval_term_node' `XOR [t1; t2]) :: tl)

  (* Equality is at least binary *)
  | `EQ, []
  | `EQ, _ :: [] -> assert false

  (* Binary equation is true if values are equal *)
  | `EQ, [t1; t2] -> ValBool (t1 = t2)

  (* Conjunctive chain of equations for higher arities *)
  | `EQ, t1 :: t2 :: tl -> 

    eval_term_node'
      `AND 
      [(eval_term_node' `EQ [t1; t2]); 
       (eval_term_node' `EQ (t2 :: tl))]

  (* TODO: reduce distinct to a quadratic set of negated equations *)
  | `DISTINCT, _ -> assert false 

  (* if-then else evaluates to second or third argument *)
  | `ITE, [p; l; r] -> if bool_of_value p then l else r

  (* if-then else must be ternary *)
  | `ITE, _ -> assert false

  (* Constant value for numeral *)
  | `NUMERAL i, [] -> ValInt (int_of_numeral i)

  (* Must be nullary *)
  | `NUMERAL _, _ -> assert false 

  (* Constant value for decimal *)
  | `DECIMAL f, [] -> ValReal (float_of_decimal f)

  (* Must be nullary *)
  | `DECIMAL _, _ -> assert false 

  (* TODO: bitvectors *)
  | `BV _, [] -> assert false

  (* Must be nullary *)
  | `BV _, _ -> assert false

  (* Must be at least unary *)
  | `MINUS, [] -> assert false

  (* Unary minus is the negative of number *)
  | `MINUS, [t] -> 

    (* Distinguish between integer and real values, else fail *)
    (match t with 
      | ValInt i -> ValInt (- i)
      | ValReal f -> ValReal (-. f)
      | _ -> assert false)

  (* Binary minus is the difference between two numbers *)
  | `MINUS, [t1; t2] -> 

    (* Distinguish between integer and real values, else fail *)
    (match t1, t2 with 
      | ValInt i1, ValInt i2 -> ValInt (i1 - i2)
      | ValReal f1, ValReal f2 -> ValReal (f1 -. f2)
      | _ -> assert false)

  (* Left-associativity higher arities *)
  | `MINUS, t1 :: t2 :: tl -> 

    eval_term_node' 
      `MINUS 
      ((eval_term_node' `MINUS [t1; t2]) :: tl) 

  (* Must be at least binary *)
  | `PLUS, [] 
  | `PLUS, _ :: [] -> assert false

  (* Binary plus is the sum of two numbers *)
  | `PLUS, [t1; t2] -> 

    (* Distinguish between integer and real values, else fail *)
    (match t1, t2 with 
      | ValInt i1, ValInt i2 -> ValInt (i1 + i2)
      | ValReal f1, ValReal f2 -> ValReal (f1 +. f2)
      | _ -> assert false)

  (* Left-associativity higher arities *)
  | `PLUS, t1 :: t2 :: tl -> 

    eval_term_node' 
      `PLUS 
      ((eval_term_node' `PLUS [t1; t2]) :: tl) 

  (* Must be at least binary *)
  | `TIMES, [] 
  | `TIMES, _ :: [] -> assert false

  (* Binary times is the product of two numbers *)
  | `TIMES, [t1; t2] -> 

    (* Distinguish between integer and real values, else fail *)
    (match t1, t2 with 
      | ValInt i1, ValInt i2 -> ValInt (i1 * i2)
      | ValReal f1, ValReal f2 -> ValReal (f1 *. f2)
      | _ -> assert false)

  (* Left-associativity higher arities *)
  | `TIMES, t1 :: t2 :: tl -> 

    eval_term_node' 
      `TIMES 
      ((eval_term_node' `TIMES [t1; t2]) :: tl) 

  (* Must be at least binary *)
  | `DIV, [] 
  | `DIV, _ :: [] -> assert false

  (* Binary division is the quotient of two numbers *)
  | `DIV, [t1; t2] -> 

    (* Only allow real values, else fail *)
    (match t1, t2 with 
      | ValReal f1, ValReal f2 -> ValReal (f1 /. f2)
      | _ -> assert false)

  (* Left-associativity higher arities *)
  | `DIV, t1 :: t2 :: tl -> 

    eval_term_node' 
      `DIV 
      ((eval_term_node' `DIV [t1; t2]) :: tl) 

  (* Must be at least binary *)
  | `INTDIV, [] 
  | `INTDIV, _ :: [] -> assert false

  (* Binary division is the quotient of two numbers *)
  | `INTDIV, [t1; t2] -> 

    (* Only allow integer values, else fail *)
    (match t1, t2 with 
      | ValInt i1, ValInt i2 -> ValInt (i1 / i2)
      | _ -> assert false)

  (* Left-associativity higher arities *)
  | `INTDIV, t1 :: t2 :: tl -> 

    eval_term_node' 
      `INTDIV 
      ((eval_term_node' `INTDIV [t1; t2]) :: tl) 

  (* Must be binary *)
  | `MOD, [] 
  | `MOD, _ :: [] -> assert false

  (* Binary modulus *)
  | `MOD, [t1; t2] -> 

    (* Only allow integer values, else fail *)
    (match t1, t2 with 
      | ValInt i1, ValInt i2 -> ValInt (i1 mod i2)
      | _ -> assert false)

  (* Modulus is at most binary *)
  | `MOD, _ -> assert false

  (* Must be unary *)
  | `ABS, [] -> assert false

  (* Absolute value *)
  | `ABS, [t] -> 

    (* Only allow integer values, else fail *)
    (match t with 
      | ValInt i -> ValInt (abs i)
      | _ -> assert false)

  (* Modulus is at most unary *)
  | `ABS, _ -> assert false

  (* Must be at least binary *)
  | `LEQ, [] 
  | `LEQ, _ :: [] -> assert false

  (* Binary relation is true if first value is less than or equal to
     second *)
  | `LEQ, [t1; t2] -> ValBool (t1 <= t2)

  (* Conjunctive chain of relations for higher arities *)
  | `LEQ, t1 :: t2 :: tl -> 

    eval_term_node'
      `AND 
      [(eval_term_node' `LEQ [t1; t2]); 
       (eval_term_node' `LEQ (t2 :: tl))]

  (* Must be at least binary *)
  | `LT, [] 
  | `LT, _ :: [] -> assert false

  (* Binary relation is true if first value is less than second *)
  | `LT, [t1; t2] -> ValBool (t1 < t2)

  (* Conjunctive chain of relations for higher arities *)
  | `LT, t1 :: t2 :: tl -> 

    eval_term_node'
      `AND 
      [(eval_term_node' `LT [t1; t2]); 
       (eval_term_node' `LT (t2 :: tl))]


  (* Must be at least binary *)
  | `GEQ, [] 
  | `GEQ, _ :: [] -> assert false

  (* Binary relation is true if first value is greater than or equal
     to second *)
  | `GEQ, [t1; t2] -> ValBool (t1 >= t2)

  (* Conjunctive chain of relations for higher arities *)
  | `GEQ, t1 :: t2 :: tl -> 

    eval_term_node'
      `AND 
      [(eval_term_node' `GEQ [t1; t2]); 
       (eval_term_node' `GEQ (t2 :: tl))]


  (* Must be at least binary *)
  | `GT, [] 
  | `GT, _ :: [] -> assert false

  (* Binary relation is true if first value is greater than
     second *)
  | `GT, [t1; t2] -> ValBool (t1 > t2)

  (* Conjunctive chain of relations for higher arities *)
  | `GT, t1 :: t2 :: tl -> 

    eval_term_node'
      `AND 
      [(eval_term_node' `GT [t1; t2]); 
       (eval_term_node' `GT (t2 :: tl))]

  (* Must be unary *)
  | `TO_REAL, [] -> assert false 

  (* Convert integer to real *)
  | `TO_REAL, [t] -> 

    (* Only allow integer values, else fail *)
    (match t with 
      | ValInt i -> ValReal (float_of_int i)
      | _ -> assert false)

  (* Must be at most unary *)
  | `TO_REAL, _ -> assert false 

  (* Must be unary *)
  | `TO_INT, [] -> assert false 

  (* Convert real to integer *)
  | `TO_INT, [t] -> 

    (* Only allow real values, else fail *)
    (match t with 
      | ValReal f -> ValInt (int_of_float f)
      | _ -> assert false)

  (* Must be at most unary *)
  | `TO_INT, _ -> assert false 

  (* Must be unary *)
  | `IS_INT, [] -> assert false 

  (* Return true if real conincides with an integer *)
  | `IS_INT, [t] -> 

    (* Only allow real values, else fail *)
    (match t with 
      | ValReal f -> ValBool ((floor f) = (ceil f))
      | _ -> assert false)

  (* Must be at most unary *)
  | `IS_INT, _ -> assert false 

  (* Must be unary *)
  | `DIVISIBLE _, [] -> assert false 

  (* Return true if integer is divisible by constant integer *)
  | `DIVISIBLE n, [t] -> 

    (* Only allow integer values, else fail *)
    (match t with 
      | ValInt i -> ValBool (i mod (int_of_numeral n) = 0)
      | _ -> assert false)

  (* Must be at most unary *)
  | `DIVISIBLE _, _ -> assert false 

  (* TODO: bitvectors *)
  | `CONCAT, _ -> assert false
  | `EXTRACT _, _ -> assert false
  | `BVNOT, _ -> assert false
  | `BVNEG, _ -> assert false
  | `BVAND, _ -> assert false
  | `BVOR, _ -> assert false
  | `BVADD, _ -> assert false
  | `BVMUL, _ -> assert false
  | `BVDIV, _ -> assert false
  | `BVUREM, _ -> assert false
  | `BVSHL, _ -> assert false
  | `BVLSHR, _ -> assert false
  | `BVULT, _ -> assert false

  (* TODO: arrays *)
  | `SELECT, _ -> assert false
  | `STORE, _ -> assert false

  (* Cannot evaluate uninterpreted functions *)
  | `UF u, l -> ValTerm (Term.mk_uf u (List.map term_of_value l))


(* Evaluate subterm and add value to cache if requested

   There is not need for a cache, since we are doing bottom-up
   evaluation. *)
let eval_term_node cache model fterm args' = 

  match fterm with 

    (* Return assignment to variable *)
    | H.Var v -> 
      (try Var.VarHashtbl.find model v with 
        | Not_found -> 
          failwith 
            (Format.sprintf 
               "Eval.eval_term_node: No model for %s" 
               (string_of_t Var.pp_print_var v)))

    (* Return computed value of non-variable term *)
    | H.Const sym 
    | H.App (sym, _) -> 

      (* Compute value for term *)
      let res = eval_term_node' (Symbol.node_of_symbol sym) args' in

      (* Add value of term to cache if requested *)
      (match cache with 
        | None -> ()
        | Some c -> Term.TermNodeHashtbl.add c (Term.T.construct fterm) res);

      (* Return computed value *)
      res
    

(* Evaluate a term to a value given an assignment to its free variables *)
let rec eval_term' cache term env = 

  (* Add variables into hash table *)
  let model = Var.VarHashtbl.create 7 in

  (* Initialize model hash table, evaluate each assigned term of a
     variable to a value. Do not enter subterms into cache. *)
  List.iter 
    (function (v, e) -> 
      Var.VarHashtbl.add model v (eval_term' None e []))
    env;

  (* Evaluate term bottom-up *)
  let value =
    Term.T.eval_t (eval_term_node cache model) (Term.node_of_term term)
  in

  (* Return value *)
  value


(* Evaluate a term to a value *)
let eval_term term env = 
  eval_term' None term env
    
(* Populate hash table with values of subterms *)
let eval_subterms cache term env = 
  let _ = eval_term' (Some cache) term env in ()

*)

(* New code using simplify *)

(* Value of an expression *)
type value =
  | ValBool of bool
  | ValNum of Numeral.t
  | ValDec of Decimal.t
  | ValTerm of Term.t


let pp_print_value ppf =
  function 
    | ValBool true -> Format.fprintf ppf "true"
    | ValBool false -> Format.fprintf ppf "false"
    | ValNum n -> Format.fprintf ppf "%a" Numeral.pp_print_numeral n
    | ValDec d -> Format.fprintf ppf "%a" Decimal.pp_print_decimal d
    | ValTerm t -> Format.fprintf ppf "%a" Term.pp_print_term t


(* Extract the Boolean value from the value of an expression *)
let bool_of_value = function 
  | ValBool b -> b
  | ValTerm t -> 
    invalid_arg ("bool_of_value for term " ^ (string_of_t Term.pp_print_term t))
  | ValDec d -> 
    invalid_arg
      (Format.asprintf
         "bool_of_value: value %a is decimal"
         Decimal.pp_print_decimal d)
  | ValNum n -> 
    invalid_arg 
      (Format.asprintf
         "bool_of_value: value %a is numeric" 
         Numeral.pp_print_numeral n)

(* Extract the integer value from the value of an expression *)
let num_of_value = function 
  | ValNum b -> b
  | ValTerm t -> 
    invalid_arg ("num_of_value for term " ^ (string_of_t Term.pp_print_term t))
  | _ -> invalid_arg "num_of_value"


(* Extract the float value from the value of an expression *)
let dec_of_value = function 
  | ValDec b -> b
  | _ -> invalid_arg "dec_of_value"


(* Check if the value is unknown *)
let value_is_unknown = function 
  | ValTerm _ -> true
  | _ -> false


(* Convert a value to a term *)
let term_of_value = function 
  | ValBool true -> Term.mk_true ()
  | ValBool false -> Term.mk_false ()
  | ValNum n -> Term.mk_num n
  | ValDec d -> Term.mk_dec d
  | ValTerm t -> t


(* Convert a term to a value *)
let rec value_of_term term = match Term.destruct term with 

  (* Term is a constant *)
  | Term.T.Const s -> 

    (

      (* Unhashcons constant symbol *)
      match Symbol.node_of_symbol s with 

        (* Term is an integer numeral *)
        | `NUMERAL n -> ValNum n

        (* Term is a real decimal *)
        | `DECIMAL d -> ValDec d

        (* Term is a propositional constant *)
        | `TRUE -> ValBool true
        | `FALSE -> ValBool false
(*
        (* Bitvectors not implemented *)
        | `BV _ -> assert false
*)
        (* Uninterpreted constant *)
        | `UF u -> ValTerm term 

        (* Fail in remaining cases, which are not constants *)
        | _ -> assert false 

    ) 

  (* Term is a negative constant symbol *)
  | Term.T.App (s, [c]) when s == Symbol.s_minus && Term.is_leaf c -> 

    (

      (* Get symbol of constant *)
      match Symbol.node_of_symbol (Term.leaf_of_term c) with 
        
        (* Term is an integer numeral *)
        | `NUMERAL n -> ValNum (Numeral.neg n)
                          
        (* Term is a real decimal *)
        | `DECIMAL d -> ValDec (Decimal.neg d)

        (* Term is not a constant *)
        | _ -> ValTerm term)
                 
  (* Term is not a constant *)
  | _ -> ValTerm term


(* Evaluate a term to a value *)
let eval_term uf_defs model term = 
  
  (* Simplify term with the model and return a value *)
  value_of_term (Simplify.simplify_term_model uf_defs model term)


(*
let num = Term.mk_num_of_int 
let dec = Term.mk_dec_of_float 
let u_i s = UfSymbol.mk_uf_symbol s [Type.Int] Type.Int 
let u_b s = UfSymbol.mk_uf_symbol s [Type.Int] Type.Bool 
let var_i s t = Term.mk_uf (u_i s) [t] 
let varn_i s i = Term.mk_uf (u_i s) [num i] 
let var_b s t = Term.mk_uf (u_b s) [t] 
let varn_b s i = Term.mk_uf (u_b s) [num i] 
let pt = Term.mk_true ()
let pf = Term.mk_false ()
let eq l r = Term.mk_eq [l; r] 
let ite p l r = Term.mk_ite p l r 
let c j1 j2 = Term.mk_and [j1; j2]
let d j1 j2 = Term.mk_or [j1; j2]
let n j = Term.mk_not j
let leq l r = Term.mk_leq [l; r] 
let lt l r = Term.mk_lt [l; r] 
let geq l r = Term.mk_geq [l; r] 
let gt l r = Term.mk_gt [l; r] 
let plus a b = Term.mk_plus [a; b] 
let minus a b = Term.mk_minus [a; b] 
let times a b = Term.mk_times [a; b] 

let v_x = Var.mk_state_var "x" Type.Int  
let v_y = Var.mk_state_var "y" Type.Int  

let v_x0 = Var.mk_state_var_instance v_x 0
let v_x1 = Var.mk_state_var_instance v_x 1

let v_y0 = Var.mk_state_var_instance v_y 0
let v_y1 = Var.mk_state_var_instance v_y 1

let t_x0 = Term.mk_var v_x0 
let t_y0 = Term.mk_var v_y0 
let t_x1 = Term.mk_var v_x1 
let t_y1 = Term.mk_var v_y1 


let main () =
  
  let ts = 
    [ Term.mk_let [v_y0, (num 2)] (plus t_x0 t_y0),  [(v_x0, t_y0); (v_y0, (num 0))] 
    ]
  in
       

  List.iter 
    (function t, e -> 
      Format.printf "%a@." Term.pp_print_term t;
      let t' = term_of_value (eval_term t e) in
      Format.printf "%a@." Term.pp_print_term t')
    ts
  

;;

main ()


*)
(*

let main () = 

  let t_t = Term.mk_true () in
  let t_f = Term.mk_false () in

  let t_1f = Term.mk_dec_of_float 1. in
  let t_2f = Term.mk_dec_of_float 2. in
  let t_3f = Term.mk_dec_of_float 3. in

  let t_1i = Term.mk_num_of_int 1 in
  let t_2i = Term.mk_num_of_int 2 in
  let t_3i = Term.mk_num_of_int 3 in

  let t = Term.mk_is_int t_1f in

  let e = eval_term t in

  Format.printf 
    "%a %a %B@."
    Term.pp_print_term t
    Term.pp_print_term (term_of_value (e []))
    (bool_of_value (e []));
  


  let u1 = UfSymbol.mk_uf_symbol "P1" [] Type.Bool in
  let u2 = UfSymbol.mk_uf_symbol "P2" [] Type.Bool in
  let u3 = UfSymbol.mk_uf_symbol "P3" [] Type.Bool in
  let a = List.map (function s -> Term.mk_uf s []) [u1; u2; u3] in
  let t = Term.mk_eq a in
 

  Format.printf 
    "%a@."
    Term.pp_print_term t;

  let e = eval_term t in

  let envs = 
    [List.combine a [t_t; t_t; t_t];
     List.combine a [t_t; t_t; t_f];
     List.combine a [t_t; t_f; t_t];
     List.combine a [t_t; t_f; t_f];
     List.combine a [t_f; t_t; t_t];
     List.combine a [t_f; t_t; t_f];
     List.combine a [t_f; t_f; t_t];
     List.combine a [t_f; t_f; t_f]]
  in

  Format.printf 
    "@[<v>%a@]@."
    (pp_print_list Term.pp_print_term "") 
    (List.map term_of_value (List.map e envs));

  let u1 = UfSymbol.mk_uf_symbol "u1" [] Type.Int in

  let u2 = UfSymbol.mk_uf_symbol "u2" [Type.Int] Type.Int in

  let t1 = Term.mk_uf u1 [] in

  let t2 = 
    Term.mk_let 
      [("x", Term.mk_num_of_int 0)] 
      (Term.mk_uf u2 [Term.mk_sym "x" Type.Int]) in
  let t2' = Term.mk_uf u2 [Term.mk_num_of_int 0] in

  let e1 = eval_term t1 in


  Format.printf 
    "%a %a@." 
    Term.pp_print_term 
    t1
    Term.pp_print_term 
    (term_of_value (e1 [(t1, Term.mk_num_of_int 0)]));


  Format.printf 
    "%a@." 
    Term.pp_print_term 
    t2;
  
  let e2 = 
    eval_term t2 [(t1, Term.mk_num_of_int 0); (t2', Term.mk_num_of_int 1)] 
  in

  Format.printf 
    "%a@." 
    Term.pp_print_term 
    (term_of_value e2);


  let e2 = eval_subterms t2 in

  let env = [(t1, Term.mk_num_of_int 0); (t2', Term.mk_num_of_int 1)] in

  Term.TermHashtbl.iter 
    (fun k v -> 
      Format.printf 
        "%a %a@."
        Term.pp_print_term k
        Term.pp_print_term (try term_of_value (v env) with Invalid_argument _ -> k))
    e2

;;

main ()

*)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
