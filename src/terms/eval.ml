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

(* Value of an expression *)
type value =
  | ValBool of bool
  | ValNum of Numeral.t
  | ValDec of Decimal.t
  | ValSBV of Bitvector.t
  | ValUBV of Bitvector.t
  | ValTerm of Term.t


(* Pretty-print a value *)
let pp_print_value ppf =
  function 
    | ValBool true -> Format.fprintf ppf "true"
    | ValBool false -> Format.fprintf ppf "false"
    | ValNum n -> Format.fprintf ppf "%a" Numeral.pp_print_numeral n
    | ValDec d -> Format.fprintf ppf "%a" Decimal.pp_print_decimal d
    | ValSBV b -> Format.fprintf ppf "%a" Bitvector.pp_print_signed_machine_integer b
    | ValUBV b -> Format.fprintf ppf "%a" Bitvector.pp_print_unsigned_machine_integer b
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
  | ValSBV b ->
    invalid_arg
      (Format.asprintf
         "bool_of_value: value %a is signed machine integer"
         Bitvector.pp_print_signed_machine_integer b)
  | ValUBV b ->
    invalid_arg
      (Format.asprintf
         "bool_of_value: value %a is unsigned machine integer"
          Bitvector.pp_print_unsigned_machine_integer b)

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

let sbv_of_value = function
  | ValSBV b -> b
  | _ -> invalid_arg "sbv_of_value"

let ubv_of_value = function
  | ValUBV b -> b
  | _ -> invalid_arg "ubv_of_value"

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
  | ValSBV b -> Term.mk_bv b
  | ValUBV b -> Term.mk_bv b
  | ValTerm t -> t


(* Convert a term to a value *)
let value_of_term term = match Term.destruct term with 

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

        (* Term is a constructor *)

        (* Term is a signed bitvector *)
        | `BV b -> ValSBV b

        (* Term is an unsigned bitvector *)
        | `UBV b -> ValUBV b

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

  (* Term is a negative constant symbol *)
  | Term.T.App (s, [c]) when s == Symbol.s_bvneg && Term.is_leaf c ->

    (

      (* Get symbol of constant *)
      match Symbol.node_of_symbol (Term.leaf_of_term c) with

      | `BV b -> ValSBV (Bitvector.sbv_neg b)

      | _ -> assert false

    )

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
