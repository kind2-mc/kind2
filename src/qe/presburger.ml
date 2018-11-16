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

open Poly

(* Formula is not in linear integer arithmetic *)
exception Not_in_LIA

(* Intermediate formula in the bottom-up conversion from term to
   Presburger atoms*)
type iformula =
  | Poly of poly
  | Formula of cformula 


(* Combine a singleton Presburger formula into another Presburger formula *)
let combine_singleton_to_iformula (if1: iformula) (if2: iformula) : iformula = 

  match if1, if2 with

    | Formula [pret1], Formula cf2 -> Formula (pret1 :: cf2)
        
    | _ ->
      failwith "The first Presburger formula must be a singleton in combine_singleton_to_iformula."


(* Add up a list of polynomials which is in iformula type and return a
   polynomial. *)
let add_iformula_list (c: Var.t -> Var.t -> int) (ifl: iformula list) : poly =

  match ifl with

    (* Cannot add up an empty list *)
    | [] -> failwith "add_iformula_list can only add up polynomials."
      
    (* Singleton list is unchanged *)
    | [Poly pl] -> pl
      
    (* List of polynomials *)
    | (Poly pl) :: ifl' ->

      (* Add to the head polynomial the tail of the list of iformulas,
         which must be polynomials *)
      List.fold_left 
        (fun accum e ->
          (match accum, e with
            | pl1, (Poly pl2) -> add_two_polys c [] pl1 pl2
            | _ -> failwith "add_iformula_list can only add up polynomials.")) 
        pl 
        ifl'
        
    | _ ->
      failwith "add_iformula_list can only add up polynomials."
        

(* Multiply a list of polynomials which is in iformula type and return
   a polynomial *)
let multiply_iformula_list (ifl: iformula list) : poly = 

  match ifl with
    
    (* Cannot multiply an empty list *)
    | [] -> failwith "multiply_iformula_list doesn't take empty list."

    (* Singleton list is unchanged *)
    | [Poly pl] -> pl

    (* List of polynomials *)
    | (Poly pl) :: ifl' ->

      (* Multiply with the head polynomial the tail of the list of
         iformulas, which must be polynomials *)
      List.fold_left 
        (fun accum e ->
          match accum, e with
            | pl1, (Poly pl2) -> multiply_two_polys pl1 pl2
            | _ -> 
              failwith "multiply_iformula_list can only multiply polynomials.")
        pl 
        ifl'
        
    | _ ->
      failwith "multiply_iformula_list can only multiply polynomials." 

(* Convert equality, which may have arity greater than two, to a
   conjunction of binary equalities *)
let unchain_EQ_to_iformula (c: Var.t -> Var.t -> int) (ifl: iformula list) : iformula =

  match ifl with

    | _::[]
    | [] -> failwith "The chain of EQ must have at least two elements."

      
    | if1 :: ifl' ->
      
      (* Convert variadic equality to conjunction of binary equations *)
      snd
        (List.fold_left
           (* We remeber the previous polynomial and equate it to the
              current polynomial *)
           (fun (prev, accum) e ->
             (match prev, e with
                 
               (* iformula must be a polynomial *)
               | Poly pl1, Poly pl2 ->
                 
                 (* Remember current polynomial for the next step *)
                 (e, 

                  (* Create new equality of current and previous
                     polynomial and add to the accumulator *)
                  combine_singleton_to_iformula 
                    (Formula 
                       [EQ (add_two_polys c [] (negate_poly pl1) pl2)]) 
                    accum)
                   
               | _ ->
                 failwith "EQ can only work with list of polynomials"
             )
           ) 
           (if1, Formula []) 
           ifl'
        )

(* Convert less-than-or-equal realation, which may have arity greater
   than two, to a conjunction of binary greater-than relations *)
let unchain_LEQ_to_iformula (c: Var.t -> Var.t -> int) (ifl: iformula list) : iformula =
  
  match ifl with

    | _::[]
    | [] ->
      failwith "The chain of LEQ must have at least two elements."

    | if1 :: ifl' ->

      (* Convert variadic relation to conjunction of binary
         greater-than relations *)
      snd
        (List.fold_left
           (* We remeber the previous polynomial and equate it to the
              current polynomial *)
           (fun (prev, accum) e ->
             (match prev, e with
                 
               (* iformula must be a polynomial *)
               | Poly pl1, Poly pl2 ->
                 
                 (* Remember current polynomial for the next step *)
                 (e, 
                  
                  (* Turn x <= y into y - x + 1 > 0 *)
                  combine_singleton_to_iformula 
                    (Formula 
                       [GT 
                           (add_two_polys 
                              c 
                              [] 
                              (add_two_polys c [] (negate_poly pl1) pl2) 
                              [(Numeral.one, None)])]) 
                    accum)
                   
               | _ -> 
                 failwith "LEQ can only work with list of polynomials."
             )
           )
           (if1, Formula []) 
           ifl'
        )


(* Convert a list of presburger formulas chained by LT into an iformula. *)
let unchain_LT_to_iformula (c: Var.t -> Var.t -> int) (ifl: iformula list) : iformula =

  match ifl with
      
    | _::[]
    | [] ->
      failwith "The chain of LT must have at least two elements."
        
    | if1::ifl' ->

      (* Convert variadic relation to conjunction of binary
         greater-than relations *)
      snd
        (List.fold_left
           (* We remeber the previous polynomial and LT it to the
              current polynomial *)
           (fun (prev, accum) e ->
             (match prev, e with

               (* iformula must be a polynomial *)
               | Poly pl1, Poly pl2 ->
                 
                 (* Remember current polynomial for the next step *)
                 (e, 

                  (* Turn x < y into y - x > 0 *)
                  combine_singleton_to_iformula 
                    (Formula 
                       [GT (add_two_polys c [] (negate_poly pl1) pl2)]) accum)
                   
               | _ -> 
                 failwith "LT can only work with list of polynomials."
             )
           ) 

           (if1, Formula []) 
           ifl'
        )
        

(* Convert a list of presburger formulas chained by GEQ into an iformula. *)
let unchain_GEQ_to_iformula (c: Var.t -> Var.t -> int) (ifl: iformula list) : iformula =

  match ifl with

    | _::[]
    | [] ->
      failwith "The chain of GEQ must have at least two elements."

    | if1::ifl' ->

      (* Convert variadic relation to conjunction of binary
         greater-than relations *)
      snd
        (List.fold_left
           (* We remeber the previous polynomial and GEQ it to the
              current polynomial *)
           (fun (prev, accum) e ->
             (match prev, e with
               
               (* iformula must be a polynomial *)
               | Poly pl1, Poly pl2 ->

                 (* Remember current polynomial for the next step *)
                 (e, 

                  (* Turn x >= y into x - y + 1 > 0 *)
                  combine_singleton_to_iformula 
                    (Formula 
                       [GT 
                           (add_two_polys 
                              c 
                              [] 
                              (add_two_polys c [] pl1 (negate_poly pl2)) 
                              [(Numeral.one, None)])]) 
                    accum)
                   
               | _ -> 
                 failwith "GEQ can only work with list of polynomials."
             )
           ) 
           (if1, Formula []) 
           ifl'
        )


(* Convert a list of presburger formulas chained by GT into an iformula. *)
let unchain_GT_to_iformula (c: Var.t -> Var.t -> int) (ifl: iformula list) : iformula =
  
  match ifl with

    | _::[]
    | [] ->
      failwith "The chain of GT must have at least two elements."

    | if1::ifl' ->

      (* Convert variadic relation to conjunction of binary
         greater-than relations *)
      snd
        (List.fold_left
           (* We remeber the previous polynomial and GT it to the
              current polynomial *)
           (fun (prev, accum) e ->
             (match prev, e with
               | Poly pl1, Poly pl2 ->
                 
                 (* Remember current polynomial for the next step *)
                 (e, 
                  
                  (* Turn x > y into x - y > 0 *)
                  combine_singleton_to_iformula 
                    (Formula 
                       [GT (add_two_polys c [] pl1 (negate_poly pl2))]) accum)
                   
               | _ -> 
                 failwith "GT can only work with list of polynomials."
             )
      ) (if1, Formula []) ifl'
    )


(* Convert an presburger formula which only contains AND and NOT at
   the atom level into cformula. *)
let to_presburger (v: Var.t list) (gf: Term.t) : cformula =

  (* Comparison function to make variables to be eliminated smaller *)
  let c = compare_variables v in 

  let res =

    (* Bottom-up fold of given term *)
    Term.eval_t

      (fun fterm args ->

         match fterm with

           | Term.T.Attr _ -> assert false

     	   | Term.T.Var var ->
             Poly [(Numeral.one, Some var)]

           | Term.T.Const sym
           | Term.T.App (sym, _) ->
             (match Symbol.node_of_symbol sym, args with
               (* true becomes 1 > 0 *)
               | `TRUE, _ -> Formula [GT [(Numeral.one, None)]]

               (* false becomes -1 > 0 *)
               | `FALSE, _ -> Formula [GT [(Numeral.(neg one), None)]]

               (* not (p > 0) becomes (-p + 1 > 0) *)
               | `NOT, [Formula [GT pl]] ->
                 Formula [GT (add_two_polys c [] [(Numeral.one, None)] (negate_poly pl))]

               (* not (p = 0) becomes (p != 0) *)
               | `NOT, [Formula [EQ pl]] -> Formula [INEQ pl]

               (* not (p != 0) becomes (p = 0) *)
               | `NOT, [Formula [INEQ pl]] -> Formula [EQ pl]

               (* not (i | p) becomes (i !| p) *)
               | `NOT, [Formula [DIVISIBLE (i, pl)]] ->
                 Formula [INDIVISIBLE (i, pl)]

               (* not (i !| p) becomes (i | p) *)
               | `NOT, [Formula [INDIVISIBLE (i, pl)]] ->
                 Formula [DIVISIBLE (i, pl)]

               (* Fail on negations of other iformulas *)

               | `NOT, [Formula cf] ->
                 failwith "NOT only take one argument, and can only appear in the atom level."

               (* Fail on implication *)

               | `IMPLIES, _ ->
                 failwith "Presburger atoms may not conatin Boolean operators."

               (* Fail on empty conjunction *)
               | `AND, [] ->
                 failwith "AND must take at least one argument."

               (* Skip over singleton conjunction *)
               | `AND, [Formula cf] -> Formula cf

               (* Conjunction of arity greater than one *)
               | `AND, ifm :: l' ->

                 (* Turn a list of iformulas into one iformula *)
                 List.fold_left 
                   (fun ifm1 ifm2 ->

                      (match ifm1, ifm2 with

                        (* iformulas must not be polynomials *)
                        | (Formula cf1), (Formula cf2) ->

                          Formula (List.concat [cf1; cf2])

                        | _ ->
                          failwith "AND only takes formula as arguments, not polynomial."

                      )
                   ) 
                   ifm 
                   l'


               (* Fail on disjunction *)
               | `OR, _ -> 
                 failwith "Presburger atoms may not conatin Boolean operators."


               (* Fail on exclusive disjunction *)
               | `XOR, _ ->
                 failwith "Presburger atoms may not conatin Boolean operators."


               (* Turn equation into iformula *)
               | `EQ, ifl ->
                 unchain_EQ_to_iformula c ifl


               (* Fail on distinct *)
               | `DISTINCT, _ ->
                 failwith "Presburger atoms may not conatin Boolean operators."


               (* Fail on if-then-else *)
               | `ITE, _ ->
                 failwith "Presburger atoms may not conatin Boolean operators."


               (* Turn numeral into polynomial of constant *)
               | `NUMERAL i, _ ->
                 Poly [(i, None)]

               (* Fail on not integer numerals *)
               | `DECIMAL _, _ -> raise Not_in_LIA
                 

               (* Unary minus *)
               | `MINUS, [if1] ->

                 (match if1 with

                   (* Turn polynomial into its negation *)
                   | Poly pl1 -> Poly (negate_poly pl1)

                   | _ -> failwith "MINUS only takes polynomials."

                 )

               (* Difference of two or more arguments *)
               | `MINUS, if1 :: ifl ->

                 (match if1 with

                   | Poly pl1 ->

                     (* Negate second and following arguments and add to

                        first polynomial *)
                     Poly 
                       (add_two_polys 
                          c 
                          [] 
                          pl1 
                          (negate_poly (add_iformula_list c ifl)))


                   | _ -> failwith "MINUS only takes polynomials."

                 )


               (* Sum of one or more arguments *)
               | `PLUS, ifl -> Poly (add_iformula_list c ifl)

               (* Multiplication of one or more arguments *)

               | `TIMES, ifl -> Poly (multiply_iformula_list ifl)

               (* Variadic less-than-or-equal *)
               | `LEQ, ifl ->

                 unchain_LEQ_to_iformula c ifl

               (* Variadic less-than *)
               | `LT, ifl ->

                 unchain_LT_to_iformula c ifl

               (* Variadic greater-than-or-equal *)
               | `GEQ, ifl ->

                 unchain_GEQ_to_iformula c ifl

               (* Variadic greater-than *)
               | `GT, ifl ->

                 unchain_GT_to_iformula c ifl

               (* Fail on real division *)
               | `DIV, _ -> raise Not_in_LIA

               (* Fail on integer division *)
               | `INTDIV, _ -> raise Not_in_LIA

               (* Fail on modulus *)
               | `MOD, _ -> raise Not_in_LIA

               (* Fail on absolute value *)
               | `ABS, _ -> raise Not_in_LIA

               (* Fail on conversion to real *)
               | `TO_REAL, _ -> raise Not_in_LIA

               (* Fail on conversion to integer *)
               | `TO_INT, _ -> raise Not_in_LIA

               (* Fail on conversion to unsigned integer8 *)
               | `TO_UINT8, _ -> raise Not_in_LIA

               (* Fail on conversion to unsigned integer16 *)
               | `TO_UINT16, _ -> raise Not_in_LIA

               (* Fail on conversion to unsigned integer32 *)
               | `TO_UINT32, _ -> raise Not_in_LIA

               (* Fail on conversion to unsigned integer64 *)
               | `TO_UINT64, _ -> raise Not_in_LIA

               (* Fail on conversion to integer8 *)
               | `TO_INT8, _ -> raise Not_in_LIA

               (* Fail on conversion to integer16 *)
               | `TO_INT16, _ -> raise Not_in_LIA

               (* Fail on conversion to integer32 *)
               | `TO_INT32, _ -> raise Not_in_LIA

               (* Fail on conversion to integer64 *)
               | `TO_INT64, _ -> raise Not_in_LIA

               (* Fail on coincidence with integer predicate *)
               | `IS_INT, _ -> raise Not_in_LIA

               (* Add uninterpreted function to polynomial as variable with
                  coefficient one *)
               | `UF s, ags -> raise Not_in_LIA

               (* Turn divisibility predicate into an iformula *)
               | `DIVISIBLE i, [Poly pl] ->
                 Formula [DIVISIBLE (i, pl)]

               | `NOT, _
               | `MINUS, _
               | `DIVISIBLE _, _

               | `BVNEG, _
               | `BVADD, _ 

               | `UBV _, _
               | `BV _, _ 
               | `BVMUL, _
               | `BVSHL, _
               | `BVUDIV, _
               | `BVNOT, _
               | `BVUREM, _
               | `BVOR, _
               | `BVLSHR, _
               | `BVAND, _

               | `SELECT _, _
               | `STORE, _


               | `BVULT, _
               | `BVULE, _
               | `BVUGT, _
               | `BVUGE, _ 
               -> raise Not_in_LIA

             )
      )
      gf
  in

  (* We must have a formula, not a polynomial at the end of the conversion *)
  match res with 
    | Poly _ -> failwith "open polynomial"
    | Formula f -> f


(* Convert a summand to a term *)
let term_of_psummand = function 

  (* Monomial contains a variable *)
  | (c, Some v) -> Term.mk_times [Term.mk_num c; Term.mk_var v]
  
  (* Monomial is a constant *)
  | (c, None) -> Term.mk_num c


(* Convert a polynomial to a term *)
let term_of_poly = function

  (* Empty polynomial *)
  | [] -> Term.mk_num Numeral.zero

  (* Singleton polynomial *)
  | [smd] -> term_of_psummand smd

  (* Polynomial with at least two monomials *)
  | l -> Term.mk_plus (List.map term_of_psummand l)


(* Convert a presburger atom to a term *)
let term_of_preAtom = function

  (* Polynomial greater than zero *)
  | GT poly -> 
    
    (match poly with 

      (* 0 > 0 becomes false *)
      | [] -> Term.mk_false ()

      | _ -> Term.mk_gt [(term_of_poly poly); Term.mk_num Numeral.zero]
        
    )

  (* Polynomial equal to zero *)
  | EQ poly -> 

    (match poly with 
      
      (* 0 = 0 becomes true *)
      | [] -> Term.mk_true ()

      | _ -> Term.mk_eq [(term_of_poly poly); Term.mk_num_of_int 0]
    )
      
  (* Polynomial not equal to zero *)
  | INEQ poly -> 

    (match poly with 
      
      (* 0 != 0 becomes false *)
      | [] -> Term.mk_false ()

      | _ -> 

        Term.mk_not (Term.mk_eq [(term_of_poly poly); Term.mk_num_of_int 0])

    )

  (* Polynomial divisible by constant *)
  | DIVISIBLE (i, poly) -> 
    
    (match poly with 

      (* i | 0 becomes true *)
      | [] -> Term.mk_true ()

      | _ -> 

        Term.mk_divisible i (term_of_poly poly)

    )

  (* Polynomial not divisible by constant *)
  | INDIVISIBLE (i, poly) ->
    
    (match poly with 

      (* i !| 0 becomes false *)
      | [] -> Term.mk_false ()

      | _ -> 

        Term.mk_not
          (Term.mk_divisible i (term_of_poly poly))

    )
          
      
(* Convert a presburger formula to a term *)
let term_of_cformula l = List.map term_of_preAtom l

(*
function
  
  (* Empty conjunction *)
  | [] -> Term.mk_true ()

  (* Singleton conjunction *)
  | [pret] -> term_of_preAtom pret

  (* Conjunction of more than one atom *)
  | l -> Term.mk_and (List.map term_of_preAtom l)
*)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
