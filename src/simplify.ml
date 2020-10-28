(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015-2017 by the Board of Trustees of the University of Iowa

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

let division_by_zero = ref false

(** Returns true iff a division by zero happened in a simplification since
    this function was last called. *)
let has_division_by_zero_happened () =
  let res = !division_by_zero in
  division_by_zero := false ;
  res

(* ********************************************************************** *)
(* Basic types                                                            *)
(* ********************************************************************** *)

(* A monomial is a non-empty ordered list of terms which are not
   polynomials to be multiplied with a constant coefficient, the
   ordering is by comparison of terms. *)
type 'a monomial = 'a * Term.t list

(* A polyomial is a constant (possibly zero) and a (possibly empty)
   orderd list of monomials to be summed up. Each monomial term occurs
   exactly once, the ordering is by lexicographic comparison of
   terms. *)
type 'a polynomial = 'a * 'a monomial list 


(* Normal forms for terms: integer and real terms are polynomials
   where all terms which are not addition or multiplication are
   abstracted to fresh variables in monomials. Boolean terms are in
   negation normal form and contain only conjunctions,
   disjunctions and negations. *)
type t = 
  | Num of Numeral.t polynomial
  | Dec of Decimal.t polynomial
  | Bool of Term.t 
  | Array of Term.t 
  | BV of Term.t

let pp_print_monomial pp ppf ((c, t) : 'a monomial) = 
  Format.fprintf 
    ppf
    "%a * %a"
    pp c
    (pp_print_list Term.pp_print_term "@ *") t

let pp_print_polynomial pp ppf (c, p) = 
  Format.fprintf ppf
    "%a + %a"
    pp c
    (pp_print_list (pp_print_monomial pp) "@ +")
    p
  

let pp_print_int_polynomial = pp_print_polynomial Numeral.pp_print_numeral

let pp_print_dec_polynomial = pp_print_polynomial Decimal.pp_print_decimal



(* ********************************************************************** *)
(* Conversions from normal forms to terms                                 *)
(* ********************************************************************** *)

(* Convert a list of monomials to a list of terms

   This function is polymorphic in the type of the monomial, hence we
   need constructors and predicates. *)
let term_list_of_monomial_list is_zero is_one mk_zero mk_const l = 

  (* Tail-recursive function with accumulator *)
  let rec term_list_of_monomial_list' accum = function 
    
    (* Base case: reverse accumulator to preserve original order *)
    | [] -> List.rev accum
              
    (* Take monomial at head of list *)
    | (c, v) :: tl -> 
      
      (* Convert monomial to the term (c * v) *)
      let t = 
        
        if is_one c then 
          
          (* Omit factor one *)
          Term.mk_times v 
            
        else 
          
        if is_zero c then 
          
          (* Return zero for coeffcient zero *)
          mk_zero ()
            
        else
          
          (* Return product of coefficient and monomials *)
          Term.mk_times ((mk_const c) :: v)

      in

      (* Recurse for tail of list *)
      term_list_of_monomial_list' (t :: accum) tl

  in

  (* Call recursive function with initial value for accumulator *)
  term_list_of_monomial_list' [] l


(* Convert a polynomial to a term

   This function is polymorphic in the type of the monomial, hence we
   need constructors and predicates. *)
let term_of_polynomial is_zero is_one mk_zero mk_const = function 

  (* Polynomial has constant zero and an empty list of monomials *)
  | (c, []) when is_zero c -> mk_zero ()

  (* Polynomial has constant zero and a non-empty list of monomials *)
  | (c, l) when is_zero c -> 

    (* Convert polynomial to the term (c1 * v1) + ... + (cn * vn) *)
    Term.mk_plus 
      (term_list_of_monomial_list is_zero is_one mk_zero mk_const l)

  (* Polynomial has a non-zero constant and an empty list of
     monomials *)
  | (c, []) -> mk_const c

  (* Polynomial has a non-zero constant and a non-empty list of
     monomials *)
  | (c, l) -> 

    (* Convert polynomial to the term (c + (c1 * v1) + ... + (cn * vn)) *)
    Term.mk_plus 
      (mk_const c :: 
         term_list_of_monomial_list is_zero is_one mk_zero mk_const l)


(* Convert an integer polynomial to a term *)
let term_of_num_polynomial = 
  term_of_polynomial 
    (Numeral.equal Numeral.zero)
    (Numeral.equal Numeral.one)
    (function () -> Term.mk_num Numeral.zero)
    Term.mk_num


(* Convert a real polynomial to a term *)
let term_of_dec_polynomial = 
  term_of_polynomial 
    (Decimal.equal Decimal.zero)
    (Decimal.equal Decimal.one) 
    (function () -> Term.mk_dec Decimal.zero)
    Term.mk_dec


(* Convert a normal form to a term *)
let term_of_nf = function 
  | Num p -> term_of_num_polynomial p
  | Dec p -> term_of_dec_polynomial p
  | Bool b -> b
  | Array b -> b
  | BV b -> b


(* ********************************************************************** *)
(* Conversions from normal forms                                          *)
(* ********************************************************************** *)


(* Return the integer polynomial in an integer normal form *)
let num_polynomial_of_nf = function 
  | Num p -> p
  | _ -> assert false


(* Return the real polynomial in a real normal form *)
let dec_polynomial_of_nf = function 
  | Dec p -> p
  | _ -> assert false


(* Return the term in a Boolean normal form *)
let bool_of_nf = function
  | Bool b -> b
  | _ -> assert false


(* ********************************************************************** *)
(* Variable-free normal forms                                             *)
(* ********************************************************************** *)


(* Return true if normal form is variable-free *)
let is_constant = function 
  | Num (_, [])
  | Dec (_, [])  -> true
  | Bool b when b == Term.t_true || b == Term.t_false -> true
  | BV _ -> false (* Technically, this isn't right, but it doesn't 
  matter in the contexts in which this function is called *)
  | Num _ | Dec _ | Bool _ | Array _ -> false


(* Return true if value is variable-free *)
let is_constant_polynomial = function 
  | (_, []) -> true
  | _ -> false
    

(* Return the constant of a polynomial *)
let const_of_polynomial = function (c, _) -> c


(* Return the constant of an integer polynomial *)
let const_of_num_polynomial = function 
  | Num p -> const_of_polynomial p
  | _ -> assert false 


(* Return the constant of a real polynomial *)
let const_of_dec_polynomial = function 
  | Dec p -> const_of_polynomial p
  | Num p -> const_of_polynomial p |> Numeral.to_big_int  |> Decimal.of_big_int 
  | _ -> assert false 

(* ********************************************************************** *)
(* Arithmetic functions on polynomials (polymorphic)                      *)
(* ********************************************************************** *)


(* Compare monomials by comparing their terms *)
let compare_monomials (_, t1) (_, t2) = compare_lists Term.compare t1 t2 


(* Add two lists of sorted monomials *)
let add_monomial_lists add is_zero l1 l2 = 

  (* Tail-recursive function with accumulator *)
  let rec add_monomial_lists' accum l1 l2 = match l1, l2 with 

    (* Base case: one of the lists is empty *)
    | _, [] -> List.rev_append accum l1
    | [], _ -> List.rev_append accum l2

    (* Terms are equal: add coefficients *)
    | (c1, t1) :: tl1, (c2, t2) :: tl2 
      when 
        List.length t1 = List.length t2 &&
        List.for_all2 Term.equal t1 t2 -> 

      (* Add coefficients *)
      let c' = add c1 c2 in

      (* Check sum of coefficients *)
      if is_zero c' then 
        
        (* Remove monomial if the coefficient vanishes *)
        add_monomial_lists' accum tl1 tl2 

      else

        (* Add coefficients of two monomials with equal terms *)
        add_monomial_lists' ((add c1 c2, t1) :: accum) tl1 tl2 

    (* First term is smaller: add to accumulator first *)
    | (c1, t1) :: tl1, (_, t2) :: _ 
      when 
        compare_lists Term.compare t1 t2 < 0 -> 

      add_monomial_lists' ((c1, t1) :: accum) tl1 l2 

    (* Second term is smaller: add to accumulator first *)
    | (_, t1) :: _, (c2, t2) :: tl2 -> 

      add_monomial_lists' ((c2, t2) :: accum) l1 tl2 

  in

  (* Call recursive function with initial value for accumulator *)
  add_monomial_lists' [] l1 l2 


(* Sum up a list of polynomials *)
let add_polynomials add zero is_zero p = 

  (* Split off coefficients of polynomials *)
  let c, m = List.split p in

  (* Sum up coefficients *)
  let c' = List.fold_left add zero c in
            
  (* Add lists of monomials *)
  let m' = List.fold_left (add_monomial_lists add is_zero) [] m in
  
  (* Return merged polynomials *)
  (c', m')


(* Multiply each monomial in the list with a constant *)
let const_multiply_monomial_list mult d m = 
  List.map (function (c, t) -> (mult c d, t)) m


(* Multiply a polynomial with a constant *)
let const_multiply_polynomial mult d (c, m) = 
  (mult d c, const_multiply_monomial_list mult d m)


(* Multiply each monomial in the list with negative one *)
let negate_monomial_list mult minus_one m = 
  const_multiply_monomial_list mult minus_one m


(* Multiply polynomial with negative one *)
let negate_polynomial mult minus_one p = 
  const_multiply_polynomial mult minus_one p


(* Multiply two lists of monomials *)
let multiply_monomial_lists mult l1 l2 = 

  (* Tail-recursive function with accumulator

     multiply_monomial_lists' l2 a m1 i2 i1

     folds over i2, multiplies each monomial with m1 and adds the
     result to the accumulator a. If i1 is not empty, take its head
     element as new m1 and repeat folding over l2.

     If l2 is empty, an empty list is returned. In the inital call i2
     must be equal to l2. *)
  let rec multiply_monomial_lists' l2 accum (c1, t1) = function 

    (* One iteration over l2 finished *)
    | [] -> 

      (function  

        (* No more elements left in l1: Return a sorted list of
           monomials *)
        | [] -> List.sort compare_monomials accum

        (* Take next element of l1 and multiply it with all elements
           of l2 *)
        | h :: tl1 -> multiply_monomial_lists' l2 accum h l2 tl1)

    (* Take head element of l2 *)
    | (c2, t2) :: tl2 -> 

      (* Pass through tail of l1 *)
      (function tl1 -> 

        (* Merge two sorted lists of terms as a new monomial *)
        let t' = List.merge Term.compare t1 t2 in 
             
        (* Continue merging tail of l2 with current head of l1 *)
        multiply_monomial_lists' 
          l2
          ((mult c1 c2, t') :: accum)
          (c1, t1)
          tl2
          tl1)

  in
  
  match l1, l2 with 
    
    (* Catch special cases of l1 or l2 empty *)
    | [], _ -> []
    | _, [] -> [] 

    (* Multiply two lists of monomials *)
    | h :: tl1, _ -> multiply_monomial_lists' l2 [] h l2 tl1
  

(* Multiply two polynomials *)
let multiply_polynomials mult is_zero zero (c1, m1) (c2, m2) = 

  (* Return polynomial as
     ((ax + c) * (bx + d)) = (abxy + adx + bcx + cd) *)
  let m' = 
    List.sort 
      compare_monomials
      (multiply_monomial_lists mult m1 m2 @ 
         const_multiply_monomial_list mult c2 m1 @ 
         const_multiply_monomial_list mult c1 m2)
  in

  (mult c1 c2, m')


(* Subtract second polynomial from first and normalize so that either
   the constant or the first coefficient of the polynomial is greater
   than zero 

   Return the sign of the factor, [true] for positive and [false] for
   negative together with the normalized result *)
let subtract_and_normalize_polynomials
    add_polynomials negate_polynomial zero is_zero lt_zero p q =

  (* Subtract second polynomial from first *)
  let r = add_polynomials [p; negate_polynomial q] in

  (* Normalize so that either the constant or the first coefficient of
     the polynomial is greater than zero *)
  match r with 

    (* Polynomial is the constanst zero *)
    | (c, []) when is_zero c -> true, r

    (* Constant is zero, first coefficient is negative *)
    | (c, (h, _) :: tl) when is_zero c && lt_zero h -> false, negate_polynomial r

    (* Constant is zero, first coefficient is not negative *)
    | (c, (h, _) :: tl) when is_zero c -> true, r

    (* Constant is not zero and negative *)
    | (c, _) when lt_zero c -> false, negate_polynomial r

    (* Constant is not zero and positive *)
    | (c, _) -> true, r


(* ********************************************************************** *)
(* Integer arithmetic functions on polynomials                            *)
(* ********************************************************************** *)


let add_num_monomial_lists = add_monomial_lists Numeral.(+) (Numeral.equal Numeral.zero)

let add_num_polynomials = add_polynomials Numeral.(+) Numeral.zero (Numeral.equal Numeral.zero)

let const_multiply_num_monomial_list = const_multiply_monomial_list Numeral.( * )

let const_multiply_num_polynomial = const_multiply_polynomial Numeral.( * )

let negate_num_monomial_list = negate_monomial_list Numeral.( * ) (Numeral.neg Numeral.one)

let negate_num_polynomial = negate_polynomial Numeral.( * ) (Numeral.neg Numeral.one)

let multiply_num_polynomials = 
  multiply_polynomials Numeral.( * ) (Numeral.equal Numeral.zero) Numeral.zero

let subtract_and_normalize_num_polynomials = 
  subtract_and_normalize_polynomials 
    add_num_polynomials 
    negate_num_polynomial 
    Numeral.zero
    (Numeral.equal Numeral.zero)
    (Numeral.gt Numeral.zero)

(* ********************************************************************** *)
(* Real arithmetic functions on polynomials                               *)
(* ********************************************************************** *)


let add_dec_monomial_lists = add_monomial_lists Decimal.(+) (Decimal.equal Decimal.zero)

let add_dec_polynomials = add_polynomials Decimal.(+) Decimal.zero (Decimal.equal Decimal.zero)

let const_multiply_dec_monomial_list = const_multiply_monomial_list Decimal.( * )

let const_multiply_dec_polynomial = const_multiply_polynomial Decimal.( * )

let negate_dec_monomial_list = negate_monomial_list Decimal.( * ) (Decimal.neg Decimal.one)

let negate_dec_polynomial = negate_polynomial Decimal.( * ) (Decimal.neg Decimal.one)

let multiply_dec_polynomials = 
  multiply_polynomials Decimal.( * ) (Decimal.equal Decimal.zero) Decimal.zero

let subtract_and_normalize_dec_polynomials = 
  subtract_and_normalize_polynomials 
    add_dec_polynomials 
    negate_dec_polynomial 
    Decimal.zero
    (Decimal.equal Decimal.zero) 
    (Decimal.gt Decimal.zero) 

(* ********************************************************************** *)
(* Functions used in {!simplify_term_node}                                *)
(* ********************************************************************** *)


(* Sum up a list of integer polynomials *)
let add_num args = 

  let args' = List.map num_polynomial_of_nf args in

  add_num_polynomials args'


(* Sum up a list of real polynomials *)
let add_dec args = 

  let args' = List.map dec_polynomial_of_nf args in

  add_dec_polynomials args'


(* Multiply two integer polynomials *)
let multiply_num p1 p2 = 

  let p1', p2' = num_polynomial_of_nf p1, num_polynomial_of_nf p2 in

  multiply_num_polynomials p1' p2'


(* Multiply two real polynomials *)
let multiply_dec p1 p2 = 

  let p1', p2' = dec_polynomial_of_nf p1, dec_polynomial_of_nf p2 in

  multiply_dec_polynomials p1' p2'


(* Sum up a list of real or integer normal forms *)
let add = function

  (* Addition is not nullary  *)
  | [] -> assert false 
    
  (* Add as integer polynomials if head of list is integer *)
  | Num _ :: _ as args -> Num (add_num args)
                    
  (* Add as real polynomials if head of list is real *)
  | Dec _ :: _ as args -> Dec (add_dec args)

  (* Cannot add other types *)
  | _ -> assert false


(* Subtract a list of polynomials *)
let minus = function 

  (* Subtraction is not nullary  *)
  | [] -> assert false 

  (* Unary integer minus: negate polynomial to (- c - p) *)
  | [Num p] -> Num (negate_num_polynomial p)

  (* Unary real minus: negate polynomial to (- c - p) *)
  | [Dec p] -> Dec (negate_dec_polynomial p)

  (* Binary integer minus or higher arity: (h - s1 - ... - sn) reduce
     to (h - (s1 + ... + sn) *)
  | Num p :: tl -> 

    Num (add_num_polynomials [p; negate_num_polynomial (add_num tl)])

  (* Binary real minus or higher arity: (h - s1 - ... - sn) reduce to
     (h - (s1 + ... + sn) *)
  | Dec p :: tl -> 

    Dec (add_dec_polynomials [p; negate_dec_polynomial (add_dec tl)])

  (* Cannot subtract other types *)
  | _ -> assert false


(* Multiply a list of polynomials *)
let times = function 

  (* Multiplication is not nullary  *)
  | [] -> assert false 
    
  (* Multiply as integer polynomials if head of list is integer *)
  | Num p :: tl -> 
    
    Num 
      (List.fold_left 
         multiply_num_polynomials 
         p 
         (List.map num_polynomial_of_nf tl))
                    
  (* Multiply as real polynomials if head of list is real *)
  | Dec p :: tl -> 

    Dec
      (List.fold_left 
         multiply_dec_polynomials 
         p 
         (List.map dec_polynomial_of_nf tl))
                     
  (* Cannot multiply other types *)
  | _ -> assert false


(* Flatten nested associative Boolean operators by lifting the
   subterms of a nested operator as subterms of the top operator: 
   (a & (b & c)) becomes (a & b & c)

   The arguments must be Boolean, real and integer terms are
   normalized to polynomials. *)
let flatten_bool_subterms s l = 

  (* Tail-recursive function with accumulator *)
  let rec flatten_bool_subterms' symbol accum = function 

    (* No more subterms, return accumulator in original order *)
    | [] -> List.rev accum

    (* Boolean operator *)
    | Bool t :: tl -> 

      let accum' =
        
        (* Get symbol of term *)
        match Term.destruct t with

          (* Symbol is the same as the top-level symbol? *)
          | Term.T.App (s, l) when s == symbol -> 

            (* Add subterms of term in reverse order to subterms of
               top term *)
            List.rev_append l accum 

          (* Keep term unchanged *)
          | _ -> t :: accum

      in

      (* Recurse for remaining subterms *)
      flatten_bool_subterms' symbol accum' tl

    (* Fail on non-boolean arguments *)
    | (Num _ | Dec _ | Array _ | BV _ ) :: _ -> assert false

  in

  (* Call tail-recursive function with initial accumulator *)
  flatten_bool_subterms' s [] l 


(* Return true if a complement of a term in the second list is in the
   first list *)
let rec has_complement l = function 
  | [] -> false 
  | h :: tl -> 
    if List.memq (Term.negate h) l then true else has_complement l tl


(* Negate a term in negation normal form

   The term must only contain conjunctions and disjunctions as Boolean
   operators, the argument of a Boolean negation must be an atom. *)
let rec negate_nnf term = match Term.destruct term with 

  (* Negate a variable *)
  | Term.T.Var v -> Term.mk_not (Term.mk_var v)

  (* Negate a constant *)
  | Term.T.Const s ->

    (* Unhashcons constant symbol *)
    (match Symbol.node_of_symbol s with 

      | `TRUE -> Term.t_false
      | `FALSE -> Term.t_true
      | `UF u -> Term.mk_not (Term.mk_uf u [])
      | _ -> assert false

    )

  (* Negate a function application *)
  | Term.T.App (s, l) -> 

    (* Unhashcons constant symbol *)
    (match Symbol.node_of_symbol s, l with 

      (* Double unary negation *)
      | `NOT, [a] -> a

      (* Negation must be unary *)
      | `NOT, _ -> assert false 

      (* Conjunction *)
      | `AND, l -> 
        Term.mk_or (List.map (function t -> negate_nnf t) l)

      (* Disjunction *)
      | `OR, l -> 
        Term.mk_and (List.map (function t -> negate_nnf t) l)

      (* Disjunction and conjunction are the only Boolean operators *)
      | `IMPLIES, _
      | `XOR, _ -> assert false

      (* Boolean equivalence must not occur *)
      | `EQ, [] -> assert false 

      | `EQ, h :: _ 
        when 
          Term.type_of_term h == Type.t_bool -> 
        assert false 

      (* Negate atoms *)
      | `EQ, _ 
      | `DISTINCT, _
      | `LEQ, _
      | `LT, _
      | `GEQ, _
      | `GT, _
      | `IS_INT, _
      | `DIVISIBLE _, _
      | `UF _, _
      | `SELECT _, _
      | `STORE, _ -> Term.mk_not term

      (* Negate both cases of ite term *)
      | `ITE, [p; l; r] -> 
        Term.mk_ite 
          p
          (negate_nnf l)
          (negate_nnf r)

      (* Non-ternary ite *)
      | `ITE, _ -> assert false

      (* Constant symbols *)
      | `FALSE, _
      | `TRUE, _
      | `NUMERAL _, _
      | `DECIMAL _, _ 
      | `UBV _, _
      | `BV _, _ -> assert false

      (* Can only negate Boolean terms *)
      | `MINUS, _
      | `PLUS, _
      | `TIMES, _
      | `DIV, _
      | `INTDIV, _
      | `MOD, _
      | `ABS, _
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

      | `BVNEG, _
      | `BVADD, _
      | `BVSUB, _
      | `BVMUL, _
      | `BVUDIV, _
      | `BVSDIV, _
      | `BVUREM, _
      | `BVSREM, _
      | `BVUDIV_I, _
      | `BVSDIV_I, _
      | `BVUREM_I, _
      | `BVSREM_I, _
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
      | `BVSGE, _
      | `BVNOT, _
      | `BVOR, _ 
      | `BVAND, _
      | `BVEXTRACT _, _ 
      | `BVCONCAT, _ 
      | `BVSIGNEXT _ , _ -> assert false 
    )    

  (* | Term.T.Attr (t, _) -> t *)


(* Negate all but the last term *)
let implies_to_or args = 

  (* Tail-recursive function with accumulator *)
  let rec implies_to_or' accum = function 
    | [] -> assert false
    | [a] -> List.rev (a :: accum)
    | Bool h :: tl -> implies_to_or' (Bool (negate_nnf h) :: accum) tl
    | (Num _ | Dec _ | Array _ | BV _ ) :: _ -> assert false
  in

  implies_to_or' [] args 


(* Subtract two normal forms and make constant or first coefficient
   positive *)
let subtract_and_normalize a b = match a, b with 

  (* Two integer polynomials *)
  | Num a, Num b -> 
    let s, r = subtract_and_normalize_num_polynomials a b in s, Num r

  (* Two real polynomials *)
  | Dec a, Dec b -> 
    let s, r = subtract_and_normalize_dec_polynomials a b in s, Dec r

  (* Cannot subtract *)
  | _ -> assert false

let relation_to_nf_bv rel = function
  (* Relation must be binary *)
  | [] 
  | [_] -> assert false

  (* Binary relation *)
  | [a; b] -> (match (rel 
                        (Term.bitvector_of_term (term_of_nf a)) 
                        (Term.bitvector_of_term (term_of_nf b))) 
               with
    | true -> Bool Term.t_true
    | false -> Bool Term.t_false)
  
  (* Arity greater than 2 *)
  | _ -> assert false

(* Normalize an n-ary relation by unchaining it into a conjunction of
   binary relations, subtracting the right-hand side from the
   left-hand side and evaluating to true or false if possible

   When normalizing, we might multiply with a negative factor and then
   need to replace the relation symbol by its converse. Hence we need
   to know the converse of the relation (primed parameters). *)
let rec relation_to_nf 
    simplify_term_node 
    rel 
    rel'
    mk_rel 
    mk_rel' 
    zero 
    t_zero = function

  (* Relation must be at least binary *)
  | [] 
  | [_] -> assert false

  (* Binary relation *)
  | [a; b] -> 

    (* Both polynomials are constant? *)
    if is_constant a && is_constant b then 

      (* Check if constants are in the relation *)
      Bool (Term.mk_bool (rel a b))

    else

      (* Subtract polynomials and make constant or first coefficient
         greater than zero and get the sign of the factor *)
      let s, a' = subtract_and_normalize a b in

      (* Polynomial has become constant, i.e. (a = a) -> (0 = 0) *)
      if is_constant a' then

        (* Return true if constant is in the relation with zero,
           otherwise false

           Use converse of relation if factor in normalization is
           negative *)
        Bool 
          (Term.mk_bool ((if s then rel else rel') a' zero))

      else

        (* Simplify (a = b) to (a - b = 0) 

           Use converse of relation if factor in normalization is
           negative *)
        Bool 
          ((if s then mk_rel else mk_rel') [term_of_nf a'; t_zero])

  (* Higher arity equation *)
  | args -> 

    (* Convert list of n elements [e_1; ...; en] to list [[e_1; e_2];
       ...; [e_n-1; e_n]] *)
    let args_chain = chain_list args in 

    (* Simplify each binary equation *)
    let args' = 
      List.map 
        (relation_to_nf simplify_term_node rel rel' mk_rel mk_rel' zero t_zero) 
        args_chain
    in

    (* Simplify conjunction of binary equations *)
    Bool
      (bool_of_nf
         (simplify_term_node
            (Term.destruct 
               (Term.mk_and (List.map term_of_nf args')))
            args'))


(* Normalize an n-ary relation by unchaining *)
let relation 
    simplify_term_node 
    rel_num
    rel'_num
    rel_dec
    rel'_dec
    rel_ubv
    rel_bv
    mk_rel 
    mk_rel' = 
  
  function

    (* Relation must be at least binary *)
    | [] 
    | [_] -> assert false

    (* Relation between integers *)
    | Num _ :: _ as args ->

      (* Compute relation between constant integer polynomials *)
      let irel p q = 
        rel_num (const_of_num_polynomial p) (const_of_num_polynomial q) 
      in

      (* Compute converse of relation between constant integer
         polynomials *)
      let irel' p q = 
        rel'_num (const_of_num_polynomial p) (const_of_num_polynomial q) 
      in

      (* Normalize relation *)
      relation_to_nf 
        simplify_term_node 
        irel 
        irel'
        mk_rel 
        mk_rel' 
        (Num (Numeral.zero, [])) 
        (Term.mk_num Numeral.zero)
        args

    (* Relation between reals *)
    | Dec _ :: _ as args -> 

      (* Compute relation between constant real polynomials *)
      let rrel p q = 
        rel_dec (const_of_dec_polynomial p) (const_of_dec_polynomial q) 
      in

      (* Compute converse of relation between constant real
         polynomials *)
      let rrel' p q = 
        rel'_dec (const_of_dec_polynomial p) (const_of_dec_polynomial q) 
      in

      (* Normalize relation *)
      relation_to_nf 
        simplify_term_node 
        rrel 
        rrel' 
        mk_rel 
        mk_rel' 
        (Dec (Decimal.zero, [])) 
        (Term.mk_dec Decimal.zero)
        args

    (* Relation must be between integers or reals *)

    | BV _ :: _ as args -> relation_to_nf_bv rel_bv args

    | (Bool _ | Array _ ) :: _ -> assert false


(* Normalize equality relation between normal forms *)
let relation_eq simplify_term_node args = 

  relation 
    simplify_term_node 
    Numeral.(=)
    Numeral.(=) 
    Decimal.(=)
    Decimal.(=)
    Bitvector.(=)
    Bitvector.(=)
    Term.mk_eq 
    Term.mk_eq args


(* Normalize less than or equal relation between normal forms *)
let relation_leq simplify_term_node = 

  relation 
    simplify_term_node
    Numeral.(<=)
    Numeral.(>=)
    Decimal.(<=)
    Decimal.(>=)
    Bitvector.ulte
    Bitvector.(<=)
    Term.mk_leq 
    Term.mk_geq 
    


(* Normalize less than relation between normal forms *)
let relation_lt simplify_term_node = 

  relation 
    simplify_term_node
    Numeral.(<)
    Numeral.(>)
    Decimal.(<)
    Decimal.(>)
    Bitvector.lt
    Bitvector.(<)
    Term.mk_lt 
    Term.mk_gt
    


(* Normalize greater than or equal relation between normal forms *)
let relation_geq simplify_term_node = 

  relation 
    simplify_term_node 
    Numeral.(>=)
    Numeral.(<=) 
    Decimal.(>=)
    Decimal.(<=)
    Bitvector.ugte 
    Bitvector.(>=)
    Term.mk_geq 
    Term.mk_leq


(* Normalize greater than relation between normal forms *)
let relation_gt simplify_term_node = 
  
  relation 
    simplify_term_node
    Numeral.(>)
    Numeral.(<)
    Decimal.(>)
    Decimal.(<)
    Bitvector.ugt
    Bitvector.(>)
    Term.mk_gt 
    Term.mk_lt
    


(* Create an atom of the given term (a variable or an uninterpreted
   function) *)
let atom_of_term t = 

  (* Get type of term *)
  let tt = Term.type_of_term t in 

  (* Term is of type integer *)
  if Type.is_int tt || Type.is_int_range tt || Type.is_enum tt then

    (* Integer polynomial for a variable is (0 + 1 * x) *)
    Num (Numeral.zero, [Numeral.one, [t]])

  (* Term is of type real *)
  else if Type.is_real tt then

    (* Real polynomial for a variable is (0 + 1 * x) *)
    Dec (Decimal.zero, [Decimal.one, [t]])

  (* Term is of type Boolean *)
  else if Type.is_bool tt then

    (* Variable is an atom *)
    Bool t

  else if Type.is_array tt then

    Array t

  (* Term is of type signed or unsigned bitvector *)
  else if (Type.is_bitvector tt || Type.is_ubitvector tt) then

    BV t

  (* Term is of some other type  *)
  else (

    (* Not implemented *)
    assert false )


let select simplify_term_node default_of_var uf_defs model fterm = function

  (* Arguments are array and index *)
  | [a; i] ->

    (* Rebuild select operation with simplified index *)
    let term' = Term.mk_select (term_of_nf a) (term_of_nf i) in

    if

      (* Result of select operation is of array type? *)
      Type.is_array
        (Term.type_of_term (Term.construct fterm))

    then

      (

        (* Rebuild term with simplified index to evaluate
           later *)
        atom_of_term term'

      )

    (* Select operation evaluates to a non-array type *)
    else

      (* Get variable and indexes *)
      let v, i' =
        Term.indexes_and_var_of_select term'
      in

      (* Get assignment to variable *)
      (try match Var.VarHashtbl.find model v with

        (* Variable must evaluate to a lambda abstraction *)
        | Model.Lambda l ->

          (* Evaluate lambda abstraction with simplified
             indexes *)
          Term.eval_t
            (simplify_term_node default_of_var uf_defs model)
            (Term.eval_lambda l i')

        (* or map *)
        | Model.Map m ->

          if Model.MIL.is_empty m then
            List.fold_left
              Term.mk_select (Term.mk_var v) ((* List.rev *) i')
            |> atom_of_term

          else

            let args = List.map (fun x ->
                Term.numeral_of_term x |> Numeral.to_int) i' in

            let value =
              try Model.MIL.find args m
              with Not_found ->
                TermLib.default_of_type
                  (Type.last_elem_type_of_array
                     (Var.type_of_var v))
            in

            (* Evaluate map with simplified indexes *)
            Term.eval_t
              (simplify_term_node default_of_var uf_defs model)
              value

        (* Variable must not evaluate to a term *)
        | Model.Term _ -> assert false

       (* Free variable without assignment in model *)
       with Not_found ->

          let t' =
            List.fold_left
              Term.mk_select
              (Term.mk_var v)
              ((* List.rev *) i')
          in

          Debug.simplify
            "Simplified %a to %a"
            Term.pp_print_term (Term.construct fterm)
            Term.pp_print_term t';

          (* Return term *)
          atom_of_term t'

      )

  (* Select operation is binary *)
  | _ -> assert false



(* ********************************************************************** *)
(* Simplify and evaluate functions                                        *)
(* ********************************************************************** *)


(* Simplify a term node to a normal form with arithmetic operations
   evaluated as far as possible 

   This function is recursive, it calls itself with modified
   arguments. It is not tail-recursive, but that is OK, because the
   the recursion depth is shallow. *)
let rec simplify_term_node default_of_var uf_defs model fterm args = 

  match fterm with 

    | Term.T.Var v -> 

      (match Var.VarHashtbl.find model v with
        
        (* Free variable with assignment in model *)
        | Model.Term v' ->
          (* This check is necessary because the SMT solver doesn't 
             differentiate between signed and unsigned BV types. We 
             do it here before simplifying the model *)
          let v'' = 
            (if (Type.is_bitvector (Var.type_of_var v)) then
              Term.mk_bv (Term.bitvector_of_term v')
             else if (Type.is_ubitvector (Var.type_of_var v)) then
              Term.mk_ubv (Term.bitvector_of_term v')
             else
              v')
          in
            Term.eval_t
              (simplify_term_node default_of_var uf_defs model)
              v''

        (* Defer evaluation of lambda abstraction or arrays *)
        | Model.Lambda _ | Model.Map _ -> atom_of_term (Term.mk_var v)

        (* Free variable without assignment in model *)
        | exception Not_found -> 
       
          (* Term obtained by evaluating variable to itself *)
          let t = Term.mk_var v in

          (* Term obtained by evaluating variable to its default *)
          let t' =
            if Var.type_of_var v |> Type.is_array then t
            else default_of_var v in

          (* Break cycle if the the variable is its own default *)
          if Term.equal t t' then atom_of_term t else

            (* Evaluate default value of variable *)
            Term.eval_t
              (simplify_term_node default_of_var uf_defs model)
              t'

      )
                   
    (* Polynomial of a constant depends on symbol *)
    | Term.T.Const s -> 
      
      (
        
        (* Unhashcons constant symbol *)
        match Symbol.node_of_symbol s with 

          (* Polynomial for a numeral is n *)
          | `NUMERAL n -> Num (n, [])

          (* Polynomial for a decimal is d *)
          | `DECIMAL d -> Dec (d, [])

          (* Propositional constant *)
          | `TRUE -> Bool (Term.t_true)
          | `FALSE -> Bool (Term.t_false)

          (* Bitvector - taking an unsigned interpretation *)
          | `BV b -> 
            
            let tbv = Term.mk_ubv b in
              BV tbv

          | `UBV b -> 

            let tbv = Term.mk_ubv b in
              BV tbv

          (* Constant with a definition *)
          | `UF uf_symbol when List.mem_assq uf_symbol uf_defs -> 
            
            (* Get definition of function *)
            let (vars, uf_def) = 
              List.assq uf_symbol uf_defs 
            in
            
             Debug.simplify
               "@[<v>Definition of %a:@,variables@ %a@,term@ %a@]"
               UfSymbol.pp_print_uf_symbol uf_symbol
               (pp_print_list Var.pp_print_var "@ ") vars
               Term.pp_print_term uf_def;

            (* Replace function by its definition *)
            let term' = 
              Term.mk_let 
                (List.fold_right2
                   (fun var def accum -> (var, def) :: accum)
                   vars
                   []
                   [])
                uf_def
            in

            (Term.eval_t 
               (simplify_term_node default_of_var uf_defs model) 
               term')

          (* Uninterpreted constant *)
          | `UF u -> atom_of_term (Term.mk_uf u [])

          (* Fail in remaining cases, which are not constants *)
          | _ -> assert false 

      )

    (* Normal form of a function application depends on its symbol *)
    | Term.T.App (s, _) -> 

      (
        
        (* Unhashcons function symbol *)
        match Symbol.node_of_symbol s with 

          (* Select from an array *)
          | `SELECT _ ->

            select simplify_term_node default_of_var uf_defs model fterm args

          (* array store *)
          | `STORE ->


            (match args with

              (* Arguments are array, index and value *)
             | [a; i; v] ->

               atom_of_term (
                 Term.mk_store (term_of_nf a) (term_of_nf i) (term_of_nf v))

              (* Store is ternary *)
              | _ -> assert false
            )
            
          | `UF _ when Symbol.is_select s ->

            select simplify_term_node default_of_var uf_defs model fterm args

          (* Function with a definition *)
          | `UF uf_symbol when List.mem_assq uf_symbol uf_defs ->

            (* Get definition of function *)
            let (vars, uf_def) =
              List.assq uf_symbol uf_defs
            in

            Debug.simplify
              "@[<v>Definition of %a:@,variables@ %a@,term@ %a@]"
              UfSymbol.pp_print_uf_symbol uf_symbol
              (pp_print_list Var.pp_print_var "@ ") vars
              Term.pp_print_term uf_def;

            (* Replace function by its definition *)
            let term' =
              Term.mk_let
                (List.fold_right2
                   (fun var def accum -> (var, def) :: accum)
                   vars
                   (List.map term_of_nf args)
                   [])
                uf_def
            in

            Debug.simplify
              "@[<v>Simplify@ %a@]" Term.pp_print_term term';

            (Term.eval_t
               (simplify_term_node default_of_var uf_defs model)
               term')

          (* Normal form for an uninterpreted function *)
          | `UF u ->

            atom_of_term (Term.mk_uf u (List.map term_of_nf args))


          (* Boolean negation *)
          | `NOT -> 

            (match args with 

              (* Evalute if argument is true *)
              | [Bool b] when b == Term.t_true -> Bool Term.t_false

              (* Evalute if argument is false *)
              | [Bool b] when b == Term.t_false -> Bool Term.t_true

              (* Construct negation of non-constant argument *)
              | [Bool b] -> Bool (negate_nnf b)

              (* Negation is Boolean and unary *)
                | _ -> (List.iter (fun t -> Format.printf "ARGS: %a@." Term.pp_print_term t) (List.map term_of_nf args) ; assert false)
            )

          (* Boolean conjunction *)
          | `AND -> 

            (match args with 

              (* Conjunction is not nullary *)
              | [] -> assert false 

              (* Return argument of unary conjunction *)
              | [a] -> a 

              (* Binary conjunction or higher arity *)
              | _ -> 

                Debug.simplify
                  "@[<hv>`AND with arguments@ %a@]"
                  (pp_print_list Term.pp_print_term "@ ")
                  (List.map term_of_nf args);

                (* Lift arguments of subterms *)
                let args' = flatten_bool_subterms Symbol.s_and args in

                (* Sort into positive and negative literals *)
                let args_neg, args_pos = 
                  List.partition Term.is_negated args'
                in

                (* Simplify to (false) if (false) is a positive literal

                   (not true) and (not false) have been simplified *)
                if List.memq Term.t_false args_pos then 

                  (* Conjunction that contains (false) simplifies to
                     (false) *)
                  Bool Term.t_false

                else

                  (

                    (* Sort positive literals, remove duplicates and
                       (true) *)
                    let _, args_pos' =
                      List.partition
                        ((==) Term.t_true)
                        (list_uniq (List.sort Term.compare args_pos))
                    in

                    (* Sort negative literals and remove duplicates 

                       We don't need to remove (false), since (not
                       false) has been evaluated to the positive
                       literal (true) *)
                    let args_neg' = 
                      list_uniq (List.sort Term.compare args_neg) 
                    in

                    (* Check if positive literal has its complement in
                       the negative literals *)
                    if has_complement args_neg' args_pos' then 

                      (* Simplifiy to [false] if a literal and its
                         complement occur *)
                      Bool Term.t_false

                    else
                      
                      (* Combine simplified positive and negative
                         literals *)
                      let args' = args_pos' @ args_neg' in

                      match args' with 

                        (* Return (true) if all literals eliminated *)
                        | [] -> Bool Term.t_true

                        (* Return single literal if eliminated to
                           singleton list *)
                        | [a] -> Bool a

                        (* Return simplified conjunction *) 
                        | _ -> Bool (Term.mk_and args')

                  )
                  
            )

          (* Boolean disjunction *)
          | `OR -> 

            (match args with 

              (* Disjunction is not nullary *)
              | [] -> assert false 

              (* Return argument of unary disjunction *)
              | [a] -> a 

              (* Binary disjunction or higher arity *)
              | _ -> 

                (* Lift arguments of subterms *)
                let args' = flatten_bool_subterms Symbol.s_or args in

                (* Sort into positive and negative literals *)
                let args_neg, args_pos = 
                  List.partition Term.is_negated args'
                in

                (* Simplify to (true) if (true) is a positive literal

                   (not true) and (not false) have been simplified *)
                if List.memq Term.t_true args_pos then 

                  (* Disjunction that contains (true) is simplified to
                     (true) *)
                  Bool Term.t_true

                else

                  (

                    (* Sort positive literals, remove duplicates and
                       (false) *)
                    let _, args_pos' =
                      List.partition
                        ((==) Term.t_false)
                        (list_uniq (List.sort Term.compare args_pos))
                    in

                    (* Sort negative literals and remove duplicates

                       We don't need to remove (true), since (not
                       true) has been evaluated to the positive
                       literal (false) *)
                    let args_neg' = 
                      list_uniq (List.sort Term.compare args_neg) 
                    in

                    (* Check if positive literal has its complement in
                       the negative literals *)
                    if has_complement args_neg' args_pos' then 

                      (* Simplifiy to (true) if a literal and its
                         complement occur *)
                      Bool Term.t_true

                    else

                      (* Combine simplified positive and negative
                         literals *)
                      let args' = args_pos' @ args_neg' in

                      match args' with 

                        (* Return (false) if all literals eliminated *)
                        | [] -> Bool Term.t_false

                        (* Return single literal if eliminated to
                           singleton list *)
                        | [a] -> Bool a

                        (* Return simplified disjunction *)
                        | _ -> Bool (Term.mk_or args')

                  )

            )

          (* Reduce implication to a disjunction *)
          | `IMPLIES -> 

            (* Negate all but the last argument *)
            let args' = implies_to_or args in

            (* Create a disjunction of modified arguments *)
            let term' = Term.mk_or (List.map term_of_nf args') in

            (* Simplify disjunction *)
            simplify_term_node 
              default_of_var 
              uf_defs model
              (Term.destruct term') 
              args' 

          (* Reduce exclusive disjunction (a xor b) to disjunction of
             conjunctions ((a & ~b) | (~a & b)) *)
          | `XOR -> 

            (match args with 

              (* Nullary or unary exclusive disjunction *)
              | [] 
              | [_] -> assert false

              (* Binary exclusive disjunction *)
              | [Bool a; Bool b] -> 

                (* Negated normalised arguments *)
                let na, nb = negate_nnf a, negate_nnf b in

                (* Simplify (a & ~b) *)
                let term_a' = 
                  bool_of_nf 
                    (simplify_term_node 
                      default_of_var 
                      uf_defs
                      model
                      (Term.destruct (Term.mk_and [a; nb])) 
                      [Bool a; Bool nb])
                in

                (* Simplify (~a & b) *)
                let term_b' = 
                  bool_of_nf
                    (simplify_term_node 
                       default_of_var 
                       uf_defs
                       model
                       (Term.destruct (Term.mk_and [na; b])) 
                       [Bool na; Bool b])
                in

                (* Simplify ((a & ~b) | (~a & b)) and return *)
                simplify_term_node 
                  default_of_var 
                  uf_defs
                  model
                  (Term.destruct (Term.mk_or [term_a'; term_b']))
                  [Bool term_a'; Bool term_b']

              (* Higher arity exclusive disjunction *)
              | Bool a :: Bool b :: tl -> 

                (* Simplify (a xor b) *)
                let term' = 
                  bool_of_nf
                    (simplify_term_node
                       default_of_var 
                       uf_defs
                       model
                       (Term.destruct (Term.mk_xor [a; b]))
                       [Bool a; Bool b])
                in

                (* Exclusive disjunction is left-associative: simplify
                   first two arguments and recursively simplify
                   exclusive disjunction with remaining arguments *)
                simplify_term_node 
                  default_of_var 
                  uf_defs
                  model
                  (Term.destruct 
                     (Term.mk_xor (term' :: (List.map bool_of_nf tl))))
                  (Bool term' :: tl)

              (* Not well-typed arguments *)
              | Bool _ :: (Num _ | Dec _ | Array _ | BV _ ) :: _
              | (Num _  | Dec _ | Array _ | BV _ ) :: _  -> assert false

            )

          (* Equation *)
          | `EQ -> 
            
            (match args with 
              
              (* Nullary or unary equation *)
              | []  -> assert false
              | [_] -> assert false

              (* Binary equivalence, reduce to (a & b) | (~a & ~b) *)
              | [Bool a; Bool b] -> 

                (* Negated normalised arguments *)
                let na, nb = negate_nnf a, negate_nnf b in

                (* Simplify (a & b) *)
                let term_a' = 
                  bool_of_nf 
                    (simplify_term_node 
                       default_of_var 
                       uf_defs
                       model
                       (Term.destruct (Term.mk_and [a; b])) 
                       [Bool a; Bool b])
                in

                (* Simplify (~a & ~b) *)
                let term_b' = 
                  bool_of_nf
                    (simplify_term_node 
                       default_of_var      
                       uf_defs
                       model
                       (Term.destruct (Term.mk_and [na; nb])) 
                       [Bool na; Bool nb])
                in

                (* Simplify ((a & b) | (~a & ~b)) and return *)
                simplify_term_node 
                  default_of_var 
                  uf_defs
                  model
                  (Term.destruct (Term.mk_or [term_a'; term_b']))
                  [Bool term_a'; Bool term_b']

              (* Equation between integers or reals *)
              | _ -> 

                relation_eq
                  (simplify_term_node default_of_var uf_defs model) 
                  args

            )

          (* Relations *)
          | `LEQ -> 

            relation_leq
              (simplify_term_node default_of_var uf_defs model) 
              args

          | `LT -> 

            relation_lt
              (simplify_term_node default_of_var uf_defs model) 
              args

          | `GEQ -> 

            relation_geq
              (simplify_term_node default_of_var uf_defs model) 
              args

          | `GT ->

            relation_gt
              (simplify_term_node default_of_var uf_defs model) 
              args

          (* If-then-else *)
          | `ITE -> 

            (match args with 

              (* Choose left branch if predicate is true *)
              | [Bool p; l; _] when p == Term.t_true -> l

              (* Choose right branch if predicate is false *)
              | [Bool p; _; r] when p == Term.t_false -> r

              (* Evaluate to a Boolean *)
              | [Bool p; Bool l; Bool r] -> Bool (Term.mk_ite p l r)

              (* Evaluate to an integer atom *)
              | [Bool p; Num l; Num r] -> 

                (atom_of_term
                   (Term.mk_ite 
                      p 
                      (term_of_num_polynomial l) 
                      (term_of_num_polynomial r)))

              (* Evaluate to a real atom *)
              | [Bool p; Dec l; Dec r] -> 

                  (atom_of_term
                     (Term.mk_ite 
                        p 
                        (term_of_dec_polynomial l) 
                        (term_of_dec_polynomial r)))

              (* Not well-typed or wrong arity *)
              | _ -> assert false 

            )

          (* Divisibility predicate *)
          | `DIVISIBLE n -> 

            (match args with 

              (* Divisibility is a unary predicate of an integer *)
              | [Num d] -> 
                
                (* Argument is constant? *)
                if is_constant_polynomial d then

                  (if 
                    
                    (* Evaluate (t divisible n) as (= 0 (mod t n)) *)
                    Numeral.equal 
                      (Numeral.(mod) (const_of_polynomial d) n)
                      Numeral.zero
                    
                   then 
                     
                     (* Simplify to (true) *)
                     Bool Term.t_true 

                   else

                     (* Simplify to (false) *)
                     Bool Term.t_false)
                     
                else
                  
                  (* Divisibility predicate becomes new atom *)
                  atom_of_term 
                    (Term.mk_divisible n (term_of_num_polynomial d))

              (* Not well-typed or wrong arity *)
              | _ -> assert false)

          (* N-ary addition *)
          | `PLUS -> add args

          (* Unary minus or n-ary difference *)
          | `MINUS -> minus args

          (* N-ary multiplication *)
          | `TIMES -> times args

          (* Real division is a monomial with polynomial subterms *)
          | `DIV -> 

            (* Evaluate to a polynomial if all arguments are constant *)
            if List.for_all is_constant args then 

              (* Get all constants of polynomials *)
              match List.map const_of_dec_polynomial args with 

                (* Integer division must be at least binary *)
                | [] 
                | [_] -> assert false 

                (* Divide first argument by remaining arguments *)
                | h :: tl -> 

                  Dec 
                    ((List.fold_left 
                        (fun a e -> 
                           if Decimal.(e = zero) then
                             (* raise (Failure "simplify_term: division by zero") *)
                             division_by_zero := true ;
                           Decimal.(a / e))
                        h 
                        tl), 
                     [])

            else

              (* Return a new monomial for non-constant division

                 TODO: `DIV is variadic and left-associative, we
                 could simplify terms like (div 2 2 a) = (div 1 a) and
                 also (div a 2 2) = (div a 1) = a *)
              Num 
                (Numeral.zero, 
                 [Numeral.one, 
                  [Term.mk_div (List.map term_of_nf args)]])

          (* Integer division is a monomial with polynomial subterms *)
          | `INTDIV -> 

            (* Evaluate to a polynomial if all arguemnts constant *)
            if List.for_all is_constant args then 

              match List.map const_of_num_polynomial args with 

                (* Integer division must be at least binary *)
                | [] 
                | [_] -> assert false 

                (* Divide first argument by remaining arguments *)
                | h :: tl -> Num ((List.fold_left Numeral.(/) h tl), [])

            else

               (* Return a new monomial for non-constant division

                  TODO: `INTDIV is variadic and left-associative, we
                  could simplify terms like (div 2 2 a) = (div 1 a)
                  and also (div a 2 2) = (div a 1) = a *)
              Num (Numeral.zero, [Numeral.one, [Term.mk_intdiv (List.map term_of_nf args)]])

          (* Moudulus is a monomial with polynomial subterms *)
          | `MOD -> 

            (match args with 

              (* Evaluate to a polynomial if both arguments are constant *)
              | [Num (n, []); Num (m, [])] -> Num (Numeral.(n mod m), [])

              (* Non-constant polynomial arguments *)
              | [a; b] -> 

                (* New polynomial with modulus as atom *)
                Num (Numeral.zero, [Numeral.one, [Term.mk_mod (term_of_nf a) (term_of_nf b)]])

              (* Modulus is only binary *)
              | _ -> assert false 

            )

          (* Absolute value is a monomial with polynomial subterms *)
          | `ABS -> 

            (match args with 

              (* Evaluate to a polynomial if integer argument is
                 constant *)
              | [Num (n, [])] -> Num ((Numeral.abs n), [])

              (* Evaluate to a polynomial if real argument is
                 constant *)
              | [Dec (d, [])] -> Dec ((Decimal.abs d), [])

              (* Non-constant real or integer polynomial argument *)
              | [a] ->

                (* New polynomial with absolute value as atom *)
                Num (Numeral.zero, [Numeral.one, [Term.mk_abs (term_of_nf a)]])

              (* Absolute value is only unary *)
              | _ -> assert false 

            )

          (* Conversion to integer is a monomial with polynomial
             subterms *)
          | `TO_INT -> 

            (match args with 

              (* Evaluate to a polynomial if real argument is
                 constant *)
              | [Dec (d, [])] -> Num (Numeral.of_big_int (Decimal.to_big_int d), [])

              (* Non-constant polynomial argument *)
              | [Dec _ as a] -> 

                (* New polynomial with integer value as atom *)
                Num (Numeral.zero, [Numeral.one, [Term.mk_to_int (term_of_nf a)]])

              | [Num _ as a] -> a

              (* Conversion is only unary *)
              | _ -> assert false 

            )
          
          | `UINT8_TO_INT ->

            (match args with 
                        
            | [BV b] -> let s = (Bitvector.length_of_bitvector (Term.bitvector_of_term b)) in
                  (match s with 
                  | 8 -> Num (Bitvector.ubv8_to_num (Term.bitvector_of_term b), [])
                  | _ -> assert false)
            
            | [Num _ as a] -> a
            
            | _ -> assert false

            )
        
          | `UINT16_TO_INT ->

            (match args with 
            
            | [BV b] -> let s = (Bitvector.length_of_bitvector (Term.bitvector_of_term b)) in
                  (match s with 
                  | 16 -> Num (Bitvector.ubv16_to_num (Term.bitvector_of_term b), [])
                  | _ -> assert false)
            
            | [Num _ as a] -> a
            
            | _ -> assert false

            )
        
          | `UINT32_TO_INT ->

            (match args with 
            
            | [BV b] -> let s = (Bitvector.length_of_bitvector (Term.bitvector_of_term b)) in
                  (match s with 
                  | 32 -> Num (Bitvector.ubv32_to_num (Term.bitvector_of_term b), [])
                  | _ -> assert false)
            
            | [Num _ as a] -> a
            
            | _ -> assert false

            )
        
          | `UINT64_TO_INT ->

            (match args with 
            
            | [BV b] -> let s = (Bitvector.length_of_bitvector (Term.bitvector_of_term b)) in
                  (match s with 
                  | 64 -> Num (Bitvector.ubv64_to_num (Term.bitvector_of_term b), [])
                  | _ -> assert false)
            
            | [Num _ as a] -> a
            
            | _ -> assert false

            )
        
          | `INT8_TO_INT ->

            (match args with 
            
            | [BV b] -> let s = (Bitvector.length_of_bitvector (Term.bitvector_of_term b)) in
                  (match s with 
                  | 8 -> Num (Bitvector.bv8_to_num (Term.bitvector_of_term b), [])
                  | _ -> assert false)
            
            | [Num _ as a] -> a
            
            | _ -> assert false

            )
        
          | `INT16_TO_INT ->

            (match args with 
            
            | [BV b] -> let s = (Bitvector.length_of_bitvector (Term.bitvector_of_term b)) in
                  (match s with 
                  | 16 -> Num (Bitvector.bv16_to_num (Term.bitvector_of_term b), [])
                  | _ -> assert false)
            
            | [Num _ as a] -> a
            
            | _ -> assert false

            )
          
          | `INT32_TO_INT ->

            (match args with 
            
            | [BV b] -> let s = (Bitvector.length_of_bitvector (Term.bitvector_of_term b)) in
                  (match s with 
                  | 32 -> Num (Bitvector.bv32_to_num (Term.bitvector_of_term b), [])
                  | _ -> assert false)
            
            | [Num _ as a] -> a
            
            | _ -> assert false

            )
        
          | `INT64_TO_INT ->

            (match args with 
            
            | [BV b] -> let s = (Bitvector.length_of_bitvector (Term.bitvector_of_term b)) in
                  (match s with 
                  | 64 -> Num (Bitvector.bv64_to_num (Term.bitvector_of_term b), [])
                  | _ -> assert false)
            
            | [Num _ as a] -> a
            
            | _ -> assert false

            )

          (* Conversion to unsigned integer8 is a monomial with polynomial
             subterms *)
          | `TO_UINT8 -> 

            (match args with 
              | [BV b] -> let s = (Bitvector.length_of_bitvector (Term.bitvector_of_term b)) in
                  (match s with 
                  | 8 -> BV b
                  | _ -> BV (Term.mk_ubv (Bitvector.bvextract 7 0 (Term.bitvector_of_term b))))
              | [Num n] -> BV (Term.mk_ubv 
                                  (Bitvector.num_to_ubv8 
                                    (Term.numeral_of_term 
                                      (term_of_nf (Num n)))))
              | _ -> assert false
            )

          (* Conversion to unsigned integer16 is a monomial with polynomial
             subterms *)
          | `TO_UINT16 -> 

            (match args with 
              | [BV b] -> let s = (Bitvector.length_of_bitvector (Term.bitvector_of_term b)) in
                  (match s with 
                  | 8 -> BV (Term.mk_ubv (Bitvector.bvsignext 8 (Term.bitvector_of_term b)))
                  | 16 -> BV b
                  | _ -> BV (Term.mk_ubv (Bitvector.bvextract 15 0 (Term.bitvector_of_term b))))
              | [Num n] ->  BV (Term.mk_ubv 
                                  (Bitvector.num_to_ubv16 
                                    (Term.numeral_of_term 
                                      (term_of_nf (Num n)))))
              | _ -> assert false
            )          

          (* Conversion to unsigned integer32 is a monomial with polynomial
             subterms *)
          | `TO_UINT32 -> 
          
            (match args with 
              | [BV b] -> let s = (Bitvector.length_of_bitvector (Term.bitvector_of_term b)) in
                  (match s with 
                  | 8 -> BV (Term.mk_ubv (Bitvector.bvsignext 24 (Term.bitvector_of_term b)))
                  | 16 -> BV (Term.mk_ubv (Bitvector.bvsignext 16 (Term.bitvector_of_term b)))
                  | 32 -> BV b
                  | _ -> BV (Term.mk_ubv (Bitvector.bvextract 31 0 (Term.bitvector_of_term b))))
              | [Num n] ->  BV (Term.mk_ubv 
                                  (Bitvector.num_to_ubv32 
                                    (Term.numeral_of_term 
                                      (term_of_nf (Num n)))))
              | _ -> assert false
            )          

          (* Conversion to unsigned integer64 is a monomial with polynomial
             subterms *)
          | `TO_UINT64 -> 
          
            (match args with 
              | [BV b] -> let s = (Bitvector.length_of_bitvector (Term.bitvector_of_term b)) in
                  (match s with 
                  | 8 -> BV (Term.mk_ubv (Bitvector.bvsignext 56 (Term.bitvector_of_term b)))
                  | 16 -> BV (Term.mk_ubv (Bitvector.bvsignext 48 (Term.bitvector_of_term b)))
                  | 32 -> BV (Term.mk_ubv (Bitvector.bvsignext 32 (Term.bitvector_of_term b)))
                  | _ -> BV b)
              | [Num n] -> BV (Term.mk_ubv 
                                  (Bitvector.num_to_ubv64 
                                    (Term.numeral_of_term 
                                      (term_of_nf (Num n)))))
              | _ -> assert false
            )          

          (* Conversion to integer8 is a monomial with polynomial
             subterms *)
          | `TO_INT8 ->
          
            (match args with 
              | [BV b] -> let s = (Bitvector.length_of_bitvector (Term.bitvector_of_term b)) in
                  (match s with 
                  | 8 -> BV b
                  | _ -> BV (Term.mk_ubv (Bitvector.bvextract 7 0 (Term.bitvector_of_term b))))
              | [Num n] -> BV (Term.mk_ubv 
                                  (Bitvector.num_to_bv8 
                                    (Term.numeral_of_term 
                                      (term_of_nf (Num n)))))
              | _ -> assert false
            )

          (* Conversion to integer16 is a monomial with polynomial
             subterms *)
          | `TO_INT16 -> 
          
            (match args with 
              | [BV b] -> let s = (Bitvector.length_of_bitvector (Term.sbitvector_of_term b)) in
                  (match s with 
                  | 8 -> BV (Term.mk_ubv (Bitvector.bvsignext 8 (Term.sbitvector_of_term b)))
                  | 16 -> BV b
                  | _ -> BV (Term.mk_ubv (Bitvector.bvextract 15 0 (Term.bitvector_of_term b))))
              | [Num n] -> BV (Term.mk_ubv 
                                  (Bitvector.num_to_bv16 
                                    (Term.numeral_of_term 
                                      (term_of_nf (Num n)))))
              | _ -> assert false
            )          

          (* Conversion to integer32 is a monomial with polynomial
             subterms *)
          | `TO_INT32 -> 
          
            (match args with 
              | [BV b] -> let s = (Bitvector.length_of_bitvector (Term.sbitvector_of_term b)) in
                  (match s with 
                  | 8 -> BV (Term.mk_ubv (Bitvector.bvsignext 24 (Term.sbitvector_of_term b)))
                  | 16 -> BV (Term.mk_ubv (Bitvector.bvsignext 16 (Term.sbitvector_of_term b)))
                  | 32 -> BV b
                  | _ -> BV (Term.mk_ubv (Bitvector.bvextract 31 0 (Term.bitvector_of_term b))))
              | [Num n] ->  BV (Term.mk_ubv 
                                  (Bitvector.num_to_bv32 
                                    (Term.numeral_of_term 
                                      (term_of_nf (Num n)))))
              | _ -> assert false
            )          

          (* Conversion to integer64 is a monomial with polynomial
             subterms *)
          | `TO_INT64 -> 
          
            (match args with 
              | [BV b] -> let s = (Bitvector.length_of_bitvector (Term.sbitvector_of_term b)) in
                  (match s with 
                  | 8 -> BV (Term.mk_ubv (Bitvector.bvsignext 56 (Term.sbitvector_of_term b)))
                  | 16 -> BV (Term.mk_ubv (Bitvector.bvsignext 48 (Term.sbitvector_of_term b)))
                  | 32 -> BV (Term.mk_ubv (Bitvector.bvsignext 32 (Term.sbitvector_of_term b)))
                  | _ -> BV b)
              | [Num n] ->  BV (Term.mk_ubv 
                                  (Bitvector.num_to_bv64 
                                    (Term.numeral_of_term 
                                      (term_of_nf (Num n)))))
              | _ -> assert false
            )
          
          | `BV2NAT -> 
          
            (match args with
              | [BV b] -> let t = term_of_nf (BV b) in
                           let tp = Term.type_of_term t in
                           let bv = Term.bitvector_of_term t in
                            if (Type.is_int8 tp || Type.is_uint8 tp) then 
                              Num (Bitvector.ubv8_to_num bv, [])
                            else if (Type.is_int16 tp || Type.is_uint16 tp) then 
                              Num (Bitvector.ubv16_to_num bv, [])
                            else if (Type.is_int32 tp || Type.is_uint32 tp) then 
                              Num (Bitvector.ubv32_to_num bv, [])
                            else if (Type.is_int64 tp || Type.is_uint64 tp) then 
                              Num (Bitvector.ubv64_to_num bv, [])
                            else 
                              assert false
              | _ -> assert false
            )

          (* Conversion to real is a monomial with polynomial
             subterms *)
          | `TO_REAL -> 

            (match args with 

              (* Evaluate to a polynomial if integer argument is
                 constant *)
              | [Num (n, [])] -> Dec (Decimal.of_big_int (Numeral.to_big_int n), [])

              (* Non-constant polynomial argument *)
              | [Num _ as a] -> 

                (* New polynomial with integer value as atom *)
                Dec (Decimal.zero, [Decimal.one, [Term.mk_to_int (term_of_nf a)]])

              | [Dec _ as a] -> a

              (* Conversion is only unary *)
              | _ -> assert false 

            )

          (* Coincidence of real with integer not implemented *)
          | `IS_INT -> assert false 

          (* Distinct not implemented *)
          | `DISTINCT -> assert false

          | `BVAND ->
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> BV (Term.mk_ubv (Bitvector.bv_and
                                                  (Term.bitvector_of_term a)
                                                  (Term.bitvector_of_term b)))
              | _ -> assert false)
          
          | `BVOR ->
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> BV (Term.mk_ubv (Bitvector.bv_or
                                                  (Term.bitvector_of_term a)
                                                  (Term.bitvector_of_term b)))
              | _ -> assert false)

          | `BVNOT ->
            (match args with 
              | [] -> assert false 
              | [BV a] -> BV (Term.mk_ubv (Bitvector.bv_not 
                                            (Term.bitvector_of_term a)))
              | _ -> assert false)
            
          | `BVSHL ->
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> BV (Term.mk_ubv (Bitvector.bv_lsh
                                                  (Term.bitvector_of_term a)
                                                  (Term.bitvector_of_term b))) 
              | _ -> assert false)

          | `BVLSHR ->
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> BV (Term.mk_ubv (Bitvector.bv_rsh
                                                  (Term.bitvector_of_term a)
                                                  (Term.bitvector_of_term b))) 
              | _ -> assert false)

          | `BVASHR ->
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> BV (Term.mk_ubv (Bitvector.bv_arsh
                                                  (Term.bitvector_of_term a)
                                                  (Term.bitvector_of_term b))) 
              | _ -> assert false)

          | `BVADD ->
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> BV (Term.mk_ubv (Bitvector.sbv_add
                                                  (Term.bitvector_of_term a)
                                                  (Term.bitvector_of_term b)))
              | _ -> assert false)

          | `BVSUB ->
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> BV (Term.mk_ubv (Bitvector.sbv_sub
                                                  (Term.bitvector_of_term a)
                                                  (Term.bitvector_of_term b)))
              | _ -> assert false)

          | `BVMUL ->
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> BV (Term.mk_ubv (Bitvector.sbv_mult
                                                  (Term.bitvector_of_term a)
                                                  (Term.bitvector_of_term b)))              
              | _ -> assert false)

          | `BVUDIV ->
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> BV (Term.mk_ubv (Bitvector.ubv_div
                                                      (Term.bitvector_of_term a)
                                                      (Term.bitvector_of_term b)))
              | _ -> assert false)

          | `BVSDIV ->
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> BV (Term.mk_ubv (Bitvector.sbv_div
                                              (Term.bitvector_of_term a)
                                              (Term.bitvector_of_term b)))
              | _ -> assert false)

          | `BVUREM ->
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> BV (Term.mk_ubv (Bitvector.ubv_rem 
                                                      (Term.bitvector_of_term a)
                                                      (Term.bitvector_of_term b)))
              | _ ->  assert false)

          | `BVSREM ->
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> BV (Term.mk_ubv (Bitvector.sbv_rem 
                                                  (Term.bitvector_of_term a)
                                                  (Term.bitvector_of_term b)))
              | _ -> assert false)

          | `BVUDIV_I ->
            assert false
          
          | `BVSDIV_I ->
            assert false

          | `BVUREM_I ->
            assert false

          | `BVSREM_I ->
            assert false

          | `BVULT -> 
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> Bool (Term.mk_bool (Bitvector.ult
                                                      (Term.bitvector_of_term a)
                                                      (Term.bitvector_of_term b)))
              | _ -> relation_lt
                      (simplify_term_node default_of_var uf_defs model) 
                      args)

          | `BVULE -> 
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> Bool (Term.mk_bool (Bitvector.ulte
                                                      (Term.bitvector_of_term a)
                                                      (Term.bitvector_of_term b)))
              | _ -> relation_leq
                      (simplify_term_node default_of_var uf_defs model) 
                      args)

          | `BVUGT ->           
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> Bool (Term.mk_bool (Bitvector.ugt
                                                      (Term.bitvector_of_term a)
                                                      (Term.bitvector_of_term b)))
              | _ -> relation_gt
                      (simplify_term_node default_of_var uf_defs model) 
                      args)

          | `BVUGE -> 
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> Bool (Term.mk_bool (Bitvector.ugte
                                                      (Term.bitvector_of_term a)
                                                      (Term.bitvector_of_term b)))
              | _ -> relation_geq
                      (simplify_term_node default_of_var uf_defs model) 
                      args)

          | `BVSLT -> 
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> Bool (Term.mk_bool (Bitvector.lt
                                                      (Term.bitvector_of_term a)
                                                      (Term.bitvector_of_term b)))
              | _ -> relation_lt
                      (simplify_term_node default_of_var uf_defs model) 
                      args)

          | `BVSLE -> 
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> Bool (Term.mk_bool (Bitvector.lte
                                                      (Term.bitvector_of_term a)
                                                      (Term.bitvector_of_term b)))
              | _ -> relation_leq
                      (simplify_term_node default_of_var uf_defs model) 
                      args)

          | `BVSGT ->
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> Bool (Term.mk_bool (Bitvector.gt
                                                      (Term.bitvector_of_term a)
                                                      (Term.bitvector_of_term b)))
              | _ -> relation_gt
                      (simplify_term_node default_of_var uf_defs model) 
                      args)

          | `BVSGE -> 
            (match args with
              | [] -> assert false
              | [BV a; BV b] -> Bool (Term.mk_bool (Bitvector.gte
                                                      (Term.bitvector_of_term a)
                                                      (Term.bitvector_of_term b)))
              | _ -> relation_geq
                      (simplify_term_node default_of_var uf_defs model) 
                      args)

          | `BVNEG -> 
            (match args with
              | [] -> assert false
              | [BV a] -> BV (Term.mk_ubv (Bitvector.sbv_neg 
                                            (Term.bitvector_of_term a)))
              | _ -> assert false)

          | `BVEXTRACT (i, j) -> 
            (match args with
              | [] -> assert false
              | [BV b] -> BV (Term.mk_ubv (Bitvector.bvextract 
                                            (Numeral.to_int i) 
                                            (Numeral.to_int j) 
                                            (Term.bitvector_of_term b)))            
              | _ -> assert false)

          | `BVSIGNEXT i ->
            (match args with
              | [] -> assert false
              | [BV b] -> BV (Term.mk_ubv (Bitvector.bvsignext
                                            (Numeral.to_int i)
                                            (Term.bitvector_of_term b)))
              | _ -> assert false)

          | `BVCONCAT -> 
            (match args with
              | [] -> assert false
              | [a] -> a
              | [BV a; BV b] -> BV (Term.mk_ubv (Bitvector.bvconcat 
                                                  (Term.bitvector_of_term a) 
                                                  (Term.bitvector_of_term b)))
              | _ -> assert false)

          (* Constant symbols *)
          | `TRUE
          | `FALSE
          | `NUMERAL _
          | `DECIMAL _
          | `UBV _ 
          | `BV _ -> assert false
          
      )

    (* Skip over attributed term *)
    (* | Term.T.Attr _ -> match args with [a] -> a | _ -> assert false *)


(* ********************************************************************** *)
(* Top-level functions                                                    *)
(* ********************************************************************** *)

(* Return the default value of the type *)
let type_default_of_var v = Var.type_of_var v |> TermLib.default_of_type


(* Simplify a term with a model *)
let simplify_term_model ?default_of_var uf_defs model term = 

  Debug.simplify
    "Simplifying@ @[<hv>%a@]@ with model@ @[<hv>%a@]"
    Term.pp_print_term term
    Model.pp_print_model
    model;

  Var.VarHashtbl.iter (fun v -> function
      | Model.Term t when Term.is_free_var t ->
        let v' = Term.free_var_of_term t in
        if Var.equal_vars v v' then
          Var.VarHashtbl.remove model v
      | _ -> ()
    ) model;
  
  (* Convert returned default value to a polynomial *)
  let default_of_var' = match default_of_var with

    (* Take the given function *)
    | Some f -> fun v -> f v

    (* Take default value for type if no function given *)
    | None -> fun v ->
        type_default_of_var v

  in

  (* Simplify term to a normal form and convert back to a term *)
  let res =
    term_of_nf
      (Term.eval_t
         (simplify_term_node default_of_var' uf_defs model) 
         term)
  in

  Debug.simplify
    "Simplified@ > @[<hv>%a@]@ to@ > @[<hv>%a@]"
    Term.pp_print_term term
    Term.pp_print_term res;

  res

(* Simplify a term *)
let simplify_term uf_defs term = 

  simplify_term_model 
    ~default_of_var:Term.mk_var
    uf_defs 
    (Model.create 7) 
    term



(*
;;

(* ********************************************************************** *)
(* Testing in the OCaml toplevel                                          *)
(* ********************************************************************** *)


open Term.Abbrev;;
let ua = UfSymbol.mk_uf_symbol "a" [] Type.t_int;;
let ub = UfSymbol.mk_uf_symbol "b" [] Type.t_real;;
let up = UfSymbol.mk_uf_symbol "P" [] Type.t_bool;;
let uq = UfSymbol.mk_uf_symbol "Q" [] Type.t_bool;;
let ur = UfSymbol.mk_uf_symbol "R" [] Type.t_bool;;
let us = UfSymbol.mk_uf_symbol "S" [] Type.t_bool;;
let ta = Term.mk_uf ua [];;
let tb = Term.mk_uf ub [];;
let tp = Term.mk_uf up [];;
let tq = Term.mk_uf uq [];;
let tr = Term.mk_uf ur [];;
let ts = Term.mk_uf us [];;
let n1d = ?%@1;;
let n1f = ?/@1.;;
let n0d = ?%@0;;
let n0f = ?/@0.;;

let n2d = ?%@2;;
let n3d = ?%@3;;
let n4d = ?%@4;;
let n5d = ?%@5;;

let n2f = ?/@2.;;
let n3f = ?/@3.;;
let n4f = ?/@4.;;
let n5f = ?/@5.;;

let vx = 
  Var.mk_state_var_instance 
    (StateVar.mk_state_var "x" Type.t_int) 
    (numeral_of_int 0);;
let vy = 
  Var.mk_state_var_instance 
    (StateVar.mk_state_var "y" Type.t_int) 
    (numeral_of_int 0);;

let vz = 
  Var.mk_state_var_instance 
    (StateVar.mk_state_var "z" Type.t_int) 
    (numeral_of_int 0);;
let tx = Term.mk_var vx;;
let ty = Term.mk_var vy;;
let tz = Term.mk_var vz;;



let v_j = Var.mk_free_var (HString.mk_hstring "j") Type.t_int;;
let v_k = Var.mk_free_var (HString.mk_hstring "k") Type.t_int;;
let v_x = Var.mk_free_var (HString.mk_hstring "x") Type.t_int;;
let v_y = Var.mk_free_var (HString.mk_hstring "y") Type.t_int;;
let v_A = Var.mk_free_var (HString.mk_hstring "A") Type.(mk_array (mk_array t_int t_int) t_int);;
let v_B = Var.mk_free_var (HString.mk_hstring "B") Type.(mk_array t_int t_int);;
let l = Term.mk_lambda [v_j; v_k] Term.(mk_minus [(mk_var v_j); (mk_var v_k)]);;
let t = Term.(mk_select (mk_select (mk_var v_A) (mk_var v_j)) (mk_var v_k));;
Term.print_term t;;


Term.print_term (Eval.term_of_value  (Eval.eval_term [] (Model.create 7) t));;

Type.print_type (Var.type_of_var v_A);;
Type.print_type (Term.type_of_term t);;

let t2 = Term.(mk_select (mk_var v_B) (mk_var v_j));;
Term.print_term t2;;
Type.print_type (Term.type_of_term t2);;

let m = 
  Model.of_list 
    [(v_j, Model.Term (Term.mk_num_of_int 1)); 
     (v_k, Model.Term (Term.mk_num_of_int 2));
     (v_A, Model.Lambda l)];;


Term.print_term (Eval.term_of_value  (Eval.eval_term [] m t));;

*)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

