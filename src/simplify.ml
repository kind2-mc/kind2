(*
This file is part of the Kind verifier

* Copyright (c) 2007-2012 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

open Lib

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
  | Int of int polynomial
  | Real of float polynomial
  | Bool of Term.t 


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
let term_of_int_polynomial = 
  term_of_polynomial 
    ((=) 0)
    ((=) 1)
    (function () -> Term.mk_num_of_int 0)
    (Term.mk_num_of_int)


(* Convert a real polynomial to a term *)
let term_of_real_polynomial = 
  term_of_polynomial 
    ((=) 0.)
    ((=) 1.)
    (function () -> Term.mk_dec_of_float 0.)
    (Term.mk_dec_of_float)


(* Convert a normal form to a term *)
let term_of_nf = function 
  | Int p -> term_of_int_polynomial p
  | Real p -> term_of_real_polynomial p
  | Bool b -> b


(* ********************************************************************** *)
(* Conversions from normal forms                                          *)
(* ********************************************************************** *)


(* Return the integer polynomial in an integer normal form *)
let int_polynomial_of_nf = function 
  | Int p -> p
  | _ -> assert false


(* Return the real polynomial in a real normal form *)
let real_polynomial_of_nf = function 
  | Real p -> p
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
  | Int (_, [])
  | Real (_, [])  -> true
  | Bool b when b == Term.t_true || b == Term.t_false -> true
  | Int _
  | Real _ 
  | Bool _ -> false


(* Return true if value is variable-free *)
let is_constant_polynomial = function 
  | (_, []) -> true
  | _ -> false
    

(* Return the constant of a polynomial *)
let const_of_polynomial = function (c, _) -> c


(* Return the constant of an integer polynomial *)
let const_of_int_polynomial = function 
  | Int p -> const_of_polynomial p
  | _ -> assert false 


(* Return the constant of a real polynomial *)
let const_of_real_polynomial = function 
  | Real p -> const_of_polynomial p
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
        List.length t1 = List.length t1 && 
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
    add_polynomials negate_polynomial zero p q =

  (* Subtract second polynomial from first *)
  let r = add_polynomials [p; negate_polynomial q] in

  (* Normalize so that either the constant or the first coefficient of
     the polynomial is greater than zero *)
  match r with 

    (* Polynomial is the constanst zero *)
    | (c, []) when c = zero -> true, r

    (* Constant is zero, first coefficient is negative *)
    | (c, (h, _) :: tl) when c = zero & h < zero -> false, negate_polynomial r

    (* Constant is zero, first coefficient is not negative *)
    | (c, (h, _) :: tl) when c = zero -> true, r

    (* Constant is not zero and negative *)
    | (c, _) when c < zero -> false, negate_polynomial r

    (* Constant is not zero and positive *)
    | (c, _) -> true, r


(* ********************************************************************** *)
(* Integer arithmetic functions on polynomials                            *)
(* ********************************************************************** *)


let add_int_monomial_lists = add_monomial_lists (+) ((=) 0)

let add_int_polynomials = add_polynomials (+) 0 ((=) 0)

let const_multiply_int_monomial_list = const_multiply_monomial_list ( * )

let const_multiply_int_polynomial = const_multiply_polynomial ( * )

let negate_int_monomial_list = negate_monomial_list ( * ) (- 1)

let negate_int_polynomial = negate_polynomial ( * ) (- 1)

let multiply_int_polynomials = multiply_polynomials ( * ) ((=) 0) 0

let subtract_and_normalize_int_polynomials = 
  subtract_and_normalize_polynomials 
    add_int_polynomials 
    negate_int_polynomial 
    0


(* ********************************************************************** *)
(* Real arithmetic functions on polynomials                               *)
(* ********************************************************************** *)


let add_real_monomial_lists = add_monomial_lists (+.) ((=) 0.)

let add_real_polynomials = add_polynomials (+.) 0. ((=) 0.)

let const_multiply_real_monomial_list = const_multiply_monomial_list ( *. )

let const_multiply_real_polynomial = const_multiply_polynomial ( *. )

let negate_real_monomial_list = negate_monomial_list ( *. ) (-. 1.)

let negate_real_polynomial = negate_polynomial ( *. ) (-. 1.)

let multiply_real_polynomials = multiply_polynomials ( *. ) ((=) 0.) 0.

let subtract_and_normalize_real_polynomials = 
  subtract_and_normalize_polynomials 
    add_real_polynomials 
    negate_real_polynomial 
    0.


(* ********************************************************************** *)
(* Functions used in {!simplify_term_node}                                *)
(* ********************************************************************** *)


(* Sum up a list of integer polynomials *)
let add_int args = 

  let args' = List.map int_polynomial_of_nf args in

  add_int_polynomials args'


(* Sum up a list of real polynomials *)
let add_real args = 

  let args' = List.map real_polynomial_of_nf args in

  add_real_polynomials args'


(* Multiply two integer polynomials *)
let multiply_int p1 p2 = 

  let p1', p2' = int_polynomial_of_nf p1, int_polynomial_of_nf p2 in

  multiply_int_polynomials p1' p2'


(* Multiply two real polynomials *)
let multiply_real p1 p2 = 

  let p1', p2' = real_polynomial_of_nf p1, real_polynomial_of_nf p2 in

  multiply_real_polynomials p1' p2'


(* Sum up a list of real or integer normal forms *)
let add = function

  (* Addition is not nullary  *)
  | [] -> assert false 
    
  (* Add as integer polynomials if head of list is integer *)
  | Int _ :: _ as args -> Int (add_int args)
                    
  (* Add as real polynomials if head of list is real *)
  | Real _ :: _ as args -> Real (add_real args)
                     
  (* Cannot add other types *)
  | _ -> assert false


(* Subtract a list of polynomials *)
let minus = function 

  (* Subtraction is not nullary  *)
  | [] -> assert false 

  (* Unary integer minus: negate polynomial to (- c - p) *)
  | [Int p] -> Int (negate_int_polynomial p)

  (* Unary real minus: negate polynomial to (- c - p) *)
  | [Real p] -> Real (negate_real_polynomial p)

  (* Binary integer minus or higher arity: (h - s1 - ... - sn) reduce
     to (h - (s1 + ... + sn) *)
  | Int p :: tl -> 

    Int (add_int_polynomials [p; negate_int_polynomial (add_int tl)])

  (* Binary real minus or higher arity: (h - s1 - ... - sn) reduce to
     (h - (s1 + ... + sn) *)
  | Real p :: tl -> 

    Real (add_real_polynomials [p; negate_real_polynomial (add_real tl)])

  (* Cannot subtract other types *)
  | _ -> assert false


(* Multiply a list of polynomials *)
let times = function 

  (* Multiplication is not nullary  *)
  | [] -> assert false 
    
  (* Multiply as integer polynomials if head of list is integer *)
  | Int p :: tl -> 
    
    Int 
      (List.fold_left 
         multiply_int_polynomials 
         p 
         (List.map int_polynomial_of_nf tl))
                    
  (* Multiply as real polynomials if head of list is real *)
  | Real p :: tl -> 

    Real
      (List.fold_left 
         multiply_real_polynomials 
         p 
         (List.map real_polynomial_of_nf tl))
                     
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
    | Int _ :: _ 
    | Real _ :: _ -> assert false

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
      | `UF _, _ -> Term.mk_not term

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
      | `CONCAT, _
      | `EXTRACT _, _
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
      | `SELECT, _
      | `STORE, _ -> assert false 

    )    


(* Negate all but the last term *)
let implies_to_or args = 

  (* Tail-recursive function with accumulator *)
  let rec implies_to_or' accum = function 
    | [] -> assert false
    | [a] -> List.rev (a :: accum)
    | Bool h :: tl -> implies_to_or' (Bool (negate_nnf h) :: accum) tl
    | Int _ :: _
    | Real _ :: _ -> assert false
  in

  implies_to_or' [] args 


(* Subtract two normal forms and make constant or first coefficient
   positive *)
let subtract_and_normalize a b = match a, b with 

  (* Two integer polynomials *)
  | Int a, Int b -> 
    let s, r = subtract_and_normalize_int_polynomials a b in s, Int r

  (* Two real polynomials *)
  | Real a, Real b -> 
    let s, r = subtract_and_normalize_real_polynomials a b in s, Real r

  (* Cannot subtract *)
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


(* We need a record type for first-class polymorphism, modules or
   objects would also work. 

   The field f is a relation and f' is its converse. *)
type 'a rel = { f : 'a . 'a -> 'a -> bool; f' : 'a . 'a -> 'a -> bool }


(* Normalize an n-ary relation by unchaining *)
let relation 
    simplify_term_node 
    { f = rel; f' = rel' } 
    mk_rel 
    mk_rel' = 
  
  function

    (* Relation must be at least binary *)
    | [] 
    | [_] -> assert false

    (* Relation between integers *)
    | Int _ :: _ as args -> 

      (* Compute relation between constant integer polynomials *)
      let irel p q = 
        rel (const_of_int_polynomial p) (const_of_int_polynomial q) 
      in

      (* Compute converse of relation between constant integer
         polynomials *)
      let irel' p q = 
        rel' (const_of_int_polynomial p) (const_of_int_polynomial q) 
      in

      (* Normalize relation *)
      relation_to_nf 
        simplify_term_node 
        irel 
        irel'
        mk_rel 
        mk_rel' 
        (Int (0, [])) 
        (Term.mk_num_of_int 0)
        args

    (* Relation between reals *)
    | Real _ :: _ as args -> 

      (* Compute relation between constant real polynomials *)
      let rrel p q = 
        rel (const_of_real_polynomial p) (const_of_real_polynomial q) 
      in

      (* Compute converse of relation between constant real
         polynomials *)
      let rrel' p q = 
        rel' (const_of_real_polynomial p) (const_of_real_polynomial q) 
      in

      (* Normalize relation *)
      relation_to_nf 
        simplify_term_node 
        rrel 
        rrel' 
        mk_rel 
        mk_rel' 
        (Real (0., [])) 
        (Term.mk_dec_of_float 0.)
        args

    (* Relation must be between integers or reals *)
    | Bool _ :: _ -> assert false


(* Normalize equality relation between normal forms *)
let relation_eq simplify_term_node args = 
  relation simplify_term_node { f = (=); f' = (=) } Term.mk_eq Term.mk_eq args


(* Normalize less than or equal relation between normal forms *)
let relation_leq simplify_term_node = 
  relation simplify_term_node { f = (<=); f' = (>=) } Term.mk_leq Term.mk_geq 


(* Normalize less than relation between normal forms *)
let relation_lt simplify_term_node = 
  relation simplify_term_node { f = (<); f' = (>) } Term.mk_lt Term.mk_gt


(* Normalize greater than or equal relation between normal forms *)
let relation_geq simplify_term_node = 
  relation simplify_term_node { f = (>=); f' = (<=) } Term.mk_geq Term.mk_leq 


(* Normalize greater than relation between normal forms *)
let relation_gt simplify_term_node = 
  relation simplify_term_node { f = (>); f' = (<) } Term.mk_gt Term.mk_lt 


(* Create an atom of the given term (a variable or an uninterpreted
   function) *)
let atom_of_term t = 

  (* Get type of term *)
  let tt = Term.type_of_term t in 

  (* Term is of type integer *)
  if Type.is_int tt then

    (* Integer polynomial for a variable is (0 + 1 * x) *)
    Int (0, [1, [t]])

        (* Term is of type real *)
  else if Type.is_real tt then

    (* Real polynomial for a variable is (0 + 1 * x) *)
    Real (0., [1., [t]])

         (* Term is of type Boolean *)
  else if Type.is_bool tt then

    (* Variable is an atom *)
    Bool t

    (* Term is of some other type (bitvector or array  *)
  else 

    (* Not implemented *)
    assert false 


(* ********************************************************************** *)
(* Simplify and evaluate functions                                        *)
(* ********************************************************************** *)


(* Simplify a term node to a normal form with arithmetic operations
   evaluated as far as possible 

   This function is recursive, it calls itself with modified
   arguments. It is not tail-recursive, but that is OK, because the
   the recursion depth is shallow. *)
let rec simplify_term_node fterm args = 

  match fterm with 

    (* Free variable *)
    | Term.T.Var v -> atom_of_term (Term.mk_var v)
                   
    (* Polynomial of a constant depends on symbol *)
    | Term.T.Const s -> 
      
      (
        
        (* Unhashcons constant symbol *)
        match Symbol.node_of_symbol s with 

          (* Polynomial for a numeral is n *)
          | `NUMERAL n -> Int (int_of_numeral n, [])

          (* Polynomial for a numeral is n *)
          | `DECIMAL d -> Real (float_of_decimal d, [])

          (* Propositional constant *)
          | `TRUE -> Bool (Term.t_true)
          | `FALSE -> Bool (Term.t_false)

          (* Bitvectors not implemented *)
          | `BV _ -> assert false

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
              | _ -> assert false
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
            simplify_term_node (Term.destruct term') args' 

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
                       (Term.destruct (Term.mk_and [a; nb])) 
                       [Bool a; Bool nb])
                in

                (* Simplify (~a & b) *)
                let term_b' = 
                  bool_of_nf
                    (simplify_term_node 
                       (Term.destruct (Term.mk_and [na; b])) 
                       [Bool na; Bool b])
                in

                (* Simplify ((a & ~b) | (~a & b)) and return *)
                simplify_term_node 
                  (Term.destruct (Term.mk_or [term_a'; term_b']))
                  [Bool term_a'; Bool term_b']

              (* Higher arity exclusive disjunction *)
              | Bool a :: Bool b :: tl -> 

                (* Simplify (a xor b) *)
                let term' = 
                  bool_of_nf
                    (simplify_term_node
                       (Term.destruct (Term.mk_xor [a; b]))
                       [Bool a; Bool b])
                in

                (* Exclusive disjunction is left-associative: simplify
                   first two arguments and recursively simplify
                   exclusive disjunction with remaining arguments *)
                simplify_term_node 
                  (Term.destruct 
                     (Term.mk_xor (term' :: (List.map bool_of_nf tl))))
                  (Bool term' :: tl)

              (* Not well-typed arguments *)
              | Bool _ :: Int _ :: _
              | Bool _ :: Real _ :: _
              | Int _ :: _ 
              | Real _ :: _  -> assert false

            )

          (* Equation *)
          | `EQ -> 
            
            (match args with 
              
              (* Nullary or unary equation *)
              | [] 
              | [_] -> assert false

              (* Binary equivalence, reduce to (a & b) | (~a & ~b) *)
              | [Bool a; Bool b] -> 

                (* Negated normalised arguments *)
                let na, nb = negate_nnf a, negate_nnf b in

                (* Simplify (a & b) *)
                let term_a' = 
                  bool_of_nf 
                    (simplify_term_node 
                       (Term.destruct (Term.mk_and [a; b])) 
                       [Bool a; Bool b])
                in

                (* Simplify (~a & ~b) *)
                let term_b' = 
                  bool_of_nf
                    (simplify_term_node 
                       (Term.destruct (Term.mk_and [na; nb])) 
                       [Bool na; Bool nb])
                in

                (* Simplify ((a & b) | (~a & ~b)) and return *)
                simplify_term_node 
                  (Term.destruct (Term.mk_or [term_a'; term_b']))
                  [Bool term_a'; Bool term_b']

              (* Equation between integers or reals *)
              | _ -> relation_eq simplify_term_node args

            )

          (* Relations *)
          | `LEQ -> relation_leq simplify_term_node args
          | `LT -> relation_lt simplify_term_node args
          | `GEQ -> relation_geq simplify_term_node args
          | `GT -> relation_gt simplify_term_node args

          (* If-then-else *)
          | `ITE -> 

            (match args with 

              (* Choose left branch if predicate is true *)
              | [Bool p; Bool l; _] when p == Term.t_true -> Bool l
              | [Bool p; Int l; _] when p == Term.t_true -> Int l
              | [Bool p; Real l; _] when p == Term.t_true -> Real l

              (* Choose right branch if predicate is false *)
              | [Bool p; _; Bool r] when p == Term.t_false -> Bool r
              | [Bool p; _; Int r] when p == Term.t_false -> Int r
              | [Bool p; _; Real r] when p == Term.t_false -> Real r

              (* Evaluate to a Boolean *)
              | [Bool p; Bool l; Bool r] -> Bool (Term.mk_ite p l r)

              (* Evaluate to an integer atom *)
              | [Bool p; Int l; Int r] -> 

                (atom_of_term
                   (Term.mk_ite 
                      p 
                      (term_of_int_polynomial l) 
                      (term_of_int_polynomial r)))

              (* Evaluate to a real atom *)
              | [Bool p; Real l; Real r] -> 

                  (atom_of_term
                     (Term.mk_ite 
                        p 
                        (term_of_real_polynomial l) 
                        (term_of_real_polynomial r)))

              (* Not well-typed or wrong arity *)
              | _ -> assert false 

            )

          (* Divisibility predicate *)
          | `DIVISIBLE n -> 

            (match args with 

              (* Divisibility is a unary predicate of an integer *)
              | [Int d] -> 
                
                (* Argument is constant? *)
                if is_constant_polynomial d then

                  (if 
                    
                    (* Evaluate (t divisible n) as (= 0 (mod t n)) *)
                    (const_of_polynomial d) mod (int_of_numeral n) = 0 
                    
                   then 
                     
                     (* Simplify to (true) *)
                     Bool Term.t_true 

                   else

                     (* Simplify to (false) *)
                     Bool Term.t_false)
                     
                else
                  
                  (* Divisibility predicate becomes new atom *)
                  atom_of_term 
                    (Term.mk_divisible n (term_of_int_polynomial d))

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
              match List.map const_of_real_polynomial args with 

                (* Integer division must be at least binary *)
                | [] 
                | [_] -> assert false 

                (* Divide first argument by remaining arguments *)
                | h :: tl -> Real ((List.fold_left (/.) h tl), [])

            else

              (* Return a new monomial for non-constant division

                 TODO: `DIV is variadic and left-associative, we
                 could simplify terms like (div 2 2 a) = (div 1 a) and
                 also (div a 2 2) = (div a 1) = a *)
              Int (0, [1, [Term.mk_div (List.map term_of_nf args)]])

          (* Integer division is a monomial with polynomial subterms *)
          | `INTDIV -> 

            (* Evaluate to a polynomial if all arguemnts constant *)
            if List.for_all is_constant args then 

              match List.map const_of_int_polynomial args with 

                (* Integer division must be at least binary *)
                | [] 
                | [_] -> assert false 

                (* Divide first argument by remaining arguments *)
                | h :: tl -> Int ((List.fold_left (/) h tl), [])

            else

               (* Return a new monomial for non-constant division

                  TODO: `INTDIV is variadic and left-associative, we
                  could simplify terms like (div 2 2 a) = (div 1 a)
                  and also (div a 2 2) = (div a 1) = a *)
              Int (0, [1, [Term.mk_intdiv (List.map term_of_nf args)]])

          (* Moudulus is a monomial with polynomial subterms *)
          | `MOD -> 

            (match args with 

              (* Evaluate to a polynomial if both arguments are constant *)
              | [Int (n, []); Int (m, [])] -> Int ((n mod m), [])

              (* Non-constant polynomial arguments *)
              | [a; b] -> 

                (* New polynomial with modulus as atom *)
                Int (0, [1, [Term.mk_mod (term_of_nf a) (term_of_nf b)]])

              (* Modulus is only binary *)
              | _ -> assert false 

            )

          (* Absolute value is a monomial with polynomial subterms *)
          | `ABS -> 

            (match args with 

              (* Evaluate to a polynomial if integer argument is
                 constant *)
              | [Int (n, [])] -> Int ((abs n), [])

              (* Evaluate to a polynomial if real argument is
                 constant *)
              | [Real (d, [])] -> Real ((abs_float d), [])

              (* Non-constant real or integer polynomial argument *)
              | [a] ->

                (* New polynomial with absolute value as atom *)
                Int (0, [1, [Term.mk_abs (term_of_nf a)]])

              (* Absolute value is only unary *)
              | _ -> assert false 

            )

          (* Conversion to integer is a monomial with polynomial
             subterms *)
          | `TO_INT -> 

            (match args with 

              (* Evaluate to a polynomial if real argument is
                 constant *)
              | [Real (d, [])] -> Int (int_of_float (floor d), [])

              (* Non-constant polynomial argument *)
              | [Real _ as a] -> 

                (* New polynomial with integer value as atom *)
                Int (0, [1, [Term.mk_to_int (term_of_nf a)]])

              (* Conversion is only unary *)
              | _ -> assert false 

            )

          (* Conversion to real is a monomial with polynomial
             subterms *)
          | `TO_REAL -> 

            (match args with 

              (* Evaluate to a polynomial if integer argument is
                 constant *)
              | [Int (n, [])] -> Real (float_of_int n, [])

              (* Non-constant polynomial argument *)
              | [Int _ as a] -> 

                (* New polynomial with integer value as atom *)
                Int (0, [1, [Term.mk_to_int (term_of_nf a)]])

              (* Conversion is only unary *)
              | _ -> assert false 

            )

          (* Coincidence of real with integer not implemented *)
          | `IS_INT -> assert false 

          (* Distinct not implemented *)
          | `DISTINCT -> assert false

          (* Bitvectors not implemented *)
          | `BVADD
          | `BVAND
          | `BVDIV
          | `BVLSHR
          | `BVMUL
          | `BVNEG
          | `BVNOT
          | `BVOR
          | `BVSHL
          | `BVULT
          | `BVUREM
          | `CONCAT
          | `EXTRACT _ -> assert false

          (* Array operations not implemented *)
          | `SELECT
          | `STORE -> assert false

          (* Constant symbols *)
          | `TRUE
          | `FALSE
          | `NUMERAL _
          | `DECIMAL _
          | `BV _ -> assert false
            
      )


(* ********************************************************************** *)
(* Top-level functions                                                    *)
(* ********************************************************************** *)


(* Simplify a term *)
let simplify_term term = 

  (* Simplify term to a normal form and convert back to a term *)
  term_of_nf
    (Term.eval_t simplify_term_node term)


(* Simplify a term with a model *)
let simplify_term_model model term = 

  (* Bind variables in the model to their values and simplify term *)
  let term' = Term.mk_let model term in simplify_term term'


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

*)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

