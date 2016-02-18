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

type psummand = Numeral.t * (Var.t option)

type poly = psummand list

type preAtom =
  | GT of poly
  | EQ of poly
  | INEQ of poly
  | DIVISIBLE of (Numeral.t * poly)
  | INDIVISIBLE of (Numeral.t * poly)

type cformula = preAtom list

(* Print summand with absolute value of coefficient, the sign is added
   by pp_print_term' and pp_print_term *)
let pp_print_psummand ppf = function 

  | (c, None) -> Numeral.pp_print_numeral ppf (Numeral.abs c)

  | (c, Some x) when Numeral.(c = one) -> 
    Var.pp_print_var ppf x

  | (c, Some x) when Numeral.(c = (neg one)) -> 
    Var.pp_print_var ppf x

  | (c, Some x) when Numeral.(c >= zero) -> 
    Numeral.pp_print_numeral ppf c; 
    Var.pp_print_var ppf x

  | (c, Some x) -> 
    Numeral.pp_print_numeral ppf (Numeral.abs c); 
    Var.pp_print_var ppf x

let rec pp_print_poly' ppf = function 

  | [] -> ()
    
  (* Second or later term *)
  | ((c, _) as s) :: tl -> 

    (* Print as addition or subtraction *)
    Format.pp_print_string ppf (if Numeral.(c > zero) then "+" else "-");
    Format.pp_print_string ppf " ";
    pp_print_psummand ppf s; 
    Format.pp_print_string ppf " ";
    pp_print_poly' ppf tl


let pp_print_poly ppf = function 

  | ((c, _) as s) :: tl -> 
    if Numeral.(c < zero) then 
      Format.pp_print_string ppf "-";
    pp_print_psummand ppf s;
    Format.pp_print_string ppf " ";
    pp_print_poly' ppf tl

  | _ -> Numeral.pp_print_numeral ppf Numeral.zero


let pp_print_preAtom ppf = function 

  | GT pl ->
    pp_print_poly ppf pl;
    Format.pp_print_string ppf "> 0";

  | EQ pl ->
    pp_print_poly ppf pl;
    Format.pp_print_string ppf "= 0";

  | INEQ pl ->
    pp_print_poly ppf pl;
    Format.pp_print_string ppf "!= 0";

  | DIVISIBLE (i, pl) ->
    Format.pp_open_hbox ppf ();
    Numeral.pp_print_numeral ppf i;
    Format.pp_print_string ppf " | ";
    pp_print_poly ppf pl;
    Format.pp_close_box ppf ()

  | INDIVISIBLE (i, pl) ->
    Format.pp_open_hbox ppf ();
    Numeral.pp_print_numeral ppf i;
    Format.pp_print_string ppf " !| ";
    pp_print_poly ppf pl;
    Format.pp_close_box ppf ()


let rec pp_print_cformula ppf cf = 
  match cf with
  | [] ->
    failwith "pp_print_cformula doesn't handle empty formula."
  
  | [pret] ->
    pp_print_preAtom ppf pret

  | pret::cf' ->
    pp_print_preAtom ppf pret;
    Format.pp_print_newline ppf ();
    Format.pp_print_string ppf " and ";
    pp_print_cformula ppf cf'


(* Compare two presburger summand by the ordering of variables. Used only when polynomials are ordered by the order of variables. *)
let compare_psummands (c: Var.t -> Var.t -> int) (ps1: psummand) (ps2: psummand) : int =

  match ps1, ps2 with
      
    | (_, None), (_, None) -> 0

    | (_, None), (_, Some _) -> 1

    | (_, Some _), (_, None) -> -1

    | (_, Some x1), (_, Some x2) -> c x1 x2



(* Negate a persburger summand. *)
let negate_psummand ((c, v): psummand) : psummand = (Numeral.(- c), v)


(* Negate a presburger term. *)
let negate_poly (pt: poly) : poly =
  List.map negate_psummand pt


(* Multiply a presburger summand with a integer. *)
let psummand_times_num ((c, v): psummand) (i: Numeral.t) : psummand = (Numeral.(c * i), v)

(*
  match ps with
  | (ps_i, None) ->
    (ps_i * i, None)
 
  | (ps_i, Some v) ->
    (ps_i * i, Some v)
*)

(* Multiply a presburger term with a integer. *)
let poly_times_num (pt: poly) (i: Numeral.t) : poly =
  List.map (fun x -> psummand_times_num x i) pt


(* Check if a presburger summand ps contains the variable v. 
   Return true when ps contains v.
   Return false otherwise. *)
let psummand_contains_variable (v: Var.t) (ps: psummand) : bool =

  match ps with 

    | (_, None) -> false
      
    | (_, Some ps_v) ->

      if (Var.compare_vars ps_v v = 0) then 
        (true)
      else 
        (false)


(* Check if a presburger is a constant number. *)
let psummand_is_constant (ps: psummand) : bool =

  match ps with 

    | (_, None) -> true
      
    | (_, Some _) -> false


(* Check if a poly is a constant. *)
let poly_is_constant (pl: poly) : bool =

  match pl with

    | [(i, None)] -> true
      
    | _ -> false


(* Get the coefficient of the variable v in a presburger term. *)
let get_coe_in_poly_anyorder (v: Var.t) (pt: poly) : Numeral.t = 

  try 

    fst(List.find (psummand_contains_variable v) pt) 
      
  with Not_found -> Numeral.zero
    

(* Get the coefficient of the variable v in a presburger term. Can
   only be used when the polynomial is ordered by *)
let get_coe_in_poly_obv (v: Var.t) (pl: poly) : Numeral.t = 

  match pl with

    | (i, Some v1) :: pl' ->
      
      if (Var.equal_vars v1 v) then i else Numeral.zero

    | _ -> Numeral.zero


let get_coe_in_poly v pl = 

  match (Flags.QE.cooper_order_var_by_elim ()) with
      
    | false -> get_coe_in_poly_anyorder v pl

    | true -> get_coe_in_poly_obv v pl


(* Check if a presburger term pret contains the variable v. 
   Return true when pf contains v.
   Return false otherwise. *)
let preAtom_contains_variable (v: Var.t) (pret: preAtom) : bool =

  match pret with

    | GT pl -> 
      Numeral.(get_coe_in_poly v pl <> zero)

    | EQ pl -> 
      Numeral.(get_coe_in_poly v pl <> zero)
        
    | INEQ pl -> 
      Numeral.(get_coe_in_poly v pl <> zero)

    | DIVISIBLE (i, pl) ->
      Numeral.(get_coe_in_poly v pl <> zero)

    | INDIVISIBLE (i, pl) ->
      Numeral.(get_coe_in_poly v pl <> zero)


(* Check if a presburger formula cf contains the variable v. 
   Return true when pf contains v.
   Return false otherwise. *)
let cformula_contains_variable (v: Var.t) (cf: cformula) : bool =

  List.exists 
    (preAtom_contains_variable v)
    cf

      

(* Add two presburger summands when they have the same variable.
   Notice that this function don't check if the variables are
   the same. It uses the variable in ps1 anyway. *)
let add_psummands (ps1: psummand) (ps2: psummand) : psummand =
  
  match ps1, ps2 with

    | (i1, Some v1), (i2, Some v2) -> (Numeral.(i1 + i2), Some v1)
        
    | (i1, None), (i2, None) -> (Numeral.(i1 + i2), None)
      
    | _ -> 
      failwith "Trying to add two summands without the same variable."
        

(* Add two presburger terms.
   The arguments must be sorted before calling this function. 

   We simultaneously consume the two polynomials, constructing an
   accumulator of monomials in descending order. At the end we reverse
   the accumulator. This function is tail-recursive and uses only
   tail-recursive functions. *)
let rec add_two_polys (c: Var.t -> Var.t -> int) (accum: poly) (pt1: poly) (pt2: poly) : poly =

  match pt1, pt2 with

    (* At the end of monomials of the first polynomial *)
    | [], _ -> 

      (* Reverse accumulator and append remaining monomials *)
      List.rev_append accum pt2

    (* At the end of monomials of the second polynomial *)
    | _, [] -> 

      (* Reverse accumulator and append remaining monomials *)
      List.rev_append accum pt1

    (* Take head monomials of both polynomials *)
    | ((c1, v1) as ps1) :: tl1, ((c2, v2) as ps2) :: tl2 ->

      (* Compare head monomials of both polynomials *)
      (match (compare_psummands c ps1 ps2) with

        (* Variables are equal or both are constants *)
        | 0 ->

          (* Add coefficients *)
          let new_summand = (Numeral.(c1 + c2), v1) in
          
          if Numeral.(fst new_summand = zero) then
            
            (* Discard monomial if coefficient is zero *)
            (add_two_polys c accum tl1 tl2)

          else

            (* Add and recurse for the remaining monomials *)
            (add_two_polys c (new_summand :: accum) tl1 tl2)

        (* Head monomial of first polynomial is smaller *)
        | i when i < 0 ->

          (* Add smaller monomial to head of accumulator (will be
             reversed at the end) *)
          (add_two_polys c (ps1 :: accum) tl1 pt2)
            
        (* Head monomial of second polynomial is greater *)
        | _ ->

          (* Add smaller monomial to head of accumulator (will be
             reversed at the end) *)
          (add_two_polys c (ps2 :: accum) pt1 tl2)    

      )
        

(* Add up a list of polynomials *)
let add_poly_list (c: Var.t -> Var.t -> int) (ptl: poly list) : poly = 

  match ptl with

    (* Empty list *)
    | [] -> [(Numeral.zero, None)]
      
    (* Take the head of the list as initial value and add the tail of
       the list *)
    | pt1 :: ptl' -> List.fold_left (add_two_polys c []) pt1 ptl'


(* Multiply two presburger terms when at least one of them is constant. *)
let multiply_two_polys (pt1: poly) (pt2: poly) : poly =

  match pt1, pt2 with

    (* Multiply by zero *)
    | [(c, None)], _ when Numeral.(c = zero) -> [(Numeral.zero, None)]
    | _, [(c, None)] when Numeral.(c = zero) -> [(Numeral.zero, None)]

    (* First polynomial is constant *)
    | [(i, None)], _ -> poly_times_num pt2 i

    (* Second polynomial is constant *)
    | _, [(i, None)] -> poly_times_num pt1 i

    | _ ->
      failwith "Can only multiply two polys when at least one of them is constant."


(* Multiply up a list of presburger terms of at least one element. *)
let multiply_poly_list (ptl: poly list) : poly =

  match ptl with 

    (* Empty list *)
    | [] -> [(Numeral.one, None)]

    (* Take the head of the list as initial value and multiply with
       the tail of the list *)
    | pt1 :: ptl' -> List.fold_left multiply_two_polys pt1 ptl'


(* Comparison of variables: variables to be eliminated earlier are
   smaller, compare as Var.t if none is to be eliminated *)
let rec compare_variables (l: Var.t list) (v1: Var.t) (v2: Var.t) : int =

  (* Order variables by order of elimination? *)
  match (Flags.QE.cooper_order_var_by_elim ()) with

    (* Use ordering on Var *)
    | false -> Var.compare_vars v1 v2

    (* Make variables to be eliminated earlier smaller *)
    | true -> 

      (match l with 

        (* Fall back to comparison if none of the variable is to be eliminated *)
        | [] -> Var.compare_vars v1 v2
          
        | h :: tl -> 

          (* Compare both variables to the first variable to be eliminated *)
          match Var.equal_vars h v1, Var.equal_vars h v2 with
              
            (* Both variable are equal *)
            | true, true -> 0
              
            (* First variable is to be eliminated first *)
            | true, false -> -1

            (* Second variable is to be eliminated first *)
            | false, true -> 1

            (* Recurse to compare with rest of variables to be eliminated *)
            | false, false -> compare_variables tl v1 v2

      )
      

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)


      
