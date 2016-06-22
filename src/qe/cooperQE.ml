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

(** 
@author Ruoyu Zhang
*)

open Poly


(* Utilities *)
(* Print out a model. *)
let pp_print_model ppf model =
  List.iter (
    fun (v, t) ->
      Var.pp_print_var ppf v;
      Format.pp_print_string ppf ": ";
      Term.pp_print_term ppf t;
      Format.pp_print_string ppf "\n"
  ) model


(* Compute the greatest common divisor of integer i1 and i2. *)
let rec greatest_common_divisor (i1: Numeral.t) (i2: Numeral.t) : Numeral.t =
  
  if Numeral.(i2 <> zero) then 
    (greatest_common_divisor i2 Numeral.(i1 mod i2)) 
  else 
    (Numeral.abs i1)


(* Compute the least common multiple of integer i1 and i2. *)
let least_common_multiple (i1: Numeral.t) (i2: Numeral.t) : Numeral.t =
  match i1, i2 with
    | c, x when Numeral.(c = zero) -> x
    | x, c when Numeral.(c = zero) -> x
    | i1, i2 -> Numeral.(abs (i1 * i2) / (greatest_common_divisor i1 i2))


(* Compute the modulo of i1 divided by i2.
   It always returns positive number and smaller than i2. *)
let modulo (i1: Numeral.t) (i2: Numeral.t) : Numeral.t =
  if Numeral.(i1 > zero) then 
    Numeral.(i1 mod i2)
  else 
    Numeral.((i1 mod i2) + i2)


(* Find the least common multiply of all the coefficients of the
   variable in the formula. Return zero if the formula does not occur
   in the formula *)
let find_lcm_in_cformula (v: Var.t) (cf: cformula) : Numeral.t =

  (* Compute lcm from in all conjuncts of the formula *)
  List.fold_left
    
    (fun i pret ->
      
      (* Get polynomial in atom *)
      (match pret with
        | GT pl
        | EQ pl
        | INEQ pl
        | DIVISIBLE (_, pl)
        | INDIVISIBLE (_, pl) ->
          
          (* Get coefficient for variable in atom *)
          let coe = get_coe_in_poly v pl in
          
          (* Variable does not occur in atom? *)
          if Numeral.(coe = zero) then 

            (* Return previous least common multiple *)
            i

          else 

            (* First occurrence of the variable *)
            if Numeral.(i = zero) then

              (* Return the absolute value of the coefficient *)
              (Numeral.abs coe)

            else

              (* Compute lcm with previous occurrences of the variable *)
              least_common_multiple i coe
      )
    ) 
    Numeral.zero 
    cf


(*
(* Find the least common multiply of all the divider*)
let find_div_lcm_in_cformula (v: Term.term) (cf: cformula) : int =
  match cf with 
  | [] ->
    0

  | _ ->
    List.fold_left(
      fun i pret ->
      (match pret with
      | GT pl ->
        i

      | DIVISIBLE (div, pl) ->
        let coe = get_coe_in_poly v pl in
        if (coe = 0)
        then (i)
        else (least_common_multiple i div)

      | INDIVISIBLE (div, pl) ->
        let coe = get_coe_in_poly v pl in
        if (coe = 0)
        then (i)
        else (least_common_multiple i div)
      )
    ) 1 cf
*)

(* Multiply the Presburger polynomial so that the absolute value of
   the coefficient of v is equal to lcm, preserving the sign of the
   coefficient. *)
let scale_coefficient_in_poly (v: Var.t) (lcm: Numeral.t) (pt: poly) : poly = 

  let coe = get_coe_in_poly v pt in
  
  match coe with
      
    | i when Numeral.(i = zero) -> pt
      
    | i when Numeral.(i > zero) ->

      (* Scale polynomial with lcm/coe, this is a positive number *)
      multiply_two_polys pt [(Numeral.(lcm / coe), None)]
        
    | i when Numeral.(i < zero) ->

      (* Scale polynomial with -lcm/coe, this is a positive number,
         since coe is negative *)
      multiply_two_polys pt [(Numeral.((neg one) * lcm / coe), None)]
        
    | _ -> 
      failwith "Impossible case for scale_coefficient_in_poly."


(* Multiply the Presburger term so that the coefficient of the
   variable to be eliminated is equal to least common multiple of the
   coefficents of all occurrences of the variable. *)
let scale_coefficient_in_preAtom (v: Var.t) (lcm: Numeral.t) (pret: preAtom) : preAtom = 

  match pret with
      
    (* Scale greater-than atom *)
    | GT pl -> GT (scale_coefficient_in_poly v lcm pl)
      
    (* Scale equation *)
    | EQ pl -> EQ (scale_coefficient_in_poly v lcm pl)
       
    (* Scale inequation atom *)
    | INEQ pl -> INEQ (scale_coefficient_in_poly v lcm pl)
      
    (* Scale divisibility atom *)
    | DIVISIBLE (i, pl) ->
      
      (* Get coefficient of variable to scale the constant in the
         divisibility predicate *)
      let coe = get_coe_in_poly v pl in
      
      (match coe with

        (* Prevent division by zero, return unchanged *)
        | i when Numeral.(i = zero) -> pret
          
        | _ -> 
          
          (* Also scale the constant in divisibility predicate *)
          DIVISIBLE (Numeral.(i * abs (lcm / coe)), scale_coefficient_in_poly v lcm pl)
      )
        
    (* Scale indivisibility atom *)
    | INDIVISIBLE (i, pl) ->
      
      (* Get coefficient of variable to scale the constant in the
         divisibility predicate *)
      let coe = get_coe_in_poly v pl in
      
      (match coe with
          
        (* Prevent division by zero, return unchanged *)
        | i when Numeral.(i = zero) -> pret
          
        | _ -> INDIVISIBLE 
          
          (* Also scale the constant in divisibility predicate *)
          (Numeral.(i * abs (lcm / coe)), scale_coefficient_in_poly v lcm pl)
          
      )


(* Multiply the Presburger formula so that the coefficient of v is
   equal to the lcm in each Presburger atom. *)
let scale_coefficient_in_cformula (v: Var.t) (lcm: Numeral.t) (cf: cformula) : cformula =

  (* Least common multiple must be positive *)
  if Numeral.(lcm <= zero) then assert false else 

    if Numeral.(lcm = one) then 
      
      (* Do not add trivial divisibility predicates (1 | x), do not
         scale the formula *)
      cf
        
    else
      
      (* Add new divisibility predicate and scale formulas *)
      ((DIVISIBLE (lcm, [lcm, Some v])) :: 
          List.map (scale_coefficient_in_preAtom v lcm) cf)

    
(* Substitute a variable with a Presburger term pt1 in a Presburger
   term pt2. *)
let substitute_variable_in_poly (c: Var.t -> Var.t -> int) (v: Var.t) (pt1: poly) (pt2: poly) : poly =

  if Numeral.(get_coe_in_poly v pt2 = zero) then 

    (* Skip if monomial has coefficient zero *)
    (pt2)

  else 

    (* Remove monomial to be substituted from polynomial and add
       scaled substitution to it *)
    (add_two_polys 
       c 
       []
       (multiply_two_polys pt1 [(get_coe_in_poly v pt2, None)]) 
       (List.filter (fun x -> not (psummand_contains_variable v x)) pt2))


(* Substitute a variable with a Presburger term pt in a Presburger
   formula pf. *)
let substitute_variable_in_preAtom (c: Var.t -> Var.t -> int) (v: Var.t) (pl: poly) (pret: preAtom) : preAtom =

  (* Propagate substitution to polynomial in formula *)
  match pret with
    
    | GT pl' -> GT (substitute_variable_in_poly c v pl pl')

    | EQ pl' -> EQ (substitute_variable_in_poly c v pl pl')

    | INEQ pl' -> INEQ (substitute_variable_in_poly c v pl pl')
        
    | DIVISIBLE (i, pl') ->
      
      DIVISIBLE (i, substitute_variable_in_poly c v pl pl')

    | INDIVISIBLE (i, pl') ->
      
      INDIVISIBLE (i, substitute_variable_in_poly c v pl pl')


(* Substitute a variable with a Presburger term pl in a Presburger
   formula cf. *)
let substitute_variable_in_cformula (c: Var.t -> Var.t -> int) (v: Var.t) (pl: poly) (cf: cformula) : cformula =
  
  (* Substitute in all atoms *)
  List.map (substitute_variable_in_preAtom c v pl) cf


(* Substitute a polynomial for a monomial containing the variable to
   be eliminated *)
let substitute_summand_in_poly (c: Var.t -> Var.t -> int) (v: Var.t) (pt1: poly) (pt2: poly) : poly =

  match get_coe_in_poly v pt2 with

    (* Skip if variable has coefficient zero *)
    | i when Numeral.(i = zero) -> pt2
      
    | i when Numeral.(i > zero) ->
      
      add_two_polys c []
        pt1
        (List.filter (fun x -> not (psummand_contains_variable v x)) pt2)
        
    | i when Numeral.(i < zero) ->
      
      add_two_polys c []
        (negate_poly pt1)
        (List.filter (fun x -> not (psummand_contains_variable v x)) pt2)

    | _ ->
      failwith "Unexpected value found in substitute_summand_in_poly"


(* Substitute a variable with a polynomial pl in a Presburger term pret
   regardless of the coefficient of v in pret. *)
let substitute_summand_in_preAtom (c: Var.t -> Var.t -> int) (v: Var.t) (pl: poly) (pret: preAtom) : preAtom = 
  match pret with
  | GT pl' ->
    GT (substitute_summand_in_poly c v pl pl')

  | EQ pl' ->
    EQ (substitute_summand_in_poly c v pl pl')

  | INEQ pl' ->
    INEQ (substitute_summand_in_poly c v pl pl')

  | DIVISIBLE (i, pl') ->
    DIVISIBLE (i, substitute_summand_in_poly c v pl pl')

  | INDIVISIBLE (i, pl') ->
    INDIVISIBLE (i, substitute_summand_in_poly c v pl pl') 


(* Substitute a variable with a Presburger term pt in a Presburger formula cf
   regardless of the coefficient of v in pf. *)
let substitute_summand_in_cformula (c: Var.t -> Var.t -> int) (v: Var.t) (pl: poly) (cf: cformula) : cformula =
  List.map (substitute_summand_in_preAtom c v pl) cf


(* Evaluate a poly pt with the model. *)
let eval_poly model (pt: poly) : Numeral.t = 
  List.fold_left (
    fun accum (coe, v) ->
      match v with
      | None ->
        Numeral.(accum + coe)

      | Some v -> 
        (* (debug qe_detailed
           "eval_poly: Model is @[<v>%a@]"
           pp_print_model model
         end); *)
        Numeral.(accum + coe * (Eval.num_of_value (Eval.eval_term [] model (Term.mk_var v))))
  ) 
    Numeral.zero
    pt


(* Find the maximum poly in the poly list. *)
let find_max_in_poly_list model (ptl: poly list) : poly =
  match ptl with
  | [] ->
    failwith "find_max_in_poly_list doesn't take empty list."

  | pt::ptl' ->
    List.fold_left(
      fun accum pt1 ->
        if Numeral.(eval_poly model accum > eval_poly model pt1)
        then (
          accum)
        else (
          pt1)
    ) pt ptl'

(*
(* FIXME *)
(* Not used for the moment. *)
(* Find a list of lower bounds for variable v and its priority 
   in the Presburger formula cf.  The formula should be already 
   been scaled with scale_coefficient_in_cformula before using 
   this function. *)
let find_all_lower_bounds_in_cformula (c: Term.term -> Term.term -> int) (v: Term.term) (cf: cformula) : (poly * int) list =

  List.fold_left 
    (fun l pret ->
      (match pret with 

        (* Greater than relation *)
        | GT pl ->
          
          (* Coefficient of [v] is positive, inequation is a lower
             bound for [v] *)
          if get_coe_in_poly v pl > 0 then 

            (
	      
              (* For the inequation lcm_coe*v + t > 0 the lower bound
                 is lcm_coe*v >= -t + 1, add this as a possible lower
                 bound *)
              let lb = 
                (add_two_polys 
                   c 
                   [] 
                   ([1, None]) 
                   (negate_poly 
                      (List.filter 
                         (fun x -> not (psummand_contains_variable v x)) pl))) in

              (* If the lower bound is a constant, it has priority of 1. *)
              if poly_is_constant lb then

                ((lb, 0):: l)

              (* If the lower bound is not a constant, it has priority of -1. *)
              else

                ((lb, 1) :: l)
            )

          (* Coefficient of [v] is negative or zero, inequation is an
             upper bound for [v] or does not contain [v] *)
          else 
            
            (* Return previous lower bounds *)
            l
              
        (* Equation *)
        | EQ pl -> 

          (* Variable occurs in the equation *)
          if get_coe_in_poly v pl <> 0 then 

            (

              (* For an equation lcm_coe*v + t = 0 the lower bound is
                 lcm_coe*v >= -t, add this as a possible lower
                 bound *)
              let lb = 
                (negate_poly 
                   (List.filter 
                      (fun x -> not (psummand_contains_variable v x)) pl)) in
               
              (* If the lower bound is a constant, it has priority of -2. *)
              if poly_is_constant lb then

                ((lb, 2):: l)

              (* If the lower bound is not a constant, it has priority of -3. *)
              else

                ((lb, 3) :: l)

            )

          (* Coefficient of [v] is zero, equation does not contain
             [v] *)
          else 
            
            (* Return previous lower bounds *)
            l

        (* Inequation *)
        | INEQ pl ->
          
          (* Variable occurs in the equation *)
          if (get_coe_in_poly v pl <> 0) then 

            (

              (* For an inequation lcm_coe*v + t != 0 the lower bound is
                 lcm_coe*v >= -t + 1, add this as a possible lower
                 bound *)
              let lb = 
                (add_two_polys 
                   c 
                   [] 
                   ([1, None]) 
                   (negate_poly 
                      (List.filter 
                         (fun x -> not (psummand_contains_variable v x)) 
                         pl))) in
              

              (* If the lower bound is a constant, it has priority of 0. *)
              if poly_is_constant lb then

                ((lb, 0):: l)

              (* If the lower bound is not a constant, it has priority of -1. *)
              else

                ((lb, 1) :: l)

            )

          (* Coefficient of [v] is zero, inequation does not contain
             [v] *)
          else 

            (* Return previous lower bounds *)
            l

        (* No lower bounds from divisibility and indivisibility atoms *)
        | DIVISIBLE _ 
        | INDIVISIBLE _ -> l
          
      )

    ) 
    [] 
    cf
*)


(* Find a list of lower bounds for variable v in the Presburger formula cf.  
   The formula should be already been scaled with scale_coefficient_in_cformula 
   before using this function. *)
let rec find_rough_lower_bounds_in_cformula (c: Var.t -> Var.t -> int) (v: Var.t) (cf: cformula) (l: poly list) : poly list=
  match cf with
  | [] ->
    
    l

  | (GT pl) :: cf' ->
    
    if Numeral.(get_coe_in_poly v pl > zero) then

      (
        (* For the inequation lcm_coe*v + t > 0 the lower bound
           is lcm_coe*v >= -t + 1, add this as a possible lower
           bound *)
        let lb = 
          (add_two_polys 
            c 
            [] 
            ([Numeral.one, None]) 
            (negate_poly 
              (List.filter (fun x -> not (psummand_contains_variable v x)) pl))
          ) in
        
        find_rough_lower_bounds_in_cformula c v cf' (lb :: l)
      )

    else

      find_rough_lower_bounds_in_cformula c v cf' l


  | (EQ pl) :: cf' ->

    if Numeral.(get_coe_in_poly v pl > zero) then

      (* For the inequation lcm_coe*v + t = 0 the lower bound
         is lcm_coe*v >= -t, immediately return this lower bound *)
      let lb = 
        (negate_poly 
          (List.filter 
            (fun x -> not (psummand_contains_variable v x)) pl)) in

      [lb]

    else if Numeral.(get_coe_in_poly v pl < zero) then

      (* For the inequation -lcm_coe*v + t = 0 the lower bound
         is lcm_coe*v >= t, immediately return this lower bound *)

      let lb = 
          (List.filter 
            (fun x -> not (psummand_contains_variable v x)) pl) in

      [lb]

    else 

      find_rough_lower_bounds_in_cformula c v cf' l

(*
  | (INEQ pl) :: cf' ->

      if get_coe_in_poly v pl > 0 then

      (
        (* For the inequation lcm_coe*v + t != 0 the lower bound
           is lcm_coe*v >= -t + 1, add this as a possible lower
           bound *)
        let lb = 
          (add_two_polys 
            c 
            [] 
            ([1, None]) 
            (negate_poly 
              (List.filter (fun x -> not (psummand_contains_variable v x)) pl))
          ) in
        
        find_rough_lower_bounds_in_cformula c v cf' (lb :: l)
      )

    else if get_coe_in_poly v pl < 0 then

      (
        (* For the inequation -lcm_coe*v + t != 0 the lower bound
           is lcm_coe*v >= t + 1, add this as a possible lower
           bound *)
        let lb = 
          (add_two_polys 
            c 
            [] 
            ([1, None]) 
            (List.filter (fun x -> not (psummand_contains_variable v x)) pl)
          ) in
        
        find_rough_lower_bounds_in_cformula c v cf' (lb :: l)
      )

    else 

      find_rough_lower_bounds_in_cformula c v cf' l

*)
  | INEQ _ :: cf' 
  | (DIVISIBLE _) :: cf'
  | (INDIVISIBLE _) :: cf' ->

     find_rough_lower_bounds_in_cformula c v cf' l
    

    
(*
(* Find the first poly dividable by lcm according to the model. *)
let rec find_dividable_lower_bound (c: Term.term -> Term.term -> int) (model: (Term.term * Term.term) list) (lcm: int) (pt: poly) : poly = 
  if ((eval_poly model pt) mod lcm = 0)
  then (
    pt
  )
  else (
    find_dividable_lower_bound c model lcm (add_two_polys c [] pt [1, None])
  )
*)


(* Use the model to compute a polynomal that satisfies the formula
   including all divisibility constraints *)
let find_divisible_lower_bound (c: Var.t -> Var.t -> int) 
  model (v: Var.t) (coe_lcm: Numeral.t) (pl: poly) : poly = 

  (* (debug qe_detailed
     "find_divisible_lower_bound for %a...@."
     Term.pp_print_term (Term.mk_var v)
     end); *)

  (* Compute an offset 
     
     j = coe_lcm * eval(v) - eval(pl)
     
     that satisfies the formula, based on the model we have.
  *)
  let j = 
    
    (* Evaluate variable in the model *)
    Numeral.((Eval.num_of_value (Eval.eval_term [] model (Term.mk_var v))) * 

             (* Multiply with the lcm coefficient *)
             coe_lcm - 
             
             (* Subtract value of the lower bound in the model *)
             (eval_poly model pl))

  in
  
  (* Add the offset to the polynomial *)
  add_two_polys c [] pl [j, None]


(* Return the first non-constant polynomial *)
let rec find_general_poly (l: poly list) : poly =

  match l with
      
    | [] -> raise Not_found
      
    | pl :: l' ->
      
      (* Skip over constant polynomials *)
      if poly_is_constant pl then find_general_poly l' else pl


(* Find a lower bound for the variable [v] to be eliminated in the
   Presburger formula [cf]. All occurrences of the variable [v] must
   have the coefficient [coe_lcm]. *)
let find_lower_bound_in_cformula (c: Var.t -> Var.t -> int) 
  model (v: Var.t) (coe_lcm: Numeral.t) (cf: cformula) : poly =

  (* Find all lower bounds for the variable to be eliminated *)
  let lower_bounds = find_rough_lower_bounds_in_cformula c v cf [] in

  (* No lower bound for variable? *)
  if lower_bounds = [] then

    (* Signal the infinitely small case *)
    (raise Not_found)
      
  else 

    (find_divisible_lower_bound c model v coe_lcm (List.hd lower_bounds))

      
(* Variable to be eliminated can be infinitely small: remove all
   inequations with the variable to be eliminated, since they can be
   satisfied and that substitute the variable with its actual value in the
   model in all remaining constraints. *)
let handle_infinitely_small_case (c: Var.t -> Var.t -> int) 
    model (v: Var.t) (cf: cformula) : cformula = 
  
  (* Filter for atoms that do not contain the variable to be
     eliminated *)
  let cf' = 
    List.filter 
      (function 
        | GT pl -> Numeral.(get_coe_in_poly v pl = zero)
        | EQ pl -> Numeral.(get_coe_in_poly v pl = zero)
        | INEQ pl -> Numeral.(get_coe_in_poly v pl = zero)
        | _ -> true
      )
      cf 
  in
  
  (* Substitute coe_lcm*v with its value in the model *)
  substitute_variable_in_cformula 
    c 
    v 
    [(Eval.num_of_value (Eval.eval_term [] model (Term.mk_var v))), None] 
    cf'


(* Check if the Presburger atom is trivial. Because all the atoms we
   have should be satisfied by the model.When the atom is trivial,
   it's trivially true. *)
let preAtom_is_trivial (pret: preAtom) : bool = 

  match pret with
      
    (* Eliminate t > 0 when t is a constant > 0 *)
    | GT [(c, None)] when Numeral.(c > zero) -> true
    
    (* Eliminate t = 0 when t is the constant 0 *)
    | EQ [(c, None)] when Numeral.(c = zero) -> true
      
    (* Eliminate t != 0 when t a constant != 0 *)
    | INEQ [(c, None)] when Numeral.(c <> zero) -> true

    (* Eliminate 1 | t *)
    | DIVISIBLE (c, _) when Numeral.(c = one)-> true

    (* Eliminate i | t when t is a constant s.t. t mod i = 0 *)
    | DIVISIBLE (i, [(c, None)]) -> Numeral.(c mod i = zero)
                         
    (* Eliminate i !| t when t is a constant s.t. t mod i != 0 *)
    | INDIVISIBLE (i, [(c, None)]) -> Numeral.(c mod i <> zero)

    | _ -> false


(* Quantifier elimination for variable v in formula cf. *)
let eliminate_variable_in_cformula (c: Var.t -> Var.t -> int) 
    model (v: Var.t) (cf: cformula) : cformula =

  (debug qe_detailed
     "Eliminating variable %a: @."
     Term.pp_print_term (Term.mk_var v)
   end);

  (* Find the least common multiple of the coefficient of all
     occurrences of the variable *)
  let coe_lcm = find_lcm_in_cformula v cf in
  
  (debug qe_detailed
     "The coe_lcm on %a is %a" 
     Term.pp_print_term (Term.mk_var v)
     Numeral.pp_print_numeral coe_lcm
   end);

  (* Variable does not occur in formula, then return unchanged *)
  if Numeral.(coe_lcm = zero) then cf else
    
    (* Scale atom to have all occurrences of the variable to be
       eliminated with the same coefficient *)
    let scf = scale_coefficient_in_cformula v coe_lcm cf in
    
    (debug qe_detailed
       "Scaling formula to:@. @[<hv>%a@]@;" 
       Poly.pp_print_cformula scf
     end);
    
    try

      (
        
        (* Compute polynomial to eliminate the variable with *)
        let lower_bound = 
          find_lower_bound_in_cformula c model v coe_lcm scf 
        in
        
        (debug qe_detailed
           "@[<hv>The lowerbound is:@ @[<v>%a@]@]@."
           Poly.pp_print_poly lower_bound
         end);

        (* Substitute polynomial for all occurrences of coe_lcm*v *)
        let ret = substitute_summand_in_cformula c v lower_bound scf in
        
        (debug qe_detailed
           "@[<hv>The result is:@ @[<v>%a@]@]@."
           Poly.pp_print_cformula ret
         end);
        
        (* Filter out all trivial atoms *)
        List.filter (fun x -> not (preAtom_is_trivial x)) ret

      )
        
    (* No lower bound for the variable to be eliminated *)
    with Not_found -> 

      (debug qe_detailed
         "No lowerbound found.@."
       end);
      
      let ret = handle_infinitely_small_case c model v scf in

      (debug qe_detailed
         "@[<hv>The result is:@ @[<v>%a@]@]@."
         Poly.pp_print_cformula ret
       end);
      
      (* Filter out all trivial atoms *)
      List.filter (fun x -> not (preAtom_is_trivial x)) ret



(* Eliminate a list of existentially quantified variables *)
let rec eliminate model (v: Var.t list) (cf: cformula) : cformula = 

  let c = compare_variables v in 

  match v with
    
    (* No more variables to be eliminated *)
    | [] -> cf

    (* Take first variable to be eliminated *)
    | v :: l' -> 

      (* Eliminate first variable *)
      let ret = eliminate_variable_in_cformula c model v cf in
      
      (* Eliminate remaining variables *)
      eliminate model l' ret


(*
let test = 
  
  Format.printf "To Presburger@.";
  let v = UfSymbol.mk_uf_symbol "v" [Type.Int] Type.Int true in
  let v0 = Term.mk_uf v [Term.mk_num_of_int 0] in
  let v1 = Term.mk_uf v [Term.mk_num_of_int 1] in
  let v2 = Term.mk_uf v [Term.mk_num_of_int 2] in
  let v3 = Term.mk_uf v [Term.mk_num_of_int 3] in
  let v4 = Term.mk_uf v [Term.mk_num_of_int 4] in
  let v5 = Term.mk_uf v [Term.mk_num_of_int 5] in

  let one = Term.mk_num_of_int 1 in
  let two = Term.mk_num_of_int 2 in
  let three = Term.mk_num_of_int 3 in

  let model = [(v0, two); (v1, one); (v2,  three); (v3, two); (v4, one); (v5, three)] in
  
  
  let pl1 = [(2, Some v1); (3, Some v2); (-4, Some v3)] in
  let pl2 = [(7, None); (2, Some v3); (1, Some v4); (3, Some v5)] in

  Format.printf "pl1 is:@. @[<hv>%a@]@;" Term.pp_print_term (term_of_poly pl1);
  (* Format.printf "It's value is:@. @[<hv>%a@]@;" Format.pp_print_int (eval_poly model pl1); *)
  Format.printf "pl2 is:@. @[<hv>%a@]@;" Term.pp_print_term (term_of_poly pl2);
  (* Format.printf "It's value is:@. @[<hv>%a@]@;" Format.pp_print_int (eval_poly model pl2); *)

  let cf1 = [DIVISIBLE (3,pl1); DIVISIBLE (7,pl2); GT (pl1); GT (pl2)] in
  Format.printf "cf1 is:@. @[<hv>%a@]@;" Presburger.pp_print_cformula cf1;
  
  let test_substitute1 = substitute_variable_in_cformula v1 [(2, Some v0)] cf1 in
  Format.printf "substitute variable v1 with 2v0:@. @[<hv>%a@]@;" Presburger.pp_print_cformula test_substitute1;

  let test_substitute2 = substitute_summand_in_cformula v1 [(2, Some v0)] cf1 in
  Format.printf "substitute summands of v1 with 2v0:@. @[<hv>%a@]@;" Presburger.pp_print_cformula test_substitute2;
  (*
  let result1 = eliminate_variable_in_cformula model v3 cf1 in
  Format.printf "Eliminating v3:@. @[<hv>%a@]@;" Presburger.pp_print_cformula result1;
  *)
 
  (*
  let test_negate = negate_poly pt1 in
  let test_times =  poly_times_int pt1 5 in
  let test_get_coe1 = get_coe_in_poly v1 pt1 in
  let test_get_coe2 = get_coe_in_poly v5 pt1 in
  let test_get_con = get_constant_summand_in_poly pt1 in
  let test_add_psum = add_psummands (2, Some v1) (3, Some v1) in
  let test_add_poly = add_two_polys [] pt1 pt2 in

  Format.printf "Comparing v1 with v2:@. %i@;" (Term.compare_terms v1 v2);
  Format.printf "Comparing v1 with v1:@. %i@;" (Term.compare_terms v1 v1);

  Format.printf "Comparing 2v1 with 3v2:@. %i@;" (compare_psummands (2, Some v1) (3, Some v2));
  Format.printf "Comparing 2v1 with 3v1:@. %i@;" (compare_psummands (2, Some v1) (3, Some v1));
  Format.printf "Comparing 2v1 with 3:@. %i@;" (compare_psummands (2, Some v1) (3, None));

  Format.printf "Negate pt1:@. @[<hv>%a@]@;" Term.pp_print_term (term_of_poly test_negate);
  Format.printf "pt1 times 5:@. @[<hv>%a@]@;" Term.pp_print_term (term_of_poly test_times);
  Format.printf "Get coe of v1 in pt1:@. %i@;" test_get_coe1;
  Format.printf "Get coe of v5 in pt1:@. %i@;" test_get_coe2;
  Format.printf "Get con of v1 in pt1:@. %i@;" test_get_con;
  Format.printf "Add 2v1 with 3v1:@. @[<hv>%a@]@;" Term.pp_print_term (convert_psummand_to_presburger_term test_add_psum);
  Format.printf "Add pt1 with pt2:@. @[<hv>%a@]@;" Term.pp_print_term (term_of_poly test_add_poly);
  *)

  (*
  let test_term1 = Term.mk_plus [Term.mk_minus [Term.mk_plus [Term.mk_times [two; Term.mk_times [three; v1]]; Term.mk_times [two; Term.mk_times [two; v2]]]; one]; Term.mk_times [three; v1]] in
  let test_term2 = Term.mk_plus [Term.mk_plus [Term.mk_plus [Term.mk_times [two; Term.mk_times [three; v2]]; Term.mk_times [two; Term.mk_times [two; v3]]]; two]; Term.mk_times [three; v1]] in
  let test_term3 = Term.mk_leq [test_term1; test_term2] in

  let test_term4 = Term.mk_plus[Term.mk_times [two; Term.mk_times [three; v1]]; Term.mk_times [three; v2]; Term.mk_times [three; v3]; two] in
  let test_term5 = Term.mk_plus[Term.mk_times [two; Term.mk_times [one; v4]]; Term.mk_times [two; v5]; Term.mk_times [three; v3]; one] in
  let test_term6 = Term.mk_gt [test_term4; test_term5] in

  let test_term7 = Term.mk_plus[Term.mk_times [two; Term.mk_times [three; v1]]; Term.mk_times [two; v2]; Term.mk_times [three; v3]; two] in
  let test_term8 = Term.mk_plus[Term.mk_times [two; Term.mk_times [one; v2]]; Term.mk_times [two; v5]; Term.mk_times [three; v3]; three] in
  let test_term9 = Term.mk_geq [test_term7; test_term8] in

  let test_term10 = Term.mk_plus[Term.mk_times [two; Term.mk_times [three; v1]]; Term.mk_times [two; v2]; Term.mk_times [three; v3]; two] in
  let test_term11 = Term.mk_plus[Term.mk_times [two; Term.mk_times [three; v1]]; Term.mk_times [two; v2]; Term.mk_times [three; v3]; two] in
  let test_term12 = Term.mk_gt [test_term10; test_term11] in
  
  let test_term13 = Term.mk_divisible (Lib.numeral_of_int 4) test_term4 in
  let test_term14 = Term.mk_divisible (Lib.numeral_of_int 2) test_term8 in

  let test_term0 = Term.mk_and [Term.mk_not test_term3; test_term6; test_term9; test_term12; test_term13; test_term14] in
  
  Format.printf "The test term is:@. @[<hv>%a@]@;" Term.pp_print_term test_term0;
  
  let n_formula = to_presburger_c test_term0 in
  Format.printf "After normalization:@. @[<hv>%a@]@;" Presburger.pp_print_cformula n_formula
  *)

(*
let to_presburger term = 
  convert_poly_to_presburger_atom (atom_term_to_poly term) 

let num = Term.mk_num_of_int 
let u s = UfSymbol.mk_uf_symbol s [Type.Int] Type.Int 
let var s i = Term.mk_uf (u s) [num i] 
let leq l r = Term.mk_leq [l; r] 
let lt l r = Term.mk_lt [l; r] 
let geq l r = Term.mk_geq [l; r] 
let gt l r = Term.mk_gt [l; r] 
let plus a b = Term.mk_plus [a; b] 
let minus a b = Term.mk_minus [a; b] 
let times a b = Term.mk_times [a; b] 

let main () = 

  (*
  Format.printf 
    "@[<h>%a@]@."
    pp_print_poly [((+ 0), Some (var "x" 0)); ((+ 1), Some (var "x" 1))];
  *)

  let t = 
    (* geq (num 0) (num 1) *)
    (* leq (num 0) (num 1) *)
    (* leq (var "x" 0)  (var "x" 1) *)
    (* lt (var "x" 0)  (var "x" 1) *)
    (* geq (num 0) (var "x" 0) *)
    (* geq (var "x" 0) (num 0) *)
    geq (var "x" 0) (num 0)
  in

  Format.printf 
    "The original formula is:@. %a@."
    Term.pp_print_term t;


  let pt = atom_term_to_poly t in
  
  Format.printf 
    "After tp presburger:@. @[<h>%a@]@."
    pp_print_poly pt

  

(*
  let pt = to_presburger t in
  
  Format.printf 
    "%a@."
    Term.pp_print_term pt
*)
  
;;

main ()

*)
*)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)


