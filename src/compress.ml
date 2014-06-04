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


(* Given a list of lists of equal length return a list of lists, where
   the n-th list contains the n-th elements of each list.

   This function is tail-recursive and returns the elements in reverse order:
   [[11;12];[21;22];[31;32]] becomes [[32; 22; 12]; [31; 21; 11]].

   Raise Invalid_argument "list_transpose" if lists are of different
   length. *)
let list_transpose = 

  let rec list_transpose' accum = 

    let rec list_transpose'' accum = function 

      | [] -> 

        (function 
          | [] -> List.rev accum
          | _ -> invalid_arg "list_transpose")

      | h :: tla ->

        (function 
          | [] -> invalid_arg "list_transpose"

          | e :: tll -> list_transpose'' ((e :: h) :: accum) tla tll)

    in

    function
      | [] -> List.rev accum

      | l :: tl -> 

        let accum' = list_transpose'' [] accum l in

        list_transpose' accum' tl

  in

  function 

    (* Handle empty list *)
    | [] -> []

    (* First element in list determines length of result list *)
    | h :: _ as l -> 

      list_transpose' (List.map (fun _ -> []) h) l


(* Apply function to all unordered pairs in the list and return
   results in a list

   [fold_pairs f [e_1; ...; e_n]] computes [r_12 = f e_1 e_2], ...
   [r_1n = f e_1 e_n], [r_23 = f e_2 e_3], ..., [r_n-1n = f e_n-1
   e_n] in this order and returns the list [r_n-1n, ..., r_12]. 

   The empty list is returned if [l] has less than two elements. *)
let fold_pairs f accum l = 

  let rec fold_pairs' f accum l = function
    
    | [] | [_] -> 
      
      (match l with 
        | [] | [_] -> accum 
        | h :: tl -> fold_pairs' f accum tl tl)
      
    | h :: s :: tl -> 
      
      fold_pairs' f (f accum h s) l (h :: tl)

  in

  fold_pairs' f accum l l


(* Apply predicate on all unordered pairs in the list and return
   true iff the predicate is true on at least one pair

   [exists_pair p [e_1; ...; e_n]] checks [p e_1 e_2], ... 
   [p e_1 e_n], [p e_2 e_3], ..., [p e_n-1 e_n] in this order 
   and returns true as soon as one of them is true. 

   [false] is returned if [l] has less than two elements. *)
let exists_pair p l = 

  let rec exists_pair' p l = function 

    | [] | [_] -> 

      (match l with 

        | [] | [_] -> false
        | h :: tl -> exists_pair' p tl tl)

    | h :: s :: tl -> 

      if p h s then true else exists_pair' p l (h :: tl)

  in

  exists_pair' p l l


(* States are equivalent if for each variable the variable is either
   an input or the values are equal *)
let equal_mod_input accum s1 s2 = 

  if

    (* Check if states are equivalent *)
    List.for_all2

      (fun (v1, t1) (v2, t2) -> 

         let sv1 = Var.state_var_of_state_var_instance v1 in

         (* Make sure we're talking about the same state variable *)
         assert  
           (StateVar.equal_state_vars
              sv1
              (Var.state_var_of_state_var_instance v2));

         (* States are equivalent if state variable is an input or
            values are equal *)
         StateVar.is_input sv1 || Term.equal t1 t2) 

      s1 
      s2 

  then 

    (

      (* Count number of clauses *)
      Stat.incr Stat.ind_compress_clauses;

      (* Generate disjunction of disequalities and add to accumulator *)
      Term.mk_or

        (List.fold_left2
           (fun a (v1, _) (v2, _) -> 

              let sv1 = Var.state_var_of_state_var_instance v1 in

              (* Skip input variables *)
              if not (StateVar.is_input sv1) then 

                (* Disequality between state variables at instants *)
                Term.negate 
                  (Term.mk_eq 
                     [Term.mk_var v1; Term.mk_var v2]) :: a 

              else a)
           []
           s1
           s2) 

      :: accum

    )

  (* States are not equivalent *)
  else accum


(* Generate blocking terms from all equivalent states *)
let check_and_block cex = 

  (* Convert counterexample to list of lists of pairs of variable at
     instant and its value *)
  let states = 
    list_transpose
      (List.map
         (fun (sv, t) ->  
            List.mapi 
              (fun i t -> 
                 (Var.mk_state_var_instance
                    sv
                    (Numeral.of_int i),
                  t))
              t)
         cex)
  in
  
  (* Generate blocking terms from equality relation *)
  let block_terms = fold_pairs equal_mod_input [] states in

  (* Return blocking terms *)
  block_terms

    
  



(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
