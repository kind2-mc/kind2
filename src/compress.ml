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


module type CompressionPred =
sig

  (* Simulation relation *)
  val check : (Var.t * Term.t) list -> (Var.t * Term.t) list -> bool

  val block : Numeral.t -> Numeral.t -> Term.t

end

(* Empty relation, is a direct and reverse simulation *)
module Empty : CompressionPred = 
struct 
  
  let check _ _ = false 

  let block _ _ = Term.t_true

end


(* s_1 simulates s_2 iff both are initial, is a reverse simulation *)
module Init : CompressionPred =
struct

  let check _ _ = false

  let block _ _ = Term.t_true

end


(* s_1 simulates s_2 iff s_1 = s_2, is a direct and reverse simulation *)
module Equal : CompressionPred =
struct 

  let check state1 state2 = 

    List.for_all2 
      (fun (v1, t1) (v2, t2) -> 
         if
           StateVar.equal_state_vars
             (Var.state_var_of_state_var_instance v1) 
             (Var.state_var_of_state_var_instance v2)
         then
           Term.equal t1 t2
         else
           assert false)
      state1
      state2

  let block offset1 offset2 = 

    Term.t_true

    
end


(* s_1 simulates s_2 iff s_1 = s_2 on those variables that are not
   input, is a reverse simulation *)
module EqualModInput : CompressionPred = 
struct
  
  let check state1 state2 = 

    List.for_all2 
      (fun (v1, t1) (v2, t2) -> 
         let sv1 = Var.state_var_of_state_var_instance v1 in
         let sv2 = Var.state_var_of_state_var_instance v2 in
         if StateVar.equal_state_vars sv1 sv2 then
           StateVar.is_input sv1 || Term.equal t1 t2
         else
           assert false)
      state1
      state2

  let block offset1 offset2 = 

    Term.t_true

end

(* Apply function to all unordered pairs in the list and return
   results in a list

   [fold_pairs f [e_1; ...; e_n]] computes [r_12 = f e_1 e_2], ...
   [r_1n = f e_1 e_n], [r_23 = f e_2 e_3], ..., [r_n-1n = f e_n-1
   e_n] in this order and returns the list [r_n-1n, ..., r_12]. 

   The empty list is returned if [l] has less than two elements. *)
let fold_pairs f l = 

  let rec fold_pairs' f l accum = function
    
    | [] | [_] -> 
      
      (match l with 
        | [] | [_] -> accum 
        | h :: tl -> fold_pairs' f tl accum tl)
      
    | h :: s :: tl -> 
      
      fold_pairs' f l ((f h s) :: accum) (h :: tl)

  in

  fold_pairs' f l [] l


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

  

let compress_path trans_sys path = 

  if exists_pair EqualModInput.check path then

    None

  else

    None
  



(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
