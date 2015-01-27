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

module SVT = StateVar.StateVarHashtbl
module VT = Var.VarHashtbl

(* Hashconsed term or hashconsed lambda expression *)
type term_or_lambda = Term of Term.t | Lambda of Term.lambda

(* A model is a map variables to assignments *)
type t = term_or_lambda VT.t

(* A path is a map of state variables to assignments *)
type path = term_or_lambda list SVT.t

(* An empty model *)
let empty_model = VT.create 7



(* Extract a path in the transition system, return an association list
   of state variables to a list of their values *)
let path_from_model state_vars get_model k =

  (* Initialize hash table with a size equal to the number of
     variables *)
  let path = SVT.create (List.length state_vars) in

  (* Add the model at each step to the path *)
  let rec path_from_model' state_vars = function 

    (* Terminate after the base instant *)
    | i when Numeral.(i < zero) -> ()

    | i -> 

      (* Get a model for the variables at instant [i] *)
      let model =
        get_model
          (List.map (fun sv -> Var.mk_state_var_instance sv i) state_vars)
      in

      VT.iter
        (fun var value ->  

           (* Get state variable from variable instance *)
           let state_var = Var.state_var_of_state_var_instance var in

           try 

             (* Get path for variable *)
             let var_values = SVT.find path state_var in

             (* Append value to path for variable *)
             SVT.replace path state_var (var_values @ [value])

           (* No netry for variable in path *)
           with Not_found -> 
             
             (* Must have had values unless i = 0 *)
             assert Numeral.(i > zero);

             (* Start path with value for variable *)
             SVT.add path state_var [value])

        model

  in

  (* Add values of all variables at instants 0 to k to path *)
  path_from_model' state_vars k;

  (* Return path *)
  path



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
