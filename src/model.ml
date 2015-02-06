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

(* Pretty-print a model *)
let pp_print_model ppf model = 

  Var.VarHashtbl.iter
    (function v -> function
       | Term t -> 
         Format.fprintf ppf
           "@[<hv 2>%a =@ %a@]@ " 
           Var.pp_print_var v 
           Term.pp_print_term t
       | Lambda l -> 
         Format.fprintf ppf
           "@[<hv 2>%a =@ %a@]@ " 
           Var.pp_print_var v 
           Term.pp_print_lambda l)
    model

(* Create a model of the given size *)
let create sz = VT.create sz

(* Create a path of the given size *)
let create_path sz = SVT.create sz

(* Import a variable assignment from a different instance *)
let import_term_or_lambda = function
  | Term t -> Term (Term.import t)
  | Lambda l -> Lambda (Term.import_lambda l)


(* Create a model of an association list *)
let of_list l = 

  (* Create hash table of initial size *)
  let model = VT.create 7 in

  (* Add associations from list to hash table *)
  List.iter 
    (fun (v, t) -> VT.add model v t)
    l;

  (* Return hash table *)
  model


(* Return an association list with the assignments in the model *)
let to_list m = 

  VT.fold
    (fun v t_or_l a -> (v, t_or_l) :: a)
    m
    []


(* Create a path of an association list *)
let path_of_list l = 

  (* Create hash table of initial size *)
  let path = SVT.create 7 in

  (* Add associations from list to hash table *)
  List.iter 
    (fun (v, t) -> SVT.add path v t)
    l;

  (* Return hash table *)
  path


(* Create a path of an association list *)
let path_of_term_list l = 

  (* Create hash table of initial size *)
  let path = SVT.create 7 in

  (* Add associations from list to hash table *)
  List.iter 
    (fun (v, t) -> SVT.add path v (List.map (fun t -> Term t) t))
    l;

  (* Return hash table *)
  path


(* Return an association list with the assignments of the path *)
let path_to_list p = 

  SVT.fold
    (fun sv t_or_l a -> (sv, t_or_l) :: a)
    p
    []


(* Extract a path in the transition system, return an association list
   of state variables to a list of their values *)
let path_from_model state_vars model k =

  (* Initialize hash table with a size equal to the number of
     variables *)
  let path = SVT.create (List.length state_vars) in

  (* Add the model at each step to the path *)
  let rec path_from_model' state_vars = function 

    (* Terminate after the base instant *)
    | i when Numeral.(i < zero) -> ()

    | i -> 

      (* Iterate over state variables, not all state variables are
         necessarily in a partial model *)
      List.iter
        (fun state_var -> 

           (* Value for variable at i *)
           let value = 
             try 

               (* Find value in model *)
               VT.find
                 model
                 (Var.mk_state_var_instance state_var i)

             with Not_found -> 

               (* Use default value if not defined in model *)
               Term
                 (TermLib.default_of_type
                    (StateVar.type_of_state_var state_var))

           in

           (* At the first offset? *)
           if Numeral.(equal i k) then 
             
             (* Start path with value for variable *)
             SVT.add path state_var [value]
               
           else

             (
               
               try 

                 (* Get current path for variable *)
                 let var_values = SVT.find path state_var in

                 (* Append value to path for variable *)
                 SVT.replace path state_var (value :: var_values)

               (* Skip if no model for variable *)
               with Not_found -> ()

             )

        )
        state_vars;

      (* Add values until i = 0 *)
      path_from_model' state_vars Numeral.(pred i)

  in

  (* Add values of all variables at instants 0 to k to path *)
  path_from_model' state_vars k;

  (* Return path *)
  path


(* Extract value at instant [k] from the path and return a model *)
let model_at_k_of_path path k = 

  (* Convert numeral to integer *)
  let k_int = Numeral.to_int k in

  (* Create hash table of same size *)
  let model = VT.create (SVT.length path) in 

  (* Iterate over path and add to model *)
  SVT.iter

    (fun sv p -> 

       (* Get k-th value from path *)
       let t_or_l = 
         try 
           List.nth p k_int
         with Failure _ ->  
           raise (Invalid_argument "model_from_path")
       in

       (* Create variable at instant *)
       let var = 
         Var.mk_state_var_instance sv k
       in

       (* Add assignment to variable to model *)
       VT.add model var t_or_l)

    path;

  (* Return created model *)
  model


(* Convert a path to a set of models *)
let models_of_path path = 

  SVT.fold

    (* Apply to each state variable and its list of values *)
    (fun sv sv_path accum -> 

       (* Initialize list of models if empty *)
       let models = 

         if accum = [] then 

           (* Create a model for each step in the path *)
           List.map
             (fun _ -> VT.create (SVT.length path))
             sv_path 

         else

           (

             (* Ensure that this path is as long as previous paths *)
             assert (List.length sv_path = List.length accum);
             
             (* Continue with list of models created so far *)
             accum

           )

       in

       (* Discard length of path *)
       let _ = 

         List.fold_left2

           (* Apply to each assignment at a step in the path and the
              respective model *)
           (fun i t_or_l m -> 

              (* Add assignment to variable to model *)
              VT.add m (Var.mk_state_var_instance sv Numeral.zero) t_or_l;

              (* Increment counter for zero *)
              Numeral.(succ i))

           (* Start first model at offset zero *)
           Numeral.zero

           (* Assignments to state variable on path *)
           sv_path

           (* One model for each offset *)
           models

       in

       (* Continue with models modified in place *)
       models)

    (* Assignments to all state variables *)
    path

    (* Initialize list of models *)
    []


(* Return true if the predicate [p] applies at one step of the path *)
let exists_on_path p path = 

  (* Convert path to a list of models *)
  let models = models_of_path path in

  (* Does predicate hold on each step? *)
  List.exists p models  
  

(* Return true if the predicate [p] applies at each step of the path *)
let for_all_on_path p path = 

  (* Convert path to a list of models *)
  let models = models_of_path path in

  (* Does predicate hold on each step? *)
  List.for_all p models  


(* Apply a function to variable and its assignment *)
let map f_var f_val model = 

  (* Create a hash table of the same size *)
  let model' = VT.create (VT.length model) in

  (* Apply functions to each variable and assignment and add results
     to fresh table *)
  VT.iter
    (fun v t_or_l -> 
       VT.add 
         model' 
         (f_var v) 
         (f_val t_or_l))
    model;

  (* Return fresh model *)
  model'


(* Add [k] to offset of all variables in model *)
let bump_var k model = map (Var.bump_offset_of_state_var_instance k) identity model


(* Add [k] to offset of all variables in model *)
let set_var_offset k model = 

  map
    (fun v -> 
       let sv = Var.state_var_of_state_var_instance v in
       Var.mk_state_var_instance sv k)
    identity 
    model


(* Apply function to variables and assignments in second model and
   combine with assignments of th first model. If a variable has an
   assignment in both models, it gets the assignment in the second
   model. *)
let apply_and_merge f model1 model2 = 

  (* Make a deep copy of the hash table *)
  let model' = VT.copy model1 in

  (* Add all assignments from second model, replace possibly existing
     assignments in first model *)
  VT.iter
    (fun v t_or_l -> 
       let v', t_or_l' = f v t_or_l in
       VT.replace model' v' t_or_l')
    model2;

  (* Return fresh model *)
  model'

(* Combine assignments of two models into one. If a variable has an
    assignment in both models, it gets the assignment in the second
    model. *)
let merge model1 model2 = 
  apply_and_merge (fun a b -> (a, b)) model1 model2

       
(* Combine assignments of two models into one with the offsets of
    variables in the second model bumped. If a variable has an
    assignment in both models, it gets the assignment in the second
    model. *)
let bump_and_merge k model1 model2 = 
  apply_and_merge 
    (fun v t_or_l -> Var.bump_offset_of_state_var_instance k v, t_or_l)
    model1 
    model2
  

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
