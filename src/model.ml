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

module SVT = StateVar.StateVarHashtbl
module VT = Var.VarHashtbl

(* Offset of the variables at each step of a path. *)
let path_offset = Numeral.zero

module MIL = Map.Make
    (struct
      type t = int list
      let rec compare l1 l2 = match l1, l2 with
        | [], [] -> 0
        | [], _ -> -1
        | _, [] -> 1
        | x :: r1, y :: r2 ->
          let c = Pervasives.compare x y in
          if c <> 0 then c
          else compare r1 r2
    end)


(* Hashconsed term or hashconsed lambda expression *)
type value =
  | Term of Term.t
  | Lambda of Term.lambda
  | Map of Term.t MIL.t


let equal_value v1 v2 = match v1, v2 with
  | Term t1, Term t2 -> Term.equal t1 t2
  | Lambda l1, Lambda l2 -> assert false (* TODO *)
  | Map m1, Map m2 -> MIL.equal Term.equal m1 m2
  | _ -> false


(* A model is a map variables to assignments *)
type t = value VT.t

(* A path is a map of state variables to assignments *)
type path = value list SVT.t

(* Pretty-print a value *)
let pp_print_term ppf term =
  (* if Term.is_bool term then *)
  (*   if Term.bool_of_term term then *)
  (*     Format.fprintf ppf "✓" (\* "true" *\) *)
  (*   else Format.fprintf ppf "✗" (\* "false" *\) *)
  (* else *)
  (* Term.pp_print_term ppf term *)
  (LustreExpr.pp_print_expr false) ppf
    (LustreExpr.unsafe_expr_of_term term)

let pp_print_term ppf term =
  if Term.(equal term t_false || equal term (mk_num_of_int 0)) then
    Format.fprintf ppf "@{<black_b>%a@}" pp_print_term term
  else pp_print_term ppf term


let width_val_of_map m =
  MIL.fold (fun _ v ->
      max (width_of_string (string_of_t pp_print_term v))
    ) m 0

      
(* Show map as an array in counteexamples *)
let pp_print_map_as_array ppf m =
  if MIL.is_empty m then Format.fprintf ppf "[]"
  else
    let val_width = width_val_of_map m in
    let dim = MIL.choose m |> fst |> List.length in
    let current = Array.make dim 0 in
    let prev = Array.make dim 0 in
    for i = 1 to dim do
      Format.fprintf ppf "[@[<hov 0>";
    done;
    let first = ref true in
    MIL.iter (fun l v ->
        Array.blit current 0 prev 0 dim;
        Array.blit (Array.of_list l) 0 current 0 dim;
        let cpt = ref 0 in
        for i = dim - 2 downto 0 do
          if current.(i) <> prev.(i) then (Format.fprintf ppf "@]]"; incr cpt);
        done;
        (* if !cpt <> !nopen then  Format.fprintf ppf ";"; *)
        if !cpt > 0 then Format.fprintf ppf ",@ "
        else if not !first then Format.fprintf ppf ",";
        for i = 1 to !cpt do
          Format.fprintf ppf "[@[<hov 0>";
        done;
        let w = width_of_string (string_of_t pp_print_term v) in
        Format.fprintf ppf "%*s%a" (val_width - w) "" pp_print_term v;
        first := false;
      ) m;
    for i = 1 to dim do
      Format.fprintf ppf "@]]";
    done

      (* "@[<hv 2><Value instant=\"%d\">@,@[<hv 2>%a@]@;<0 -2></Value>@]"  *)


type array_model =
  | ItemValue of Term.t
  | ItemArray of int * array_model array


let rec allocate_model sizes =
  match sizes with
  | [] ->
    ItemValue (Term.t_false)

  | s :: rs ->
    ItemArray
      (s,
       Array.init s (fun _ -> allocate_model rs))


let dimension_of_map m =
  MIL.fold (fun l _ acc -> List.map2 max acc l)
    m (fst @@ MIL.choose m)
  |> List.map succ


let rec add_at_indexes l v arm =
  match l, arm with
  | [], ItemValue _ -> ItemValue v
  | i :: l, ItemArray (s, a) ->
    let new_a_i = add_at_indexes l v a.(i) in
    a.(i) <- new_a_i;
    arm
  | _ -> assert false

let rec map_to_array_model m =
  allocate_model (dimension_of_map m)
  |> MIL.fold add_at_indexes m


let rec pp_print_array_model ppf index = function
  | ItemValue v ->
    Format.fprintf ppf
      "@[<hv 2><Item index=\"%d\">@,@[<hv 2>%a@]@;<0 -2></Item>@]"
      index
      Term.pp_print_term v
  | ItemArray (s, a) ->
    Format.fprintf ppf
      "@[<hv 2><Array size=\"%d\">@,%a@;<0 -2></Array>@]"
      s
      (pp_print_listi pp_print_array_model "@,") (Array.to_list a)


(* Show map as xml in counteexamples *)
let pp_print_map_as_xml ppf m =
  let arm = map_to_array_model m in
  pp_print_array_model ppf 0 arm


(* Print a value of the model *)  
let pp_print_value ppf = function 
  | Term t -> pp_print_term ppf t
  | Lambda l -> Term.pp_print_lambda ppf l
  | Map m -> Format.fprintf ppf "@[<hov 0>%a@]" pp_print_map_as_array m


let pp_print_value_xml ppf = function 
  | Term t -> Term.pp_print_term ppf t
  | Lambda l -> Term.pp_print_lambda ppf l
  | Map m ->
    try
      pp_print_map_as_xml ppf m
    with Not_found -> ()


(* Pretty-print a model *)
let pp_print_model ppf model = 
  Var.VarHashtbl.iter
    (fun v value ->
      Format.fprintf ppf
        "@[<hv 2>%a =@ %a@]@."
        Var.pp_print_var v
        pp_print_value value
    )
    model

(* Create a model of the given size *)
let create sz = VT.create sz

(* Create a path of the given size *)
let create_path sz = SVT.create sz

(* Import a variable assignment from a different instance *)
let import_value = function
  | Term t -> Term (Term.import t)
  | Lambda l -> Lambda (Term.import_lambda l)
  | Map m ->
    Map (MIL.fold (fun l v acc ->
        MIL.add l (Term.import v) acc)
        m MIL.empty)


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


let find_value_vi vi model =
  let rec find prev vi =
    try
      let va = VT.find model vi in
      match va with
      | Term t when Term.is_free_var t ->
        find (Some va) (Term.free_var_of_term t)
      | _ -> va
    with Not_found ->
      match prev with
      | None -> raise Not_found
      | Some va -> va
  in
  find None vi


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
               find_value_vi (Var.mk_state_var_instance state_var i) model

             with Not_found ->

               (* Use default value if not defined in model *)
               let ty = StateVar.type_of_state_var state_var in
               match Type.node_of_type ty with
               | Type.Array (te, ti) ->
                 Lambda (Term.mk_lambda
                           [Var.mk_fresh_var ti]
                           (TermLib.default_of_type te))
               | _ ->
                 Term (TermLib.default_of_type ty)

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


(* Return the length of the paths *)
let path_length path = 

  (* There is no Hashtbl.S.choose, and no way to get a single key as
     of now, so we need to iterate over all entries anyways. Then we
     can just as well check if all lists are of equal length. *)
  SVT.fold
    (fun _ l a -> 
       let r = List.length l in
       assert (a < 0 || r = a);
       a)
    path
    (- 1)


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
              VT.add m (Var.mk_state_var_instance sv path_offset) t_or_l;

              (* Increment counter for zero: ACTUALLY UNUSED *)
              Numeral.(succ i))

           (* Start first model at offset zero: ACTUALLY UNUSED *)
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
let bump_var k model = 
  map
    (fun v -> Var.bump_offset_of_state_var_instance v k) 
    identity model


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
    (fun v t_or_l -> Var.bump_offset_of_state_var_instance v k, t_or_l)
    model1 
    model2
  

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
