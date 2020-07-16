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


(* ********************************************************************** *)
(* Utility functions                                                      *)
(* ********************************************************************** *)


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


let offset_of_vars m = 

  match 

    Var.VarHashtbl.fold
      (fun v _ -> function 

         (* Offset not yet determined *)
         | None -> 

           (* Return offset of state variable instance if it is a
              non-constant state variable *)
           if Var.is_state_var_instance v then 
             Some (Var.offset_of_state_var_instance v)
           else
             None

         (* Some variable with offset [o] encountered *)
         | Some o -> 

           (* Ensure all variable have the same offset *)
           assert 
             (if Var.is_state_var_instance v then 
                Numeral.(equal (Var.offset_of_state_var_instance v) o)
              else
                true);

           (* Continue *)
           Some o)
      m
      None

  (* Fail on empty model *)
  with Some o -> o | None -> assert false 



(* ********************************************************************** *)
(* Simulation relation: Equality modulo input variables                   *)
(* ********************************************************************** *)

let counter =
  let i = ref 0 in
  fun () -> i := !i + 1 ; !i

(* Name of the uninterpreted function symbol *)
let equal_mod_input_string = ref "__compress_equal_mod_input"

let function_symbol_name () =
  !equal_mod_input_string

let new_function_symbol_name () =
  equal_mod_input_string := Printf.sprintf "__compress_equal_mod_input_%i" (counter ())


let only_bv trans_sys =
  match TransSys.get_logic trans_sys with
  | `SMTLogic "QF_BV"
  | `SMTLogic "QF_ABV"
  | `SMTLogic "QF_UFBV"
  | `SMTLogic "QF_AUFBV" -> true
  | `SMTLogic _
  | `None -> false
  | `Inferred l -> TermLib.FeatureSet.(mem BV l && not(mem IA l))


(* Declare uninterpreted function symbol *)
let init_equal_mod_input declare_fun trans_sys =

  new_function_symbol_name () ;
  
  let uf_distinct = 
    UfSymbol.mk_uf_symbol
      !equal_mod_input_string
      (List.fold_left 
         (fun a sv -> 
            if not (StateVar.is_input sv) then 
              StateVar.type_of_state_var sv :: a 
            else a)
         []
         (List.sort 
            StateVar.compare_state_vars
            (TransSys.state_vars trans_sys)))
      (if only_bv trans_sys then Type.mk_ubv 64 else Type.t_int)
  in
  
  declare_fun uf_distinct


(* States are equivalent if for each variable the variable is either
   an input or the values are equal *)
let equal_mod_input only_bv accum s1 s2 =

  let uf_distinct = 
    UfSymbol.uf_symbol_of_string !equal_mod_input_string
  in

  if

    (* Check if states are equivalent *)
    List.for_all2 (fun (v1, val1) (v2, val2) -> 
        let sv1 = Var.state_var_of_state_var_instance v1 in
        (* Make sure we're talking about the same state variable *)
        assert  
          (StateVar.equal_state_vars
             sv1 (Var.state_var_of_state_var_instance v2));
        (* States are equivalent if state variable is an input or
           values are equal *)
        StateVar.is_input sv1 || Model.equal_value val1 val2
      ) s1 s2 

  then 

    (

      (* Count number of clauses *)
      Stat.incr Stat.ind_compress_equal_mod_input;

      (* Blocking term to force states not equivalent *)
      let term =

        (* Use uninterpreted function symbol or disjunction of equations? *)
        if true then

          (
            
            (* Return the offset of the first variable, skipping
               over constant state variables 

               The list of variables is never empty *)
            let rec aux = function
              | [] -> assert false
              | (v, _) :: tl -> 
                if Var.is_state_var_instance v then 
                  Var.offset_of_state_var_instance v
                else
                  aux tl
            in

            (* Equation f(v1, ..., vn) = i *)
            let term_of_state s =
              let n =
                if only_bv then
                  Term.mk_ubv (Bitvector.num_to_ubv64 (aux s))
                else
                  Term.mk_num (aux s)
              in
              Term.mk_eq
                [Term.mk_uf
                   uf_distinct 
                   (List.fold_right
                      (fun (v, _) a -> 
                         if 
                           not 
                             (StateVar.is_input
                                (Var.state_var_of_state_var_instance v))
                         then Term.mk_var v :: a else a) s []);
                 n]
            in              

            (* Equation to force first state distinct from others *)
            let t1 = term_of_state s1 in

            (* Equation to force second state distinct from others *)
            let t2 = term_of_state s2 in

            (* Add conjunction of equations as blocking clause *)
            Term.mk_and [t1; t2]

          )

        else

          (* Generate disjunction of disequalities and add to accumulator *)
          (Term.mk_or

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
                s2))

      in

      Debug.compress
        "Compression clause@ %a" Term.pp_print_term term;

      term :: accum

    )

  (* States are not equivalent *)
  else accum


(* ********************************************************************** *)
(* Simulation relation: later state has same successors as earlier state  *)
(* ********************************************************************** *)

let same_successors_blocked = ref []  

let same_successors_incr_k () = same_successors_blocked := []

let rec instantiate_trans_succ var_uf_map i term = 

  Term.map
    (fun _ t -> 

       (* Subterm is a variable? *)
       if Term.is_free_var t then 

         (* Get variable of term *)
         (let v = Term.free_var_of_term t in

          if 

            (* Variable at previous instant? *)
            Var.is_state_var_instance v &&

            Numeral.equal 
              (Var.offset_of_state_var_instance v) 
              Numeral.zero

          then

            (* Get state variable of variable *)
            let sv = Var.state_var_of_state_var_instance v in

            (* Replace previous state variable with variable instant
               of first state *)
            Term.mk_var (Var.mk_state_var_instance sv i)

          else if 

            (* Variable at current instant? *)
            Var.is_state_var_instance v &&

            Numeral.equal 
              (Var.offset_of_state_var_instance v) 
              Numeral.one

          then

            (

              (* State variable *)
              let state_var = Var.state_var_of_state_var_instance v in

              (* Constant symbol for variable *)
              let uf_symbol = 

                try 

                  (* Get symbol from map *)
                  List.assq state_var var_uf_map 

                (* Every state variable is in the map *)
                with Not_found -> assert false

              in

              (* Replace current state variable with fresh constant *)
              Term.mk_uf uf_symbol [] 

            )

          else

            t

         )

       else
         
         (* Subterm is not a variable or an uninterpreted predicate to
            substitute *)
         t)

    term

let same_successors declare_fun uf_defs trans accum sj si = 

  (* Get offset of first state *)
  let i = offset_of_vars si in

  (* Get offset of second state *)
  let j_plus_one = offset_of_vars sj in

  let j = Numeral.pred j_plus_one in

  if 

    (* Don't compare a state to itself or if states have already been
       blocked *)
    Numeral.(equal i j) 
    || List.exists 
      (fun (s, t) -> Numeral.equal i s && Numeral.equal t j) 
      !same_successors_blocked 

  then

    (KEvent.log L_debug
       "Not considering state pair (%a,%a)"
       Numeral.pp_print_numeral i
       Numeral.pp_print_numeral j;

     accum)

  else

    (* Map offset of variables for first state to zero *)
    let si' = Model.set_var_offset Numeral.zero si in

    (* Map offset of variables for second state to one *)
    let sj' = Model.set_var_offset Numeral.one sj in

    (* Evaluate T[i,j+1] *)
    match Eval.eval_term uf_defs (Model.merge si' sj') trans with 

      (* j+1 is a successor of i *)
      | Eval.ValBool true -> 

        (KEvent.log L_debug
           "Possibly compressible path: (%a,%a) have a common successor"
           Numeral.pp_print_numeral i
           Numeral.pp_print_numeral j;

         (* Create a fresh uninterpreted constant for each state
            variable *)
         let var_uf_map = 
           Var.VarHashtbl.fold
             (fun v _ accum -> 

                (* State variable *)
                let sv = Var.state_var_of_state_var_instance v in

                (* Fresh uninterpreted symbol of the same type *)
                let u = UfSymbol.mk_fresh_uf_symbol [] (Var.type_of_var v) in

                (* Declare symbol in sovler instance *)
                declare_fun u;

                (* Return pair of state variable and symbol *)
                (sv, u) :: accum)
             si
             []
         in

         (* Turn T[0,1] to T[i,x] *)
         let trans_si = instantiate_trans_succ var_uf_map i trans in

         (* Turn T[0,1] to T[j,x] *)
         let trans_sj = instantiate_trans_succ var_uf_map j trans in

         (* Compress with T[i,x] & ~T[j,x] *)
         let block_term = Term.mk_and [trans_si; Term.negate trans_sj] in

         (* Remember state pairs to not block again *)
         same_successors_blocked := (i, j) :: !same_successors_blocked;

         (* Count number of clauses *)
         Stat.incr Stat.ind_compress_same_successors;

         (* Add compression formula *)
         block_term :: accum)

      | Eval.ValBool false ->       

        (KEvent.log L_debug
           "Cannot compress path: (%a,%a) have different successors"
           Numeral.pp_print_numeral i
           Numeral.pp_print_numeral j;

         accum)

      | Eval.ValTerm t -> 

        (KEvent.log L_debug
           "@[<v>Transition system evaluates to@,@[<hv>%a@]@]"
           Term.pp_print_term t;

         assert false)

      | _ -> assert false


let same_predecessors_blocked = ref []  

let same_predecessors_incr_k () = same_predecessors_blocked := []

let rec instantiate_trans_pred var_uf_map i term = 

  Term.map
    (fun _ t -> 

       (* Subterm is a variable? *)
       if Term.is_free_var t then 

         (* Get variable of term *)
         (let v = Term.free_var_of_term t in

          if 

            (* Variable at previous instant? *)
            Var.is_state_var_instance v &&

            Numeral.equal 
              (Var.offset_of_state_var_instance v) 
              Numeral.one

          then

            (* Get state variable of variable *)
            let sv = Var.state_var_of_state_var_instance v in

            (* Replace previous state variable with variable instant
               of first state *)
            Term.mk_var (Var.mk_state_var_instance sv i)

          else if 

            (* Variable at current instant? *)
            Var.is_state_var_instance v &&

            Numeral.equal 
              (Var.offset_of_state_var_instance v) 
              Numeral.zero

          then

            (

              (* State variable *)
              let state_var = Var.state_var_of_state_var_instance v in

              (* Constant symbol for variable *)
              let uf_symbol = 

                try 

                  (* Get symbol from map *)
                  List.assq state_var var_uf_map 

                (* Every state variable is in the map *)
                with Not_found -> assert false

              in

              (* Replace current state variable with fresh constant *)
              Term.mk_uf uf_symbol [] 

            )

          else

            t

         )

       else
         
         (* Subterm is not a variable or an uninterpreted predicate to
            substitute *)
         t)

    term


let same_predecessors declare_fun uf_defs trans accum sj si = 

  (* Get offset of first state *)
  let i_minus_one = offset_of_vars si in

  (* Get offset of second state *)
  let j = offset_of_vars sj in

  let i = Numeral.succ i_minus_one in

  if 

    (* Don't compare a state to itself or if states have already been
       blocked *)
    Numeral.(equal i j) 
    || List.exists 
      (fun (s, t) -> Numeral.equal i s && Numeral.equal t j) 
      !same_predecessors_blocked 

  then

    (KEvent.log L_debug
       "Not considering state pair (%a,%a)"
       Numeral.pp_print_numeral i
       Numeral.pp_print_numeral j;

     accum)

  else

    (* Map offset of variables for first state to zero *)
    let si' = Model.set_var_offset Numeral.zero si in

    (* Map offset of variables for second state to one *)
    let sj' = Model.set_var_offset Numeral.one sj in

    (* Evaluate T[i-1,j] *)
    match Eval.eval_term uf_defs (Model.merge si' sj') trans with 

      (* j+1 is a successor of i *)
      | Eval.ValBool true -> 

        (KEvent.log L_debug
           "Possibly compressible path: (%a,%a) have a common predecessor"
           Numeral.pp_print_numeral i
           Numeral.pp_print_numeral j;

         (* Create a fresh uninterpreted constant for each state
            variable *)
         let var_uf_map = 
           Var.VarHashtbl.fold
             (fun v _ accum -> 

                (* State variable *)
                let sv = Var.state_var_of_state_var_instance v in

                (* Fresh uninterpreted symbol of the same type *)
                let u = UfSymbol.mk_fresh_uf_symbol [] (Var.type_of_var v) in

                (* Declare symbol in sovler instance *)
                declare_fun u;

                (* Return pair of state variable and symbol *)
                (sv, u) :: accum)
             si
             []
         in

         (* Turn T[0,1] to T[x,i] *)
         let trans_si = instantiate_trans_pred var_uf_map i trans in

         (* Turn T[0,1] to T[x,j] *)
         let trans_sj = instantiate_trans_pred var_uf_map j trans in

         (* Compress with T[x,i] & ~T[x,j] *)
         let block_term = Term.mk_and [trans_si; Term.negate trans_sj] in

         (* Remember state pairs to not block again *)
         same_predecessors_blocked := (i, j) :: !same_predecessors_blocked;

         (* Count number of clauses *)
         Stat.incr Stat.ind_compress_same_predecessors;

         (* Add compression formula *)
         block_term :: accum)

      | Eval.ValBool false ->       

        (KEvent.log L_debug
           "Cannot compress path: (%a,%a) have different predecesors"
           Numeral.pp_print_numeral i
           Numeral.pp_print_numeral j;

         accum)

      | Eval.ValTerm t -> 

        (KEvent.log L_debug
           "@[<v>Transition system evaluates to@,@[<hv>%a@]@]"
           Term.pp_print_term t;

         assert false)

      | _ -> assert false


(* ********************************************************************** *)
(* Top-level functions                                                    *)
(* ********************************************************************** *)

let init declare_fun trans_sys = 

  init_equal_mod_input declare_fun trans_sys 


let incr_k () = 

  same_successors_incr_k ();
  same_predecessors_incr_k ()


(* Generate blocking terms from all equivalent states *)
let check_and_block declare_fun trans_sys path = 

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
         (List.sort 
            (fun (sv1, p) (sv2, p) ->
               StateVar.compare_state_vars sv1 sv2)
            (Model.path_to_list path)))
  in

  (* Initialize list of blocking terms *)
  let block_terms = [] in

  (* Generate blocking terms from equality relation *)
  let block_terms = 

    if Flags.BmcKind.compress_equal () then 

      fold_pairs (equal_mod_input (only_bv trans_sys)) block_terms states

    else 

      block_terms

  in

  (* Generate blocking terms from same successor relation *)
  let block_terms = 

    if Flags.BmcKind.compress_same_succ () then 

      fold_pairs
        (same_successors
           declare_fun
           (TransSys.uf_defs trans_sys)
           (TransSys.trans_of_bound (Some declare_fun) trans_sys Numeral.one))
        block_terms 
        (Model.models_of_path path)

    else

      block_terms

  in

  (* Generate blocking terms from same predecessor relation *)
  let block_terms = 

    if Flags.BmcKind.compress_same_pred () then 

      fold_pairs
        (same_predecessors
           declare_fun
           (TransSys.uf_defs trans_sys)
           (TransSys.trans_of_bound (Some declare_fun) trans_sys Numeral.one))
        block_terms 
        (Model.models_of_path path)

    else 

      block_terms

  in

  (* Return blocking terms *)
  block_terms

    
  



(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
