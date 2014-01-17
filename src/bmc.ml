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


(* Use configured SMT solver *)
module BMCSolver = SMTSolver.Make (Config.SMTSolver)


(* High-level methods for BMC solver *)
module S = SolverMethods.Make (BMCSolver)


(* ********************************************************************** *)
(* Solver instances and cleanup                                           *)
(* ********************************************************************** *)


(* Solver instance if created *)
let ref_solver = ref None


(* Output statistics *)
let pp_print_stat ppf = 

  Format.fprintf
    ppf
    "Statistics of %a module:@.@.%t@.%t@.%t"
    pp_print_kind_module `BMC
    Stat.pp_print_misc_stats
    Stat.pp_print_bmc_stats
    Stat.pp_print_smt_stats


(* Clean up before exit *)
let on_exit () =
    
  (* Stop all timers *)
  Stat.bmc_stop_timers ();
  Stat.smt_stop_timers ();

  (* Output statistics *)
  Event.stat 
    `BMC 
    [Stat.misc_stats_title, Stat.misc_stats;
     Stat.bmc_stats_title, Stat.bmc_stats;
     Stat.smt_stats_title, Stat.smt_stats];

  (* Delete solver instance if created *)
  (try 
     match !ref_solver with 
       | Some solver -> 
         S.delete_solver solver; 
         ref_solver := None
       | None -> ()
   with 
     | e -> 
       Event.log `BMC Event.L_error
         "Error deleting solver_init: %s" 
         (Printexc.to_string e))


(* ********************************************************************** *)
(* Counterexample traces                                                  *)
(* ********************************************************************** *)


(* Print out the trace of one variable from the counter example *)
let rec pp_print_trace ppf = function

  | (abstract_var, k, i, counter_example) ->

    if (k >= i) then    

      (
        
        Format.fprintf 
          ppf 
          "%a    " 
          Term.pp_print_term 
          (List.assoc 
             (Var.mk_state_var_instance abstract_var (Lib.numeral_of_int i)) 
             counter_example);
        
        pp_print_trace ppf (abstract_var, k, i + 1, counter_example)
      
      )
      
    else 
      
      (
        
        (* End the line when finished *)
        Format.fprintf ppf "\n@." 
          
      )
      

(* Print out the counter example *)
let rec pp_print_counter_example ppf = function 
  
  | ([], k, counter_example) -> ()
    
  | (abstract_var :: tl, k, counter_example) ->
    
    Format.fprintf ppf "%a    " StateVar.pp_print_state_var abstract_var;
    pp_print_trace ppf (abstract_var, k, 0, counter_example);
    pp_print_counter_example ppf (tl, k, counter_example)
      

(* Get a list of all the variables from transition system up to k steps. *)
let rec get_concrete_vars_for_k_steps ts k = 
  if (k >= 1) then 
  (
  
    (* Get the variables in state k*)
    let k_vars = 
      List.map (
        fun state_var ->
          Var.mk_state_var_instance state_var (Lib.numeral_of_int k)
      ) (TransSys.state_vars ts)
    in

    (* Append variables in state k with variables in all states before k. *)
    List.rev_append k_vars (get_concrete_vars_for_k_steps ts (k - 1))
    
  )

  else
  
    (* For the base case, get the variables for the initial state. *)
    List.map (
      fun state_var ->
        Var.mk_state_var_instance state_var (Lib.numeral_of_int 0)
    ) (TransSys.state_vars ts)


(* Filter the list of properties to eliminate the ones which doesn't hold in 
   the kth step. 
   
   Assumption: The conjuction of the property list should be invalid in the 
   kth step, and there is a check-sat query returning SAT right before calling
   this function. *)
	
	

let rec filter_property_list solver ts abstract_var_list concrete_var_list k prop_pairs =
  (debug bmc
          "filter_property_list :  0"
          end);
  if (List.length prop_pairs = 0) then 
    []
  else (
    (debug bmc
          "filter_property_list :  1"
          end);
    (* Get the model faultifying the conjuction of all properties in the 
       prop_pairs *)
    let model = S.get_model solver concrete_var_list in    

    (* Abstract the model so that it corresponds with the properties which 
       contain only initial state *)
    let abstract_model = List.map (
      fun (var, value) -> 
        ((Var.bump_offset_of_state_var_instance 
            (Lib.numeral_of_int (-1 * (k))) var)
          , value)
    ) model 
		
    in
		
	(*	let prop_off_state = List.map (
      fun (prop_name, prop) -> 				
        ((TranSys.bump_state 
            (Lib.numeral_of_int (k)) var)
          , value)
    ) ts.TransSys.props 
		
		in*)
		
    (debug bmc
          "filter_property_list :  2"
          end);
    (* prop_pairs' are the properties still hold, disproved_prop_pairs are 
       the properties which have been faltified by the model *)
    let (prop_pairs', disproved_prop_pairs) = 
      List.partition(     
        fun (prop_name, prop) -> 
          Eval.bool_of_value (Eval.eval_term (TransSys.bump_state k prop) model)
      ) ts.TransSys.props 
    in
		
		ts.TransSys.props <- prop_pairs';
		ts.TransSys.props_invalid <- disproved_prop_pairs;
		
    (debug bmc
          "filter_property_list :  3"
          end);
    (* Print out the properties which have been disproved *)
    List.iter(
      fun (dis_prop_name, dis_prop) -> 
        (debug findbug
          "Property %s disproved for %d induction"
          dis_prop_name
          (k + 1)
          end)
    ) ts.TransSys.props_invalid;

    List.iter (Event.disproved `BMC) (List.map fst disproved_prop_pairs);


    (* Print out the counter example *)
    (debug findbug
      "@[<hv>The counter_example is:\n@[<hv>%a@]@]@."
      pp_print_counter_example
      (abstract_var_list, k, model) end);       
          
    (* Continue with the properties which is not faultified by the
       previous counter example. *)
             
    (* If all the properties are faultified by the model *)
    if (List.length ts.TransSys.props = 0) then
      []
            
    else       
    (
    
      (* Instantiate the unfaultified properties into the step k. *)
      let k_prop_pairs' = 
        List.map (
          fun (prop_name', prop') -> 
            (prop_name', TransSys.bump_state k prop')
        ) ts.TransSys.props 
      in
			
              
      (* Conjunct the k properties into one formula *)
      let conjuncted_property' = 
        (Term.mk_and (List.map snd k_prop_pairs')) 
      in
              
      (* Check the if the conjuncted properties holds for the kth
         step *)
      S.assert_term solver (Term.mk_not conjuncted_property');
      
      (* If the properties still don't hold *)
      if (S.check_sat solver) then
      (
      
        (* If there is only one property left, it doesn't hold in the
           kth step. *)
        if (List.length prop_pairs' = 1) then 
         []
                
        (* There are more than one property left to check, we need to
         filter again. *)
        else 
              
          filter_property_list 
            solver 
            ts 
            abstract_var_list 
            concrete_var_list
            k
            prop_pairs'
      )
      
      (* The conjuncted property holds, return them all. *)
      else
      (
        (debug bmc
          "All bad properties gone, proceed with remaining properties"
          end);
                    
        prop_pairs'
      )
    )
  )


(* Bounded model checking *)
let rec bmc solver ts abstract_var_list k prop_pairs invariants_1=
  Event.log `BMC Event.L_info "BMC loop at k=%d" k;
  (debug findbug "------------bmc starts prop_pairs length = %d at k= %d" (List.length (ts.TransSys.props)) k end);

  Event.progress `BMC k;

  Stat.set k Stat.bmc_k;

  Stat.update_time Stat.bmc_total_time; 

  if (k == 1) then
  (
    ts.TransSys.props <- invariants_1 @ ts.TransSys.props;
    (debug findbug "------------after adding invariants at step 1, prop_pairs length = %d" 
	  (List.length (ts.TransSys.props)) end);
  );

  (* Event.log 1 "%t@." pp_print_stat; *)

  (* The disproved property pairs. *)
  let disproved_pairs = (list_subtract (ts.TransSys.props) prop_pairs) in
  
  (* Print out the properties which have been disproved *)
  (debug findbug
    "Disproved properties so far: %d"
    (List.length disproved_pairs)
    end);
	(*	
       
  List.iter(
    fun (dis_prop_name, dis_prop) -> 
      (debug bmc
        "%s"
        dis_prop_name
        end)
  ) disproved_pairs;*)
  (*
  (debug findbug
    "-------------Properties need to be proved so far:"
    end);
       
    List.iter(
    fun (prop_name, invar) -> 
      (debug bmc
        "%s: %a" prop_name
        Term.pp_print_term invar
        end)
  ) ts.TransSys.props;
  *)
  Event.bmcstate (k + 1) (List.map fst disproved_pairs);
	
  (debug bmc
    "BMC message of step %d sent"
    (k + 1)
    end);

  (* There is no property to check. *)
  if (List.length ts.TransSys.props = 0) then 
  (
  
    (debug bmc
      "No more property to check."
      end);
    
    ()
  )
    
  else 

  (* Instantiate the property for step k *)
  let k_prop_pairs = 
    List.map 
    (
      fun (prop_name, prop) -> 
        (prop_name, TransSys.bump_state k prop)
    ) ts.TransSys.props 
  in
    
    
  (* Get all the variables up to step k
  
     It's used for acquiring model *)

  let concrete_var_list = get_concrete_vars_for_k_steps ts k in


  (* Get the conjuncted property for the kth step *)
  let conjuncted_property = (Term.mk_and (List.map snd k_prop_pairs)) in

  (* Check if the conjuncted property holds, push the transition function
     T(k, k + 1) *)
  
  S.push solver;
  
  S.assert_term solver (Term.mk_not conjuncted_property);
  
  (* If the conjuncted property doesn't hold. *)
  if (S.check_sat solver) then
  (
    (* Filter out the properties which doesn't hold for the kth step. *)
 (debug findbug "------------conjuncted property doesn't hold!" end);
    let prop_pairs' = 
      filter_property_list 
        solver 
        ts 
        abstract_var_list 
        concrete_var_list 
        k 
        prop_pairs
				 
    in
    (* If all the properties are faultified for step k, end the
       checking. *)
    if (List.length prop_pairs' = 0) then 
    (
      (debug bmc
        "All properties failed at step %d"
        (k + 1)
        end);

    )

    (* If there are some properties holds in the kth step, push the
       transition function T(k, k + 1), and continue to check for the 
       (k + 1)th step. *)
    else 
    (
      S.pop solver;
      
      S.assert_term solver (TransSys.constr_of_bound (k + 1) ts);
			S.assert_term solver (TransSys.invars_of_bound (k + 1) ts);

      bmc solver ts abstract_var_list (k + 1) prop_pairs' invariants_1
    )
    
  )
  
  (* If the conjuncted property holds, push the transition function T(k, k + 1) 
     then continue to check for (k + 1) step *)
  else 
  (

    S.pop solver;
    
    S.assert_term solver (TransSys.constr_of_bound (k + 1) ts);
		S.assert_term solver (TransSys.invars_of_bound (k + 1) ts);

    bmc solver ts abstract_var_list (k + 1) prop_pairs invariants_1
  )
  

(* Entry point *)
let main transSys =
  (*Lib.minisleep 5.0;*)
	
  Stat.start_timer Stat.bmc_total_time;
  let props = ref [] in
  let invariants_1 = ref [] in 
	let flag = ref true in
  let counter = ref 0 in
 
	while !flag do
		 Lib.minisleep 0.5;				
		 let messages = Event.recv () in
     List.iter
	     (fun message -> 
         match message with
        
  		    (* Add invariant to the property list to verify when it's received. *)
          | (Event.Invariant (_, invar)) ->

					  flag := false;
	          if 
					    List.for_all 
	               (fun v -> 
							     (int_of_numeral (Var.offset_of_state_var_instance v)) = 0) 
						     (TransSys.vars_of_term invar) 
					  then
						  (
	             (debug findbug
                 "invariant_'0 invariant_property_%d = %a" !counter
                 Term.pp_print_term invar
                 end);
	              transSys.TransSys.props <- ("invariant_property_"^(string_of_int !counter), invar) :: transSys.TransSys.props;
						  )
	          
	          else
	           (
	             (debug findbug
                 "invariant_'1 invariant_property_%d = %a" !counter
                 Term.pp_print_term invar
                 end);
	             invariants_1 := ("invariant_property_"^(string_of_int !counter), invar) :: !invariants_1;
	           ); 
        
	          counter := !counter + 1;
       
        (* Irrelevant message received. *)
        | _ ->
					()
    
        ) messages;
	done;
	
 
  
  
  match transSys.TransSys.props with
    
    (* Terminate when there is nothing to check *)
    | [] -> Event.log `BMC Event.L_error "No property to check"

    | prop_pairs ->

      (* Determine logic for the SMT solver *)
      let logic = TransSys.get_logic transSys in

      (* Create solver instance *)
      let solver = 
        S.new_solver ~produce_assignments:true logic
      in
      
      (* Create a reference for the solver. Only used in on_exit. *)
      ref_solver := Some solver;
      
      (* Get all the variable of abstract state.
         
         It's used when acquiring model. *)
      let abstract_var_list = TransSys.state_vars transSys in
			props := prop_pairs @ !invariants_1;

      (* Provide the initial case *)
      S.assert_term solver (TransSys.init_of_bound 0 transSys);
			S.assert_term solver (TransSys.invars_of_bound 0 transSys);
			
      (* Enter the bounded model checking loop begin with the initial state. *)
      bmc solver transSys abstract_var_list 0 !props !invariants_1


  


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
