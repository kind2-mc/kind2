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
(*./kind2 --enable interpreter --debug smt --debug parse microwave.lus*)
open Lib


(* Use configured SMT solver *)
module BMCSolver = SMTSolver.Make (Config.SMTSolver)


(* High-level methods for BMC solver *)
module S = SolverMethods.Make (BMCSolver)


(* Dummy exit method, need to terminate all processes here in case we
   are interrupted *)
let on_exit () = ()
let len_different = ref false

(**If the lengths of input streams are different, return the shortest length.*)
let calculate_shortest_length_of_input_stream l =
  let len = ref (List.length (snd (List.hd l))) in
  
  List.iter 
    (fun(y,x) ->
      if (List.length x) = 0
      then (Event.log `Interpreter Event.L_fatal 
            "Warning: No input is provided for state variable %s" 
              (StateVar.name_of_state_var y)) 
      else if ((List.length x) < !len) 
           then (len_different := true;len := (List.length x))) 
      l;
    !len


(* Main entry point *)
let main input_file transSys =
  
  let inputs = InputParser.read_file input_file in
  
  (* user interpreter steps input*)
  let steps = Flags.interpreter_steps () in
  
  (* Number of instants to simulate *)
  let shortest_length = calculate_shortest_length_of_input_stream inputs in
  
  (* Number of instants input *)
  let k =
    if steps <= 0
    then ((if !len_different 
          then 
            Event.log `Interpreter Event.L_fatal 
            "Warning: Input streams have different lengths. Simulation up to the shortest length of the input streams.");
          shortest_length) 
    else if steps > shortest_length
         then ((if !len_different 
                 then (Event.log `Interpreter Event.L_fatal 
                       "Warning: The length of input streams are not long enough to simulate up to %d steps" steps;
                       Event.log `Interpreter Event.L_fatal 
                       "Warning: Simulation will continue nondeterministically after %d instant" (shortest_length-1)));
          	   steps)
          else steps
  in

  Event.log `Interpreter Event.L_fatal "Interpreter running up to k = %d" k;

  (* let inputs = InputParser.main x in *)

  
  let l = 3 in

  (* Determine logic for the SMT solver *)
  let logic = TransSys.get_logic transSys in

  (* Create solver instance *)
  let solver = 
    S.new_solver ~produce_assignments:true logic
  in
      
  let state_vars = TransSys.state_vars transSys in
  
  (* Provide the initial case *)
  S.assert_term solver (TransSys.init_of_bound 0 transSys);
  
  let rec assert_t t i =
    
    if i <= 0 then 

      () 

    else  

      (
  (**)      
        S.assert_term solver (TransSys.constr_of_bound i t);
        
        assert_t transSys (i - 1)
          
      )
      
  in
  
(**assert equation of state varariable and its value at each instance*)
  List.iter

    (fun (state_var, values) -> 
       let _ = List.fold_left

         (fun instant instant_value ->
           if ((int_of_numeral instant) < k)
           then(
         	 let var = Var.mk_state_var_instance state_var instant in
             let equation = Term.mk_eq [Term.mk_var var; instant_value] in
             S.assert_term solver equation);	
             incr_numeral instant)
            
         (numeral_of_int 0)
         
         values

       in

       ()
    ) 

    inputs;
    
  (**Get value for each variable*)
  if (S.check_sat solver) then
		
	let rec aux acc state_var k =
		
		if (int_of_numeral k) < 0 then
			
			let model = S.get_model solver acc in
			
			List.map snd model
			
		else
			
			aux ((Var.mk_state_var_instance state_var k)::acc) state_var (decr_numeral k)
	in
    let v = 
			
      List.map 
			
        (fun sv -> 
					
           (sv,(aux [] sv (numeral_of_int (k-1)))))
					
        state_vars 
				
    in
		
    Event.log_counterexample `Interpreter v

  else

    Event.log `Interpreter Event.L_error "Transition relation not satisfiable"
  

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
