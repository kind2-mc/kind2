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

(*./kind2 --enable interpreter --debug smt --debug parse microwave.lus*)
open Lib


(* Solver instance if created *)
let ref_solver = ref None


(* Exit and terminate all processes here in case we are interrupted *)
let on_exit _ = 

  (* Delete solver instance if created *)
  (try 
     match !ref_solver with 
       | Some solver -> 
         SMTSolver.delete_instance solver;  
         ref_solver := None
       | None -> ()
   with 
     | e -> 
       KEvent.log L_error
         "Error deleting solver_init: %s" 
         (Printexc.to_string e))


(* Assert transition relation for all steps below [i] *)
let rec assert_trans solver t i =
  
  (* Instant zero is base instant *)
  if Numeral.(i < one) then () else  
    
    (

      (* Assert transition relation from [i-1] to [i] *)
      SMTSolver.assert_term solver
        (TransSys.trans_of_bound (Some (SMTSolver.declare_fun solver)) t i);
                            
      (* Continue with for [i-2] and [i-1] *)
      assert_trans solver t Numeral.(i - one)

    )
    

(* Main entry point *)
let main input_file input_sys aparam trans_sys =

  KEvent.set_module `Interpreter;

  let input_scope = TransSys.scope_of_trans_sys trans_sys @
                    LustreIdent.user_scope in

  let trans_svars = TransSys.state_vars trans_sys in
  (*trans_svars |> List.iter (fun sv -> KEvent.log_uncond "%a" StateVar.pp_print_state_var sv) ;*)

  (* Read inputs from file *)
  let inputs =
    if input_file = "" then []
    else
      try InputParser.read_file input_scope input_file
      with Sys_error e -> 
        (* Output warning *)
        KEvent.log L_warn "@[<v>Error reading interpreter input file.@,%s@]" e;
        raise (Failure "main")
  in

  let nb_inputs = List.filter StateVar.is_input trans_svars |> List.length in

  (* Check that constant inputs are indeed constant. *)
  inputs |> List.iter (
    function
    | ((sv, _), head :: tail) when StateVar.is_const sv ->
      tail |> List.fold_left (
        fun acc value ->
          if acc != value then (
            KEvent.log L_warn
              "Input %s is constant, but input values differ: \
              got %a and, later, %a."
              (StateVar.name_of_state_var sv)
              Term.pp_print_term acc
              Term.pp_print_term value ;
            Failure "main" |> raise
          ) ;
          acc
      ) head |> ignore
    | _ -> ()
  ) ;

  (* Remove sliced inputs *)
  let inputs = List.filter (fun ((sv,_), _) ->
      List.exists (StateVar.equal_state_vars sv) trans_svars
    ) inputs
  in

  (* Minimum number of steps in input *)
  let input_length = 
    List.fold_left 
      (fun accum (_, inputs) -> 
         min (if accum = 0 then max_int else accum) (List.length inputs))
      0
      inputs
  in

  (* Check if all inputs are of the same length *)
  List.iter
    (fun ((state_var, _), inputs) -> 

       (* Is input longer than minimum? *)
       if List.length inputs > input_length then

         (* Output warning *)
         KEvent.log L_warn 
           "Input for %s is longer than other inputs"
           (StateVar.name_of_state_var state_var))

    inputs;

  (* Number of steps to simulate *)
  let steps = 

    match Flags.Interpreter.steps () with 

    (* Simulate length of smallest input if number of steps not given *)
    | s when s <= 0 -> input_length

    (* Length of simulation given by user *)
    | s -> 

      (* Lenghth of simulation greater than input? *)
      if s > input_length && nb_inputs > 0 then

        KEvent.log L_warn 
          "Input is not long enough to simulate %d steps. \
           Simulation is nondeterministic." 
          input_length;

      (* Simulate for given length *)
      s

  in

  KEvent.log L_info "Interpreter running up to k=%d" steps;

  (* Determine logic for the SMT solver *)
  let logic = TransSys.get_logic trans_sys in

  (* Create solver instance *)
  let solver = 
    Flags.Smt.solver ()
    |> SMTSolver.create_instance ~produce_assignments:true logic
  in

  (* Create a reference for the solver. Only used in on_exit. *)
  ref_solver := Some solver;

  (* Defining uf's and declaring variables. *)
  TransSys.define_and_declare_of_bounds
    trans_sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.(~- one) Numeral.(of_int steps) ;

  (* Assert initial state constraint *)
    SMTSolver.assert_term solver
      (TransSys.init_of_bound (Some (SMTSolver.declare_fun solver))
         trans_sys Numeral.zero);

  (* Assert transition relation up to number of steps *)
  assert_trans solver trans_sys (Numeral.of_int steps);

  (* Assert equation of state variable and its value at each
     instant *)
  List.iter

    (fun ((state_var, indexes), values) ->

       List.iteri 
         (fun instant instant_value ->

            (* Only assert up to the maximum number of steps *)
            if instant < steps then
            (
              (* Create variable at instant *)
              let var = 
                Var.mk_state_var_instance 
                  state_var 
                  (Numeral.of_int instant)
                |> Term.mk_var
              in

              (* Select index of instance variable *)
              let var = List.fold_left (
                fun acc i ->
                Term.mk_select acc (Term.mk_num_of_int i)
              ) var indexes |> Term.convert_select in

              (* Constrain variable to its value at instant *)
              let equation = 
                Term.mk_eq [var; instant_value] 
              in

              (* Assert equation *)
              SMTSolver.assert_term solver equation
            )
          )
         values)

    inputs;

  KEvent.log L_info 
    "Parsing interpreter input file %s"
    (Flags.input_file ()); 

  (* Run the system *)
  if (SMTSolver.check_sat solver) then

    (

      (* Extract execution path from model *)
      let path = 
        Model.path_from_model 
          (TransSys.state_vars trans_sys)
            (* (SMTSolver.get_model solver) *)
            (SMTSolver.get_var_values solver
               (TransSys.get_state_var_bounds trans_sys)
               (TransSys.vars_of_bounds trans_sys
                  Numeral.zero (Numeral.of_int steps)))
          Numeral.(pred (of_int steps))
      in

      (* Output execution path *)
      KEvent.execution_path
        input_sys
        aparam
        trans_sys 
        (Model.path_to_list path)

    )

  else

    (* Transition relation must be satisfiable *)
    KEvent.log L_error "Transition relation not satisfiable"


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
