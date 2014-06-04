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

(* Use configured SMT solver *)
module INDSolver = SMTSolver.Make (Config.SMTSolver)

(* High-level methods for BMC solver *)
module S = SolverMethods.Make (INDSolver)

(* ********************************************************************** *)
(* Solver instances and cleanup                                           *)
(* ********************************************************************** *)

(* Current step in BMC. *)
let bmcK = ref 0


(* Solver instance if created *)
let ref_solver = ref None


(* Output statistics *)
let print_stats () =

  Event.stat 
    `IND 
    [Stat.misc_stats_title, Stat.misc_stats;
     Stat.ind_stats_title, Stat.ind_stats;
     Stat.smt_stats_title, Stat.smt_stats]


(* Clean up before exit *)
let on_exit () =

  (* Stop all timers *)
  Stat.ind_stop_timers ();
  Stat.smt_stop_timers ();

  (* Output statistics *)
  print_stats ();

  (* Delete solver instance if created *)
  (try 
     match !ref_solver with 
       | Some solver -> 
         S.delete_solver solver; 
         ref_solver := None
       | None -> ()
   with 
     | e -> 
       Event.log `IND Event.L_error 
         "Error deleting solver_init: %s" 
         (Printexc.to_string e))


(* Assert transition system for instants 0..k *)
let rec assert_trans_k solver trans_sys k =

  (* Terminate when when at the base instant *)
  if k < 1 then () else 

    (

      (* Assert T[x_k-1,x_k] *)
      S.assert_term 
        solver
        (TransSys.trans_of_bound 
           (Numeral.pred (Numeral.of_int k)) 
           trans_sys);
      
      (* Recurse for instants 0..k-1 *)
      assert_trans_k solver trans_sys (k - 1)

    )


(* Return a list of the given terms at each instant 0..k *)
let rec terms_k term accum k =

  if k < 1 then accum else
    
    terms_k 
      term
      ((Term.bump_state (Numeral.of_int (k - 1)) term) :: accum)
      (k-1)
      

(* Check for messages and update associated lists *)
let handle_events
    solver
    trans_sys
    propertiesToCheck
    assumedProps
    invariants
    k
    reset =

  (* Add invariant to the transition system and assert in solver
     instances *)
  let add_invariant inv = 

    (* Add invariant to the transition system *)
    TransSys.add_invariant trans_sys inv;

    (* Add prime to invariant *)
    let inv_1 = Term.bump_state Numeral.one inv in

    (* Assert invariant in solver instance for initial state *)
    S.assert_term solver inv;
    S.assert_term solver inv_1
    
  in

  (* Receive all queued messages 

     Side effect: Terminate when ControlMessage TERM is received.*)
  let messages = Event.recv () in
  
  List.fold_left 
    (fun (propertiesToCheck, assumedProps, invariants, restart) message ->
       
       match message with

         (* Add invariant to list of invariants *)
         | (Event.Invariant (_, inv)) -> 

           (* Add invariant to the transition system and assert in
               solver instance *)
           add_invariant inv;

           (propertiesToCheck, assumedProps, inv :: invariants, reset)

         (* Check bmc state and eliminated disproved properties *)
         | Event.BMCState (bmcK', disprovedPropsList) ->

           bmcK := bmcK';

           List.iter
             (fun (name, prop) -> 
                if List.mem name disprovedPropsList then
                  TransSys.add_invalid_prop trans_sys (name, prop))
             trans_sys.TransSys.props;

           (* If there is a assumed property disproved by BMC, add all
              the assumed properties back to check again.*)
           if 

             (List.exists
                (fun (_, p) -> List.mem (fst p) disprovedPropsList) 
                assumedProps) 
           
           then
             
             (
             
               ((list_subtract 
                   (propertiesToCheck @ (List.map snd assumedProps)) 
                   trans_sys.TransSys.props_invalid), 
                [], invariants, true)

             )

           (* Otherwise, assert assumed properties upto k-1 and send
              out the valid properties *)
           else

             (
               
               let (validProps, assumedProps') = 
                 List.partition
                   (fun (l, p) -> bmcK' >= l) 
                   assumedProps
               in
               
               let assumedPropsUptok_1 =
                 List.map
                   (fun (_, prop) -> (terms_k (snd prop) [] (k-1))) 
                   assumedProps'
               in

               S.assert_term
                 solver
                 (Term.mk_and (List.flatten assumedPropsUptok_1));

               List.iter
                 (fun (l, p) -> 
                    (debug ind "Property %s proved at inductive step k = %d" (fst p) l end);

Event.proved `IND (Some l) p) validProps;
(propertiesToCheck, assumedProps', invariants, reset)
)
| (Event.Proved (_, _, p)) ->
  let (name, prop) = 
    (List.find (fun x -> fst x = p) trans_sys.TransSys.props) 
  in
  TransSys.add_valid_prop trans_sys (name, prop);

  ((List.filter (fun x -> fst x <> p) propertiesToCheck), assumedProps, invariants, reset)

(* Add disproved properties to transys props_invalid*)
| (Event.Disproved (_, _, p)) ->
  TransSys.add_invalid_prop trans_sys (List.find (fun x -> fst x = p) trans_sys.TransSys.props);             
  (* If there exist a disproved property in the assumed property list, *)
  (* we add the entire assumed properties back to the properties list to check again*)
  (* otherwise, we continue by eliminating the invalid properties*)
  if (List.exists (fun (k, prop) -> fst prop = p) assumedProps) then
    (
      (list_subtract (propertiesToCheck@(List.map snd assumedProps)) trans_sys.TransSys.props_invalid, [], invariants, true)
    )
  else
    (list_subtract propertiesToCheck trans_sys.TransSys.props_invalid, assumedProps, invariants, reset)

(* Irrelevant message received. *)
| _ ->
  (propertiesToCheck, assumedProps, invariants, reset)
) 
(propertiesToCheck, assumedProps, invariants, reset)
  messages

(* Eliminate properties that are not implied by the transition system
   at step k*)
let filter_properties solver ts k props =

  (*just current k is enough*)
  let state_vars = TransSys.vars_of_bounds ts Numeral.zero k in

  let uf_defs = ts.TransSys.uf_defs in

  (* Get the model that falsifies the conjuction of all properties in
     the props *)
  let model = S.get_model solver state_vars in 

  (* Bump the properties to k *)    
  List.partition
    (fun (name, prop) -> 
       Eval.bool_of_value 
         (Eval.eval_term uf_defs model (Term.bump_state k prop))) 
    props

(* Inductive step *)
let rec ind 
    solver 
    ts
    preK
    k
    propertiesToCheck
    propertiesToCheckNextK 
    assumedProperties 
    invariants =

  (debug ind "Inductive step at k = %d" k in
   Event.log `IND Event.L_info "Inductive step loop at k=%d" k);

  Stat.set k Stat.ind_k;

  Stat.update_time Stat.ind_total_time; 

  (* Update state from messages received *)
  let (propertiesToCheck', assumedProperties', invariants', reset') =
    handle_events
      solver
      ts
      propertiesToCheck
      assumedProperties
      invariants
      k
      false
  in

  (* Assert invariants for instant k 

     TODO: Only when we have just incremented k? *)
  S.assert_term solver (TransSys.invars_of_bound (Numeral.of_int k) ts);

  (* Restart induction process if an assumed property is disproved *)
  if reset' then restart ts k invariants';
  
  (* Properties remain to check for current k? *)
  if List.length propertiesToCheck' <> 0 then

    (
    
      (* If the induction process checks for a new k, push the
         transition system to the new k and assert all invariants *)
      if preK <> k then

        (

          (* Assert invariants and valid properties at step k. Then
              push the transition function from (k-1)th step to kth
              step T(k-1, k), then begin the check. *)
          S.assert_term
            solver
            (Term.bump_state
               (Numeral.of_int k)
               (Term.mk_and
                  (List.map snd (List.map snd assumedProperties'))));

          S.assert_term
            solver
            (Term.bump_state
               (Numeral.of_int k)
               (Term.mk_and invariants'));

          S.assert_term
            solver
            (Term.bump_state
               (Numeral.of_int k)
               (Term.mk_and
                  (List.map snd ts.TransSys.props_valid)));

          S.assert_term
            solver
            (TransSys.trans_of_bound
               (Numeral.of_int k)
               ts);

        );

      S.push solver;

      (* Instantiate the properties upto step k-1 and at step k *)
      let propsUptoK_1 = 
          (TransSys.props_of_bound (Numeral.of_int (k-1)) ts)
      in

      let propsAtK = 
        List.map 
          (fun (name, prop) -> Term.bump_state (Numeral.of_int k) prop)
          propertiesToCheck' 
      in

      S.assert_term solver propsUptoK_1;

      S.assert_term solver (Term.mk_not (Term.mk_and propsAtK));
      
      (* If the transitions system does not entail the propertiesToCheck*)
      if (S.check_sat solver) then

        (
          
          let (propertiesToCheck', propertiesToCheckNextK') = 
            filter_properties solver ts (Numeral.of_int k) propertiesToCheck' 
          in

          List.iter
            (fun (name, prop) -> 
               (debug ind "Property %s falsified at induction step k = %d" name k end);)
propertiesToCheckNextK';
S.pop solver;
ind solver ts k k propertiesToCheck' (propertiesToCheckNextK@propertiesToCheckNextK') assumedProperties' invariants'
)
(* If the transitions system entails the propertiesToCheck*)
else
  (
    (* If BMC already pass induction k*)
    if !bmcK >= k then
      (
        List.iter
          (fun (name, prop) -> 
             (debug ind "Property %s proved at inductive step k = %d" name k end);) 
(propertiesToCheck'@(List.map snd assumedProperties'));
List.iter
  (Event.proved `IND (Some k)) 
  ((propertiesToCheck'@(List.map snd assumedProperties')));
if List.length propertiesToCheckNextK <> 0 then
  (
    S.pop solver;
    ind solver ts k (k+1) propertiesToCheckNextK [] [] invariants'
  )
)
else
  (
    let assumedProps = List.map (fun p -> (k, p)) propertiesToCheck' in 
    if List.length propertiesToCheckNextK <> 0 then
      (
        S.pop solver;
        ind solver ts k (k+1) propertiesToCheckNextK [] (assumedProps@assumedProperties') invariants'
      )
    else
      ( 
        (*write a reccursive function!!!!!!!!*)
        while ((!bmcK < k) || List.length assumedProperties <> 0) do
          (
            (*minisleep 0.5 sec to wait for BMC to catch up*)
            Lib.minisleep 0.5;
            let (propsToCheck, assumedProps, inv, reset') = 
              handle_events solver ts [] (assumedProps@assumedProperties') invariants' k false
            in
            if List.length propsToCheck <> 0 then
              (
                S.pop solver;
                ind solver ts k k propsToCheck [] [] invariants'
              )
          )done;
        List.iter 
          (fun (name, prop) -> 
             (debug ind "Property %s holds at induction step k = %d" name k end);) 
(propertiesToCheck'@(List.map snd assumedProperties'));
)
)
)
)
(* If there remains any properties to check*)
else if List.length propertiesToCheckNextK <> 0 then
  (
    ind solver ts k (k+1) propertiesToCheckNextK [] assumedProperties invariants'
  )
else
  (
    (debug ind "All good properties proved or disproved!" end);
)

(**Restart induction process whenever an assumed property is disproved*)
and restart ts k invariants = 

    Event.log `IND Event.L_info "Restart inductive step";
  
  Stat.incr Stat.ind_restarts;

  (* Delete solver instance *)
  (match !ref_solver with 
    | Some s -> S.delete_solver s
    | None -> ());

  let propertiesToCheck = 
    (list_subtract 
       (list_subtract ts.TransSys.props ts.TransSys.props_valid) ts.TransSys.props_invalid) 

  in
  
  init ts propertiesToCheck invariants k true


(* Initialize the inductive step *)
and init trans_sys propertiesToCheck invariants k reset =

    (* Determine logic for the SMT solver *)
    let logic = TransSys.get_logic trans_sys in

    (* Create solver instance *)
    let solver = 
      S.new_solver ~produce_assignments:true logic
    in
    
    (* Create a reference for the solver. Only used in on_exit. *)
    ref_solver := Some solver;

    (* Declare uninterpreted function symbols *)
    TransSys.iter_state_var_declarations
      trans_sys
      (S.declare_fun solver);
    
    (* Define functions *)
    TransSys.iter_uf_definitions
      trans_sys
      (S.define_fun solver);

    if reset then

      (

        (* Assert transition system for instants 0..k *)
        assert_trans_k solver trans_sys k;

        ind solver trans_sys (k - 1) k propertiesToCheck [] [] invariants

      )

    else

      (

        ind solver trans_sys 0 1 propertiesToCheck [] [] [] 

      )


(* Entry point *)
let main transSys =

  Stat.start_timer Stat.ind_total_time;

  let propertiesToCheck = transSys.TransSys.props in

  init transSys propertiesToCheck [] 1 false




  
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
