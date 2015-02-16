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

type abstraction = string list list

(* Pretty prints an abstraction. *)
let pp_print_abstraction ppf =
  Format.fprintf
    ppf
    "@[<v>%a@]"
    (pp_print_list
       (pp_print_list Format.pp_print_string ".")
       ",@,")

let first_abstraction sys =
  TransSys.get_all_subsystems sys
  |> List.filter
       (fun s ->
        sys != s
        && (TransSys.get_contracts s <> []))
  |> List.map TransSys.get_scope

(* Looks for a system to refine. *)
let refine sys = function

  | [] ->
     (* Cannot refine an empty abtsraction. *)
     Format.printf "Cannot refine an empty abstraction.\n" ;
     None

  | abstraction ->
     let all_sys =
       TransSys.get_all_subsystems sys
       (* Reversing to start from top level. *)
       |> List.rev
     in

     (* Loops over the subsystem, looks for a refinable subsystem. *)
     let rec loop = function
       | subsys :: tail ->
          let sub_scope = TransSys.get_scope subsys in

          if List.mem sub_scope abstraction then (
            (* [subsys] is currently abstracted, can we refine it? *)

            if
              (* All subrequirements for [subsys] hold for [sys] *)
              TransSys.proved_requirements_of sys sub_scope
              (* and we previously proved [subsys] respects its
                 contract. *)
              && TransSys.is_contract_proved subsys
              (* and subsys proved all its subrequirements. *)
              && TransSys.subrequirements_valid subsys
            then (

              Event.log
                L_info
                "Resetting properties to unknown." ;

              
              TransSys.reset_non_valid_props_to_unknown sys ;
              TransSys.reset_invariants sys ;

              (* Refining [subsys], removing it from abstraction. *)
              Some
                  ( abstraction
                    |> List.filter
                         (fun scope -> scope <> sub_scope) )


            )

            else (

              (* Condition for refinement not satisfied. Looping. *)
              loop tail
            )

          ) else
            (* [subsys is currently not abtracted, looping. *)
            loop tail

       | [] ->
          (* Found nothing to abstract. *)
          None

     in

     loop all_sys


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
