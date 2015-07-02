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

type _ t = 
  | Lustre : LustreNode.t SubSystem.t -> LustreNode.t t
  | Native : unit SubSystem.t -> unit t
  | Horn : unit SubSystem.t -> unit t


let read_input_lustre input_file = Lustre (LustreInput.of_file input_file) 

let read_input_native input_file = assert false 

let read_input_horn input_file = assert false 




(*
let next_analyis (type s) : s t -> 'a ->  (SubSystem.scope * (SubSystem.scope * bool) list) option = function

  | Lustre subsystem -> Refiner.next_analysis subsystem 
  | Native subsystem -> Refiner.next_analysis subsystem 
  | Horn subsystem -> Refiner.next_analysis subsystem 
*)

(* Return a transition system with [top] as the main system, sliced to
   abstractions and implementations as in [abstraction_map. ]*)
let trans_sys_of_analysis (type s) : s t -> Analysis.param -> TransSys.t = function 

  | Lustre subsystem -> 

    (function analysis -> LustreTransSys.trans_sys_of_nodes subsystem analysis)
    
  | Native _ -> assert false
    
  | Horn _ -> assert false



let pp_print_path_pt (type s) : s t -> TransSys.t -> bool -> Format.formatter -> Model.path -> unit = function 

  | Lustre subsystem -> (fun t b ppf m -> LustrePath.pp_print_path_pt t subsystem b ppf m)

  | Native _ -> (fun _ _ _ -> assert false)

  | Horn _ -> (fun _ _ _ -> assert false)


let pp_print_path_xml (type s) : s t -> TransSys.t -> bool -> Format.formatter -> Model.path -> unit = function 

  | Lustre subsystem -> (fun t b ppf m -> LustrePath.pp_print_path_xml t subsystem b ppf m)

  | Native _ -> (fun _ _ _ -> assert false)

  | Horn _ -> (fun _ _ _ -> assert false)



let slice_to_term (type s) (subsystem : s t) term : s SubSystem.t = match subsystem with 

  | Lustre subsystem -> subsystem

  | Native subsystem -> subsystem

  | Horn subsystem -> subsystem



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
