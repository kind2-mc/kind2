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
  | Horn : unit -> unit t


let read_input () = 

  let input_file = Flags.input_file () in

  match Flags.input_format () with 

    | `Lustre -> Lustre (LustreInput.of_file input_file) 
    | `Native -> assert false
    | `Horn -> assert false


let next_analyis (type s) : s t -> 'a ->  (SubSystem.scope * (SubSystem.scope * bool) list) option = function

  | Lustre subsystem -> Refiner.next_analysis subsystem 
  | Native subsystem -> Refiner.next_analysis subsystem 
  | Horn subsystem -> Refiner.next_analysis subsystem 


(* Return a transition system with [top] as the main system, sliced to
   abstractions and implementations as in [abstraction_map. ]*)
let trans_sys_of_analysis (type s) : s t -> (SubSystem.scope * (SubSystem.scope * bool) list) -> TransSys.t = function 

  | Lustre subsystem -> (function (top, abstraction_map) ->

      LustreTransSys.trans_sys_of_nodes subsystem top abstraction_map)
    
  | Native _ -> (function _ -> assert false)
    
  | Horn _ -> (function _ -> assert false)



let pp_print_path_pt (type s) : s t -> bool -> Format.formatter -> Model.path -> unit = function 

  | Lustre subsystem -> (fun b ppf m -> LustrePath.pp_print_path_pt b ppf m)

  | Native _ -> (fun _ _ _ -> assert false)

  | Horn _ -> (fun _ _ _ -> assert false)


let pp_print_path_xml (type s) : s t -> bool -> Format.formatter -> Model.path -> unit = function 

  | Lustre { source } -> (fun b ppf m -> LustrePath.pp_print_path_xml b ppf m)

  | Native _ -> (fun _ _ _ -> assert false)

  | Horn _ -> (fun _ _ _ -> assert false)




(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
