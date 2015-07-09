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





let next_analysis_of_strategy (type s) : s t -> 'a -> Analysis.param option = function

  | Lustre subsystem -> 

    (function _ -> 
      
      let nodes = 
        LustreNode.nodes_of_subsystem subsystem
      in
      
      assert (nodes <> []);
      
      Some
        { Analysis.top = 
            List.hd nodes
            |> LustreNode.scope_of_node;
          Analysis.abstraction_map = 
            List.fold_left 
              (fun m n -> Scope.Map.add (LustreNode.scope_of_node n) false m)
              Scope.Map.empty nodes;
          Analysis.assumptions = [] }
    )
    
  | Native subsystem -> (function _ -> assert false)
  | Horn subsystem -> (function _ -> assert false)


(* Return a transition system with [top] as the main system, sliced to
   abstractions and implementations as in [abstraction_map. ]*)
let trans_sys_of_analysis (type s) : s t -> Analysis.param -> TransSys.t * s t = function 

  | Lustre subsystem -> 

    (function analysis -> 
      let t, s = 
        LustreTransSys.trans_sys_of_nodes subsystem analysis
      in
      (t, Lustre s)
      
    )
    
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



let slice_to_abstraction_and_term
    (type s)
    (input_sys: s t)
    analysis
    trans_sys
    term
  : s t = 

  (* Map term to the lowest subsystem *)
  let trans_sys', term' =  
    TransSys.term_map_to_subsystem trans_sys term
  in

  let analysis' = 
    { analysis with 
        Analysis.top = TransSys.scope_of_trans_sys trans_sys' }
  in

  match input_sys with 
    
    | Lustre subsystem -> 

      Lustre
        (LustreSlicing.slice_to_abstraction_and_property
           analysis'
           term'
           subsystem)
                            
  | Native subsystem -> Native subsystem

  | Horn subsystem -> Horn subsystem



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
