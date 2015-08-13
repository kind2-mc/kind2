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

module A = Analysis
module Sys = TransSys

let get_params results subs_of_scope sys =
  let subs = subs_of_scope sys in
  try (
    match A.results_find sys results with
    | [] -> assert false
    | result :: _ ->
      let abstraction, assumptions =
        result.A.param.A.abstraction_map, result.A.param.A.assumptions
      in
      None
  ) with Not_found -> Some (
    (* First time analyzing this system, abstracting everything. *)
    subs |> List.fold_left (fun abs (scope, b) ->
      Scope.Map.add scope b abs
    ) (Scope.Map.empty)
  )

module type Strategy = sig
  val next_analysis:
    A.results -> (Scope.t -> (Scope.t * bool) list) -> (Scope.t * bool) list ->
    A.param option
end

module MonolithicStrategy : Strategy = struct
  let next_analysis results subs_of_scope = function
    | (top,_) :: tail -> (
      try (
        match A.results_find top results with
        | [] -> assert false
        (* Not the first analysis, done. *)
        | _ -> None
      ) with Not_found -> Some { (* First analysis, creating [A.param]. *)
        (* We will analyze the top node. *)
        A.top = top ;
        (* All sub-systems are concrete. *)
        A.abstraction_map = tail |> List.fold_left (fun map (scope,_) ->
          Scope.Map.add scope false map
        ) (Scope.Map.empty) ;
        (* No assumption. *)
        A.assumptions = [] ;
      }
    )
    | [] -> failwith "[strategy] \
      no system to analyze (empty list of scopes)\
    "
end


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
