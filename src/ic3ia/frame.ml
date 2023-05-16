(* This file is part of the Kind 2 model checker.

   Copyright (c) 2022 by the Board of Trustees of the University of Iowa

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

module CS = Cube.CubeSet

type t =
  | Ft of Term.t
  | Fi of CS.t

let empty = Fi CS.empty

let is_empty = function
  | Fi cubes -> CS.is_empty cubes
  | _ -> false

let mk_frame t = Ft t

let cubes = function
  | Fi cubes -> cubes
  | _ -> assert false

let to_term = function
  | Ft t -> t
  | Fi cubes -> (
    CS.elements cubes
    |> List.map (fun c -> Cube.to_term c |> Term.mk_not)
    |> Term.mk_and
  )