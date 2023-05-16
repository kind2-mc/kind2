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

module TS = Term.TermSet

type t = TS.t

module CubeSet = Set.Make(TS)

module CubeMap = Map.Make(TS)

let empty = TS.empty

let add = TS.add

let remove = TS.remove

let literals = TS.elements

let subsumes = TS.subset

let contains = TS.mem

let to_term c = literals c |> Term.mk_and

let pp_print_cube fmt c =
   Format.fprintf fmt "%a" Term.pp_print_term (to_term c)
