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

type t

module CubeSet : Set.S with type elt = t

module CubeMap : Map.S with type key = t

val empty : t

val add : Term.t -> t -> t

val remove : Term.t -> t -> t

val literals : t -> Term.t list

val subsumes : t -> t -> bool

val contains : Term.t -> t -> bool

val to_term : t -> Term.t

val pp_print_cube : Format.formatter -> t -> unit
