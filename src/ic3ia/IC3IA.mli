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

(** Property-directed reachability (aka IC3) with Implicit Abstraction 

    Adaptation of the PDR algorithm implemented by JKind, based on
    "Efficient implementation of property directed reachability"
    by Niklas Een, Alan Mishchenko, and Robert Brayton.

    SMT extension based on "IC3 Modulo Theories via Implicit Predicate Abstraction"
    by Alessandro Cimatti, Alberto Griggio, Sergio Mover, and Stefano Tonetta

    @author Daniel Larraz *)

exception UnsupportedFeature of string

(** Entry point *)
val main : bool -> bool -> Property.t -> 'a InputSystem.t -> Analysis.param -> TransSys.t -> unit
    
(** Cleanup before exit *)
val on_exit : TransSys.t option -> unit
