(* This file is part of the Kind 2 model checker.

   Copyright (c) 2025 by the Board of Trustees of the University of Iowa

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

 (** @author Rob Lorch *)

(** Print the response to a check, given the systems of its groups of
    queries, analyzed or not *)
val pp_print_results: MoxiInput.check -> TransSys.t list -> unit

(** The term with every atom that uses a variable of an enumeration sort
    other than in an equation with its values written as a case split over
    the values of these variables, as certificates are printed (exposed for
    testing) *)
val split_enum_atoms : Term.t -> Term.t
