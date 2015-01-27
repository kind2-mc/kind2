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


(** Term or lambda expression *)
type term_or_lambda = Term of Term.t | Lambda of Term.lambda
    
(** A model is a list of variables and assignemnts *)
type t = term_or_lambda Var.VarHashtbl.t

(** A path is a map of state variables to assignments *)
type path = term_or_lambda list StateVar.StateVarHashtbl.t

(** An empty model *)
val empty_model : t


(** Extract a path in the transition system, return an association
    list of state variables to a list of their values.

    The second argument is a function returning assignments to the
    variables, see {!SolverMethods.S.get_model}. The path is extracted
    from instant zero up to instant [k], which is the third argument. *)
val path_from_model : StateVar.t list -> (Var.t list -> t) -> Numeral.t -> path


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
