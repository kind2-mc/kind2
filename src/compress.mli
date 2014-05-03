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

(** Simulation relation for compression *)
module type CompressionPred =
sig val p : (Term.t * Term.t) list -> bool end

(** Output signature of functor *)
module type S =
sig

  (** [compress_path t m] checks if the path in [m] is compressible for
      the transition system [t], and returns a constraint to block the
      compressible path *)
  val compress_path : TransSys.t -> (Var.t * Term.t) list -> Term.t

end

module Equal : CompressionPred

module Make (P: CompressionPred) : S



(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
