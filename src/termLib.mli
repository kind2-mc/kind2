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

(** Utilty functions for transition systems 

    Functions that use term data structures and can be used by
    any module above {!TransSys} go here.
*)

type invariants = Term.t list
type model = (Var.t * Term.t) list
type path = (StateVar.t * Term.t list) list
type property = (string * Term.t)
type properties = property list
type cex = (property list * path)
type cexs = cex list


(** {1 Properties of transition systems} *)


(** Source of a contract. *)
type contract_source =

  (** Contract is from an annotation. *)
  | ContractAnnot of string * Lib.position

(** Source of a property *)
type prop_source =

  (** Property is from an annotation *)
  | PropAnnot of Lib.position

  (** Property comes from a contract of a node. *)
  | Contract of contract_source

  (** Property is a requirement for a subsystem: scope of the
      subsystem and position. *)
  | SubRequirement of ((string list * Lib.position) list * string list * Lib.position)

  (** Property was generated, for example, from a subrange
      constraint *)
  | Generated of StateVar.t list

  (** Property is an instance of a property in a called node

      Reference the instantiated property by the [scope] of the
      subsystem and the name of the property *)
  | Instantiated of string list * string 



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
