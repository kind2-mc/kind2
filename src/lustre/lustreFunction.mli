(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

(** A contract has an identifier and a position in the input. It
    consists of a state variable stands for the conjunction of its
    require clauses, and one state variable that stand for each ensure
    clause.

    The requirement of a global contract may be assumed
    invariant. Each ensures of a global or mode contract is a separate
    proof obligation for the node. 

    The conjunction of the requirements of all global contracts, and
    the disjunction of the requirements of all mode contracts is a
    proof obligation for all calling nodes. *)
type contract =
  { 

    contract_name : LustreIdent.t;
    (** Identifier of contract *)

    contract_pos: Lib.position;
    (** Position of the contract in the input *)

    contract_req : LustreExpr.expr;
    (** Invariant from requirements of contract *)

    contract_ens : LustreExpr.expr
    (** Invariant from ensures of contract *)

  }

type t = 

  {

    name : LustreIdent.t;
    (** Name of the function *)

    inputs : StateVar.t LustreIndex.t;
    (** Input streams to the function

        The inputs are considered as a list with an integer indexes
        correpsonding to their position in the formal parameters if
        there is more than one input parameter. If there is only one
        input parameter, the list index is omitted, the index is empty
        if there are no input parameters. *)

    outputs : StateVar.t LustreIndex.t;
    (** Output streams to the function

        The outputs are considered as a list with an integer indexes
        correpsonding to their position in the formal parameters. *)

    output_ufs : UfSymbol.t LustreIndex.t;
    (** Uninterpreted function symbol for output stream to enforce
        functionality constraint *)

    global_contracts : contract list;
    (** Global contracts *)

    mode_contracts : contract list;
    (** Mode contracts *)

  }

(** Return a function of the given name without inputs, outputs and
    contracts *)
val empty_function : LustreIdent.t -> t


(** Return the name of the node *)
val name_of_function : t -> LustreIdent.t

(** Return the scope of the node *)
val scope_of_function : t -> Scope.t


(** {1 Function Lists} *)

(** Return the function of the given name from a list of functions *)
val function_of_name : LustreIdent.t -> t list -> t 

(** Return true if a function of the given name exists in the a list of function *)
val exists_function_of_name : LustreIdent.t -> t list -> bool 


val pp_print_function : bool -> Format.formatter -> t -> unit
