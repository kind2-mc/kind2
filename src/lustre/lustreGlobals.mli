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

(** Global declarations for Lustre input 

    @author Christoph Sticksel *)

(** *)

module HStringMap = HString.HStringMap

type state_var_bounds = (LustreExpr.expr LustreExpr.bound_or_fixed list)
        StateVar.StateVarHashtbl.t

type adt_field_info =
  | AdtFieldPlain
  | AdtFieldNested of HString.t

type adt_info = {
  disc_field : HString.t;
  ctor_fields : (HString.t * adt_field_info) list HStringMap.t;
}

type adt_map = adt_info HStringMap.t

type t =
  {
    free_constants : (LustreIdent.t * Var.t LustreIndex.t * bool) list;
    (** Free constants: ident, variable index, is_generated *)

    state_var_bounds : state_var_bounds;
    (** Register bounds of state variables for later use *)

    global_constraints: LustreExpr.t list;
    (** Constraints on free constants *)

    adt_map : adt_map;
    (** ADT type metadata for counterexample reconstruction *)
  }

