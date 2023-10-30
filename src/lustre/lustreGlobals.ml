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

(* Abbreviations *)
module E = LustreExpr

type t = 

  { 

    (* Free constants *)
    free_constants : (LustreIdent.t * Var.t LustreIndex.t) list;
    
    (* register bounds of state variables for later use *)
    state_var_bounds : (E.expr E.bound_or_fixed list) StateVar.StateVarHashtbl.t;

    (* Constraints on free constants *)
    global_constraints: E.t list;
  }

