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

(** Removes multiple assignment from an if block by pulling out equations
   with multiple assignment and using temp variables. 
  Example: 
   if cond
   then 
      y1, y2 = node(expr1);
   else
      y1 = expr2;
      y2 = expr3;
   fi
  -->
   t1, t2 = node(expr1);
   if cond
   then 
      y1 = t1;
      y2 = t2;
   else
      y1 = expr2;
      y2 = expr3;
   fi

  For each temp variable, we also generate a new declaration.

  @author Rob Lorch
*)

(** Desugars a declaration list to remove multiple assignment from if blocks and frame
    blocks. *)
val remove_mult_assign : TypeCheckerContext.tc_context -> LustreAst.declaration list -> LustreAst.declaration list * GeneratedIdentifiers.t GeneratedIdentifiers.StringMap.t
