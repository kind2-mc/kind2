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

(** Simplify a Lustre AST to normalized Lustre nodes 

    

    @author Christoph Sticksel
*)

val eval_ast_expr :
  LustreExpr.expr LustreExpr.bound_or_fixed list -> LustreContext.t ->
  LustreAst.expr -> LustreExpr.t LustreIndex.t * LustreContext.t

val eval_ast_type :
  LustreContext.t -> LustreAst.lustre_type -> Type.t LustreIndex.t

val eval_ast_type_flatten :
  bool -> LustreContext.t -> LustreAst.lustre_type -> Type.t LustreIndex.t

val eval_bool_ast_expr :
  LustreExpr.expr LustreExpr.bound_or_fixed list ->  LustreContext.t ->
  Lib.position -> LustreAst.expr -> LustreExpr.t * LustreContext.t

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
