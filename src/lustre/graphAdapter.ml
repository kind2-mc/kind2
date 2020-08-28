(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020 by the Board of Trustees of the University of Iowa

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

(** Converts the graph 
   
   @author Apoorv Ingle *)

module R = Res
module LA = LustreAst
(* type payload = {k:LustreAst.ident; v:LA.declaration option}
 * let payload_compare p1 p2 = Stdlib.compare p1.k p2.k *)
                          
module G = Graph.Make(struct
               type t = LA.ident
               let compare = Stdlib.compare
               let pp_print_t = LA.pp_print_ident
             end)

module IMap = Map.Make(struct
                  type t = LA.ident
                  let compare i1 i2 = Stdlib.compare i1 i2
                end)

type 'a graph_result = ('a, Lib.position * string) result  
let graph_error err = Error (Lib.dummy_pos, err)
let (>>=) = R.(>>=)                     

let rec mk_graph_type: LA.lustre_type -> G.t = function
  | TVar (_, i) -> G.singleton i
  | Bool _
  | Int _
  | UInt8 _
  | UInt16 _
  | UInt32 _ 
  | UInt64 _ 
  | Int8 _ 
  | Int16 _
  | Int32 _
  | Int64 _
  | Real _
  | EnumType _ -> G.empty
  | IntRange (_, e1, e2) -> G.union (mk_graph_expr e1) (mk_graph_expr e2)
  | UserType (_, i) -> G.singleton i
  | AbstractType  (_, i) -> G.singleton i
  | TupleType (_, tys) -> List.fold_left G.union G.empty (List.map (fun t -> mk_graph_type t) tys)
  | RecordType (_, ty_ids) -> List.fold_left G.union G.empty (List.map (fun (_, _, t) -> mk_graph_type t) ty_ids)
  | ArrayType (_, (ty, e)) -> G.union (mk_graph_type ty) (mk_graph_expr e)
  | TArr (_, aty, rty) -> G.union (mk_graph_type aty) (mk_graph_type rty)
      
and mk_graph_expr: LA.expr -> G.t
  = function
  | LA.Ident (_, i) -> G.singleton i
  | LA.Const _ -> G.empty
  | LA.UnaryOp _ -> Lib.todo __LOC__
  | LA.BinaryOp _ ->Lib.todo __LOC__
  | LA.TernaryOp _ -> Lib.todo __LOC__
  | _ -> Lib.todo __LOC__
  
let mk_graph_const_decl: LA.const_decl -> G.t
  = function
  | FreeConst (_, i, _) -> G.singleton i
  | UntypedConst (_, i, e) -> G.connect (mk_graph_expr e) i 
  | TypedConst (_, i, e, ty) -> G.connect (G.union (mk_graph_expr e) (mk_graph_type ty)) i

                                  
let mk_graph_type_decl: LA.type_decl -> G.t
  = function
  | FreeType (_, i) -> G.singleton i 
  | AliasType (_, i, ty) -> G.connect (mk_graph_type ty) i
 
let mk_graph: LA.declaration ->  G.t = function
  | TypeDecl (pos, tydecl) -> mk_graph_type_decl tydecl 
  | ConstDecl (pos, cdecl) -> mk_graph_const_decl cdecl
  | NodeDecl _ -> Lib.todo __LOC__
  | FuncDecl _ -> Lib.todo __LOC__
  | ContractNodeDecl  _ -> Lib.todo __LOC__ 
  | NodeParamInst  _ -> Lib.todo __LOC__

let rec mk_decl_map: LA.t -> LA.declaration IMap.t =
  function  
  | [] -> IMap.empty
  | (LA.TypeDecl (_, FreeType (_, i)) as tyd) :: decls ->
     IMap.union (fun k v1 v2 -> Some v2) (IMap.singleton i tyd) (mk_decl_map decls)  
  | (LA.TypeDecl (_, AliasType (_, i, _)) as tyd) :: decls ->
     IMap.union (fun k v1 v2 -> Some v2) (IMap.singleton i tyd) (mk_decl_map decls)
  | (LA.ConstDecl (_, FreeConst (_, i, _)) as cnstd) :: decls ->
     IMap.union (fun k v1 v2 -> Some v2) (IMap.singleton i cnstd) (mk_decl_map decls)
  | (LA.ConstDecl (_, UntypedConst (_, i, _)) as cnstd) :: decls ->
     IMap.union (fun k v1 v2 -> Some v2) (IMap.singleton i cnstd) (mk_decl_map decls)
  | (LA.ConstDecl (_, TypedConst (_, i, e, ty)) as cnstd) :: decls ->
     IMap.union (fun k v1 v2 -> Some v2) (IMap.singleton i cnstd) (mk_decl_map decls)
  | NodeDecl _ :: _-> Lib.todo __LOC__
  | FuncDecl _ :: _-> Lib.todo __LOC__
  | ContractNodeDecl _ :: _ -> Lib.todo __LOC__ 
  | NodeParamInst _ :: _-> Lib.todo __LOC__

                      
let dependency_graph_decls: LA.t -> G.t
  = fun decls ->
  List.fold_left G.union G.empty (List.map mk_graph decls)

let rec extract_decls: LA.declaration IMap.t -> LA.ident list -> LA.t graph_result
  = fun decl_map ->
  function
  | [] -> R.ok []
  | i :: is -> (try (R.ok (IMap.find i decl_map)) with
                | Not_found -> graph_error ("Identifier " ^ i ^ " is not defined."))
               >>= (fun d -> (extract_decls decl_map is)
                             >>= (fun ds -> R.ok (d :: ds)))
                              
    
and sort_type_and_const_decls: LA.t -> LA.t graph_result = fun decls ->
  let is_type_or_const_decl: LA.declaration -> bool = fun d ->
    match d with
    | TypeDecl _
      | ConstDecl _ -> true
    | _ -> false in
  (* 1. get all type and constant declarations  *)
  let type_or_const_decls = List.filter (is_type_or_const_decl) decls in
  (* 2. make an id :-> decl map  *)
  let decl_map = mk_decl_map decls in
  (* build a dependency graph *)
  let dg = dependency_graph_decls type_or_const_decls in
  (* 3. try to sort it, raise an error if it is cyclic, or extract decls from the decl_map *)
  (try (R.ok (G.topological_sort dg)) with
   | Graph.CyclicGraphException ->
      graph_error ("Cyclic dependency in declaration of types or constants detected"))
  >>= fun sorted_ids -> extract_decls decl_map sorted_ids                          
  
and sort_decls: LA.t -> LA.t graph_result = fun _ -> Lib.todo __LOC__

