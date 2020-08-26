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


module LA = LustreAst

module G = Graph.Make(struct
               type t = LustreAst.ident * LA.declaration list
               let compare (i1, _) (i2, _) = Stdlib.compare i1 i2
               let pp_print_t = Lib.pp_print_pair LA.pp_print_ident Lib.pp_print_ignore ""
             end)
                               
let rec mk_graph_type: LA.lustre_type -> G.t = function
  | TVar (_, i) -> G.singleton (i, [])
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
  | Real _ -> G.empty
  | IntRange (_, e1, e2) -> G.union (mk_graph_expr e1) (mk_graph_expr e2)
  | UserType (_, i) -> G.singleton (i, [])
  | AbstractType  (_, i) -> G.singleton (i, [])
  | TupleType (_, tys) -> List.fold_left G.union G.empty (List.map (fun t -> mk_graph_type t) tys)
  | RecordType (_, ty_ids) -> List.fold_left G.union G.empty (List.map (fun (_, _, t) -> mk_graph_type t) ty_ids)
  | ArrayType (_, (ty, e)) -> G.union (mk_graph_type ty) (mk_graph_expr e)
  | EnumType _ -> G.empty
  | TArr (_, aty, rty) -> G.union (mk_graph_type aty) (mk_graph_type rty)
      
and mk_graph_expr: LA.expr -> G.t
  = function
    (* Identifiers *)
  | Ident (_, i) -> G.singleton (i, [])
  | ModeRef (_, is) -> List.fold_left G.union G.empty (List.map (fun i -> G.singleton (i, [])) is)

  | RecordProject _ 
  | TupleProject _ -> G.empty
  (* Values *)
  | Const (p, c) -> G.empty
  (* Operators *)
   | UnaryOp (_, _, e) -> mk_graph_expr e 
   | BinaryOp (_, _, e1, e2) -> G.union (mk_graph_expr e1) (mk_graph_expr e2)
   (* | TernaryOp of position * ternary_operator * expr * expr * expr
   * | NArityOp of position * n_arity_operator * expr list
   * | ConvOp of position * conversion_operator * expr
   * | CompOp of position * comparison_operator * expr * expr
   * (\* Structured expressions *\)
   * | RecordExpr of position * ident * (ident * expr) list
   * | GroupExpr of position * group_expr * expr list
   * (\* Update of structured expressions *\)
   * | StructUpdate of position * expr * label_or_index list * expr
   * | ArrayConstr of position * expr * expr 
   * | ArraySlice of position * expr * (expr * expr) 
   * | ArrayIndex of position * expr * expr
   * | ArrayConcat of position * expr * expr
   * (\* Quantified expressions *\)
   * | Quantifier of position * quantifier * typed_ident list * expr
   * (\* Clock operators *\)
   * | When of position * expr * clock_expr
   * | Current of position * expr
   * | Condact of position * expr * expr * ident * expr list * expr list
   * | Activate of position * ident * expr * expr * expr list
   * | Merge of position * ident * (ident * expr) list
   * | RestartEvery of position * ident * expr list * expr
   * (\* Temporal operators *\)
   * | Pre of position * expr
   * | Last of position * ident
   * | Fby of position * expr * int * expr
   * | Arrow of position * expr * expr
   * (\* Node calls *\)
   * | Call of position * ident * expr list
   * | CallParam of position * ident * lustre_type list * expr list *)
  | _ -> Lib.todo __LOC__

and mk_graph_type_decl: Lib.position -> LA.type_decl -> G.t = fun pos ->
  function
  | FreeType (_, i) as ty -> G.singleton (i, [LA.TypeDecl (pos, ty)]) 
  | AliasType (_, i, ety) as ty -> G.connect (mk_graph_type ety) (i, [LA.TypeDecl (pos, ty)])

let mk_graph_const_decl: LA.const_decl -> G.t =
  function
  | FreeConst (_, i, _) -> G.singleton (i, [])
  | UntypedConst (_, i, e) -> G.connect (mk_graph_expr e) (i, [])  
  | TypedConst (_, i, e, ty) -> G.connect (G.union (mk_graph_type ty) (mk_graph_expr e)) (i, [])
                              
let get_graph: LA.declaration -> G.t =
  function
  | TypeDecl (pos, tydecl) -> mk_graph_type_decl pos tydecl 
  | ConstDecl (_, cdecl) -> mk_graph_const_decl cdecl
  | NodeDecl _ -> Lib.todo __LOC__
  | FuncDecl _ -> Lib.todo __LOC__
  | ContractNodeDecl  _ -> Lib.todo __LOC__ 
  | NodeParamInst  _ -> Lib.todo __LOC__

let rec dependency_graph_decls: LA.t -> G.t
  = fun decls -> 
  List.fold_left G.union G.empty (List.map get_graph decls)
                      
and sort_type_decls: LA.t -> (LA.ident * LA.t) list = fun decls ->
  let is_type_or_const_decl: LA.declaration -> bool = fun d ->
    match d with
    | TypeDecl _
      | ConstDecl _ -> true
    | _ -> false in
  let type_or_const_decls = List.filter (is_type_or_const_decl) decls in
  let dg = dependency_graph_decls type_or_const_decls in
  G.topological_sort (dg)                                   

  
and sort_decls: LA.t -> (LA.ident * LA.t) list = fun _ -> Lib.todo __LOC__
