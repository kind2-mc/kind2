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

(** Graph analysis on Lustre Ast Declarations  
    Builds a dependency graph of the lustre declarations,
    to detect circular dependencies and reject them and
    re-orders node and contract declarations to resolve
    forward references   

   @author: Apoorv Ingle *)

module R = Res
module LA = LustreAst
                          
module G = Graph.Make(struct
               type t = LA.ident
               let compare = Stdlib.compare
               let pp_print_t = LA.pp_print_ident
             end)

module IMap = Map.Make(struct
                  type t = LA.ident
                  let compare i1 i2 = Stdlib.compare i1 i2
                end)

type id_pos_map = (Lib.position list) IMap.t 
(** stores all the positions of the occurance of an id *)
                
let add_pos: id_pos_map -> LA.ident -> Lib.position -> id_pos_map = fun m i p ->
  IMap.update i
    (function
     | None -> Some (p :: [])
     | Some ps -> Some (p :: ps))
    m
let union_pos: id_pos_map -> id_pos_map -> id_pos_map = fun m1 m2 ->
  IMap.union (fun k v1 v2 -> Some (v1@v2)) m1 m2

let singleton_pos: LA.ident -> Lib.position -> id_pos_map = fun i p ->
  IMap.singleton i (p::[])

let find_id_pos: id_pos_map -> LA.ident -> Lib.position option = fun m i ->
  match (IMap.find_opt i m) with
  | None -> None
  | Some [] -> None
  | Some (p::ps) -> Some p 
  
let singleton_g_pos: string -> LA.ident -> Lib.position -> (G.t * id_pos_map) =
  fun suffix i p -> (G.singleton (suffix ^ i), singleton_pos (suffix ^ i) p) 

let union_g_pos: (G.t * id_pos_map) -> (G.t * id_pos_map) -> (G.t * id_pos_map) = 
  fun (g1, pos_m1) (g2, pos_m2) -> (G.union g1 g2, union_pos pos_m1 pos_m2)

let empty_g_pos: (G.t * id_pos_map) = (G.empty, IMap.empty) 

let connect_g_pos: (G.t * id_pos_map) -> LA.ident -> Lib.position -> (G.t * id_pos_map) =
  fun (g, pos_m) i p -> (G.connect g i, add_pos pos_m i p)  

                      
type 'a graph_result = ('a, Lib.position * string) result  
let graph_error pos err = Error (pos, err)
let (>>=) = R.(>>=)                     

          
(* Suffixes for declaration types *)
let ty_suffix = "type "
let const_suffix = ""
let node_suffix = ""
let contract_suffix = "contract "
let mode_suffix = "mode "

                
let rec mk_graph_type: LA.lustre_type -> (G.t * id_pos_map) = function
  | TVar (pos, i) -> singleton_g_pos ty_suffix i pos
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
  | EnumType _ -> (G.empty, IMap.empty)
  | IntRange (_, e1, e2) -> let g1, pos_m1 = (mk_graph_expr e1) in
                            let g2, pos_m2 = (mk_graph_expr e2) in
                            (G.union g1 g2, union_pos pos_m1 pos_m2)
  | UserType (pos, i) -> singleton_g_pos ty_suffix i pos
  | AbstractType (pos, i) -> singleton_g_pos ty_suffix i pos
  | TupleType (pos, tys) -> List.fold_left union_g_pos empty_g_pos  (List.map (fun t -> mk_graph_type t) tys)
  | RecordType (pos, ty_ids) -> List.fold_left union_g_pos empty_g_pos (List.map (fun (_, _, t) -> mk_graph_type t) ty_ids)
  | ArrayType (_, (ty, e)) -> union_g_pos (mk_graph_type ty) (mk_graph_expr e)
  | TArr (_, aty, rty) -> union_g_pos (mk_graph_type aty) (mk_graph_type rty)
      
and mk_graph_expr: LA.expr -> (G.t * id_pos_map)
  = function
  | LA.Ident (pos, i) -> singleton_g_pos "" i pos
  | LA.Const _ -> empty_g_pos
  | LA.RecordExpr (_, _, ty_ids) ->
     List.fold_left union_g_pos empty_g_pos (List.map (fun ty_id -> mk_graph_expr (snd ty_id)) ty_ids)
  | LA.UnaryOp (_, _, e) -> mk_graph_expr e
  | LA.BinaryOp (_, _, e1, e2) -> union_g_pos (mk_graph_expr e1) (mk_graph_expr e2) 
  | LA.CompOp (_, _, e1, e2) -> union_g_pos (mk_graph_expr e1) (mk_graph_expr e2) 
  | LA.TernaryOp (_, _, e1, e2, e3) -> union_g_pos (mk_graph_expr e1)
                                         (union_g_pos (mk_graph_expr e2) (mk_graph_expr e3)) 
  | LA.RecordProject (_, e, _) -> mk_graph_expr e
  | LA.TupleProject (_, e, _) -> mk_graph_expr e
  | LA.ArrayConstr (_, e1, e2) -> union_g_pos (mk_graph_expr e1) (mk_graph_expr e2) 
  | LA.ArraySlice (_, e1, (e2, e3)) -> union_g_pos (union_g_pos (mk_graph_expr e1) (mk_graph_expr e2)) (mk_graph_expr e3) 
  | LA.ArrayIndex (_, e1, e2) -> union_g_pos (mk_graph_expr e1) (mk_graph_expr e2)
  | LA.ArrayConcat  (_, e1, e2) -> union_g_pos (mk_graph_expr e1) (mk_graph_expr e2)
  | LA.GroupExpr (_, _, es) -> List.fold_left union_g_pos empty_g_pos (List.map mk_graph_expr es)
  | LA.Pre (_, e) -> mk_graph_expr e
  | LA.Last (pos, i) -> singleton_g_pos "" i pos
  | LA.Fby (_, e1, _, e2) ->  union_g_pos (mk_graph_expr e1) (mk_graph_expr e2) 
  | LA.Arrow (_, e1, e2) ->  union_g_pos (mk_graph_expr e1) (mk_graph_expr e2) 
  | _ -> Lib.todo __LOC__
  
let mk_graph_const_decl: LA.const_decl -> (G.t * id_pos_map)
  = function
  | LA.FreeConst (pos, i, ty) -> connect_g_pos (mk_graph_type ty) (const_suffix ^ i) pos
  | LA.UntypedConst (pos, i, e) -> connect_g_pos (mk_graph_expr e) (const_suffix ^ i) pos 
  | LA.TypedConst (pos, i, e, ty) -> connect_g_pos (union_g_pos (mk_graph_expr e) (mk_graph_type ty)) (const_suffix ^ i) pos 

                                  
let mk_graph_type_decl: LA.type_decl -> (G.t * id_pos_map)
  = function
  | FreeType (pos, i) -> singleton_g_pos ty_suffix  i pos 
  | AliasType (pos, i, ty) -> connect_g_pos (mk_graph_type ty) (ty_suffix ^ i) pos

let rec mk_graph_contract_node_eqn: LA.contract_node_equation -> (G.t * id_pos_map)
  = function
  | LA.ContractCall (pos, i, _, _) -> singleton_g_pos contract_suffix i pos
  | LA.Assume (_, _, _, e) ->
     List.fold_left union_g_pos empty_g_pos
       (List.map (fun (i, p) -> singleton_g_pos node_suffix i p) (get_node_call_from_expr e))
  | LA.Guarantee (_, _, _, e) ->
     List.fold_left union_g_pos empty_g_pos
       (List.map (fun (i, p) -> singleton_g_pos node_suffix i p) (get_node_call_from_expr e))
  | LA.Mode (_, _, reqs, ensures) ->
     let calls_ps = List.map (fun (_,_, e) -> e) (reqs @ ensures) in
     let sub_graphs = List.map (mk_graph_expr) calls_ps in
     List.fold_left union_g_pos empty_g_pos sub_graphs
  | _ -> empty_g_pos

and get_node_call_from_expr: LA.expr -> (LA.ident * Lib.position) list
  = function
  | Ident _
  | ModeRef _
  | RecordProject _ -> [] 
  | TupleProject (_, e, _) -> get_node_call_from_expr e
  (* Values *)
  | LA.Const _ -> []
  (* Operators *)
  | LA.UnaryOp (_, _, e) -> get_node_call_from_expr e
  | LA.BinaryOp (_, _, e1, e2) -> (get_node_call_from_expr e1)
                                  @ (get_node_call_from_expr e2)
  | LA.TernaryOp (_, _, e1, e2, e3) -> (get_node_call_from_expr e1)
                                       @ (get_node_call_from_expr e2)
                                       @ (get_node_call_from_expr e3)
  | LA.NArityOp (_, _, es) -> List.flatten (List.map get_node_call_from_expr es)
  | LA.ConvOp (_, _, e) -> get_node_call_from_expr e
  | LA.CompOp (_, _, e1, e2) -> (get_node_call_from_expr e1) @ (get_node_call_from_expr e2)
  (* Structured expressions *)
  | LA.RecordExpr (_, _, id_exprs) -> List.flatten (List.map (fun (_, e) -> get_node_call_from_expr e) id_exprs)
  | LA.GroupExpr (_, _, es) -> List.flatten (List.map get_node_call_from_expr es) 
  (* Update of structured expressions *)
  | LA.StructUpdate (_, _, _, e) -> get_node_call_from_expr e
  | LA.ArrayConstr (_, e1, e2) -> (get_node_call_from_expr e1) @ (get_node_call_from_expr e2)
  | LA.ArraySlice (_, e1, (e2, e3)) -> (get_node_call_from_expr e1)
                                       @ (get_node_call_from_expr e2)
                                       @ (get_node_call_from_expr e3)
  | LA.ArrayIndex (_, e1, e2) -> (get_node_call_from_expr e1) @ (get_node_call_from_expr e2)
  | LA.ArrayConcat (_, e1, e2) -> (get_node_call_from_expr e1) @ (get_node_call_from_expr e2)
  (* Quantified expressions *)
  | LA.Quantifier (_, _, _, e) -> get_node_call_from_expr e 
  (* Clock operators *)
  | LA.When (_, e, _) -> get_node_call_from_expr e
  | LA.Current (_, e) -> get_node_call_from_expr e
  | LA.Condact (pos, _,_, i, _, _) -> [(node_suffix ^ i, pos)]
  | LA.Activate (pos, i, _, _, _) -> [(node_suffix ^ i, pos)]
  | LA.Merge (_, _, id_exprs) ->
     List.flatten (List.map (fun (_, e) -> get_node_call_from_expr e) id_exprs)
  | LA.RestartEvery (pos, i, es, e1) ->
     (node_suffix ^ i, pos)
     :: (List.flatten (List.map get_node_call_from_expr es)) @ get_node_call_from_expr e1
  (* Temporal operators *)
  | LA.Pre (_, e) -> get_node_call_from_expr e
  | LA.Last _ -> []
  | LA.Fby (_, e1, _, e2) -> (get_node_call_from_expr e1) @ (get_node_call_from_expr e2)
  | LA.Arrow (_, e1, e2) -> (get_node_call_from_expr e1) @ (get_node_call_from_expr e2)
  (* Node calls *)
  | LA.Call (pos, i, es) -> (node_suffix ^ i, pos) :: List.flatten (List.map get_node_call_from_expr es)
  | LA.CallParam _ -> []

let mk_graph_contract_decl: LA.contract_node_decl -> (G.t * id_pos_map)
  = fun (_, _, _, _, c) ->
  List.fold_left union_g_pos empty_g_pos (List.map mk_graph_contract_node_eqn c)
       
let extract_node_calls: LA.node_item list -> (LA.ident * Lib.position) list
  = List.fold_left
      (fun acc eqn ->
        (match eqn with
         | LA.Body bneq ->
            (match bneq with
             | LA.Assert (_, e) -> get_node_call_from_expr e
             | LA.Equation (_, _, e) -> get_node_call_from_expr e
             | LA.Automaton _ -> [] ) (* We do not support automation yet. *)
         | _ -> []) @ acc) [] 
       
let mk_graph_node_decl: Lib.position -> LA.node_decl -> (G.t * id_pos_map)
  = fun pos (i, _, _, _, _, _, nitems, contract_opt) ->
  let cg = connect_g_pos (match contract_opt with
                      | None -> empty_g_pos
                      | Some c -> List.fold_left union_g_pos empty_g_pos
                                    (List.map mk_graph_contract_node_eqn c)) (node_suffix^i) pos in
  let node_refs = extract_node_calls nitems in
  List.fold_left (fun g (nr, p) -> union_g_pos g (singleton_g_pos node_suffix nr p)) cg node_refs
                         

let add_decl: 'a IMap.t -> LA.ident -> 'a -> 'a IMap.t
  = fun m i dec -> IMap.add i dec m
                      
let check_and_add: 'a IMap.t -> Lib.position
                       -> string -> LA.ident -> 'a -> ('a IMap.t) graph_result
  = fun m pos suffix i tyd ->
  if IMap.mem (suffix ^ i) m 
  then graph_error pos ("Identifier " ^ i ^ " is already declared")
  else R.ok (add_decl m (suffix ^ i) tyd)
(** reject program if identifier is already declared  *)
       
let rec  mk_decl_map: LA.declaration IMap.t -> LA.t -> (LA.declaration IMap.t) graph_result =
  fun m ->
  function  
  | [] -> R.ok m 

  | (LA.TypeDecl (pos, FreeType (_, i)) as tydecl) :: decls
    | (LA.TypeDecl (pos, AliasType (_, i, _)) as tydecl) :: decls ->
     check_and_add m pos ty_suffix i tydecl >>= fun m' ->
     mk_decl_map m' decls 

  | (LA.ConstDecl (pos, FreeConst (_, i, _)) as cnstd) :: decls
    | (LA.ConstDecl (pos, UntypedConst (_, i, _)) as cnstd) :: decls
    | (LA.ConstDecl (pos, TypedConst (_, i, _, _)) as cnstd) :: decls -> 
     check_and_add m pos const_suffix i cnstd  >>= fun m' ->
     mk_decl_map m' decls 

  | (LA.NodeDecl (pos, (i, _, _, _, _, _, _, _)) as ndecl) :: decls
    | (LA.FuncDecl (pos, (i, _, _, _, _, _, _, _)) as ndecl) :: decls ->
     check_and_add m pos node_suffix i ndecl  >>= fun m' ->
     mk_decl_map m' decls

  | LA.ContractNodeDecl (pos, (i, _, _, _, _)) as cndecl :: decls ->
     check_and_add m pos contract_suffix i cndecl >>= fun m' ->
     mk_decl_map m' decls

  | LA.NodeParamInst _ :: _-> Lib.todo __LOC__
(** builds an id :-> decl map  *)

let rec mk_contract_map: LA.contract_node_equation IMap.t -> LA.contract -> (LA.contract_node_equation IMap.t) graph_result
  = fun m -> function
  | [] -> R.ok m
  | (LA.GhostConst (FreeConst (pos, i, _)) as cnstd) :: eqns
  | (LA.GhostConst (UntypedConst (pos, i, _)) as cnstd) :: eqns
  | (LA.GhostConst (TypedConst (pos, i, _, _)) as cnstd) :: eqns -> 
     check_and_add m pos const_suffix i cnstd  >>= fun m' ->
     mk_contract_map m' eqns 
  | (LA.GhostVar (FreeConst (pos, i, _)) as cnstd) :: eqns
  | (LA.GhostVar (UntypedConst (pos, i, _)) as cnstd) :: eqns
  | (LA.GhostVar (TypedConst (pos, i, _, _)) as cnstd) :: eqns -> 
     check_and_add m pos const_suffix i cnstd  >>= fun m' ->
     mk_contract_map m' eqns 
  | (LA.Assume (pos, name_opt, _, _) as eqn) :: eqns ->
     let eqn_name =
       (match name_opt with
        | None -> "Assumption<" ^ Lib.string_of_t Lib.pp_print_position pos ^">"
        | Some n -> n) in
     check_and_add m pos const_suffix eqn_name eqn  >>= fun m' ->
     mk_contract_map m' eqns 
  | (LA.Guarantee (pos, name_opt, _, _) as eqn) :: eqns ->
     let eqn_name =
       (match name_opt with
        | None -> "Gurantee<" ^ Lib.string_of_t Lib.pp_print_position pos ^">"
        | Some n -> n) in
     check_and_add m pos const_suffix eqn_name eqn  >>= fun m' ->
     mk_contract_map m' eqns 
  | LA.Mode (pos, i, _, _)  as eqn :: eqns ->
     check_and_add m pos const_suffix i eqn  >>= fun m' ->
     mk_contract_map m' eqns 
  | LA.ContractCall _ :: eqns -> mk_contract_map m eqns

             
let mk_graph_decls: LA.t -> (G.t * id_pos_map) 
  = let mk_graph: LA.declaration -> (G.t * id_pos_map) = function
      | TypeDecl (pos, tydecl) -> mk_graph_type_decl tydecl 
      | ConstDecl (pos, cdecl) -> mk_graph_const_decl cdecl
      | NodeDecl (pos, ndecl) -> mk_graph_node_decl pos ndecl
      | FuncDecl (pos, ndecl) -> mk_graph_node_decl pos ndecl
      | ContractNodeDecl  (pos, cdecl) -> mk_graph_contract_decl cdecl
      | NodeParamInst  _ -> Lib.todo __LOC__ in
    fun decls ->
    List.fold_left union_g_pos empty_g_pos (List.map mk_graph decls)

let mk_graph_contract_eqns: LA.contract -> (G.t * id_pos_map)
  = let mk_graph: LA.contract_node_equation -> (G.t * id_pos_map)
      = function
      | LA.GhostConst _
        | LA.GhostVar _
        | LA.Assume _
        | LA.Guarantee _
        | LA.Mode _
        | LA.ContractCall _ -> empty_g_pos in 
    fun eqns ->
    List.fold_left union_g_pos empty_g_pos (List.map mk_graph eqns)
  
  
let rec extract_decls: ('a IMap.t * id_pos_map) -> LA.ident list -> ('a list) graph_result
  = fun (decl_map, i_pos_map) ->
  function
  | [] -> R.ok []
  | i :: is -> (try (R.ok (IMap.find i decl_map)) with
                | Not_found -> match (find_id_pos i_pos_map i) with
                                   | None -> failwith ("Identifier " ^ i ^ " not found. This should not happen")
                                   | Some p -> graph_error p ("Identifier " ^ i ^ " is not defined."))
               >>= (fun d -> (extract_decls (decl_map, i_pos_map) is)
                             >>= (fun ds -> R.ok (d :: ds)))
    
let sort_decls: ('a IMap.t -> 'a list -> 'a IMap.t graph_result)
                -> ('a list -> (G.t * id_pos_map))
                -> 'a list -> ('a list) graph_result
  = fun mk_map mk_graph decls ->
  (* 1. make an id :-> decl map  *)
  mk_map IMap.empty decls >>= fun decl_map ->
  (* 2. build a dependency graph *)
  let (dg, pos_info) = mk_graph decls in
  (* 3. try to sort it, raise an error if it is cyclic, or extract sorted decls from the decl_map *)
  (try (R.ok (G.topological_sort dg)) with
   | Graph.CyclicGraphException ids ->
      graph_error Lib.dummy_pos
        ("Cyclic dependency detected in definition of identifiers: "
  ^ Lib.string_of_t (Lib.pp_print_list LA.pp_print_ident ", ") ids))
  >>= fun sorted_ids -> let dependency_sorted_ids = List.rev sorted_ids in
                        Log.log L_trace "sorted ids: %a" (Lib.pp_print_list LA.pp_print_ident ",")  dependency_sorted_ids;
                          extract_decls (decl_map, pos_info) dependency_sorted_ids

let sort_declarations = sort_decls mk_decl_map mk_graph_decls

let sort_contract_equations = sort_decls mk_contract_map mk_graph_contract_eqns
                                
