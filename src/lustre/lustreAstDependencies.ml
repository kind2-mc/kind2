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
    forward references.

    Note {Types of dependency analysis}: There are three different kinds of graph dependency analysis done here.
    1. Top level constants and type declarations (starts at [mk_graph_decls]) 
    2. Between Nodes and contracts (starts at [mk_graph_decls])
    3. Equations of nodes, Equations of contracts

   TODO: This should module should supercede LustreDependencies when it hardens.     

   @author: Apoorv Ingle *)

module R = Res
module LA = LustreAst
module LH = LustreAstHelpers
module SI = LA.SI

type 'a graph_result = ('a, Lib.position * string) result  

let graph_error pos err = Error (pos, err)

let (>>=) = R.(>>=)                     
let (>>) = R.(>>)                     
          
module G = Graph.Make(struct
               type t = LA.ident
               let compare = Stdlib.compare
               let pp_print_t = LA.pp_print_ident
             end)

module IMap = struct
  include (Map.Make(struct
               type t = LA.ident
               let compare i1 i2 = Stdlib.compare i1 i2
             end))
  let keys: 'a t -> key list = fun m -> List.map fst (bindings m)             
end

type id_pos_map = (Lib.position list) IMap.t
(** stores all the positions of the occurance of an id *)

type node_summary = (int list) IMap.t
(** The node summary contains the positions of the input streams of a node that are used in their current value. *)
                  
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

let remove: (G.t * id_pos_map) -> LA.ident -> (G.t * id_pos_map) =
  fun (g, pos_m) i -> (G.remove_vertex g i, pos_m)
                      
let map_g_pos: (LA.ident -> LA.ident) -> (G.t * id_pos_map) -> (G.t * id_pos_map) =
  fun f (g, pos_info) -> 
     let pos_info' = List.fold_left (fun m (k, v) -> IMap.add k v m) IMap.empty
                       (List.map (fun (k, v) -> (f k, v)) (IMap.bindings pos_info)) in
     let g' = G.map f g in 
     (g', pos_info') 
                      
                      
(* Suffixes for declaration types *)
let ty_suffix = "type "
let const_suffix = ""
let node_suffix = ""
let contract_suffix = "contract "
let mode_suffix = "mode "

(*****************************************************************************
 * Type 1: Dependency Analysis for top level type and constant declarations  *
 *****************************************************************************)
                
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
    | EnumType _ -> empty_g_pos
  | IntRange (_, e1, e2) -> union_g_pos (mk_graph_expr e1) (mk_graph_expr e2)
  | UserType (pos, i) -> singleton_g_pos ty_suffix i pos
  | AbstractType (pos, i) -> singleton_g_pos ty_suffix i pos
  | TupleType (pos, tys) -> List.fold_left union_g_pos empty_g_pos  (List.map (fun t -> mk_graph_type t) tys)
  | RecordType (pos, ty_ids) -> List.fold_left union_g_pos empty_g_pos (List.map (fun (_, _, t) -> mk_graph_type t) ty_ids)
  | ArrayType (_, (ty, e)) -> union_g_pos (mk_graph_type ty) (mk_graph_expr e)
  | TArr (_, aty, rty) -> union_g_pos (mk_graph_type aty) (mk_graph_type rty)
(** This graph is useful for analyzing top level constant and type declarations *)
                        
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
  | LA.ModeRef (pos, ids) -> singleton_g_pos mode_suffix (List.nth ids (List.length ids - 1) ) pos 
  | e -> Lib.todo (__LOC__ ^ " " ^ Lib.string_of_t Lib.pp_print_position (LH.pos_of_expr e))  
(** This graph is useful for analyzing top level constant and type declarations *)
       
let mk_graph_const_decl: LA.const_decl -> (G.t * id_pos_map)
  = function
  | LA.FreeConst (pos, i, ty) -> connect_g_pos (mk_graph_type ty) (const_suffix ^ i) pos
  | LA.UntypedConst (pos, i, e) -> connect_g_pos (mk_graph_expr e) (const_suffix ^ i) pos 
  | LA.TypedConst (pos, i, e, ty) -> connect_g_pos (union_g_pos (mk_graph_expr e) (mk_graph_type ty)) (const_suffix ^ i) pos 

                                   
let mk_graph_type_decl: LA.type_decl -> (G.t * id_pos_map)
  = function
  | FreeType (pos, i) -> singleton_g_pos ty_suffix  i pos 
  | AliasType (pos, i, ty) -> connect_g_pos (mk_graph_type ty) (ty_suffix ^ i) pos

(***********************************************************
 * Type 2: Dependency Analysis Between nodes and contracts *
 ***********************************************************)
                            
let rec get_node_call_from_expr: LA.expr -> (LA.ident * Lib.position) list
  = function
  | Ident _ -> []
  | ModeRef (pos, is) -> if List.length is = 1 then []
                       else [(contract_suffix ^ List.hd is, pos)]  
  | RecordProject (_, e, _)
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
  | LA.CallParam _ as e-> Lib.todo (__LOC__ ^ (Lib.string_of_t Lib.pp_print_position (LH.pos_of_expr e)))
(** Returns all the node calls from an expression *)

let  mk_graph_contract_node_eqn: LA.contract_node_equation -> (G.t * id_pos_map)
  = function
  | LA.ContractCall (pos, i, es, _) ->
     union_g_pos
       (singleton_g_pos contract_suffix i pos)
       (List.fold_left union_g_pos empty_g_pos
          (List.map (fun (i, p) -> singleton_g_pos node_suffix i p)
             (List.flatten (List.map get_node_call_from_expr es))))
  | LA.Assume (_, _, _, e) ->
     List.fold_left union_g_pos empty_g_pos
       (List.map (fun (i, p) -> singleton_g_pos node_suffix i p) (get_node_call_from_expr e))
  | LA.Guarantee (_, _, _, e) ->
     List.fold_left union_g_pos empty_g_pos
       (List.map (fun (i, p) -> singleton_g_pos node_suffix i p) (get_node_call_from_expr e))
  | LA.Mode (pos, i, reqs, ensures) ->
     let calls_ps = List.flatten (List.map (fun (_,_, e) -> get_node_call_from_expr e) (reqs @ ensures)) in
     let sub_graphs = (List.map (fun (i, p) -> singleton_g_pos node_suffix i p) calls_ps) in
     List.fold_left union_g_pos empty_g_pos sub_graphs
  | LA.GhostConst c 
    | LA.GhostVar c ->
     match c with
     | FreeConst _ -> empty_g_pos
     | UntypedConst (pos, i, e) ->
        List.fold_left union_g_pos empty_g_pos
          (List.map (fun (i, p) -> singleton_g_pos node_suffix i p) (get_node_call_from_expr e))
     | TypedConst (pos, i, e, ty) ->
        List.fold_left union_g_pos empty_g_pos
          (List.map (fun (i, p) -> singleton_g_pos node_suffix i p) (get_node_call_from_expr e))
(** This builds a graph with all the node call dependencies from the equations of the contract  *)
       
let mk_graph_contract_decl: Lib.position -> LA.contract_node_decl -> (G.t * id_pos_map)
  = fun pos (i , _, _, _, c) ->
  connect_g_pos (List.fold_left union_g_pos empty_g_pos (List.map mk_graph_contract_node_eqn c))
    (contract_suffix ^ i) pos
(** This builds a graph with all the node call dependencies from the equations of the contract  *)
  
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
(** Extracts all the node calls from a node item *)
  
let mk_graph_node_decl: Lib.position -> LA.node_decl -> (G.t * id_pos_map)
  = fun pos (i, _, _, _, _, _, nitems, contract_opt) ->
  let cg = connect_g_pos
             (match contract_opt with
              | None -> empty_g_pos
              | Some c -> List.fold_left union_g_pos empty_g_pos
                            (List.map mk_graph_contract_node_eqn c))
             (node_suffix^i) pos in
  let node_refs = extract_node_calls nitems in
  List.fold_left (fun g (nr, p) -> union_g_pos g (connect_g_pos (singleton_g_pos node_suffix nr p) i pos)) cg node_refs
(** Builds a dependency graph between the node in question to node calls 
 *  seen in the definition of the node and the inlined contract *)

(*********************************************************************
 * Common infrastructure for type 1 and type 2 dependency analysis   *
 *********************************************************************)

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
                            
let mk_graph_decls: LA.t -> (G.t * id_pos_map) 
  = let mk_graph: LA.declaration -> (G.t * id_pos_map) = function
      | TypeDecl (pos, tydecl) -> mk_graph_type_decl tydecl 
      | ConstDecl (pos, cdecl) -> mk_graph_const_decl cdecl
      | NodeDecl (pos, ndecl) -> mk_graph_node_decl pos ndecl
      | FuncDecl (pos, ndecl) -> mk_graph_node_decl pos ndecl
      | ContractNodeDecl (pos, cdecl) -> mk_graph_contract_decl pos cdecl
      | NodeParamInst  _ -> Lib.todo __LOC__ in
    fun decls ->
    List.fold_left union_g_pos empty_g_pos (List.map mk_graph decls)
(** Builds a dependency graph for top-level types and constant defintions (for type 1 analysis) 
   and nodes and contracts (for type 2 analysis)
   See Note {Types of dependency analysis} for more information about different kinds of
   dependency analysis  *)
    
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
(** Given a list of ids, finds the associated payload from the playload map *)
             
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
      if List.length ids > 1
      then (match (find_id_pos pos_info (List.hd ids)) with
            | None -> failwith ("Cyclic dependency found but Cannot find position for identifier "
                                ^ (List.hd ids) ^ " This should not happen!") 
            | Some p -> graph_error p
                          ("Cyclic dependency detected in definition of identifiers: "
                           ^ Lib.string_of_t (Lib.pp_print_list LA.pp_print_ident ", ") ids))
      else failwith "Cyclic dependency with no ids detected. This should not happen!")
  >>= fun sorted_ids -> let dependency_sorted_ids = List.rev sorted_ids in
                        Log.log L_trace "sorted ids: %a" (Lib.pp_print_list LA.pp_print_ident ",")  dependency_sorted_ids;
                        extract_decls (decl_map, pos_info) dependency_sorted_ids
(** Accepts a function to generate a declaration map, 
    a function to generate the graph of the declarations,
    runs a topological sort on the ids extracted from the map and then 
    returns the sorted declarations (or an error if circular dependency is detected)  *)
                        
let sort_declarations decls =
  sort_decls mk_decl_map mk_graph_decls decls
(** Returns a topological order of declarations *)  


(************************************************************************
 * Type 3. Dependency Analysis of contract equations and node equations *
 ************************************************************************)

let rec vars_with_flattened_nodes: (int list) IMap.t -> LA.expr -> LA.SI.t = fun m ->
  function
  | Ident (_ , i) -> SI.singleton i 
  | ModeRef _ -> SI.empty
  | RecordProject (_, e, _) -> vars_with_flattened_nodes m e 
  | TupleProject (_, e, _) -> vars_with_flattened_nodes m e
  (* Values *)
  | Const _ -> SI.empty

  (* Operators *)
  | UnaryOp (_,_,e) -> vars_with_flattened_nodes m e
  | BinaryOp (_,_,e1, e2) -> vars_with_flattened_nodes m e1
                             |> SI.union (vars_with_flattened_nodes m e2)
  | TernaryOp (_,_, e1, e2, e3) -> vars_with_flattened_nodes m e1
                                   |> SI.union (vars_with_flattened_nodes m e2)
                                   |> SI.union (vars_with_flattened_nodes m e3) 
  | NArityOp (_, _,es) -> SI.flatten (List.map (vars_with_flattened_nodes m) es)
  | ConvOp  (_,_,e) -> vars_with_flattened_nodes m e
  | CompOp (_,_,e1, e2) -> (vars_with_flattened_nodes m e1) |> SI.union (vars_with_flattened_nodes m e2)

  (* Structured expressions *)
  | RecordExpr (_, _, flds) -> SI.flatten (List.map (vars_with_flattened_nodes m) (snd (List.split flds)))
  | GroupExpr (_, _, es) -> SI.flatten (List.map (vars_with_flattened_nodes m) es)

  (* Update of structured expressions *)
   | StructUpdate (_, e1, _, e2) -> SI.union (vars_with_flattened_nodes m e1) (vars_with_flattened_nodes m e2)
   | ArrayConstr (_, e1, e2) -> SI.union (vars_with_flattened_nodes m e1) (vars_with_flattened_nodes m e2)
   | ArrayIndex (_, e1, e2) -> SI.union (vars_with_flattened_nodes m e1) (vars_with_flattened_nodes m e2)
   | ArraySlice (_, e1, (e2, e3)) -> SI.union (vars_with_flattened_nodes m e3) (SI.union (vars_with_flattened_nodes m e1) (vars_with_flattened_nodes m e2))
   | ArrayConcat (_, e1, e2) -> SI.union (vars_with_flattened_nodes m e1) (vars_with_flattened_nodes m e2)

   (* Quantified expressions *)
   | Quantifier (_, _, qs, e) -> SI.diff (vars_with_flattened_nodes m e) (SI.flatten (List.map LH.vars_of_ty_ids qs)) 

   (* Clock operators *)
  | When (_, e, clkE) -> vars_with_flattened_nodes m e
  | Current  (_, e) -> vars_with_flattened_nodes m e
  | Condact (_, e1, e2, i, es1, es2) ->
     SI.add i (SI.flatten (vars_with_flattened_nodes m e1 :: vars_with_flattened_nodes m e2:: (List.map (vars_with_flattened_nodes m) es1) @
                             (List.map (vars_with_flattened_nodes m) es2)))
  | Activate (_, _, e1, e2, es) -> SI.flatten (vars_with_flattened_nodes m e1
                                               :: vars_with_flattened_nodes m e2
                                               :: List.map (vars_with_flattened_nodes m)  es)
  | Merge (_, _, es) -> List.split es |> snd |> List.map (vars_with_flattened_nodes m) |> SI.flatten
  | RestartEvery (_, i, es, e) -> SI.add i (SI.flatten (vars_with_flattened_nodes m e :: List.map (vars_with_flattened_nodes m) es)) 

  (* Temporal operators *)
  | Pre (_, e) -> SI.empty
  | Last (_, i) -> SI.empty
  | Fby (_, e1, _, e2) -> SI.union (vars_with_flattened_nodes m e1) (vars_with_flattened_nodes m e2)
  | Arrow (_, e1, e2) ->  SI.union (vars_with_flattened_nodes m e1) (vars_with_flattened_nodes m e2)

  (* Node calls *)
  | Call (_, i, es) -> (match IMap.find_opt i m with
                       | None -> failwith ("cannot find node call summary for "^ i ^". Should not happen")
                       | Some idx ->
                          if List.length idx = 0
                          then SI.empty
                          else (SI.flatten (List.map (vars_with_flattened_nodes m) es)))
  | CallParam (_, i, _, es) -> (SI.flatten (List.map (vars_with_flattened_nodes m) es))
(** get all the variables except node names from an expression *)

let summarize_ip_vars: LA.ident list -> SI.t -> int list = fun ips critial_ips ->
  (List.fold_left (fun (acc, nums) i ->
       if SI.mem i critial_ips
       then (nums::acc, nums+1)
       else (acc, nums+1)) ([], 0)) ips |> fst 
                             
let mk_node_summary: node_summary -> LA.node_decl -> node_summary =
  fun s (i, imported, _, ips, ops, vars, items, _) ->
  if not imported
  then 
  let op_vars = List.map (fun o -> LH.extract_op_ty o |> fst) ops in
  let ip_vars = List.map (fun o -> LH.extract_ip_ty o |> fst) ips in
  let node_equations = List.concat (List.map LH.extract_node_equation items) in
  let process_one_eqn = fun (LA.StructDef (_, lhss), e) ->
    let lhs_vars = LA.SI.elements (LA.SI.flatten (List.map LH.vars_of_struct_item lhss)) in
    let ms = List.map (Lib.flip IMap.singleton (LA.SI.elements (vars_with_flattened_nodes s e))) lhs_vars in
    List.fold_left (IMap.union (fun k v1 v2 -> Some v2)) IMap.empty ms in
  
  let node_equation_dependency_map = List.fold_left (IMap.union (fun k v1 v2 -> Some v2)) IMap.empty
                                       (List.map process_one_eqn node_equations) in

  Log.log L_trace "Node equation dependency map for node %a {\n %a \n}"
    LA.pp_print_ident i
    (Lib.pp_print_list (Lib.pp_print_pair (LA.pp_print_ident) (Lib.pp_print_list (LA.pp_print_ident) ", ") "->") "\n")
    (IMap.bindings node_equation_dependency_map)
  ; let mk_g = fun (lhs, vars) ->  G.connect (List.fold_left G.union G.empty (List.map G.singleton vars)) lhs in
    let g = List.fold_left G.union G.empty (List.map mk_g (IMap.bindings node_equation_dependency_map)) in
    Log.log L_trace "Node equation graph: %a" G.pp_print_graph g
    ; let vars_op_depends_on = List.concat (List.map (fun i -> G.to_vertex_list (G.reachable g i)) op_vars) in
      Log.log L_trace "Reachable vars: %a" (Lib.pp_print_list LA.pp_print_ident ", ") vars_op_depends_on
      ; let critical_ips = SI.inter (SI.of_list vars_op_depends_on) (SI.of_list ip_vars) in
        if (SI.is_empty critical_ips)
        then IMap.add i [] s
        else IMap.add i (summarize_ip_vars ip_vars critical_ips) s
  else IMap.add i ((List.fold_left (fun (acc, num) _ -> (num::acc, num+1)) ([], 0) ips) |> fst) s   
(** Computes the node call summary the node to the input stream of the node. *)
                      
let rec mk_graph_expr2: node_summary -> LA.expr -> (G.t * id_pos_map) = fun m ->
  function
  | LA.Ident (pos, i) -> singleton_g_pos "" i pos
  | LA.ModeRef (pos, ids) -> singleton_g_pos mode_suffix (List.nth ids (List.length ids - 1) ) pos 
  | LA.Const _ -> empty_g_pos

  | LA.RecordExpr (pos, i, ty_ids) ->
     List.fold_left union_g_pos (singleton_g_pos "" i pos) (List.map (fun ty_id -> mk_graph_expr2 m (snd ty_id)) ty_ids)
  | LA.StructUpdate (_, e1, _, e2) -> union_g_pos (mk_graph_expr2 m e1) (mk_graph_expr2 m e2) 
  | LA.UnaryOp (_, _, e)
    | LA.ConvOp (_, _, e) -> mk_graph_expr2 m e
  | LA.BinaryOp (_, _, e1, e2) -> union_g_pos (mk_graph_expr2 m e1) (mk_graph_expr2 m e2) 
  | LA.CompOp (_, _, e1, e2) -> union_g_pos (mk_graph_expr2 m e1) (mk_graph_expr2 m e2) 
  | LA.TernaryOp (_, _, e1, e2, e3) -> union_g_pos (mk_graph_expr2 m e1)
                                         (union_g_pos (mk_graph_expr2 m e2) (mk_graph_expr2 m e3)) 
  | LA.RecordProject (_, e, _) -> mk_graph_expr2 m e
  | LA.TupleProject (_, e, _) -> mk_graph_expr2 m e
  | LA.ArrayConstr (_, e1, e2) -> union_g_pos (mk_graph_expr2 m e1) (mk_graph_expr2 m e2) 
  | LA.ArraySlice (_, e1, (e2, e3)) -> union_g_pos (union_g_pos (mk_graph_expr2 m e1) (mk_graph_expr2 m e2)) (mk_graph_expr2 m e3) 
  | LA.ArrayIndex (_, e1, e2) -> mk_graph_expr2 m e1
  | LA.ArrayConcat  (_, e1, e2) -> union_g_pos (mk_graph_expr2 m e1) (mk_graph_expr2 m e2)
  | LA.GroupExpr (_, _, es) -> List.fold_left union_g_pos empty_g_pos (List.map (mk_graph_expr2 m) es)
  | LA.When (_, e, _) -> mk_graph_expr2 m e
  | LA.Current (_, e) -> mk_graph_expr2 m e
  | LA.Condact (p, _, _, _, e1s, e2s) -> List.fold_left union_g_pos empty_g_pos (List.map (mk_graph_expr2 m) (e1s @ e2s))
  | LA.Activate (p, _, _, _, es) -> List.fold_left union_g_pos empty_g_pos (List.map (mk_graph_expr2 m) es)
  | LA.Merge (p, _, cs) -> List.fold_left union_g_pos empty_g_pos (List.map (fun (_, e) -> (mk_graph_expr2 m) e) cs) 
  | LA.RestartEvery (p, _, es,_) -> List.fold_left union_g_pos empty_g_pos (List.map (mk_graph_expr2 m) es)

  | LA.Pre (_, e) -> map_g_pos (fun v -> v ^ "$p") (mk_graph_expr2 m e) 
  | LA.Last (pos, i) -> singleton_g_pos "" i pos
  | LA.Fby (_, e1, _, e2) ->  union_g_pos (mk_graph_expr2 m e1) (mk_graph_expr2 m e2) 
  | LA.Arrow (_, e1, e2) ->  union_g_pos (mk_graph_expr2 m e1) (mk_graph_expr2 m e2)
  | LA.Call (_, i, es) ->
     (match IMap.find_opt i m with
      | None -> failwith ("Cannot find summary of node " ^ i ^ ". This should not happen.")
      | Some b -> if List.length b = 0
                  then empty_g_pos
                  else
                    let es' = List.map (List.nth es) b in 
                    List.fold_left union_g_pos empty_g_pos (List.map (mk_graph_expr2 m) es'))
  | e -> Lib.todo (__LOC__ ^ " " ^ Lib.string_of_t Lib.pp_print_position (LH.pos_of_expr e))
(** This graph is useful for analyzing equations assuming that the nodes/contract call
    recursive calling has been resolved already.
    The generated graph would be useful only if the 
    pre's are abstracted out first and then passed into this 
    function using [LH.abstract_pre_subexpressions] *)

let mk_graph_const_decl2: node_summary -> LA.const_decl -> (G.t * id_pos_map)
  = fun m -> function
  | LA.FreeConst (pos, i, ty) -> connect_g_pos (mk_graph_type ty) (const_suffix ^ i) pos
  | LA.UntypedConst (pos, i, e) -> connect_g_pos (mk_graph_expr2 m e) (const_suffix ^ i) pos 
  | LA.TypedConst (pos, i, e, ty) -> connect_g_pos (union_g_pos (mk_graph_expr2 m e) (mk_graph_type ty)) (const_suffix ^ i) pos

       
let mk_graph_contract_eqns: node_summary -> LA.contract -> (G.t * id_pos_map)
  = fun m -> let mk_graph: LA.contract_node_equation -> (G.t * id_pos_map)
      = function
      | LA.GhostConst c -> mk_graph_const_decl2 m c
      | LA.GhostVar c -> mk_graph_const_decl2 m c
      | LA.Mode (pos, i, reqs, ens) ->
         let g = List.fold_left (fun g e -> union_g_pos g (mk_graph_expr2 m e))
                   empty_g_pos (List.map (fun (_, _,  e) -> e) (reqs @ ens)) in
         connect_g_pos g (mode_suffix ^ i) pos 
      | LA.Assume _ 
        | LA.Guarantee _
        | LA.ContractCall _ -> empty_g_pos in 
    fun eqns ->
    List.fold_left union_g_pos empty_g_pos (List.map mk_graph eqns)

let expression_current_streams: node_summary -> LA.expr -> LA.ident list = 
  fun ns e ->
  let g = mk_graph_expr2 ns (LH.abstract_pre_subexpressions e) in
  G.to_vertex_list (G.get_vertices (fst g))
(** all the variables who's current value is used in the expression *)
    
    
let analyze_circ_contract_equations: node_summary -> LA.contract -> unit graph_result  = fun m c ->
  let dg, pos_info = mk_graph_contract_eqns m c in
  (try (R.ok (G.topological_sort dg)) with
   | Graph.CyclicGraphException ids ->
      if List.length ids > 1
      then (match (find_id_pos pos_info (List.hd ids)) with
            | None -> failwith ("Cyclic dependency found but Cannot find position for identifier "
                                ^ (List.hd ids) ^ " This should not happen!") 
            | Some p -> graph_error p
                          ("Cyclic dependency detected in definition of identifiers: "
                           ^ Lib.string_of_t (Lib.pp_print_list LA.pp_print_ident ", ") ids))
      else failwith "Cyclic dependency with no ids detected. This should not happen!")
  >> R.ok ()


let mk_graph_eqn: node_summary -> LA.node_equation -> (G.t * id_pos_map) =
  let handle_one_lhs: (G.t * id_pos_map) -> LA.struct_item -> (G.t * id_pos_map) = fun rhs_g lhs ->
    match lhs with
    | LA.SingleIdent (p, i) -> connect_g_pos rhs_g i p 
    | LA.ArrayDef (p, arr, is) ->
       let arr' = arr ^ "$" ^ (List.fold_left (fun acc i -> acc ^ "$" ^ i) "" is) in 
    connect_g_pos (List.fold_left (fun g i -> remove g i) rhs_g is)  arr' p

    (* None of these items below are supported at parsing yet. *)
    | LA.TupleStructItem (p, _)
      | LA.TupleSelection (p, _, _)
      | LA.FieldSelection (p, _, _)
      | LA.ArraySliceStructItem (p, _, _)
      ->  Lib.todo (__LOC__ ^ " " ^ Lib.string_of_t Lib.pp_print_position p) in
  fun m -> function
  | Equation (pos, (LA.StructDef (_, lhss)), e) ->
     let rhs_g = mk_graph_expr2 m (LH.abstract_pre_subexpressions e) in
     List.fold_left union_g_pos empty_g_pos (List.map (handle_one_lhs rhs_g) lhss)
  | _ -> empty_g_pos
  
let rec mk_graph_node_items: node_summary -> LA.node_item list -> (G.t * id_pos_map) =
  fun m -> function
  | [] -> empty_g_pos
  | (Body eqn) :: items -> union_g_pos (mk_graph_eqn m eqn) (mk_graph_node_items m items) 
  | _ :: items -> mk_graph_node_items m items
  
let analyze_circ_node_equations: node_summary -> LA.ident list -> LA.node_item list -> unit graph_result =
  fun m consts eqns ->
  Log.log L_trace "Checking circularity in node equations"
  ; let dg, pos_info = mk_graph_node_items m eqns in
    let dg' = List.fold_left (fun g i -> G.remove_vertex g i) dg consts in
    (try (R.ok (G.topological_sort dg')) with
     | Graph.CyclicGraphException ids ->
        if List.length ids > 1
        then (match (find_id_pos pos_info (List.hd ids)) with
              | None -> failwith ("Cyclic dependency found but Cannot find position for identifier "
                                  ^ (List.hd ids) ^ " This should not happen!") 
              | Some p -> graph_error p
                            ("Cyclic dependency detected in definition of identifiers: "
                             ^ Lib.string_of_t (Lib.pp_print_list LA.pp_print_ident ", ") ids))
        else failwith "Cyclic dependency with no ids detected. This should not happen!")
    >> R.ok ()



         
