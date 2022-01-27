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

    Note {Types of dependency analysis}: There are three different kinds of 
    graph dependency analysis and sorting done here.
    1. Top level constants and type declarations and functions (starts at [mk_graph_decls]) 
    2. Nodes and contracts (starts at [mk_graph_decls])
    3. Sorting equations of contracts and cirular analysis of node equations 

   TODO: This should module should supercede LustreDependencies when it hardens.     

   @author Apoorv Ingle *)

module R = Res
module LA = LustreAst
module LH = LustreAstHelpers
module SI = LA.SI

open LustreReporting
          
type 'a graph_result = ('a, Lib.position * string) result  

let graph_error pos err = Error (pos, err)

let (>>=) = R.(>>=)                     
let (>>) = R.(>>)                     
          
module G = Graph.Make(struct
               type t = LA.ident
               let compare = HString.compare
               let pp_print_t = LA.pp_print_ident
             end)

module IMap = struct
  include (Map.Make(struct
               type t = LA.ident
               let compare i1 i2 = HString.compare i1 i2
             end))
  (* let keys: 'a t -> key list = fun m -> List.map fst (bindings m) *)         
end

module IntMap = struct
  include (Map.Make(struct
               type t = int
               let compare i1 i2 = Int.compare i1 i2
             end))
  (* let keys: 'a t -> key list = fun m -> List.map fst (bindings m) *)            
end
            
type id_pos_map = (Lib.position list) IMap.t
(** stores all the positions of the occurance of an id *)

type node_summary = ((int list) IntMap.t) IMap.t
(** The node summary contains the positions of the input streams 
    of a node that are used in their current value for each output stream. 

    Eg. Assume a node N(a1, a2, a3, a4) returns (r1, r2, r3) where
    r1 does not depend on any input stream's current value,
    r2 depends on the current value of a4 and a3 and 
    r3 depends on the current value of a1.
    
    The node summary's entry that is generated for N will be
    [0:->[], 1:-> [2, 3], 2:->[1]].

    The reason as to why we store it using indices is because 
    we would substitute the indices with the actual call parameters
    during the circularity analysis for equations.

    For functions and imported nodes we make a conservative assumption
    that each output stream is dependent on the current values 
    of all the arguments.
    
    We generate the node summary entry by doing a rechablility analysis 
    for each of the output streams equations. 
 
*)

type contract_summary = (LA.ident list) IMap.t
(** The contract summary contains the symbols that are exported  
    from a contract i.e. mode names and ghost constants and variables.
    which can be referenced after the contract is imported  *)

type dependency_analysis_data =
  { graph_data: G.t            (* How are the ids related  *)
  ; id_pos_data: id_pos_map    (* Where do the Id's appear*)
  ; csummary: contract_summary (* What symbols does the contract export *)
  ; nsummary: node_summary     (* Node summaries  *)
  }
(** The store for memoizing the lustre program dependencies  *)


(** {1 Pretty Printing } *)
let pp_print_node_summary ppf m =
  let pp_print_val ppf m =
    Lib.pp_print_list (fun ppf (i, b) ->
        Format.fprintf ppf "(%a:%a)"
          Format.pp_print_int i
          (Lib.pp_print_list Format.pp_print_int ", ") b)  ", "
      ppf (IntMap.bindings m) in
  Lib.pp_print_list (fun ppf (i, b) ->
      Format.fprintf ppf "(%a->%a)"
        LA.pp_print_ident i
        pp_print_val b
    ) ", " ppf (IMap.bindings m)  
(** Pretty print the node summary  *)

let pp_print_contract_summary ppf m  =
  Lib.pp_print_list (fun ppf (i, b) ->
      Format.fprintf ppf "(%a :-> %a)"
        LA.pp_print_ident i
        (Lib.pp_print_list LA.pp_print_ident ", ") b)  ", "
    ppf (IMap.bindings m)

let pp_print_analysis_data ppf ad =
  Format.fprintf ppf ("Node Summary: %a\n"
                      ^^ "Contract Summary: %a\n")
  pp_print_node_summary ad.nsummary
  pp_print_contract_summary ad.csummary

(*
let pp_print_id_pos ppf m =
  Lib.pp_print_list (fun ppf (i, b) ->
      Format.fprintf ppf "(%a :-> %a)"
        LA.pp_print_ident i
        (Lib.pp_print_list Lib.pp_print_position ", ") b)  ", "
    ppf (IMap.bindings m)
*)

(** {1 Helper functions } *)
  
let empty_node_summary: node_summary = IMap.empty

let empty_contract_summary: contract_summary = IMap.empty

let empty_dependency_analysis_data =
  { graph_data = G.empty
  ; id_pos_data = IMap.empty
  ; csummary = empty_contract_summary
  ; nsummary = empty_node_summary
  }
  
let add_pos: id_pos_map -> LA.ident -> Lib.position -> id_pos_map = fun m i p ->
  IMap.update i
    (function
     | None -> Some ([p])
     | Some ps -> Some (p :: ps))
    m

let union_pos: id_pos_map -> id_pos_map -> id_pos_map = fun m1 m2 ->
  IMap.union (fun _ v1 v2 -> Some (v1@v2)) m1 m2

let singleton_pos: LA.ident -> Lib.position -> id_pos_map = fun i p ->
  IMap.singleton i [p]

let find_id_pos: id_pos_map -> LA.ident -> Lib.position option = fun m i ->
  match (IMap.find_opt i m) with
  | None -> None
  | Some [] -> None
  | Some (p::_) -> Some p 
                  
let singleton_dependency_analysis_data: HString.t -> LA.ident -> Lib.position -> dependency_analysis_data =
  fun prefix i p -> { graph_data = G.singleton (HString.concat2 prefix i)
                    ; id_pos_data = singleton_pos (HString.concat2 prefix i) p
                    ; csummary  = empty_contract_summary
                    ; nsummary = empty_node_summary } 

let union_dependency_analysis_data : dependency_analysis_data -> dependency_analysis_data -> dependency_analysis_data = 
  fun { graph_data = g1; id_pos_data = pos_m1; csummary = cs1; nsummary = ns1 }
      { graph_data = g2; id_pos_data = pos_m2; csummary = cs2; nsummary = ns2 }
  -> { graph_data = G.union g1 g2
     ; id_pos_data = union_pos pos_m1 pos_m2
     ; csummary = IMap.union (fun _ _ v2 -> Some v2) cs1 cs2
     ; nsummary = IMap.union (fun _ _ v2 -> Some v2) ns1 ns2 }

let connect_g_pos: dependency_analysis_data -> LA.ident -> Lib.position -> dependency_analysis_data =
  fun ad i p -> { ad with graph_data = G.connect ad.graph_data i
                        ; id_pos_data = add_pos ad.id_pos_data i p }  

let remove: dependency_analysis_data -> LA.ident -> dependency_analysis_data =
  fun ad i -> {ad with graph_data = G.remove_vertex ad.graph_data i}
                      
let map_g_pos: (LA.ident -> LA.ident) -> dependency_analysis_data -> dependency_analysis_data =
  fun f ad -> 
     let pos_info' = List.fold_left (fun m (k, v) -> IMap.add k v m) IMap.empty
                       (List.map (fun (k, v) -> (f k, v)) (IMap.bindings ad.id_pos_data)) in
     let g' = G.map f ad.graph_data in 
     {ad with graph_data = g'; id_pos_data = pos_info'} 
                      
                      
(* Suffixes for declaration types *)
let ty_prefix = HString.mk_hstring "type "
let const_prefix = HString.mk_hstring ""
let node_prefix = HString.mk_hstring ""
let contract_prefix = HString.mk_hstring "contract "
let mode_prefix = HString.mk_hstring "mode "
let empty_hs = HString.mk_hstring ""

(** {1 Dependency Analysis functions } *)
                
(*****************************************************************************
 * Type 1: Dependency Analysis for top level type and constant declarations  *
 *****************************************************************************)
                
let rec mk_graph_type: LA.lustre_type -> dependency_analysis_data = function
  | TVar (pos, i) -> singleton_dependency_analysis_data ty_prefix i pos
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
    | Real _ -> empty_dependency_analysis_data
  | EnumType (pos, _, evals) ->
     List.fold_left union_dependency_analysis_data empty_dependency_analysis_data
       (List.map (Lib.flip (singleton_dependency_analysis_data const_prefix) pos) evals)   
  | IntRange (_, e1, e2) -> union_dependency_analysis_data (mk_graph_expr e1) (mk_graph_expr e2)
  | UserType (pos, i) -> singleton_dependency_analysis_data ty_prefix i pos
  | AbstractType (pos, i) -> singleton_dependency_analysis_data ty_prefix i pos
  | TupleType (_, tys) -> List.fold_left union_dependency_analysis_data empty_dependency_analysis_data  (List.map (fun t -> mk_graph_type t) tys)
  | GroupType (_, tys) -> List.fold_left union_dependency_analysis_data empty_dependency_analysis_data  (List.map (fun t -> mk_graph_type t) tys)
  | RecordType (_, ty_ids) -> List.fold_left union_dependency_analysis_data empty_dependency_analysis_data (List.map (fun (_, _, t) -> mk_graph_type t) ty_ids)
  | ArrayType (_, (ty, e)) -> union_dependency_analysis_data (mk_graph_type ty) (mk_graph_expr e)
  | TArr (_, aty, rty) -> union_dependency_analysis_data (mk_graph_type aty) (mk_graph_type rty)
(** This graph is useful for analyzing top level constant and type declarations *)

and mk_graph_expr: LA.expr -> dependency_analysis_data
  = function
  | LA.Ident (pos, i) -> singleton_dependency_analysis_data empty_hs i pos
  | LA.Const _ -> empty_dependency_analysis_data
  | LA.RecordExpr (_, _, ty_ids) ->
     List.fold_left union_dependency_analysis_data empty_dependency_analysis_data (List.map (fun ty_id -> mk_graph_expr (snd ty_id)) ty_ids)
  | LA.UnaryOp (_, _, e) -> mk_graph_expr e
  | LA.ConvOp (_, _, e) -> mk_graph_expr e
  | LA.BinaryOp (_, _, e1, e2) -> union_dependency_analysis_data (mk_graph_expr e1) (mk_graph_expr e2) 
  | LA.CompOp (_, _, e1, e2) -> union_dependency_analysis_data (mk_graph_expr e1) (mk_graph_expr e2) 
  | LA.TernaryOp (_, _, e1, e2, e3) -> union_dependency_analysis_data (mk_graph_expr e1)
                                         (union_dependency_analysis_data (mk_graph_expr e2) (mk_graph_expr e3)) 
  | LA.RecordProject (_, e, _) -> mk_graph_expr e
  | LA.TupleProject (_, e, _) -> mk_graph_expr e
  | LA.ArrayConstr (_, e1, e2) -> union_dependency_analysis_data (mk_graph_expr e1) (mk_graph_expr e2) 
  | LA.ArraySlice (_, e1, (e2, e3)) -> union_dependency_analysis_data (union_dependency_analysis_data (mk_graph_expr e1) (mk_graph_expr e2)) (mk_graph_expr e3) 
  | LA.ArrayIndex (_, e1, e2) -> union_dependency_analysis_data (mk_graph_expr e1) (mk_graph_expr e2)
  | LA.ArrayConcat  (_, e1, e2) -> union_dependency_analysis_data (mk_graph_expr e1) (mk_graph_expr e2)
  | LA.GroupExpr (_, _, es) -> List.fold_left union_dependency_analysis_data empty_dependency_analysis_data (List.map mk_graph_expr es)
  | LA.Pre (_, e) -> mk_graph_expr e
  | LA.Last (pos, i) -> singleton_dependency_analysis_data empty_hs i pos
  | LA.Fby (_, e1, _, e2) ->  union_dependency_analysis_data (mk_graph_expr e1) (mk_graph_expr e2) 
  | LA.Arrow (_, e1, e2) ->  union_dependency_analysis_data (mk_graph_expr e1) (mk_graph_expr e2)
  | LA.ModeRef (pos, ids) ->
     if List.length ids > 1 then
       singleton_dependency_analysis_data empty_hs (List.fold_left HString.concat2 contract_prefix (Lib.drop_last ids)) pos
     else
       singleton_dependency_analysis_data mode_prefix (List.hd ids) pos 
  | LA.Call (_, _, es) ->
     List.fold_left union_dependency_analysis_data empty_dependency_analysis_data
       (List.map mk_graph_expr es)
  | _ -> empty_dependency_analysis_data
(*   | e -> 
     Log.log L_trace "%a located at %a"
       LA.pp_print_expr e
       Lib.pp_print_position (LH.pos_of_expr e) 
     ; Lib.todo (__LOC__ ^ " " ^ Lib.string_of_t Lib.pp_print_position (LH.pos_of_expr e))   *)
(** This graph is useful for analyzing top level constant and type declarations *)
       
let mk_graph_const_decl: LA.const_decl -> dependency_analysis_data
  = function
  | LA.FreeConst (pos, i, ty) -> connect_g_pos (mk_graph_type ty) (HString.concat2 const_prefix i) pos
  | LA.UntypedConst (pos, i, e) -> connect_g_pos (mk_graph_expr e) (HString.concat2 const_prefix i) pos 
  | LA.TypedConst (pos, i, e, ty) ->
    connect_g_pos
      (union_dependency_analysis_data
        (mk_graph_expr e)
        (mk_graph_type ty))
      (HString.concat2 const_prefix i)
      pos 

                                   
let mk_graph_type_decl: LA.type_decl -> dependency_analysis_data
  = function
  | FreeType (pos, i) -> singleton_dependency_analysis_data ty_prefix  i pos 
  | AliasType (pos, i, ty) -> connect_g_pos (mk_graph_type ty) (HString.concat2 ty_prefix i) pos

(***********************************************************
 * Type 2: Dependency Analysis Between nodes and contracts *
 ***********************************************************)
                            
let rec get_node_call_from_expr: LA.expr -> (LA.ident * Lib.position) list
  = function
  | Ident _ -> []
  | ModeRef (pos, is) -> if List.length is = 1 then []
                       else [(HString.concat2 contract_prefix (List.hd is), pos)]  
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
  | LA.Condact (pos, e1, e2, i, e3, e4) -> (HString.concat2 node_prefix i, pos)
    :: (get_node_call_from_expr e1) @ (get_node_call_from_expr e2)
    @ (List.flatten (List.map get_node_call_from_expr e3))
    @ (List.flatten (List.map get_node_call_from_expr e4))
  | LA.Activate (pos, i, e1, e2, e3) -> (HString.concat2 node_prefix i, pos)
    :: (get_node_call_from_expr e1) @ (get_node_call_from_expr e2)
    @ (List.flatten (List.map get_node_call_from_expr e3))
  | LA.Merge (_, _, id_exprs) ->
     List.flatten (List.map (fun (_, e) -> get_node_call_from_expr e) id_exprs)
  | LA.RestartEvery (pos, i, es, e1) ->
     (HString.concat2 node_prefix i, pos)
     :: (List.flatten (List.map get_node_call_from_expr es)) @ get_node_call_from_expr e1
  (* Temporal operators *)
  | LA.Pre (_, e) -> get_node_call_from_expr e
  | LA.Last _ -> []
  | LA.Fby (_, e1, _, e2) -> (get_node_call_from_expr e1) @ (get_node_call_from_expr e2)
  | LA.Arrow (_, e1, e2) -> (get_node_call_from_expr e1) @ (get_node_call_from_expr e2)
  (* Node calls *)
  | LA.Call (pos, i, es) -> (HString.concat2 node_prefix i, pos) :: List.flatten (List.map get_node_call_from_expr es)
  | LA.CallParam _ as e-> Lib.todo (__LOC__ ^ (Lib.string_of_t Lib.pp_print_position (LH.pos_of_expr e)))
(** Returns all the node calls from an expression *)

let  mk_graph_contract_node_eqn: LA.contract_node_equation -> dependency_analysis_data
  = function
  | LA.AssumptionVars _ -> empty_dependency_analysis_data
  | LA.ContractCall (pos, i, es, _) ->
     union_dependency_analysis_data
       (singleton_dependency_analysis_data contract_prefix i pos)
       (List.fold_left union_dependency_analysis_data empty_dependency_analysis_data
          (List.map (fun (i, p) -> singleton_dependency_analysis_data node_prefix i p)
             (List.flatten (List.map get_node_call_from_expr es))))
  | LA.Assume (_, _, _, e) ->
     List.fold_left union_dependency_analysis_data empty_dependency_analysis_data
       (List.map (fun (i, p) -> singleton_dependency_analysis_data node_prefix i p) (get_node_call_from_expr e))
  | LA.Guarantee (_, _, _, e) ->
     List.fold_left union_dependency_analysis_data empty_dependency_analysis_data
       (List.map (fun (i, p) -> singleton_dependency_analysis_data node_prefix i p) (get_node_call_from_expr e))
  | LA.Mode (_, _, reqs, ensures) ->
     let calls_ps = List.flatten (List.map (fun (_,_, e) -> get_node_call_from_expr e) (reqs @ ensures)) in
     let sub_graphs = (List.map (fun (i, p) -> singleton_dependency_analysis_data node_prefix i p) calls_ps) in
     List.fold_left union_dependency_analysis_data empty_dependency_analysis_data sub_graphs
  | LA.GhostConst c 
    | LA.GhostVar c ->
     match c with
     | FreeConst _ -> empty_dependency_analysis_data
     | UntypedConst (_, _, e) ->
        List.fold_left union_dependency_analysis_data empty_dependency_analysis_data
          (List.map (fun (i, p) -> singleton_dependency_analysis_data node_prefix i p) (get_node_call_from_expr e))
     | TypedConst (_, _, e, _) ->
        List.fold_left union_dependency_analysis_data empty_dependency_analysis_data
          (List.map (fun (i, p) -> singleton_dependency_analysis_data node_prefix i p) (get_node_call_from_expr e))
(** This builds a graph with all the node call dependencies from the equations of the contract  *)
       
let mk_graph_contract_decl: Lib.position -> LA.contract_node_decl -> dependency_analysis_data
  = fun pos (i , _, _, _, c) ->
  connect_g_pos (List.fold_left union_dependency_analysis_data empty_dependency_analysis_data (List.map mk_graph_contract_node_eqn c))
    (HString.concat2 contract_prefix i) pos
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
          | AnnotProperty (_, _, e) -> get_node_call_from_expr e
          | _ -> []) @ acc) [] 
(** Extracts all the node calls from a node item *)
  
let mk_graph_node_decl: Lib.position -> LA.node_decl -> dependency_analysis_data
  = fun pos (i, _, _, _, _, _, nitems, contract_opt) ->    
  let cg = connect_g_pos
             (match contract_opt with
              | None -> empty_dependency_analysis_data
              | Some c -> List.fold_left union_dependency_analysis_data empty_dependency_analysis_data
                            (List.map mk_graph_contract_node_eqn c))
             (HString.concat2 node_prefix i) pos in

  let node_refs = extract_node_calls nitems in
  List.fold_left
    (fun g (nr, p) -> union_dependency_analysis_data g
                        (connect_g_pos
                           (singleton_dependency_analysis_data node_prefix nr p) i pos))
    cg node_refs
(** Builds a dependency graph between the node in question to node calls 
 *  seen in the definition of the node and the inlined contract *)

(*********************************************************************
 * Common infrastructure for type 1 and type 2 dependency analysis   *
 *********************************************************************)

let add_decl: 'a IMap.t -> LA.ident -> 'a -> 'a IMap.t
  = fun m i dec -> IMap.add i dec m
                 
let check_and_add: 'a IMap.t -> Lib.position
                   -> HString.t -> LA.ident -> 'a -> ('a IMap.t) graph_result
  = fun m pos prefix i tyd ->
  if IMap.mem (HString.concat2 prefix i) m 
  then graph_error pos ("Identifier " ^ (HString.string_of_hstring i) ^ " is already declared")
  else R.ok (add_decl m (HString.concat2 prefix i) tyd)
(** reject program if identifier is already declared  *)
  
let rec  mk_decl_map: LA.declaration IMap.t -> LA.t -> (LA.declaration IMap.t) graph_result =
  fun m ->
  function  
  | [] -> R.ok m 

  | (LA.TypeDecl (span, FreeType (_, i)) as tydecl) :: decls
  | (LA.TypeDecl (span, AliasType (_, i, _)) as tydecl) :: decls ->
    let {LA.start_pos = pos} = span in
    check_and_add m pos ty_prefix i tydecl >>= fun m' ->
    mk_decl_map m' decls 

  | (LA.ConstDecl (span, FreeConst (_, i, _)) as cnstd) :: decls
  | (LA.ConstDecl (span, UntypedConst (_, i, _)) as cnstd) :: decls
  | (LA.ConstDecl (span, TypedConst (_, i, _, _)) as cnstd) :: decls -> 
    let {LA.start_pos = pos} = span in
    check_and_add m pos const_prefix i cnstd  >>= fun m' ->
    mk_decl_map m' decls 

  | (LA.NodeDecl (span, (i, _, _, _, _, _, _, _)) as ndecl) :: decls
  | (LA.FuncDecl (span, (i, _, _, _, _, _, _, _)) as ndecl) :: decls ->
    let {LA.start_pos = pos} = span in
    check_and_add m pos node_prefix i ndecl  >>= fun m' ->
    mk_decl_map m' decls

  | LA.ContractNodeDecl (span, (i, _, _, _, _)) as cndecl :: decls ->
    let {LA.start_pos = pos} = span in
    check_and_add m pos contract_prefix i cndecl >>= fun m' ->
    mk_decl_map m' decls

  | LA.NodeParamInst _ :: _-> Lib.todo __LOC__
(** builds an id :-> decl map  *)
                            
let mk_graph_decls: LA.t -> dependency_analysis_data 
  = let mk_graph: LA.declaration -> dependency_analysis_data = function
      | TypeDecl (_, tydecl) -> mk_graph_type_decl tydecl 
      | ConstDecl (_, cdecl) -> mk_graph_const_decl cdecl
      | NodeDecl ({LA.start_pos = pos}, ndecl) -> mk_graph_node_decl pos ndecl
      | FuncDecl ({LA.start_pos = pos}, ndecl) -> mk_graph_node_decl pos ndecl
      | ContractNodeDecl ({LA.start_pos = pos}, cdecl) -> mk_graph_contract_decl pos cdecl
      | NodeParamInst  _ -> Lib.todo __LOC__ in
    fun decls ->
    List.fold_left union_dependency_analysis_data empty_dependency_analysis_data (List.map mk_graph decls)
(** Builds a dependency graph for top-level types and constant defintions (for type 1 analysis) 
   and nodes and contracts (for type 2 analysis)
   See Note {Types of dependency analysis} for more information about different kinds of
   dependency analysis  *)

let extract_decls: 'a IMap.t -> LA.ident list -> ('a list) graph_result
  = fun decl_map ids ->
  R.ok (List.concat (List.map (fun i -> match (IMap.find_opt i decl_map) with
                     | None -> []
                     | Some i' -> [i']) ids)) 
(** Given a list of ids, finds the associated payload from the playload map.
    It ignores ids that it cannot find as they may be globals. 
 *)

    
let split_contract_equations: LA.contract -> (LA.contract * LA.contract)
  = let split_eqns: (LA.contract * LA.contract) -> LA.contract_node_equation -> (LA.contract * LA.contract)
      = fun (ps, qs) -> fun e ->
      match e with
      | LA.GhostConst _
      | LA.GhostVar _
      | LA.ContractCall _
      | LA.Mode _ -> e::ps, qs
      | LA.Guarantee _
      | LA.Assume _
      | LA.AssumptionVars _ -> ps, e::qs
    in
    List.fold_left (split_eqns) ([],[])
    
let rec vars_with_flattened_nodes: node_summary -> LA.expr -> LA.SI.t list = fun m ->
  function
  | Ident (_ , i) -> [SI.singleton i]
  | ModeRef _ -> [SI.empty]
  | RecordProject (_, e, _) -> vars_with_flattened_nodes m e 
  | TupleProject (_, e, _) -> vars_with_flattened_nodes m e
  (* Values *)
  | Const _ -> [SI.empty]

  (* Operators *)
  | UnaryOp (_,_,e) -> vars_with_flattened_nodes m e
  | BinaryOp (_,_,e1, e2) ->
    let e1' = vars_with_flattened_nodes m e1 in
    let e2' = vars_with_flattened_nodes m e2 in
    [SI.union (SI.flatten e1') (SI.flatten e2')]
  | TernaryOp (_,_, e1, e2, e3) ->
    let e1' = vars_with_flattened_nodes m e1 in
    let e2' = vars_with_flattened_nodes m e2 in
    let e3' = vars_with_flattened_nodes m e3 in
    [List.fold_left SI.union SI.empty (e1' @ e2' @ e3')]
  | NArityOp (_, _,es) ->
    let es' = List.map (vars_with_flattened_nodes m) es in
    [es' |> List.flatten |> SI.flatten]
  | ConvOp  (_,_,e) -> [SI.flatten (vars_with_flattened_nodes m e)]
  | CompOp (_,_,e1, e2) ->
    let e1' = vars_with_flattened_nodes m e1 in
    let e2' = vars_with_flattened_nodes m e2 in
    [SI.union (SI.flatten e1') (SI.flatten e2')]
  (* Structured expressions *)
  | RecordExpr (_, _, flds) ->
    let flds' = List.map (vars_with_flattened_nodes m) (snd (List.split flds)) in
    [flds' |> List.flatten |> SI.flatten]
  | GroupExpr (_, _, es) ->
    let es' = List.map (vars_with_flattened_nodes m) es in
    [es' |> List.flatten |> SI.flatten]

  (* Update of structured expressions *)
  | StructUpdate (_, e1, _, e2) ->
    let e1' = vars_with_flattened_nodes m e1 in
    let e2' = vars_with_flattened_nodes m e2 in
    [SI.union (SI.flatten e1') (SI.flatten e2')]
  | ArrayConstr (_, e1, e2) ->
    let e1' = vars_with_flattened_nodes m e1 in
    let e2' = vars_with_flattened_nodes m e2 in
    [SI.union (SI.flatten e1') (SI.flatten e2')]
  | ArrayIndex (_, e1, e2) ->
    let e1' = vars_with_flattened_nodes m e1 in
    let e2' = vars_with_flattened_nodes m e2 in
    [SI.union (SI.flatten e1') (SI.flatten e2')]
  | ArraySlice (_, e1, (e2, e3)) ->
    let e1' = vars_with_flattened_nodes m e1 in
    let e2' = vars_with_flattened_nodes m e2 in
    let e3' = vars_with_flattened_nodes m e3 in
    [List.fold_left SI.union SI.empty (e1' @ e2' @ e3')]
  | ArrayConcat (_, e1, e2) ->
    let e1' = vars_with_flattened_nodes m e1 in
    let e2' = vars_with_flattened_nodes m e2 in
    [SI.union (SI.flatten e1') (SI.flatten e2')]

  (* Quantified expressions *)
  | Quantifier (_, _, qs, e) ->
    let e' = vars_with_flattened_nodes m e in
    [SI.diff (SI.flatten e') (SI.flatten (List.map LH.vars_of_ty_ids qs))]
  (* Clock operators *)
  | When (_, e, _) -> [SI.flatten (vars_with_flattened_nodes m e)]
  | Current  (_, e) -> [SI.flatten (vars_with_flattened_nodes m e)]
  | Condact (_, e1, e2, i, es1, es2) ->
    let e1' = SI.flatten (vars_with_flattened_nodes m e1) in
    let e2' = SI.flatten (vars_with_flattened_nodes m e2) in
    let es1' = List.flatten (List.map (vars_with_flattened_nodes m) es1) in
    let es2' = List.flatten (List.map (vars_with_flattened_nodes m) es2) in
     [SI.add i (SI.flatten (e1' :: e2' :: es1' @ es2'))]
  | Activate (_, _, e1, e2, es) ->
    let e1' = SI.flatten (vars_with_flattened_nodes m e1) in
    let e2' = SI.flatten (vars_with_flattened_nodes m e2) in
    let es' = List.flatten (List.map (vars_with_flattened_nodes m) es) in
    [SI.flatten (e1' :: e2' :: es')]
  | Merge (_, _, es) ->
    let es' = List.split es |> snd |> List.map (vars_with_flattened_nodes m) in
    [es' |> List.flatten |> SI.flatten]
  | RestartEvery (_, i, es, e) ->
    let e' = SI.flatten (vars_with_flattened_nodes m e) in
    let es' = List.flatten (List.map (vars_with_flattened_nodes m) es) in
    [SI.add i (SI.flatten (e' :: es'))]

  (* Temporal operators *)
  | Pre (_, _) -> [SI.empty]
  | Last (_, _) -> [SI.empty]
  | Fby (_, e1, _, e2)
  | Arrow (_, e1, e2) ->
    let e1' = vars_with_flattened_nodes m e1 in
    let e2' = vars_with_flattened_nodes m e2 in
    [SI.union (SI.flatten e1') (SI.flatten e2')]

  (* Node calls *)
  | Call (_, i, es) ->
    (* Format.eprintf "call expr: %a\n\n" (Lib.pp_print_list LA.pp_print_expr ";") es;
    Format.eprintf "call: %a\n\n" HString.pp_print_hstring i; *)
    (match IMap.find_opt i m with
      | None -> assert false (* guaranteed by lustreSyntaxChecks *)
      | Some ns ->
        let sum_bds = IntMap.bindings ns in
        let es' = List.flatten (List.map (vars_with_flattened_nodes m) es) in
(*         Format.eprintf "sum_bds: %a\n\n"
        (Lib.pp_print_list
          (Lib.pp_print_pair
            Format.pp_print_int
            (Lib.pp_print_list Format.pp_print_int ",")
            ":")
        ";")
        sum_bds;
        Format.eprintf "es': %a\n\n"
          (Lib.pp_print_list Format.pp_print_string ",")
          (LA.SI.fold (fun key x -> key :: x) (LA.SI.flatten es') []); *)
        List.concat (List.map
          (fun (_, b) -> List.map
            (fun i -> match List.nth_opt es' i with
              | Some x -> x
              | None -> SI.empty)
            b)
          sum_bds))
  | CallParam (_, _, _, es) ->
    let es' = List.flatten (List.map (vars_with_flattened_nodes m) es) in
    [SI.flatten es']
(** get all the variables and flatten node calls using 
    the node summary for an expression *)
             
let rec mk_contract_eqn_map: LA.contract_node_equation IMap.t -> LA.contract -> (LA.contract_node_equation IMap.t) graph_result
  = fun m ->
  function
  | [] -> R.ok m
  | (LA.GhostConst (FreeConst (pos, i, _)) as gc) :: eqns
    | (LA.GhostConst (UntypedConst (pos, i, _)) as gc) :: eqns
    | (LA.GhostConst (TypedConst (pos, i, _, _)) as gc) :: eqns -> 
     check_and_add m pos empty_hs i gc >>= fun m' -> mk_contract_eqn_map m' eqns  
  | (LA.GhostVar (FreeConst (pos, i, _)) as gc) :: eqns
    | (LA.GhostVar (UntypedConst (pos, i, _)) as gc) :: eqns
    | (LA.GhostVar (TypedConst (pos, i, _, _)) as gc) :: eqns -> 
     check_and_add m pos empty_hs i gc >>= fun m' -> mk_contract_eqn_map m' eqns  
  | (LA.ContractCall (pos, i, _, _ ) as cc ) :: eqns -> 
     check_and_add m pos contract_prefix i cc >>= fun m' -> mk_contract_eqn_map m' eqns  
  | (LA.Mode (pos, i, _, _) as mode) :: eqns ->
     check_and_add m pos mode_prefix i mode >>= fun m' -> mk_contract_eqn_map m' eqns  
  | _ -> assert false
              

let rec mk_graph_expr2: node_summary -> LA.expr -> dependency_analysis_data list graph_result
  = fun m ->
  function
  | LA.Ident (pos, i) -> R.ok [singleton_dependency_analysis_data empty_hs i pos]
  | LA.ModeRef (pos, ids) ->
     R.ok [singleton_dependency_analysis_data mode_prefix (List.nth ids (List.length ids - 1) ) pos] 
  | LA.Const _ ->
     R.ok [empty_dependency_analysis_data]

  | LA.RecordExpr (pos, i, ty_ids) ->
     R.seq (List.map (fun ty_id -> mk_graph_expr2 m (snd ty_id)) ty_ids) >>= fun gs -> 
     R.ok [List.fold_left union_dependency_analysis_data
             (singleton_dependency_analysis_data empty_hs i pos)
             (List.concat gs)]
  | LA.StructUpdate (_, e1, _, e2) ->
     mk_graph_expr2 m e1 >>= fun g1 ->
     mk_graph_expr2 m e2 >>= fun g2 ->
     R.ok [List.fold_left union_dependency_analysis_data
             empty_dependency_analysis_data (g1 @ g2)] 
  | LA.UnaryOp (_, _, e)
    | LA.ConvOp (_, _, e) -> mk_graph_expr2 m e
  | LA.BinaryOp (_, _, e1, e2)
    | LA.CompOp (_, _, e1, e2) ->
     mk_graph_expr2 m e1 >>= fun g1 ->
     mk_graph_expr2 m e2 >>= fun g2 ->
     R.ok [List.fold_left union_dependency_analysis_data
             empty_dependency_analysis_data (g1 @ g2)] 

  | LA.TernaryOp (p, _, e1, e2, e3) ->
     (mk_graph_expr2 m e1) >>= fun g1 -> 
     let g1 = List.fold_left union_dependency_analysis_data empty_dependency_analysis_data g1 in
     (mk_graph_expr2 m e2) >>= fun g2 ->
     (mk_graph_expr2 m e3) >>= fun g3 ->
     if (List.length g3 != List.length g2)
     then
       (Debug.parse ("e2: %a"
                         ^^ "\ne3: %a"
                         ^^ "\ng2 length %a: %a"
                         ^^ "\ng3 length %a: %a")
          LA.pp_print_expr e2
          LA.pp_print_expr e3
          Format.pp_print_int (List.length g2)
          (Lib.pp_print_list G.pp_print_graph ", ") (List.map (fun g -> g.graph_data) g2)
          Format.pp_print_int (List.length g3)
          (Lib.pp_print_list G.pp_print_graph ", ") (List.map (fun g -> g.graph_data) g3)
       ; graph_error p "Width of each branch is not the same.")
     else
       R.ok (List.map (fun g -> union_dependency_analysis_data g1 g)
               (List.map2 (fun g g' -> union_dependency_analysis_data g g') g2 g3))
  | LA.RecordProject (_, e, _)
    | LA.TupleProject (_, e, _) -> mk_graph_expr2 m e
  | LA.ArrayConstr (_, e1, e2) ->
     mk_graph_expr2 m e1 >>= fun g1 ->
     mk_graph_expr2 m e2 >>= fun g2 -> 
     R.ok [List.fold_left union_dependency_analysis_data empty_dependency_analysis_data (g1 @ g2)] 
  | LA.ArraySlice (_, e1, (e2, e3)) ->
     mk_graph_expr2 m e1 >>= fun g1 ->
     mk_graph_expr2 m e2 >>= fun g2 ->
     mk_graph_expr2 m e3 >>= fun g3 ->
     R.ok [List.fold_left union_dependency_analysis_data empty_dependency_analysis_data
             (g1 @ g2 @ g3) ]
  | LA.ArrayIndex (_, e1, _) -> mk_graph_expr2 m e1

  | LA.ArrayConcat  (_, e1, e2) ->
     mk_graph_expr2 m e1 >>= fun g1 ->
     mk_graph_expr2 m e2 >>= fun g2 -> 
     R.ok [List.fold_left union_dependency_analysis_data empty_dependency_analysis_data (g1 @ g2)] 
  | LA.GroupExpr (_, ExprList, es) ->
    R.seq (List.map (mk_graph_expr2 m) es) >>= fun gs -> R.ok (List.concat gs)
  | LA.GroupExpr (_, _, es) ->
     R.seq (List.map (mk_graph_expr2 m) es) >>= fun gs ->
     R.ok [List.fold_left
             union_dependency_analysis_data
             empty_dependency_analysis_data
             (List.concat gs)]

  | LA.When (_, e, _) -> mk_graph_expr2 m e
  | LA.Current (_, e) -> mk_graph_expr2 m e
  | LA.Condact (pos, _, _, n, e1s, e2s) ->
     let node_call = LA.Call(pos, n, e1s) in
     mk_graph_expr2 m node_call >>= fun gs ->
     R.seq (List.map (mk_graph_expr2 m) e2s) >>= fun d_gs -> 
     let default_gs = List.concat d_gs in
     if List.length gs != List.length default_gs
     then graph_error pos "In condact width of default values does not match width of node call"
     else R.ok (List.map2 union_dependency_analysis_data gs default_gs)
  | LA.Activate (pos, n, _, _, es) ->
     let node_call = LA.Call(pos, n, es) in
     mk_graph_expr2 m node_call
  | LA.Merge (_, _, cs) ->
     R.seq (List.map (fun (_, e) -> (mk_graph_expr2 m) e) cs) >>= fun gs ->
     R.ok [List.fold_left union_dependency_analysis_data empty_dependency_analysis_data
        (List.concat gs)] 
  | LA.RestartEvery (p, n, es, _) ->
     let node_call = LA.Call(p, n, es) in
     mk_graph_expr2 m node_call
  | LA.Pre (_, e) ->
     mk_graph_expr2 m e >>= fun g ->
       R.ok (List.map (map_g_pos (fun v -> HString.concat2 v (HString.mk_hstring "$p"))) g) 
  | LA.Last (pos, i) -> R.ok [singleton_dependency_analysis_data (HString.mk_hstring "last$") i pos]
  | LA.Fby (p, e1, _, e2)
  | LA.Arrow (p, e1, e2) as e ->
     mk_graph_expr2 m e1 >>= fun g1 ->
     mk_graph_expr2 m e2 >>= fun g2 ->
     if (List.length g1 != List.length g2) then
       (
         Debug.parse ("LHS: %a\n"
                          ^^ "LHS graphs : %a\n"
                          ^^ " RHS: %a\n"
                          ^^ " RHS: graphs %a\n") 
           LA.pp_print_expr e1
           (Lib.pp_print_list G.pp_print_graph ",") (List.map (fun g -> g.graph_data) g1)
           LA.pp_print_expr e2
           (Lib.pp_print_list G.pp_print_graph ",") (List.map (fun g -> g.graph_data) g2)
       ; graph_error p ("In expression " ^ (Lib.string_of_t LA.pp_print_expr e)  
                             ^ " width of right hand side is not equal to left hand side of arrow.")
       )
     else 
       R.ok (List.map2 (fun l r -> union_dependency_analysis_data l r ) g1 g2)

  | LA.Call (_, i, es) ->
     (match IMap.find_opt i m with
      | None -> assert false (* guaranteed by lustreSyntaxChecks *)
      | Some summary ->
         let sum_bds = IntMap.bindings summary in
         R.seq (List.map (mk_graph_expr2 m) es) >>= fun gs ->
         let ip_gs = List.concat gs in
         (* For each output stream, return the associated graph of the input expression 
            whose current value it depends on. If the output stream does not depend on 
            any input stream's current value, return an empty graph. *)
         R.ok (List.map (fun (_, b) ->
             if List.length b = 0
             then empty_dependency_analysis_data
             else (List.fold_left union_dependency_analysis_data empty_dependency_analysis_data
                     (List.map (List.nth ip_gs) b))
           ) sum_bds))
  | e -> Lib.todo (__LOC__ ^ " " ^ Lib.string_of_t Lib.pp_print_position (LH.pos_of_expr e))
(** This graph is useful for analyzing equations assuming that the nodes/contract call
    recursive calling has been resolved already.
    The generated graph would be useful only if the 
    pre's are abstracted out first and then passed into this 
    function using [LH.abstract_pre_subexpressions] *)


let mk_graph_contract_node_eqn2: dependency_analysis_data -> LA.contract_node_equation -> dependency_analysis_data
  = fun ad ->
  function
  | LA.AssumptionVars _ -> ad
  | LA.ContractCall (pos, i, es, _) ->
     connect_g_pos 
       (List.fold_left union_dependency_analysis_data ad
          (List.map (fun e -> mk_graph_expr (LH.abstract_pre_subexpressions e)) es))
       (HString.concat2 contract_prefix i) pos
    
  | LA.Assume (_, _, _, e)
    | LA.Guarantee (_, _, _, e) -> union_dependency_analysis_data ad (mk_graph_expr (LH.abstract_pre_subexpressions e))
  | LA.Mode (pos, i, reqs, ensures) ->
     let mgs = List.fold_left
                 union_dependency_analysis_data
                 ad
                 (List.map (fun (_,_, e) ->
                      mk_graph_expr
                        ((LH.abstract_pre_subexpressions e)))
                    (reqs @ ensures)) in
     connect_g_pos mgs
       (HString.concat2 mode_prefix i) pos
  | LA.GhostConst c 
    | LA.GhostVar c ->
     match c with
     | FreeConst _ -> ad
     | UntypedConst (pos, i, e)
       | TypedConst (pos, i, e, _) ->
        let vars = vars_with_flattened_nodes ad.nsummary (LH.abstract_pre_subexpressions e) in
        let effective_vars = LA.SI.elements (SI.flatten vars) in
        connect_g_pos
          (List.fold_left (fun g v ->
               union_dependency_analysis_data g (singleton_dependency_analysis_data empty_hs v pos))
             ad effective_vars)
          i pos

(*
let mk_graph_const_decl2: node_summary -> LA.const_decl -> dependency_analysis_data graph_result
  = fun m ->
  function
  | LA.FreeConst (pos, i, ty) ->
     R.ok (connect_g_pos (mk_graph_type ty) (const_prefix ^ i) pos)
  | LA.UntypedConst (pos, i, e) ->
     (mk_graph_expr2 m e) >>= fun g -> 
     R.ok (connect_g_pos
             (List.fold_left union_dependency_analysis_data empty_dependency_analysis_data g)
             (const_prefix ^ i) pos) 
  | LA.TypedConst (pos, i, e, ty) ->
     mk_graph_expr2 m e >>= fun g -> 
     R.ok (connect_g_pos
             (union_dependency_analysis_data
                (List.fold_left
                   union_dependency_analysis_data
                   empty_dependency_analysis_data g)
                (mk_graph_type ty)) (const_prefix ^ i) pos)


let mk_graph_contract_eqns: node_summary -> LA.contract -> dependency_analysis_data graph_result
  = fun  m ->
  let mk_graph: LA.contract_node_equation -> dependency_analysis_data graph_result
    = function
    | LA.GhostConst c -> mk_graph_const_decl2 m c
    | LA.GhostVar c -> mk_graph_const_decl2 m c
    | LA.Mode (pos, i, reqs, ens) ->
       let es = List.map (fun (_, _,  e) -> e) (reqs @ ens) in
       R.seq (List.map (mk_graph_expr2 m) es) >>= fun gs ->
       let g = List.fold_left union_dependency_analysis_data
                 empty_dependency_analysis_data (List.concat gs) in 
       R.ok (connect_g_pos g (mode_prefix ^ i) pos) 
    | LA.Assume _ 
      | LA.Guarantee _ 
      | LA.ContractCall _ -> R.ok empty_dependency_analysis_data 
  in
  fun eqns ->
  R.seq (List.map mk_graph eqns) >>= fun gs -> 
  R.ok (List.fold_left union_dependency_analysis_data empty_dependency_analysis_data gs) 
*)

let expression_current_streams: dependency_analysis_data -> LA.expr -> LA.ident list graph_result
  = fun ad e ->
  let vars = vars_with_flattened_nodes ad.nsummary (LH.abstract_pre_subexpressions e) in
  let vs = LA.SI.elements (SI.flatten vars) in
  let memo = ref G.VMap.empty in
  let rechable_vs = List.concat (List.map
    (fun v -> G.to_vertex_list (G.memoized_reachable memo ad.graph_data v))
    vs)
  in
  Debug.parse "Current Stream Usage for %a: %a"
    (Lib.pp_print_list G.pp_print_vertex ", ") vs
    (Lib.pp_print_list G.pp_print_vertex ", ") rechable_vs 
  ; R.ok rechable_vs
(** all the variables who's current value is used in the expression *)

let check_eqn_no_current_vals: LA.SI.t -> dependency_analysis_data -> LA.expr -> unit graph_result
  = fun node_out_streams ad e -> 
  expression_current_streams ad e >>= fun s ->
  R.ok (SI.inter node_out_streams (LA.SI.of_list s)) >>= fun assume_vars_out_streams -> 
  Debug.parse "node_params: %a non pre vars of e: %a"
    (Lib.pp_print_list LA.pp_print_ident ", ") (SI.elements node_out_streams)
    (Lib.pp_print_list LA.pp_print_ident ", ")
    (SI.elements (LH.vars (LH.abstract_pre_subexpressions e)))
  ; R.guard_with (R.ok (SI.is_empty assume_vars_out_streams))
      (graph_error (LH.pos_of_expr e)
         ("Contract assumption or mode requirements cannot depend on "
          ^ "current values of output parameters but found: "
          ^ (Lib.string_of_t (Lib.pp_print_list LA.pp_print_ident ", ")
               (SI.elements assume_vars_out_streams))))
(** Make sure that no idents in the first argument occur in the expression *)
  
   
let mk_graph_contract_decl2 
  = fun ad (_ , _, _, _, c) ->
  List.fold_left union_dependency_analysis_data
    ad
    (List.map (mk_graph_contract_node_eqn2 ad) c)

let validate_contract_equation: LA.SI.t -> dependency_analysis_data -> LA.contract_node_equation -> unit graph_result
  = fun ids ad ->
  function
  | LA.Assume (_, _, _, e) ->
     check_eqn_no_current_vals ids ad e
  | LA.Mode (_, _, reqs, _) ->
     let req_es = List.map (fun (_, _, e) -> e) reqs in
     R.seq_ (List.map (check_eqn_no_current_vals ids ad) req_es) 
  | _ -> R.ok()                             
(** Check if any of the out stream vars of the node 
   is being used at its current value in assumption or mode requires *)

let sort_and_check_contract_eqns: dependency_analysis_data
                                  -> LA.contract_node_decl
                                  -> LA.contract_node_decl graph_result
  = fun ad ((i, params , ips, ops, contract) as decl)->
  Debug.parse "Sorting contract equations for %a" LA.pp_print_ident i
  ; let ip_ids = List.map (fun ip -> LH.extract_ip_ty ip |> fst) ips in
    let op_ids = List.map (fun ip -> LH.extract_op_ty ip |> fst) ops in
    let ids_to_skip = SI.of_list (ip_ids @ op_ids) in 
    let ad' = mk_graph_contract_decl2 ad decl in
    (try (R.ok (G.topological_sort ad'.graph_data)) with
     | Graph.CyclicGraphException ids ->
        let ids = List.map HString.mk_hstring ids in
        if List.length ids > 1
        then (match (find_id_pos ad'.id_pos_data (List.hd ids)) with
              | None -> graph_error Lib.dummy_pos
                          ("Cyclic dependency found but Cannot find position for identifier "
                           ^ (HString.string_of_hstring (List.hd ids)) ^ " This should not happen!") 
              | Some p -> graph_error p
                            ("Cyclic dependency detected in definition of identifiers: "
                             ^ Lib.string_of_t (Lib.pp_print_list LA.pp_print_ident ", ") ids))
        else graph_error Lib.dummy_pos "Cyclic dependency with no ids detected. This should not happen!")

    >>= fun sorted_ids ->
    let equational_vars = List.filter (fun i -> not (SI.mem i ids_to_skip)) (List.rev sorted_ids) in
    let (to_sort_eqns, rest) = split_contract_equations contract in
    mk_contract_eqn_map IMap.empty to_sort_eqns >>= fun eqn_map ->
         extract_decls eqn_map equational_vars >>= fun contract' ->
      Debug.parse "sorted contract equations for contract %a %a"
        LA.pp_print_ident i
        (Lib.pp_print_list LA.pp_print_contract_item "\n") contract'

      ; R.seq_ (List.map (validate_contract_equation (SI.of_list op_ids) ad') contract) 
        >> R.ok(i, params , ips, ops, contract' @ rest)
(** This function does two things: 
   1. Sort the contract equations according to their dependencies
      - The assumptions and guarantees are added to the bottom of the list as 
        no other contract equation can depend on it. 
   2. Ensures the assumptions and requires in each mode does not use the current value
      of the output streams. *)


let sort_declarations: LA.t -> (LA.t * LA.ident list) graph_result
  = fun decls ->
  (* 1. make an id :-> decl map  *)
  mk_decl_map IMap.empty decls >>= fun decl_map ->
  (* 2. build a dependency graph *)
  let ad = mk_graph_decls decls in
  (* 3. try to sort it, raise an error if it is cyclic, or extract sorted decls from the decl_map *)
  (try (R.ok (G.topological_sort ad.graph_data)) with
   | Graph.CyclicGraphException ids ->
      let ids = List.map HString.mk_hstring ids in
      if List.length ids > 1
      then (match (find_id_pos ad.id_pos_data (List.hd ids)) with
            | None -> graph_error Lib.dummy_pos
                        ("Cyclic dependency found but Cannot find position for identifier "
                         ^ (HString.string_of_hstring (List.hd ids)) ^ " This should not happen!") 
            | Some p -> graph_error p
                          ("Cyclic dependency detected in definition of identifiers: "
                           ^ Lib.string_of_t (Lib.pp_print_list LA.pp_print_ident ", ") ids))
      else graph_error Lib.dummy_pos
             "Cyclic dependency with no ids detected. This should not happen!")
  >>= fun sorted_ids ->
  let dependency_sorted_ids = List.rev sorted_ids in
  let is_contract_node node_name =
    try String.equal (HString.sub node_name 0 9) "contract "
    with _ -> false
  in
  let toplevel_nodes = ad.graph_data |> G.non_target_vertices
    |> G.to_vertex_list
    |> List.filter (fun s -> not (is_contract_node s))
  in
  Debug.parse "sorted ids: %a" (Lib.pp_print_list LA.pp_print_ident ",")  dependency_sorted_ids;
  extract_decls decl_map dependency_sorted_ids >>= fun sorted_decls ->
  R.ok (sorted_decls, toplevel_nodes)
(** Accepts a function to generate a declaration map, 
    a function to generate the graph of the declarations,
    runs a topological sort on the ids extracted from the map and then 
    returns the sorted declarations (or an error if circular dependency is detected)  *)
  

(************************************************************************
 * Type 3. Dependency Analysis of contract equations and node equations *
 ************************************************************************)

let summarize_ip_vars: LA.ident list -> SI.t -> int list = fun ips critial_ips ->
  (List.fold_left (fun (acc, nums) i ->
       if SI.mem i critial_ips
       then (nums::acc, nums+1)
       else (acc, nums+1)) ([], 0)) ips |> fst 
(** Helper function to generate a node summary *)
  
let mk_node_summary: node_summary -> LA.node_decl -> node_summary
    = fun s (i, imported, _, ips, ops, _, items, _) ->
  if not imported
  then 
    let op_vars = List.map (fun o -> LH.extract_op_ty o |> fst) ops in
    let ip_vars = List.map (fun o -> LH.extract_ip_ty o |> fst) ips in
    let node_equations = List.concat (List.map LH.extract_node_equation items) in
    let process_one_eqn = fun (LA.StructDef (_, lhss), e) ->
      let lhs_vars = LA.SI.elements (LA.SI.flatten (List.map LH.vars_of_struct_item lhss)) in
      let vars = SI.flatten (vars_with_flattened_nodes s e) in
      let ms = List.map (Lib.flip IMap.singleton (LA.SI.elements vars)) lhs_vars in
      List.fold_left (IMap.union (fun _ _ v2 -> Some v2)) IMap.empty ms
    in
    let node_equation_dependency_map = List.fold_left
      (IMap.union (fun _ _ v2 -> Some v2)) IMap.empty
      (List.map process_one_eqn node_equations)
    in

    Debug.parse "Node equation dependency map for node %a {\n %a \n}"
      LA.pp_print_ident i
      (Lib.pp_print_list (Lib.pp_print_pair (LA.pp_print_ident) (Lib.pp_print_list (LA.pp_print_ident) ", ") "->") "\n")
      (IMap.bindings node_equation_dependency_map);
    let mk_g = fun (lhs, vars) ->  G.connect (List.fold_left G.union G.empty (List.map G.singleton vars)) lhs in
    let g = List.fold_left G.union G.empty (List.map mk_g (IMap.bindings node_equation_dependency_map)) in

    Debug.parse "Node equation graph: %a" G.pp_print_graph g;
    let memo = ref G.VMap.empty in
    let vars_op_depends_on = List.map (fun i -> G.to_vertex_list (G.memoized_reachable memo g i)) op_vars in
    let critical_ips = List.map
      (fun vs -> SI.inter (SI.of_list vs) (SI.of_list ip_vars)
      |> summarize_ip_vars ip_vars) vars_op_depends_on
    in
    let ns = (List.fold_left
        (fun (op_idx, m) cip -> (op_idx+1, IntMap.add op_idx cip m))
        (0, IntMap.empty) critical_ips
      |> snd)
    in
    IMap.add i ns s
  else
    IMap.add
      i
      ((List.fold_left (fun (op_idx, m) _ ->
            (op_idx+1, IntMap.add op_idx [] m)) (0, IntMap.empty) ops) |> snd)
      s
(** Computes the node call summary of the node to the input stream of the node.
    
    For imported nodes and imported functions we assume that output streams do not depend on 
    any of the input streams. This restriction is in place to avoid rejecting valid programs.
 *)


let get_contract_exports: contract_summary -> LA.contract_node_equation -> LA.ident list
  = fun m ->
  function
  | LA.GhostConst (LA.FreeConst (_, i, _))
    | LA.GhostConst (LA.UntypedConst (_, i, _))
    | LA.GhostConst (LA.TypedConst (_, i, _, _))
    | LA.GhostVar (LA.FreeConst (_, i, _))
    | LA.GhostVar (LA.UntypedConst (_, i, _))
    | LA.GhostVar (LA.TypedConst (_, i, _, _))
    | LA.Mode (_, i, _, _) -> [i]
  | LA.ContractCall (_, cc, _, _) ->
     (match (IMap.find_opt cc m) with
     | Some ids -> List.map (fun i -> HString.concat (HString.mk_hstring "::") [cc;i]) ids
     | None -> failwith ("Undeclared contract " ^ (HString.string_of_hstring cc) ^ ". Should not happen!"))  
 | _ -> []
(** Traverses all the contract equations to make a contract export list. *)

let mk_contract_summary: contract_summary -> LA.contract_node_decl -> contract_summary
  = fun m (i, _, _, _, contract) ->
  let export_ids = List.concat (List.map (get_contract_exports m) contract) in
  IMap.add i export_ids m 
(** Make contract summary that is a list of all symbols that a contract exports *)
                                            
let mk_graph_eqn: node_summary
                  -> LA.node_equation
                  -> dependency_analysis_data graph_result =
  let handle_one_lhs: dependency_analysis_data
                      -> LA.struct_item
                      -> dependency_analysis_data
    = fun rhs_g lhs ->
    match lhs with
    | LA.SingleIdent (p, i) -> connect_g_pos rhs_g i p 
    | LA.ArrayDef (p, arr, is) ->
      let hs_dollar = HString.mk_hstring "$" in
      let arr' = HString.concat hs_dollar
        [arr;(List.fold_left
          (fun acc i -> HString.concat hs_dollar [acc;i])
          empty_hs
          is)]
      in 
      connect_g_pos (List.fold_left (fun g i -> remove g i) rhs_g is)  arr' p
    (* None of these items below are supported at parsing yet. *)
    | LA.TupleStructItem (p, _)
      | LA.TupleSelection (p, _, _)
      | LA.FieldSelection (p, _, _)
      | LA.ArraySliceStructItem (p, _, _)
      ->  Lib.todo ("Parsing not supported" ^ __LOC__
                    ^ " " ^ Lib.string_of_t Lib.pp_print_position p) in
  fun m -> function
        | Equation (pos, (LA.StructDef (_, lhss)), e) ->
           (* We need to find the mapping of graphs from the 
              lhs of the equation to the rhs of the equations 
              such that the width of each of the lhs and rhs 
              especially if it is just an identifier.
            *)
           mk_graph_expr2 m (LH.abstract_pre_subexpressions e) >>= fun rhs_g -> 
           (Debug.parse "For lhss=%a: width RHS=%a, width LHS=%a"
              (Lib.pp_print_list LA.pp_print_struct_item ", ") lhss
              Format.pp_print_int (List.length rhs_g)
              Format.pp_print_int (List.length lhss)
           ;
             if (List.length rhs_g = List.length lhss)
             then  (R.ok (List.fold_left union_dependency_analysis_data
                            empty_dependency_analysis_data
                            (List.map2 handle_one_lhs rhs_g lhss)))
             else (graph_error pos ("Left hand side of the equation has width "
                                    ^ Stdlib.string_of_int (List.length lhss)
                                    ^ " and right hand side of the equation has width "
                                    ^ Stdlib.string_of_int (List.length rhs_g)
                                    ^ ". They should be of same width.")))
        | _ -> R.ok (empty_dependency_analysis_data)
(** Make a dependency graph from the equations. Each LHS has an edge that goes into its RHS definition. *)
             
let rec mk_graph_node_items: node_summary -> LA.node_item list -> dependency_analysis_data graph_result =
  fun m -> function
  | [] -> R.ok empty_dependency_analysis_data
  | (Body eqn) :: items -> 
       (mk_graph_eqn m eqn) >>= fun g ->
       (mk_graph_node_items m items) >>=
         fun gs -> 
         R.ok (union_dependency_analysis_data g gs)
  | _ :: items -> mk_graph_node_items m items
(** Traverse all the node items to make a dependency graph  *)

let rec mk_state_map: LA.state IMap.t -> LA.state list -> (LA.state IMap.t) graph_result
  = fun m ->
  function
  | [] -> R.ok m
  | LA.State (pos, i, _, _, _, _, _) as s :: ss ->
     check_and_add m pos empty_hs i s >>= fun m' -> mk_state_map m' ss        

let rec check_valid_transition_branch: LA.state IMap.t -> LA.transition_branch -> unit graph_result
  = fun m ->
  function
  | LA.Target (TransRestart (_, (pos, i)))
    | LA.Target (TransResume (_, (pos, i))) ->
     if (IMap.mem i m)
     then R.ok()
     else graph_error pos ("In Automaton Cannot find target transition branch " ^ HString.string_of_hstring i)
  | TransIf (_, _, b, b_opt) ->
     check_valid_transition_branch m b
     >> (match b_opt with
         | Some b -> check_valid_transition_branch m b
         | None -> R.ok ())

let check_valid_state_transition: LA.state IMap.t -> LA.state -> unit graph_result
  = fun m ->
  function
  | LA.State (_, _, _, _, _, trans_opt1, trans_opt2) ->
     (match trans_opt1 with
     | Some (_, branch) -> check_valid_transition_branch m branch
     | None -> R.ok ())
    >>  (match trans_opt2 with
     | Some (_, branch) -> check_valid_transition_branch m branch
     | None -> R.ok ())


let check_only_one_initial_state: LA.state list -> unit graph_result
  = fun ss ->
  let initial_states = List.filter (fun (LA.State(_, _, b, _, _, _, _)) -> b) ss in
  if List.length initial_states <= 1
  then R.ok ()
  else
    let pis = List.map (fun (LA.State (p, i, _, _, _, _, _)) -> (p, i)) ss in
    graph_error (fst (List.hd pis))
      ("Automaton cannot have more than one initial state but found states: "
      ^ (Lib.string_of_t ((Lib.pp_print_list LA.pp_print_ident) ", ") (List.map snd pis)))

let analyze_states: LA.state list -> unit graph_result
  = fun states -> 
  mk_state_map IMap.empty states >>= fun state_map ->
  R.seq_ (List.map (check_valid_state_transition state_map) states)
  >> check_only_one_initial_state states
(* Checks that the transition states are valid and there is atmost one initial state *)

let rec analyze_automaton_states: node_summary -> LA.state -> unit graph_result =
  fun m ->
  function
  | State (_, _, _, _, eqns, _, _) ->
     R.seq (List.map (mk_graph_eqn m) eqns) >>= fun gs -> 
     let ad = List.fold_left union_dependency_analysis_data empty_dependency_analysis_data gs in
     (try (R.ok (G.topological_sort ad.graph_data)) with
      | Graph.CyclicGraphException ids ->
        let ids = List.map HString.mk_hstring ids in
        if List.length ids > 1
        then (match (find_id_pos ad.id_pos_data (List.hd ids)) with
              | None -> fail_no_position ("Cyclic dependency found but cannot find position for identifier "
                                          ^ (HString.string_of_hstring (List.hd ids)) ^ " This should not happen!") 
              | Some p -> graph_error p
                            ("Cyclic dependency detected in equations with identifiers: "
                            ^ Lib.string_of_t (Lib.pp_print_list HString.pp_print_hstring ", ") ids))
        else fail_no_position "Cyclic dependency with no ids detected. This should not happen!")
     >> analyze_automatons m eqns 
     >> R.ok ()
  
and analyze_automatons: node_summary -> LA.node_equation list -> unit graph_result =
  fun m ->
  function
  | [] -> R.ok ()
  | LA.Automaton (_, _, states, _) :: items ->
     (R.seq_ (List.map (analyze_automaton_states m) states))
     >> analyze_states states
     >> analyze_automatons m items
  | _ :: items -> analyze_automatons m items
(** checks all the automatons in the node *)
                
let analyze_circ_node_equations: node_summary -> LA.node_item list -> unit graph_result =
  fun m eqns ->
  Debug.parse "Checking circularity in node equations"
  ; mk_graph_node_items m eqns >>= fun ad ->
    (try (R.ok (G.topological_sort ad.graph_data)) with
     | Graph.CyclicGraphException ids ->
        let ids = List.map HString.mk_hstring ids in
        if List.length ids > 1
        then (match (find_id_pos ad.id_pos_data (List.hd ids)) with
              | None -> graph_error Lib.dummy_pos
                          ("Cyclic dependency found but cannot find position for identifier "
                           ^ (HString.string_of_hstring (List.hd ids)) ^ " This should not happen!") 
              | Some p -> graph_error p
                            ("Cyclic dependency detected in equations with identifiers: "
                             ^ Lib.string_of_t (Lib.pp_print_list LA.pp_print_ident ", ") ids))
        else graph_error Lib.dummy_pos "Cyclic dependency with no ids detected. This should not happen!")
    >> R.ok ()
(** Check for node equations, we need to flatten the node calls using [node_summary] generated *)
    
let check_node_equations: dependency_analysis_data
                          -> LA.node_decl
                          -> LA.node_decl graph_result
  = fun ad ((i, imported, params, ips, ops, locals, items, contract_opt) as ndecl)->
  (if not imported then
     analyze_circ_node_equations ad.nsummary items
     >> analyze_automatons ad.nsummary (LH.extract_equation items) 
   else R.ok())
  >> match contract_opt with
     | None -> R.ok ndecl
     | Some c ->
        sort_and_check_contract_eqns ad (HString.concat (HString.mk_hstring "inline$") [contract_prefix;i], params, ips, ops, c) >>=
          fun (_, _, _, _, c') -> R.ok (i, imported, params, ips, ops, locals, items, Some c')
(** Check if node equations do not have circularity and also, if the node has a contract
    sort the contract equations. *)
    
let rec generate_summaries: dependency_analysis_data -> LA.t -> dependency_analysis_data
  = fun ad ->
  function
  | [] -> ad
  | LA.FuncDecl (_, ndecl) :: decls ->
     let ns = mk_node_summary ad.nsummary ndecl in
     generate_summaries {ad with nsummary = IMap.union (fun _ _ v2 -> Some v2) ad.nsummary ns} decls
  | LA.NodeDecl (_, ndecl) :: decls ->
     let ns = mk_node_summary ad.nsummary ndecl in
     generate_summaries {ad with nsummary = IMap.union (fun _ _ v2 -> Some v2) ad.nsummary ns} decls
  | LA.ContractNodeDecl (_, cdecl) :: decls ->
     let cs = mk_contract_summary ad.csummary cdecl in
     generate_summaries {ad with csummary = IMap.union (fun _ _ v2 -> Some v2) ad.csummary cs } decls
  | _ :: decls -> generate_summaries ad decls
(** This function generates the node summary and contract summary data
    This function requires that the program does not have any forward references. *)

let rec sort_and_check_equations: dependency_analysis_data -> LA.t -> LA.t graph_result = 
  fun ad ->
  function
  | LA.FuncDecl (span, ndecl) :: ds ->
    check_node_equations ad ndecl >>= fun ndecl' ->
    sort_and_check_equations ad ds >>= fun ds' ->
    R.ok (LA.FuncDecl (span, ndecl') :: ds')
  | LA.NodeDecl (span, ndecl) :: ds ->
    check_node_equations ad ndecl >>= fun ndecl' ->
    sort_and_check_equations ad ds >>= fun ds' ->
    R.ok (LA.NodeDecl (span, ndecl') :: ds')
  | LA.ContractNodeDecl (span, contract_body) :: ds ->
    sort_and_check_contract_eqns ad contract_body >>= fun contract_body' ->
    sort_and_check_equations ad ds >>= fun decls' ->
    R.ok (LA.ContractNodeDecl (span, contract_body') :: decls' )  
  | d :: ds -> sort_and_check_equations ad ds >>= fun ds' -> R.ok (d :: ds')
  | [] -> R.ok ([])
(** Sort equations for contracts and check if node and function equations have circular dependencies  *)

let sort_globals decls =
  sort_declarations decls >>= fun (sorted_decls, _) -> 
  Debug.parse "Sorting types and constants declarations done.
                   \n============\n%a\n============\n"
    LA.pp_print_program sorted_decls
  ; R.ok sorted_decls
(** Returns a topological order to resolve forward references 
    of global constants and type definitions. *)  

let sort_and_check_nodes_contracts decls =
  (* Step 1. Sort the declarations according in their dependency order
     This rules out the cases where we have recursive node or contract definitions *)
  sort_declarations decls >>= fun (sorted_decls, toplevel_nodes) -> 
  Debug.parse "Sorting functions, nodes and contracts done.
                   \n============\n%a\n============\n"
    LA.pp_print_program sorted_decls

  (* Step 2. Generate node and contract summaries *)
  ; let analysis_data = generate_summaries empty_dependency_analysis_data sorted_decls in
    Debug.parse "Generated contract and node summaries.
                     \n============\n%a\n============\n"
      pp_print_analysis_data analysis_data

    (* Step 3. Sort contract equations and check for node equation circularity *)
    ; sort_and_check_equations analysis_data sorted_decls >>= fun final_decls ->
      Debug.parse "Sorting equations done.
                       \n============\n%a\n============\n"
        LA.pp_print_program final_decls
        ; R.ok (final_decls, toplevel_nodes)
(** Returns a topological order of declarations to resolve all forward refernce. 
    It also reorders contract equations and checks for circularity of node equations *)  



    



    
