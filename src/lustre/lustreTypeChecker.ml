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
(** Type checking the surface syntax of Lustre programs
  
  @author Apoorv Ingle *)

(* TODO: Introduce GroupType which is like tuple type but has flattened cannonical structure*)

module R = Res

module LA = LustreAst
module SI = LA.SI
module LC = LustreContext
module LH = LustreAstHelpers
module GA = GraphAdapter
                        
(** Returns [Ok] if the type check/type inference runs fine 
 * or reports an error at position with the error *)
type 'a tc_result = ('a, Lib.position * string) result

let (>>=) = R.(>>=)
let (>>) = R.(>>)
          
(** Type alias for lustre type from LustreAst  *)
type tc_type  = LA.lustre_type
              
(** String of the type to display in type errors *)
let string_of_tc_type: tc_type -> string = fun t -> Lib.string_of_t LA.pp_print_lustre_type t
                                                  
(** Map for types with identifiers as keys *)
module IMap = Map.Make(struct
                  type t = LA.ident
                  let compare i1 i2 = Stdlib.compare i1 i2
                end)

let sort_typed_ident: LA.typed_ident list -> LA.typed_ident list = fun ty_idents ->
  List.sort (fun (_,i1,_) (_,i2,_) -> Stdlib.compare i1 i2) ty_idents

let sort_idents: LA.ident list -> LA.ident list = fun ids ->
  List.sort (fun i1 i2 -> Stdlib.compare i1 i2) ids

type ty_alias_store = tc_type IMap.t
(** A store of type Aliases, i.e. for user defined types  *)

type ty_store = tc_type IMap.t
(** A store of identifier and their types*)

type const_store = (LA.expr * tc_type) IMap.t 
(** A Store of constant identifier and their (const) values with types. 
 *  The values of the associated identifiers should be evaluated to a 
 *  Bool or an Int at constant propogation phase of type checking *)

type ty_set = SI.t
(** set of valid user type identifiers *)
            
(** Pretty print type synonyms*)
let pp_print_type_syn ppf = fun i ty -> 
  Format.fprintf ppf "(%a:=%a), " LA.pp_print_ident i LA.pp_print_lustre_type ty

(** Pretty print type bindings*)
let pp_print_type_binding ppf = fun i ty -> 
  Format.fprintf ppf "(%a:%a), " LA.pp_print_ident i LA.pp_print_lustre_type ty

(** Pretty print value bindings (used for constants)*)
let pp_print_val_binding ppf = fun i (v, ty) ->
  Format.fprintf ppf "(%a:%a :-> %a), " LA.pp_print_ident i LA.pp_print_lustre_type ty LA.pp_print_expr v

(** Pretty print type context *)
let pp_print_ty_syns ppf = IMap.iter (pp_print_type_syn ppf)   

(** Pretty print type context *)
let pp_print_tymap ppf = IMap.iter (pp_print_type_binding ppf)   

(** Pretty print value store *)
let pp_print_vstore ppf = IMap.iter (pp_print_val_binding ppf)

(** Pretty print declared types *)
let pp_print_u_types ppf = SI.iter (fun i -> LA.pp_print_ident ppf i)
                         
type tc_context = { ty_syns: ty_alias_store (* store of the type alias mappings *)
                  ; ty_ctx: ty_store        (* store of the types of identifiers *)
                  ; vl_ctx: const_store     (* store of typed constants to its value*)
                  ; u_types: ty_set         (* store of all declared user types,
                                               this is poor mans kind (type of type) context *)
                  }
(** Type Checker context *)

let empty_context: tc_context = { ty_syns = IMap.empty
                                ; ty_ctx = IMap.empty
                                ; vl_ctx = IMap.empty
                                ; u_types = SI.empty }
(** The empty context with no information *)
                              
let pp_print_tc_context ppf ctx
  = Format.fprintf ppf
      ("TypeSynonyms={%a}\n"
       ^^ "TypeContext={%a}\n"
       ^^ "ConstValueContext={%a}"
       ^^ "DeclaredTypes={%a}")
      pp_print_ty_syns (ctx.ty_syns)
      pp_print_tymap (ctx.ty_ctx)
      pp_print_vstore (ctx.vl_ctx)
      pp_print_u_types (ctx.u_types)
  
(** Pretty print the complete type checker context*)
  
(**********************************************
 * Helper functions for type checker workings *
 **********************************************)

(** [typeError] returns an [Error] of [tc_result] *)
let type_error pos err = R.error (pos, "Type error: " ^ err)

let member_ty_syn: tc_context -> LA.ident -> bool
  = fun ctx i -> IMap.mem i (ctx.ty_syns)
           
let member_ty: tc_context -> LA.ident -> bool
  = fun ctx i -> IMap.mem i (ctx.ty_ctx)

let member_u_types : tc_context -> LA.ident -> bool
  = fun ctx i -> SI.mem i ctx.u_types
  
let member_val: tc_context -> LA.ident -> bool
  = fun ctx i -> IMap.mem i (ctx.vl_ctx)

let lookup_ty_syn: tc_context -> LA.ident -> tc_type
  = fun ctx i -> IMap.find i (ctx.ty_syns)
(** picks out the type synonym from the context *)

let lookup_ty: tc_context -> LA.ident -> tc_type
  = fun ctx i -> let ty = IMap.find i (ctx.ty_ctx) in
                 match ty with
                 | LA.UserType (_, uid) ->
                    if (member_ty_syn ctx uid)
                    then (lookup_ty_syn ctx uid)
                    else ty
                 | _ ->  ty
(** Picks out the type from the variable to type context map *)

let lookup_const: tc_context -> LA.ident -> (LA.expr * tc_type)
  = fun ctx i -> IMap.find i (ctx.vl_ctx)

let add_ty_syn: tc_context -> LA.ident -> tc_type -> tc_context
  = fun ctx i ty -> {ctx with ty_syns = IMap.add i ty (ctx.ty_syns)}

let add_ty: tc_context -> LA.ident -> tc_type -> tc_context
  = fun ctx i ty -> {ctx with ty_ctx = IMap.add i ty (ctx.ty_ctx)}

let add_ty_decl: tc_context -> LA.ident -> tc_context
  = fun ctx i -> {ctx with u_types = SI.add i (ctx.u_types)}

let remove_ty: tc_context -> LA.ident -> tc_context
  = fun ctx i -> {ctx with ty_ctx= IMap.remove i (ctx.ty_ctx)}
                  
let add_const: tc_context -> LA.ident -> LA.expr -> tc_type -> tc_context
  = fun ctx i e ty -> {ctx with vl_ctx = IMap.add i (e, ty) ctx.vl_ctx} 

let union: tc_context -> tc_context -> tc_context
  = fun ctx1 ctx2 -> { ty_syns = (IMap.union (fun k v1 v2 -> Some v2) (ctx1.ty_syns) (ctx2.ty_syns))
                     ; ty_ctx = (IMap.union (fun k v1 v2 -> Some v2) (ctx1.ty_ctx) (ctx2.ty_ctx))
                     ; vl_ctx = (IMap.union (fun k v1 v2 -> Some v2) (ctx1.vl_ctx) (ctx2.vl_ctx))
                     ; u_types = SI.union ctx1.u_types ctx2.u_types 
                     }

let singleton_ty: LA.ident -> tc_type -> tc_context
  = fun i ty -> add_ty empty_context i ty

let singleton_const: LA.ident -> LA.expr -> tc_type -> tc_context =
  fun i e ty -> add_const empty_context i e ty

let extract_ip_ty: LA.const_clocked_typed_decl -> LA.ident * tc_type
  = fun  (_, i, ty, _, _) -> (i, ty)

let extract_op_ty: LA.clocked_typed_decl -> LA.ident * tc_type
  = fun (_, i, ty, _) -> (i, ty)

let is_const_arg: LA.const_clocked_typed_decl -> bool
  = fun (_, _, _, _, is_const) -> is_const

let extract_arg_ctx: LA.const_clocked_typed_decl -> tc_context
  = fun input -> let (i, ty) = extract_ip_ty input in
                 singleton_ty i ty

let extract_ret_ctx: LA.clocked_typed_decl -> tc_context
  = fun op -> let (i, ty) = extract_op_ty op in
              singleton_ty i ty

let extract_consts: LA.const_clocked_typed_decl -> tc_context
  = fun (pos, i, ty, _, is_const) ->
  if is_const
  then singleton_const i (LA.Ident (pos, i)) ty
  else empty_context 

let is_type_num: tc_type -> bool = function
    LA.Int _
  | LA.UInt8 _       
  | LA.UInt16 _   
  | LA.UInt32 _   
  | LA.UInt64 _  
  | LA.Int8 _   
  | LA.Int16 _    
  | LA.Int32 _    
  | LA.Int64 _    
  | LA.IntRange _
  | LA.Real _ -> true
  | _ -> false

let is_type_int: tc_type -> bool = function
    LA.Int _
  | LA.UInt8 _       
  | LA.UInt16 _   
  | LA.UInt32 _   
  | LA.UInt64 _  
  | LA.Int8 _   
  | LA.Int16 _    
  | LA.Int32 _    
  | LA.Int64 _    
  | LA.IntRange _ -> true
  | _ -> false

let is_type_unsigned_machine_int: tc_type -> bool = function
  | LA.UInt8 _       
  | LA.UInt16 _   
  | LA.UInt32 _   
  | LA.UInt64 _ -> true    
  | _ -> false  

let is_type_signed_machine_int: tc_type -> bool = function
  | LA.Int8 _       
  | LA.Int16 _   
  | LA.Int32 _   
  | LA.Int64 _ -> true    
  | _ -> false  
       
let is_type_machine_int: tc_type -> bool = fun ty ->
  is_type_signed_machine_int ty || is_type_unsigned_machine_int ty 

let is_machine_type_of_associated_width: (tc_type * tc_type) -> bool = function
  | LA.Int8 _, LA.UInt8 _       
  | LA.Int16 _,LA.UInt16 _   
  | LA.Int32 _, LA.UInt32 _   
  | LA.Int64 _, LA.UInt64 _
  | LA.UInt8 _, LA.UInt8 _       
  | LA.UInt16 _,LA.UInt16 _   
  | LA.UInt32 _, LA.UInt32 _   
  | LA.UInt64 _, LA.UInt64 _ -> true
  | _ -> false    

  
(**********************************************
 * Type inferring and type checking functions *
 **********************************************)

let infer_type_const: Lib.position -> LA.constant -> tc_type
  = fun pos -> function
  | Num _ -> Int pos
  | Dec _ -> Real pos
  | _ -> Bool pos
(** Infers type of constants *)
      
let rec infer_type_expr: tc_context -> LA.expr -> tc_type tc_result
  = fun ctx -> function
  (* Identifiers *)
  | LA.Ident (pos, i) ->
     (try R.ok (lookup_ty ctx i) with
      | Not_found -> type_error pos ("Unbound identifier: " ^ i)) 
  | LA.ModeRef (pos, is) ->      
     let lookup_mode_ty ctx i =
       (try R.ok (lookup_ty ctx i) with
        | Not_found -> type_error pos ("Unbound identifier: " ^ i)) in
     (R.seq (List.map (lookup_mode_ty ctx) is))
     >>= (fun tys ->
         if List.length tys = 1
         then R.ok (List.hd tys)
         else R.ok (LA.TupleType (pos, tys)))
  | LA.RecordProject (pos, expr, fld) ->
     (infer_type_expr ctx expr)
     >>= (fun rec_ty ->
      match rec_ty with
      | LA.RecordType (_, flds) ->
         let typed_fields = List.map (fun (_, i, ty) -> (i, ty)) flds in
         (match (List.assoc_opt fld typed_fields) with
          | Some ty -> R.ok ty
          | None -> type_error pos ("No field named " ^ fld ^ "found in record type")) 
      | _ -> type_error pos ("Cannot project field out of non record expression type "
                             ^ string_of_tc_type rec_ty))
  | LA.TupleProject (pos, e1, e2) -> Lib.todo __LOC__ 

  (* Values *)
  | LA.Const (pos, c) -> R.ok (infer_type_const pos c)

  (* Operator applications *)
  | LA.UnaryOp (pos, op, e) ->
      infer_type_unary_op ctx pos e op
  | LA.BinaryOp (pos, bop, e1, e2) ->
     infer_type_binary_op ctx pos bop e1 e2
  | LA.TernaryOp (pos, top, con, e1, e2) ->
     infer_type_expr ctx con
     >>= (function
          | Bool _ ->  (infer_type_expr ctx e1)
                       >>= (fun e1_ty ->
              check_type_expr ctx e1 e1_ty
              >> R.ok e1_ty)
          | c_ty  ->  type_error pos ("Expected a boolean expression but found "
                                      ^ string_of_tc_type c_ty))
  | LA.NArityOp _ -> Lib.todo __LOC__          (* One hot expression is not supported *)    
  | LA.ConvOp (pos, cop, e) ->
      infer_type_conv_op ctx pos e cop
  | LA.CompOp (pos, cop, e1, e2) ->
     infer_type_comp_op ctx pos e1 e2 cop

  (* Structured expressions *)
  | LA.RecordExpr (pos, _, flds) ->
     let infer_field: tc_context -> (LA.ident * LA.expr) -> (LA.typed_ident) tc_result
       = fun ctx (i, e) -> infer_type_expr ctx e
                           >>= fun ty -> R.ok (LH.pos_of_expr e, i, ty) 
     in R.seq (List.map (infer_field ctx) flds)
        >>=  (fun fld_tys -> R.ok (LA.RecordType (pos, fld_tys)))    
  | LA.GroupExpr (pos, struct_type, exprs)  ->
     (match struct_type with
      | LA.ExprList 
        | LA.TupleExpr ->
         R.seq (List.map (infer_type_expr ctx) exprs)
         >>= fun tys -> R.ok (LA.TupleType (pos, tys))
      | LA.ArrayExpr ->
         R.seq (List.map (infer_type_expr ctx) exprs)
         >>= (fun tys ->
          let elty = List.hd tys in
          R.ifM (R.seqM (&&) true (List.map (eq_lustre_type ctx elty) tys))
            (let arr_ty = List.hd tys in
                 let arr_size = LA.Const (pos, Num (string_of_int (List.length tys))) in
                 R.ok (LA.ArrayType (pos, (arr_ty, arr_size))))
            (type_error pos "All expressions must be of the same type in an Array")))
    
  (* Update structured expressions *)
  | LA.ArrayConstr (pos, b_expr, sup_expr) ->
     infer_type_expr ctx b_expr
     >>=  (fun b_ty ->
      infer_type_expr ctx sup_expr
      >>= (fun sup_ty ->
             if is_expr_int_type ctx sup_expr
             then R.ok (LA.ArrayType (pos, (b_ty, sup_expr)))
             else type_error pos "Array cannot have non numeral type as its bounds"))
  | LA.StructUpdate (pos, r, i_or_ls, e) ->
     if List.length i_or_ls != 1
     then type_error pos ("List of labels or indices for structure update is not supported") 
     else
       (match List.hd i_or_ls with
        | LA.Label (pos, l) ->  
           infer_type_expr ctx r
           >>= (function 
                | RecordType (_, flds) as r_ty ->
                   (let typed_fields = List.map (fun (_, i, ty) -> (i, ty)) flds in
                    (match (List.assoc_opt l typed_fields) with
                     | Some f_ty ->
                        infer_type_expr ctx e
                        >>= (fun e_ty -> 
                         R.ifM (eq_lustre_type ctx f_ty e_ty)
                           (R.ok r_ty)
                           (type_error pos ("Type mismatch. Type of record label " ^ l
                                              ^ " is of type "
                                              ^ string_of_tc_type f_ty
                                              ^ " but the type of the expression is "
                                              ^ string_of_tc_type e_ty)))
                     | None -> type_error pos ("No field named " ^ l ^ "found in record type")))
                | r_ty -> type_error pos ("Cannot do an update on non-record type "
                                          ^ string_of_tc_type r_ty))
        | _ -> type_error pos ("Only labels can be used for record expressions"
                               ^ " but found index "
                               ^ Lib.string_of_t LA.pp_print_label_or_index (List.hd i_or_ls)))  
  | LA.ArraySlice (pos, e1, (il, iu)) ->
     if is_expr_int_type ctx il && is_expr_int_type ctx iu
     then infer_type_expr ctx e1
          >>= (fun ty ->
              match ty with
              | ArrayType (_, (b_ty, s)) ->
                 R.ok (LA.ArrayType (pos, (b_ty, LH.abs_diff pos il iu)))
              | _ -> type_error pos ("Slicing can only be done on an type Array "
                                     ^ "but found type "
                                     ^ Lib.string_of_t LA.pp_print_lustre_type ty))
     else type_error pos ("Slicing should have integer types")
  | LA.ArrayIndex (pos, e, i) ->
     infer_type_expr ctx i >>= fun index_type ->
     if is_expr_int_type ctx i
     then infer_type_expr ctx e
          >>= (function
               | ArrayType (_, (b_ty, _)) -> R.ok b_ty
               | ty -> type_error pos ("Indexing can only be done on an type Array "
                                       ^ "but found type "
                                       ^ Lib.string_of_t LA.pp_print_lustre_type ty))
     else type_error pos ("Array index should have an integer type "
                          ^ " but found " ^ string_of_tc_type index_type)

  | LA.ArrayConcat (pos, arr1, arr2) ->
     infer_type_expr ctx arr1
     >>= (function
          | ArrayType (_, (b_ty1, size1)) as ty1 ->
             infer_type_expr ctx arr2
             >>= (function 
                  | ArrayType (_, (b_ty2, size2)) as ty2->
                     R.ifM (R.seqM (&&) true [eq_lustre_type ctx b_ty1 b_ty2
                                            ; R.ok(is_expr_int_type ctx size1)
                                            ; R.ok(is_expr_int_type ctx size2)] )
                       (R.ok (LA.ArrayType (pos, (b_ty1, LH.add_exp pos size1 size2))))
                       (type_error pos ("Cannot concat array of two different types "
                                        ^ string_of_tc_type ty1 ^ " and "
                                        ^ string_of_tc_type ty2 ))
                  | ty2 -> type_error pos ("Cannot concat non-array type "
                                           ^ string_of_tc_type ty2)) 
          | ty1  -> type_error pos ("Cannot concat non-array type "
                                    ^ string_of_tc_type ty1))

  (* Quantified expressions *)
  | LA.Quantifier (pos, _, qs, e) ->
     let extn_ctx = List.fold_left union ctx
                      (List.map (fun (_, i, ty) -> singleton_ty i ty) qs) in
     infer_type_expr extn_ctx e 

  (* Clock operators *)
  | LA.When (_, e, _) -> infer_type_expr ctx e
  | LA.Current (_, e) -> infer_type_expr ctx e
  | LA.Condact (pos, c, _, node, args, defaults) ->
     check_type_expr ctx c (Bool pos)
     >> infer_type_expr ctx (Call (pos, node, args))
     >>= fun r_ty ->
     R.seq (List.map (infer_type_expr ctx) defaults)
     >>= (fun d_tys -> 
       R.ifM (eq_lustre_type ctx r_ty (TupleType (pos, d_tys)))
         (R.ok r_ty)
         (type_error pos "Defaults do not have the same type as node call"))
  | LA.Activate (pos, node, cond, rcond, args) ->
     check_type_expr ctx cond (Bool pos)
     >> infer_type_expr ctx (Call (pos, node, args))
  | LA.Merge (pos, i, mcases) ->
     infer_type_expr ctx (LA.Ident (pos, i))
     >> let case_tys = List.map snd mcases |> List.map (infer_type_expr ctx) in
        R.seq case_tys
        >>= fun tys ->
        let main_ty = List.hd tys in
        R.ifM (R.seqM (&&) true (List.map (eq_lustre_type ctx main_ty) tys))
        (R.ok main_ty)
        (type_error pos ("All expressions in merge expected to be the same type "
                             ^ string_of_tc_type main_ty))
  | LA.RestartEvery (pos, node, args, cond) ->
     check_type_expr ctx cond (LA.Bool pos)
     >> infer_type_expr ctx (LA.Call (pos, node, args))
                                
  (* Temporal operators *)
  | LA.Pre (pos, e) -> infer_type_expr ctx e
  | LA.Last (pos, i) -> infer_type_expr ctx (LA.Ident (pos, i))
  | LA.Fby (pos, e1, _, e2) ->
     infer_type_expr ctx e1 >>= fun ty1 ->
      infer_type_expr ctx e2 >>= fun ty2 ->
      R.ifM (eq_lustre_type ctx ty1 ty2)
        (R.ok ty1)
        (type_error pos ("Both the expressions in `Fby` should be of the same type."
                         ^ "Found types " ^ string_of_tc_type ty1
                         ^ " and " ^ string_of_tc_type ty2))
  | LA.Arrow (pos, e1, e2) ->
     infer_type_expr ctx e1 >>= fun ty1 ->
     infer_type_expr ctx e2 >>= fun ty2 ->
     R.ifM (eq_lustre_type ctx ty1 ty2)
       (R.ok ty1)
       (type_error pos
          ("Arrow types do not match " ^ string_of_tc_type ty1
           ^ " and " ^ string_of_tc_type ty2)) 
     
  (* Node calls *)
  | LA.Call (pos, i, arg_exprs) ->
     Log.log L_trace "Inferring type for node call %a" LA.pp_print_ident i  
    ; let infer_type_node_args: tc_context -> LA.expr list -> tc_type tc_result
        = fun ctx args ->
        R.seq (List.map (infer_type_expr ctx) args)
        >>= (fun arg_tys ->
          if List.length arg_tys = 1 then R.ok (List.hd arg_tys)
          else R.ok (LA.TupleType (pos, arg_tys))) in
      (try (match (lookup_ty ctx i) with
            | TArr (_, exp_arg_tys, exp_ret_tys) ->
               infer_type_node_args ctx arg_exprs
               >>= (fun given_arg_tys ->
                R.ifM (eq_lustre_type ctx exp_arg_tys given_arg_tys)
                  (R.ok exp_ret_tys)                         
                  (type_error pos ("Node arguments expected to have type "
                                           ^ string_of_tc_type exp_arg_tys
                                           ^ " but found type "
                                           ^ string_of_tc_type given_arg_tys)))
            | ty -> type_error pos
                      ("Expected node type to be a function type, but found type"
                       ^ string_of_tc_type ty)) with
       | Not_found -> type_error pos ("No node with name: " ^ i ^ " found"))  
  | LA.CallParam _ -> Lib.todo __LOC__
(** Infer the type of a [LA.expr] with the types of free variables given in [tc_context] *)

and check_type_expr: tc_context -> LA.expr -> tc_type -> unit tc_result
  = fun ctx expr exp_ty ->
  match expr with
  (* Identifiers *)
  | Ident (pos, i) as ident ->
     infer_type_expr ctx ident >>= fun ty ->
     R.guard_with (eq_lustre_type ctx ty exp_ty)
       (type_error pos ("Identifier " ^ i
                        ^ " does not match expected type "
                        ^ string_of_tc_type exp_ty
                        ^ " with infered type "
                        ^ string_of_tc_type ty))
  | ModeRef (pos, ids) -> Lib.todo __LOC__
  | RecordProject (pos, expr, fld) -> check_type_record_proj pos ctx expr fld exp_ty
  | TupleProject (pos, e1, e2) -> Lib.todo __LOC__ 

  (* Operators *)
  | UnaryOp (pos, op, e) ->
     infer_type_unary_op ctx pos e op
     >>= fun inf_ty -> R.guard_with (eq_lustre_type ctx inf_ty exp_ty)
                     (type_error pos ("Cannot unify type "
                                      ^ string_of_tc_type exp_ty
                                      ^ " with inferred type "
                                      ^ string_of_tc_type inf_ty))
  | BinaryOp (pos, op, e1, e2) -> 
     infer_type_binary_op ctx pos op e1 e2 >>= fun inf_ty ->
     R.guard_with (eq_lustre_type ctx inf_ty exp_ty)
       (type_error pos (" Cannot unify type "
                        ^ string_of_tc_type exp_ty
                        ^ " with infered type " ^ string_of_tc_type inf_ty))
  | LA.TernaryOp (pos, op, con, e1, e2) ->
     infer_type_expr ctx con
     >>= (function 
          | Bool _ ->
             infer_type_expr ctx e1
             >>= fun ty1 -> infer_type_expr ctx e2
             >>= fun ty2 -> R.guard_with (eq_lustre_type ctx ty1 ty2)
                              (type_error pos
                                 ("Cannot unify type " ^ string_of_tc_type ty1
                                  ^ "with type " ^ string_of_tc_type ty2))
          | ty -> type_error pos ("ITE condition expression "
                                  ^ "Expected: " ^ string_of_tc_type (Bool pos)
                                  ^ "Found: " ^ string_of_tc_type ty))
  | NArityOp _ -> Lib.todo __LOC__ (* One hot expression is not supported down stream*)
  | ConvOp (pos, cvop, e) ->
     infer_type_conv_op ctx pos e cvop >>= fun inf_ty ->
     R.guard_with (eq_lustre_type ctx inf_ty exp_ty)
       (type_error pos ("Cannot unify expected type "
                        ^ string_of_tc_type exp_ty
                        ^ " with inferred type "
                        ^ string_of_tc_type inf_ty))
  | CompOp (pos, cop, e1, e2) ->
     infer_type_comp_op ctx pos e1 e2 cop >>= fun inf_ty ->
     R.guard_with (eq_lustre_type ctx inf_ty exp_ty)
       (type_error pos ("Cannot unify expected type "
                        ^ string_of_tc_type exp_ty
                        ^ " with type " ^ string_of_tc_type inf_ty))

  (* Values/Constants *)
  | Const (pos, c) ->
     let cty = infer_type_const pos c in
     R.guard_with (eq_lustre_type ctx cty exp_ty)
       (type_error pos ("Cannot match expected type "
                        ^ string_of_tc_type exp_ty ^
                          " with type "
                          ^ string_of_tc_type cty))

  (* Structured expressions *)
  | RecordExpr (pos, _, flds) ->
     let (ids, es) = List.split flds in
     let mk_ty_ident p i t = (p, i, t) in    
     R.seq (List.map (infer_type_expr ctx) es)
     >>= fun inf_tys ->
     let inf_r_ty = LA.RecordType (pos, (List.map2 (mk_ty_ident pos) ids inf_tys)) in
     R.guard_with (eq_lustre_type ctx exp_ty inf_r_ty)
       (type_error pos
          ("Cannot match expected type "
           ^ string_of_tc_type exp_ty
           ^ " with type "
           ^ string_of_tc_type inf_r_ty))
  | GroupExpr (pos, group_ty, es) ->
     (match group_ty with
      (* These should be tuple type  *)
      | ExprList
        | TupleExpr ->
         (match exp_ty with
          | TupleType (_, tys) ->
             if List.length tys != List.length es
             then type_error pos "Size of tuple does not match size of expression list"
             else R.seq_ (List.map2 (check_type_expr ctx) es tys)
          | _ -> type_error pos ("Expression list and Tuple list "
                                 ^ "should be of type Tuple but found "
                                 ^ string_of_tc_type exp_ty))
      (* This should be array type *)
      | ArrayExpr ->
         match exp_ty with
         | ArrayType (_, (b_ty, _)) ->
            R.seq_ (Lib.list_apply (List.map (check_type_expr ctx) es) b_ty)
         | _ -> type_error pos ("Array type expected but found "
                                ^ string_of_tc_type exp_ty))

  (* Update of structured expressions *)
  | StructUpdate (pos, r, i_or_ls, e) ->
     if List.length i_or_ls != 1
     then type_error pos ("List of labels or indices for structure update is not supported") 
     else (match List.hd  i_or_ls with
           | LA.Label (pos, l) ->  
              infer_type_expr ctx r
              >>= (fun r_ty ->
               match r_ty with
               | RecordType (_, flds) ->
                  (let typed_fields = List.map (fun (_, i, ty) -> (i, ty)) flds in
                   (match (List.assoc_opt l typed_fields) with
                    | Some ty -> check_type_expr ctx e ty 
                    | None -> type_error pos ("No field named " ^ l ^ "found in record type")))
               | _ -> type_error pos ("Cannot do an update on non-record type "
                                      ^ string_of_tc_type r_ty))
           | _ -> type_error pos ("Only a label can be used for record expressions"
                                  ^ " but found index "
                                  ^ Lib.string_of_t LA.pp_print_label_or_index (List.hd i_or_ls)))
  | ArrayConstr (pos, b_exp, sup_exp) ->
     infer_type_expr ctx b_exp
     >>= fun b_ty -> infer_type_expr ctx sup_exp
     >>= fun sup_ty ->
                     let arr_ty = (LA.ArrayType (pos, (b_ty, b_exp))) in
                     R.guard_with (eq_lustre_type ctx exp_ty arr_ty)
                       (type_error pos ("Expecting array type "
                                        ^ string_of_tc_type exp_ty
                                        ^ " but found "
                                        ^ string_of_tc_type arr_ty))
  | ArrayIndex (pos, e, idx) ->
     infer_type_expr ctx idx >>= fun index_type -> 
     if is_expr_int_type ctx idx
     then check_type_expr ctx e (ArrayType (pos, (exp_ty, (LA.Const (pos, Num "42")))))
                          (* TODO: can also be a constant arithmetic expression *)
     else type_error pos ("Array index should have an integer type "
                          ^ " but found " ^ string_of_tc_type index_type)
  | ArraySlice _ -> Lib.todo __LOC__
  | ArrayConcat _ -> Lib.todo __LOC__

  (* Quantified expressions *)
  | Quantifier (pos, _, qs, e) ->
     let extn_ctx = List.fold_left union ctx
                      (List.map (fun (_, i, ty) -> singleton_ty i ty) qs) in
     check_type_expr extn_ctx e exp_ty

  (* Clock operators *)
  | When (_, e, _) -> check_type_expr ctx e exp_ty
  | Current (_, e) -> check_type_expr ctx e exp_ty
  | Condact (pos, c, _, node, args, defaults) ->
     check_type_expr ctx c (Bool pos)
     >> check_type_expr ctx (Call (pos, node, args)) exp_ty
     >>  R.seq (List.map (infer_type_expr ctx) defaults)
     >>= fun d_tys -> R.guard_with (eq_lustre_type ctx exp_ty (TupleType (pos, d_tys)))
                        (type_error pos "Condact defaults do not have the same type as node call")
  | Activate (pos, node, cond, rcond, args) -> 
     check_type_expr ctx cond (Bool pos)
     >> check_type_expr ctx (Call (pos, node, args)) exp_ty 
  | Merge (pos, i, mcases) ->
     infer_type_expr ctx (LA.Ident (pos, i))
     >> R.seq_ (List.map (fun e -> check_type_expr ctx e exp_ty)
                  (List.map snd mcases))
  | RestartEvery (pos, node, args, cond) ->
     check_type_expr ctx cond (LA.Bool pos)
     >> check_type_expr ctx (LA.Call (pos, node, args)) exp_ty

  (* Temporal operators *)
  | Pre (pos, e) -> check_type_expr ctx e exp_ty
  | Last (pos, i) ->
     infer_type_expr ctx (LA.Ident (pos, i))
     >>= fun ty -> R.guard_with (eq_lustre_type ctx ty exp_ty)
                     (type_error pos ("Indentifier " ^ i
                                      ^ " does not match expected type "
                                      ^ string_of_tc_type exp_ty
                                      ^ " with infered type "
                                      ^ string_of_tc_type ty))
  | Fby (pos, e1, _, e2) ->
     check_type_expr ctx e1 exp_ty
     >> check_type_expr ctx e2 exp_ty
  | Arrow (pos, e1, e2) ->
     infer_type_expr ctx e1
     >>= fun ty1 ->  check_type_expr ctx e2 ty1

  (* Node calls *)
  | Call (pos, i, args) ->
     R.seq (List.map (infer_type_expr ctx) args)
     >>= fun arg_tys ->
     let arg_ty = if List.length arg_tys = 1 then List.hd arg_tys
                  else TupleType (pos, arg_tys) in 
     check_type_expr ctx (LA.Ident (pos, i)) (TArr (pos, arg_ty, exp_ty))
  | CallParam _ -> Lib.todo __LOC__
(** Type checks an expression and returns [ok] 
 * if the expected type is the given type [tc_type]  
 * returns an [Error of string] otherwise *)

and infer_type_unary_op: tc_context -> Lib.position -> LA.expr -> LA.unary_operator -> tc_type tc_result
  = fun ctx pos e op ->
  infer_type_expr ctx e >>= fun ty -> 
  match op with
  | LA.Not ->
     R.ifM (eq_lustre_type ctx ty (Bool pos))
       (R.ok (LA.Bool pos))
       (type_error pos ("Expected argument of type bool "
                        ^ "but found type " ^ string_of_tc_type ty))
  | LA.BVNot ->
     if is_type_machine_int ty
     then R.ok ty
     else type_error pos ("Cannot apply the bit-value not operator "
                          ^ "to a non machine integer value of type "
                          ^ string_of_tc_type ty)
  | LA.Uminus ->
     if (is_type_num ty)
     then R.ok ty
     else type_error pos ("Unary minus cannot be applied" 
                          ^ "to non number expression of type "
                          ^ string_of_tc_type ty)
(** Infers type of unary operator application *)

and are_args_num: tc_context -> Lib.position -> tc_type -> tc_type -> bool tc_result
  = fun ctx pos ty1 ty2 ->
  let num_tys = [
      LA.Int pos
    ; LA.UInt8 pos     
    ; LA.UInt16 pos  
    ; LA.UInt32 pos
    ; LA.UInt64 pos
    ; LA.Int8 pos
    ; LA.Int16 pos
    ; LA.Int32 pos
    ; LA.Int64 pos
    ; LA.IntRange (pos, Const (pos, Num "1"), Const (pos, Num "1")) 
    ; LA.Real pos] in
  let are_equal_types: tc_context -> tc_type -> tc_type -> tc_type -> bool tc_result
    = fun ctx ty1 ty2 ty ->
    R.seqM (&&) true [ eq_lustre_type ctx ty1 ty
                     ; eq_lustre_type ctx ty2 ty ] in
  R.seqM (||) false (List.map (are_equal_types ctx ty1 ty2) num_tys) 
(** This is an ugly fix till we have polymorphic unification, may be qualified types? *)
  
and infer_type_binary_op: tc_context -> Lib.position
                          -> LA.binary_operator -> LA.expr -> LA.expr
                          -> tc_type tc_result
  = fun ctx pos op e1 e2 ->
  infer_type_expr ctx e1 >>= fun ty1 ->
  infer_type_expr ctx e2 >>= fun ty2 ->
  match op with
  | LA.And | LA.Or | LA.Xor | LA.Impl ->
     R.ifM (eq_lustre_type ctx ty1 (Bool pos))
       (R.ifM (eq_lustre_type ctx ty2 (Bool pos))
          (R.ok (LA.Bool pos))
          (type_error pos ("Expected second argument of operator to" 
                           ^ " be of type bool but found type"
                           ^ string_of_tc_type ty2)))
       (type_error pos ("Expected first argument of operator to" 
                           ^ " be of type bool but found type"
                           ^ string_of_tc_type ty1))
  | LA.Mod ->
     R.ifM (eq_lustre_type ctx ty1 (Int pos))
       (R.ifM (eq_lustre_type ctx ty2 (Int pos))
          (R.ok (LA.Int pos))
          (type_error pos ("Expected second argument of operator to" 
                           ^ " be of type int but found type"
                           ^ string_of_tc_type ty2)))
       (type_error pos ("Expected first argument of operator to" 
                           ^ " be of type int but found type"
                           ^ string_of_tc_type ty1))
  | LA. Minus | LA.Plus | LA.Times -> 
     are_args_num ctx pos ty1 ty2 >>= fun is_num ->
     if is_num
     then R.ok ty2
     else type_error pos ("Expected arguments to be of same"
                          ^" numeric type but found types " ^ string_of_tc_type ty1
                          ^ " and " ^ string_of_tc_type ty2)
  | LA.Div ->
     are_args_num ctx pos ty1 ty2 >>= fun is_num ->
     if is_num
     then if (is_expr_term_zero e2)
          then type_error pos ("Cannot divide by zero")
          else R.ok ty2
     else type_error pos ("Expected arguments to be of same"
                          ^" numeric type but found types " ^ string_of_tc_type ty1
                          ^ " and " ^ string_of_tc_type ty2)
  | LA.IntDiv ->
     if is_type_int ty1 && is_type_int ty2
     then if (is_expr_term_zero e2)
          then type_error pos ("Cannot divide by zero")
          else R.ok (LA.Int pos)
     else type_error pos ("Expected arguments of type integer "
                          ^ "but found types " ^ string_of_tc_type ty1
                          ^ " and " ^ string_of_tc_type ty2)
  | LA.BVAnd | LA.BVOr ->
     R.ifM (eq_lustre_type ctx ty1 ty2)
       (if is_type_machine_int ty1 && is_type_machine_int ty2
        then R.ok ty2
        else type_error pos ("Expected arguments of type machine integer but "
                             ^ "found types " ^ string_of_tc_type ty1
                             ^ " and " ^ string_of_tc_type ty2))
       (type_error pos ("Both sides of the operator should be"
                        ^ " of the same type but found type "
                        ^ string_of_tc_type ty1
                        ^ " and " ^ string_of_tc_type ty2))
  | LA.BVShiftL | LA.BVShiftR ->
     if (is_type_signed_machine_int ty1 || is_type_unsigned_machine_int ty1)
     then (if (is_type_unsigned_machine_int ty2
               && is_machine_type_of_associated_width (ty1, ty2))
           then if is_expr_of_consts ctx e2
                then R.ok ty1
                else type_error pos "Expected second argument of shift operator to be a constant"
           else type_error pos ("Expected second argument of shift operator to be a constant "
                                ^ "of type unsigned machine integer of the same width as first argument "
                                ^ "but found type " ^ string_of_tc_type ty1))
     else type_error pos ("Expected first argument of shift operator to be "
                          ^ "of type signed or unsigned machine integer "
                          ^ "but found type " ^ string_of_tc_type ty1 ) 
(** infers the type of binary operators  *)

and infer_type_conv_op: tc_context -> Lib.position
                        ->  LA.expr -> LA.conversion_operator
                        -> tc_type tc_result
  = fun ctx pos e op ->
  infer_type_expr ctx e >>= fun ty ->
  match op with
  | ToInt ->
     if is_type_num ty
     then R.ok (LA.Int pos)
     else type_error pos ("Cannot convert a non-number type "
                          ^ string_of_tc_type ty
                          ^ " to type "
                          ^ string_of_tc_type (Int pos))
  | ToReal ->
     if is_type_num ty
     then R.ok (LA.Real pos)
     else type_error pos ("Cannot convert a non-number type "
                          ^ string_of_tc_type ty
                          ^ " to type "
                          ^ string_of_tc_type (Real pos))
  | ToInt8 ->
     if is_type_num ty
     then R.ok (LA.Int8 pos)
     else type_error pos ("Cannot convert a non-number type "
                                  ^ string_of_tc_type ty
                                  ^ " to type "
                                  ^ string_of_tc_type (Int8 pos))
  | ToInt16 ->
     if is_type_num ty
     then R.ok (LA.Int16 pos)
     else type_error pos ("Cannot convert a non-number type "
                          ^ string_of_tc_type ty
                          ^ " to type "
                          ^ string_of_tc_type (Int16 pos))
  | ToInt32 ->
     if is_type_num ty
     then R.ok (LA.Int32 pos)
     else type_error pos ("Cannot convert a non-number type "
                          ^ string_of_tc_type ty
                          ^ " to type "
                          ^ string_of_tc_type (Int32 pos))
  | ToInt64 ->
     if is_type_num ty
     then R.ok (LA.Int64 pos)
     else type_error pos ("Cannot convert a non-number type "
                          ^ string_of_tc_type ty
                          ^ " to type "
                          ^ string_of_tc_type (Int64 pos))
  | ToUInt8 ->
     if is_type_num ty
     then R.ok (LA.UInt8 pos)
     else type_error pos ("Cannot convert a non-number type "
                          ^ string_of_tc_type ty
                          ^ " to type "
                          ^ string_of_tc_type (UInt8 pos))
  | ToUInt16 ->
     if is_type_num ty
     then R.ok (LA.UInt16 pos)
     else type_error pos ("Cannot convert a non-number type "
                          ^ string_of_tc_type ty
                          ^ " to type "
                          ^ string_of_tc_type (UInt16 pos))
  | ToUInt32 ->
     if is_type_num ty
     then R.ok (LA.UInt32 pos)
     else type_error pos ("Cannot convert a non-number type "
                          ^ string_of_tc_type ty
                          ^ " to type "
                          ^ string_of_tc_type (UInt32 pos))
  | ToUInt64 ->
     if is_type_num ty
     then R.ok (LA.UInt64 pos)
     else type_error pos ("Cannot convert a non-number type "
                          ^ string_of_tc_type ty
                          ^ " to type "
                          ^ string_of_tc_type (UInt64 pos))
(** Converts from given type to the intended type aka casting *)
    
and infer_type_comp_op: tc_context -> Lib.position -> LA.expr -> LA.expr
                        -> LA.comparison_operator -> tc_type tc_result
  = fun ctx pos e1 e2 op ->
  infer_type_expr ctx e1 >>= fun ty1 ->
  infer_type_expr ctx e2 >>= fun ty2 ->
  match op with
  | Neq  | Eq ->
     R.ifM (eq_lustre_type ctx ty1 ty2)
       (R.ok (LA.Bool pos))
       (type_error pos ("Both sides of the expression expected to be"
                        ^ " isomorphic types but found " ^ string_of_tc_type ty1
                        ^ " and " ^ string_of_tc_type ty2))
  | Lte  | Lt  | Gte | Gt ->
     are_args_num ctx pos ty1 ty2
     >>= fun is_num ->
     if is_num
     then R.ok (LA.Bool pos)
     else type_error pos ("Both sides of the expression should be of"
                          ^ " type same numeral type but found " ^ string_of_tc_type ty1
                          ^ " and " ^ string_of_tc_type ty2)
(** infer the type of comparison operator application *)
                  
and check_type_record_proj: Lib.position -> tc_context -> LA.expr -> LA.index -> tc_type -> unit tc_result =
  fun pos ctx expr idx exp_ty -> 
  infer_type_expr ctx expr
  >>= function
  | RecordType (_, flds) as rec_ty ->
     (try R.ok (List.find (fun (_, i, _) -> i = idx) flds) with
      | Not_found -> type_error pos ("Cannot project field " ^ idx
                                     ^ " from given record type "
                                     ^ string_of_tc_type rec_ty))
     >>= fun (_, _, fty) ->
     R.guard_with (eq_lustre_type ctx fty exp_ty)
       (type_error pos ("Cannot match expected type "
                        ^ string_of_tc_type exp_ty
                        ^ " with infered type "
                        ^ string_of_tc_type fty))
  | rec_ty -> type_error pos ("Cannot project field " ^ idx
                              ^ " from a non record type "
                              ^ string_of_tc_type rec_ty)       

and check_type_const_decl: tc_context -> LA.const_decl -> tc_type -> unit tc_result =
  fun ctx const_decl exp_ty ->
  match const_decl with
  | FreeConst (pos, i, _) ->
     let inf_ty = (lookup_ty ctx i) in
     R.guard_with (eq_lustre_type ctx inf_ty exp_ty)
       (type_error pos
              ("Identifier constant " ^ i
               ^ " expected to have type " ^ string_of_tc_type inf_ty
               ^ " but found type " ^ string_of_tc_type exp_ty))
  | UntypedConst (pos, i, e) ->
     infer_type_expr ctx e
     >>= fun inf_ty ->
     R.guard_with (eq_lustre_type ctx inf_ty exp_ty)
       (type_error pos
          ("Identifier constant " ^ i
           ^ " expected to have type " ^ string_of_tc_type exp_ty
           ^ " but found type " ^ string_of_tc_type inf_ty))
  | TypedConst (pos, i, exp, _) ->
     infer_type_expr ctx exp
     >>= fun inf_ty -> R.guard_with (eq_lustre_type ctx inf_ty exp_ty)
                         (type_error pos
                            ("Identifier constant " ^ i
                             ^ " expects type " ^ string_of_tc_type exp_ty
                             ^ " but expression is of type " ^ string_of_tc_type inf_ty))

and check_type_node_decl: tc_context -> LA.node_decl -> tc_type -> unit tc_result
  = fun ctx
        (node_name, is_extern, params, input_vars, output_vars, ldecls, items, contract)
        exp_ty ->
  let local_var_binding: tc_context -> LA.node_local_decl -> tc_context tc_result = fun ctx ->
    function
    | LA.NodeConstDecl (pos, const_decls) ->
       Log.log L_trace "Extracting typing context from const declaration: %a"
         LA.pp_print_const_decl const_decls
      ; tc_ctx_const_decl ctx const_decls 
    | LA.NodeVarDecl (pos, (_, v, ty, _)) ->
       check_type_well_formed ctx ty
       >> R.ok (add_ty ctx v ty)
  in
  Log.log L_trace "TC declaration node: %a {" LA.pp_print_ident node_name
  (* if the node is extern, we will not have any body to typecheck *)
  ; if is_extern
    then R.ok ( Log.log L_trace "External Node, no body to type check."
              ; Log.log L_trace "TC declaration node %a done }" LA.pp_print_ident node_name)
    else (
      Log.log L_trace "Params: %a (skipping)" LA.pp_print_node_param_list params
    ; (* store the input constants passed in the input 
         also remove the node name from the context as we should not have recursive
         nodes *)
      let ip_constants_ctx = List.fold_left union (remove_ty ctx node_name)
                               (List.map extract_consts input_vars) in
      (* These are inputs to the node *)
      let ctx_plus_ips = List.fold_left union ip_constants_ctx
                           (List.map extract_arg_ctx input_vars) in
      (* These are outputs of the node *)
      let ctx_plus_ops_and_ips = List.fold_left union ctx_plus_ips
                                   (List.map extract_ret_ctx output_vars) in
      (* Type check the contract *)
      (match contract with
             | None -> R.ok ()
             | Some c ->
                tc_ctx_of_contract ctx_plus_ops_and_ips c
                >>= fun con_ctx -> check_type_contract con_ctx c)
      (* add local variable binding in the context *)
      >> R.seq (List.map (local_var_binding ctx_plus_ips) ldecls)
      >>= fun local_var_ctxts ->
      (* Local TC context is input vars + output vars + local const + var decls *)
      let local_ctx = List.fold_left union ctx_plus_ops_and_ips local_var_ctxts in
      Log.log L_trace "Local Typing Context {%a}" pp_print_tc_context local_ctx
      (* Type check the node items now that we have all the local typing context *)
      ; R.seq_ (List.map (do_item local_ctx) items)
        >> R.ok (Log.log L_trace "TC declaration node %a done }"
                   LA.pp_print_ident node_name))

and do_node_eqn: tc_context -> LA.node_equation -> unit tc_result = fun ctx ->
  function
  | LA.Assert (pos, e) ->
     Log.log L_trace "Checking assertion: %a" LA.pp_print_expr e
    ; check_type_expr ctx e (Bool pos)
  | LA.Equation (_, lhs, expr)  as eqn ->
     Log.log L_trace "Checking equation: %a" LA.pp_print_node_body eqn
    (* This is a special case where we have undeclared identifiers 
       as short hands for assigning values to arrays aka recursive technique *)
     ; let get_array_def_context: LA.struct_item -> tc_context = 
        function
        | ArrayDef (pos, _, is) ->
           List.fold_left (fun c i -> add_ty c i (LA.Int pos)) empty_context is 
        | _ -> empty_context in
      let ctx_from_lhs: tc_context -> LA.eq_lhs -> tc_context
        = fun ctx (LA.StructDef (_, items)) ->
        List.fold_left union ctx (List.map get_array_def_context items) in
      let new_ctx = ctx_from_lhs ctx lhs in
      Log.log L_trace "checking node equation lhs"
      ; infer_type_expr new_ctx expr >>= fun ty ->
      Log.log L_trace "LHS has type %a" LA.pp_print_lustre_type ty
      ; check_type_struct_def (ctx_from_lhs ctx lhs) lhs ty
  | LA.Automaton (pos, _, _, _) ->
    R.ok (Log.log L_trace "Skipping Automation")

and do_item: tc_context -> LA.node_item -> unit tc_result = fun ctx ->
  function
  | LA.Body eqn -> do_node_eqn ctx eqn
  | LA.AnnotMain _ as ann ->
     Log.log L_trace "Node Item Skipped (Main Annotation): %a" LA.pp_print_node_item ann
    ; R.ok ()
  | LA.AnnotProperty (_, _, e) as ann ->
     Log.log L_trace "Checking Node Item (Annotation Property): %a (%a)"
       LA.pp_print_node_item ann LA.pp_print_expr e
    ; check_type_expr ctx e (Bool (LH.pos_of_expr e))
  
and check_type_struct_item: tc_context -> LA.struct_item -> tc_type -> unit tc_result
  = fun ctx st exp_ty ->
  match st with
  | SingleIdent (pos, i) ->
     let inf_ty = lookup_ty ctx i in
     R.ifM (R.seqM (||) false [ eq_lustre_type ctx exp_ty inf_ty
                              ; eq_lustre_type ctx exp_ty (TupleType (pos,[inf_ty])) ])
       (if member_val ctx i
        then type_error pos ( "Constant " ^ i ^ " cannot be re-defined")
        else R.ok ())
       (type_error pos ("Expected type " ^ string_of_tc_type exp_ty
                        ^ " for expression " ^ i
                        ^ " but found type " ^ string_of_tc_type inf_ty))
  | ArrayDef (pos, base_e, idxs) ->
     let array_idx_expr =
       List.fold_left (fun e i -> LA.ArrayIndex (pos, e, i))
         (LA.Ident (pos, base_e))
         (List.map (fun i -> LA.Ident (pos, i)) idxs) in
     check_type_expr ctx array_idx_expr exp_ty
  | TupleStructItem _ -> Lib.todo __LOC__
  | TupleSelection _ -> Lib.todo __LOC__
  | FieldSelection _ -> Lib.todo __LOC__
  | ArraySliceStructItem _ -> Lib.todo __LOC__

and check_type_struct_def: tc_context -> LA.eq_lhs -> tc_type -> unit tc_result
  = fun ctx (StructDef (pos, lhss)) exp_ty ->
  (* This is a structured type, and we would want the expected type exp_ty to be a tuple type *)
  (Log.log L_trace "Checking if structure definition: %a has type %a \nwith local context %a"
     (Lib.pp_print_list LA.pp_print_struct_item ",") lhss
     LA.pp_print_lustre_type exp_ty
     pp_print_tc_context ctx
  
  (** check if the members of LHS are constants or enums before assignment *)
  ; let lhs_vars = SI.flatten (List.map LH.vars_of_struct_item lhss) in
   if (SI.for_all (fun i -> not (member_val ctx i)) lhs_vars)
    then (match exp_ty with
          | TupleType (_, exp_ty_lst) ->
             Log.log L_trace "Tuple Type: %a" LA.pp_print_lustre_type exp_ty
            ; if List.length lhss = List.length exp_ty_lst
              then R.seq_ (List.map2 (check_type_struct_item ctx) lhss exp_ty_lst)
              else type_error pos ("Term structure on left hand side of the equation"
                                   ^ " does not match expected type "
                                   ^ Lib.string_of_t LA.pp_print_lustre_type exp_ty 
                                   ^ " on right hand side of the node equation")
          (* We are dealing with simple types, so lhs has to be a singleton list *)
          | _ -> Log.log L_trace "Simple Type: %a" LA.pp_print_lustre_type exp_ty
               ; if (List.length lhss != 1)
                 then type_error pos ("Term structure on left hand side of the equation"
                                      ^ " does not match expected type structure "
                                      ^ Lib.string_of_t LA.pp_print_lustre_type exp_ty 
                                      ^ " on right hand side of the node equation")
                 else let lhs = List.hd lhss in
                      check_type_struct_item ctx lhs exp_ty)
  else type_error pos "Cannot reassign value to a constant or enum.")
(** The structure of the left hand side of the equation 
 * should match the type of the right hand side expression *)

and tc_ctx_contract_eqn: tc_context -> LA.contract_node_equation -> tc_context tc_result
  = fun ctx -> function
  | GhostConst c -> tc_ctx_const_decl ctx c 
  | GhostVar c -> tc_ctx_const_decl ~const_real:false ctx c
  | Assume (pos, _, _, e) -> R.ok ctx
  | Guarantee _ -> R.ok ctx
  | Mode (pos, name, _, _) -> R.ok (add_ty ctx name (Bool pos)) 
  | ContractCall _ -> R.ok ctx
  
and check_type_contract_decl: tc_context -> LA.contract_node_decl -> unit tc_result
  = fun ctx (cname, params, args, rets, contract) ->
  Log.log L_trace "TC Contract decl: %a {" LA.pp_print_ident cname 
  (* build the appropriate local context *)
  ; let arg_ctx = List.fold_left union ctx (List.map extract_arg_ctx args) in
  let ret_ctx = List.fold_left union arg_ctx (List.map extract_ret_ctx rets) in
  let local_const_ctx = List.fold_left union ret_ctx (List.map extract_consts args) in
  (* get the local const var declarations into the context *)
  R.seq (List.map (tc_ctx_contract_eqn local_const_ctx) contract)
  >>= fun ctxs ->
  let local_ctx = List.fold_left union local_const_ctx ctxs in
  check_type_contract local_ctx contract
  >> R.ok (Log.log L_trace "TC Contract Decl %a done }" LA.pp_print_ident cname)

and check_type_contract: tc_context -> LA.contract -> unit tc_result
  = fun ctx eqns ->
  R.seq_ (List.map (check_contract_node_eqn ctx) eqns)

and check_contract_node_eqn: tc_context -> LA.contract_node_equation -> unit tc_result
  = fun ctx eqn ->
  Log.log L_trace "checking contract equation: %a" LA.pp_print_contract_item eqn 
  ; match eqn with
  | GhostConst _
  | GhostVar _ ->  R.ok () (* These is already checked while extracting ctx *)
  | Assume (pos, _, _, e) -> check_type_expr ctx e (Bool pos)
  | Guarantee (pos, _, _, e) -> check_type_expr ctx e (Bool pos)
  | Mode (pos, _, reqs, ensures) ->
     R.seq_ (Lib.list_apply (List.map (check_type_expr ctx)
                               (List.map (fun (_,_, e) -> e) (reqs @ ensures)))
               (Bool pos)) 
  | ContractCall (pos, cname, args, rets) ->
     R.seq(List.map (infer_type_expr ctx) rets)
     >>= fun ret_tys ->  
     let ret_ty = if List.length ret_tys = 1
                  then List.hd ret_tys
                  else LA.TupleType (pos, ret_tys) in
     check_type_expr ctx (LA.Call (pos, cname, args))(ret_ty) 

and tc_ctx_const_decl
  = fun ?const_real:(const_real=true) ctx ->
  function
  | LA.FreeConst (pos, i, ty) ->
     check_type_well_formed ctx ty
     >> if member_ty ctx i
        then type_error pos ("Constant " ^ i ^ " is already declared.")
        else R.ok (add_ty (add_const ctx i (LA.Ident (pos, i)) ty) i ty)
  | LA.UntypedConst (pos, i, e) ->
     if member_ty ctx i
     then type_error pos ("Constant " ^ i ^ " is already declared.")
     else infer_type_expr ctx e >>= fun ty ->
          (if const_real then
          check_expr_of_consts ctx e 
          else R.ok ()) >>
                 R.ok (add_ty (add_const ctx i e ty) i ty)
  | LA.TypedConst (pos, i, e, exp_ty) ->
     if member_ty ctx i
     then type_error pos ("Constant " ^ i ^ " is already declared.")
     else check_type_expr (add_ty ctx i exp_ty) e exp_ty
          >> (if const_real then
               check_expr_of_consts ctx e 
             else R.ok ())
                  >> R.ok (add_ty (add_const ctx i e exp_ty) i exp_ty)
(** Fail if a duplicate constant is detected  *)

     
and tc_ctx_of_ty_decl: tc_context -> LA.type_decl -> tc_context tc_result
  = fun ctx ->
  function
  | LA.AliasType (pos, i, ty) ->
     check_type_well_formed ctx ty
       >> (match ty with
      | LA.EnumType (pos, n, econsts) ->
         (match n with
          | None ->
             type_error pos "Necessary Enum name not found"
          | Some ename ->
             if (List.for_all (fun e -> not (member_ty ctx e)) econsts)
                && (List.for_all (fun e -> not (member_val ctx e)) econsts)
             then
               let mk_ident = fun i -> LA.Ident (pos, i) in
               let enum_type_bindings = List.map ((Lib.flip singleton_ty) 
                                                    (LA.UserType (pos, ename)))
                                          econsts in
               let enum_const_bindings = Lib.list_apply ((List.map2 (Lib.flip singleton_const)
                                                            (List.map mk_ident econsts) econsts))
                                           (LA.UserType (pos, ename)) in
               (* Adding enums into the typing context consists of 3 parts *)
               (* 1. add the enum type as a valid type in context*)
               R.ok ( List.fold_left union (add_ty_decl ctx ename)
               (* 2. Lift all enum constants (terms) with associated user type of enum name *)
                        (enum_type_bindings
               (* 3. Lift all the enum constants (terms) into the value store as constants *)
                         @ enum_const_bindings))
             else
               type_error pos "Cannot redeclare constants or enums")
      | _ -> check_type_well_formed ctx ty
             >> R.ok (add_ty_syn ctx i ty))
  | LA.FreeType (_, i) -> R.ok (add_ty_decl ctx i)

and tc_ctx_of_node_decl: Lib.position -> tc_context -> LA.node_decl -> tc_context tc_result
  = fun pos ctx (nname, _, _ , ip, op,_ ,_ ,_) ->
  Log.log L_trace
    "Extracting typing context from node declaration: %a"
    LA.pp_print_ident nname
  ; if (member_ty ctx nname)
    then type_error pos ("Node " ^ nname ^ " is already declared.")
    else build_node_fun_ty pos ctx ip op
         >>= fun fun_ty -> R.ok (add_ty ctx nname fun_ty)
(** computes the type signature of node or a function *)

and tc_ctx_contract_node_eqn: tc_context -> LA.contract_node_equation -> tc_context tc_result
  = fun ctx ->
  function
  | LA.GhostConst c -> tc_ctx_const_decl ctx c
  | LA.GhostVar c -> tc_ctx_const_decl ~const_real:false ctx c
  | LA.Mode (pos, mname, _, _) ->
     if (member_ty ctx mname)
     then type_error pos ("Mode " ^ mname ^ " is already declared")
     else R.ok (add_ty ctx mname (Bool pos)) 
  | _ -> R.ok ctx
                         
and tc_ctx_of_contract: tc_context -> LA.contract -> tc_context tc_result
  = fun ctx con -> R.seq_chain (tc_ctx_contract_node_eqn) ctx con
                         
and tc_ctx_of_contract_node_decl: Lib.position -> tc_context
                                  -> LA.contract_node_decl
                                  -> tc_context tc_result
  = fun pos ctx (cname, params, inputs, outputs, contract) ->
  Log.log L_trace
    "Extracting typing context from contract declaration: %a"
    LA.pp_print_ident cname
  ; if (member_ty ctx cname)
    then type_error pos ("Node " ^ cname ^ " is already declared.")
    else build_node_fun_ty pos ctx inputs outputs
         >>= fun fun_ty -> R.ok (add_ty ctx cname fun_ty)

and tc_ctx_of_declaration: tc_context -> LA.declaration -> tc_context tc_result
    = fun ctx' ->
    function
    | LA.ConstDecl (_, const_decl) -> tc_ctx_const_decl ctx' const_decl
    | LA.NodeDecl (pos, node_decl) -> tc_ctx_of_node_decl pos ctx' node_decl
    | LA.FuncDecl (pos, node_decl) -> tc_ctx_of_node_decl pos ctx' node_decl
    | LA.ContractNodeDecl (pos, contract_decl) ->
       tc_ctx_of_contract_node_decl pos ctx' contract_decl
    | _ -> R.ok ctx'

and tc_context_of: tc_context -> LA.t -> tc_context tc_result
  = fun ctx decls ->
  R.seq_chain (tc_ctx_of_declaration) ctx decls 
(** Obtain a global typing context, get constants and function decls*)
  
and build_type_and_const_context: tc_context -> LA.t -> tc_context tc_result
  = fun ctx ->
  function
  | [] -> R.ok ctx
  | TypeDecl (_, ty_decl) :: rest ->
     tc_ctx_of_ty_decl ctx ty_decl
     >>= fun ctx' -> build_type_and_const_context ctx' rest
  | ConstDecl (_, const_decl) :: rest ->
     tc_ctx_const_decl ctx const_decl
     >>= fun ctx' -> build_type_and_const_context ctx' rest                   
  | _ :: rest -> build_type_and_const_context ctx rest
(** Process top level type declarations and make a type context with 
 * user types, enums populated *)
               
and check_type_well_formed: tc_context -> tc_type -> unit tc_result
  = fun ctx ->
  function
  | LA.TArr (_, arg_ty, res_ty) ->
     check_type_well_formed ctx arg_ty
     >> check_type_well_formed ctx res_ty
  | LA.RecordType (_, idTys) ->
       (R.seq_ (List.map (fun (_, _, ty)
                  -> check_type_well_formed ctx ty) idTys))
  | LA.ArrayType (pos, (b_ty, s)) ->
     if is_expr_int_type ctx s && is_expr_of_consts ctx s
     then check_type_well_formed ctx b_ty
     else type_error pos ("Invalid expression in array bounds")
  | LA.TupleType (_, tys) ->
     R.seq_ (List.map (check_type_well_formed ctx) tys)
  | LA.UserType (pos, i) -> if (member_ty_syn ctx i || member_u_types ctx i)
                          then R.ok () else type_error pos ("Undefined type " ^ i) 
  | _ -> R.ok ()
(** Does it make sense to have this type i.e. is it inhabited? 
 * We do not want types such as int^true to creep in the typing context *)
       
and build_node_fun_ty: Lib.position -> tc_context
                       -> LA.const_clocked_typed_decl list
                       -> LA.clocked_typed_decl list -> tc_type tc_result
  = fun pos ctx args rets ->
  let fun_const_ctx = List.fold_left (fun ctx (i,ty) -> add_const ctx i (LA.Ident (pos,i)) ty)
                        ctx (List.filter is_const_arg args |> List.map extract_ip_ty) in
  let fun_ctx = List.fold_left (fun ctx (i, ty)-> add_ty ctx i ty) fun_const_ctx (List.map extract_ip_ty args) in   
  let ops = List.map snd (List.map extract_op_ty rets) in
  let ips = List.map snd (List.map extract_ip_ty args) in
  let ret_ty = if List.length ops = 1 then List.hd ops else LA.TupleType (pos, ops) in
  let arg_ty = if List.length ips = 1 then List.hd ips else LA.TupleType (pos, ips) in
  check_type_well_formed fun_ctx ret_ty
  >> check_type_well_formed fun_ctx arg_ty
  >>  R.ok (LA.TArr (pos, arg_ty, ret_ty))
(** Function type for nodes will be [TupleType ips] -> [TupleTy outputs]  *)

(** Compute Equality for lustre types  *)
and eq_lustre_type : tc_context -> LA.lustre_type -> LA.lustre_type -> bool tc_result
  = fun ctx t1 t2 ->
  match (t1, t2) with
  (* Type Variable *)
  | TVar (_, i1), TVar (_, i2) -> R.ok (i1 = i2)

  (* Simple types *)
  | Bool _, Bool _ -> R.ok true
  | Int _, Int _ -> R.ok true
  | UInt8 _, UInt8 _ -> R.ok true
  | UInt16 _, UInt16 _ -> R.ok true              
  | UInt32 _, UInt32 _ -> R.ok true
  | UInt64 _,UInt64 _ -> R.ok true 
  | Int8 _, Int8 _ -> R.ok true 
  | Int16 _, Int16 _ -> R.ok true
  | Int32 _, Int32 _ -> R.ok true
  | Int64 _, Int64 _ -> R.ok true
  | Real _, Real _ -> R.ok true

  (* Integer Range *)
  | IntRange _, IntRange _ -> R.ok true
  | IntRange _, Int _ -> R.ok true
  | Int _, IntRange _ -> R.ok true

  (* Lustre V6 features *)
  | UserType (_, i1), UserType (_, i2) -> R.ok (i1 = i2)
  | AbstractType (_, i1), AbstractType (_, i2) -> R.ok (i1 = i2)
  | TupleType (_, tys1), TupleType (_, tys2) ->
     if List.length tys1 = List.length tys2
     then (R.seqM (&&) true (List.map2 (eq_lustre_type ctx) tys1 tys2))
     else R.ok false
  | RecordType (_, tys1), RecordType (_, tys2) ->
     R.seq (List.map2 (eq_typed_ident ctx)
              (sort_typed_ident tys1)
              (sort_typed_ident tys2))
     >>= fun isEqs -> R.ok (List.fold_left (&&) true isEqs)
  | ArrayType (pos1, arr1), ArrayType (pos2, arr2) -> eq_type_array ctx arr1 arr2 
  | EnumType (_, n1, is1), EnumType (_, n2, is2) ->
     R.ok (n1 = n2 && (List.fold_left (&&) true (List.map2 (=) (sort_idents is1) (sort_idents is2))))

  (* node/function type *)
  | TArr (_, arg_ty1, ret_ty1), TArr (_, arg_ty2, ret_ty2) ->
     R.seqM (&&) true [ eq_lustre_type ctx arg_ty1 arg_ty2
                      ; eq_lustre_type ctx ret_ty1 ret_ty2 ]

  (* special case for type synonyms *)
  | UserType (_, u), ty
    | ty, UserType (_, u) ->
     if member_ty_syn ctx u
     then let ty_alias  = lookup_ty_syn ctx u in 
          eq_lustre_type ctx ty ty_alias
     else R.ok false
  (* Another special case for tuple equality type *)
  | TupleType (_, tys), t
    | t, TupleType (_, tys) ->
     if List.length tys = 1
     then (eq_lustre_type ctx (List.hd tys) t)
     else R.ok false  
  | _, _ -> R.ok false

and is_expr_int_type: tc_context -> LA.expr -> bool  = fun ctx e ->
  R.safe_unwrap false
    (infer_type_expr ctx e
      >>= fun ty -> eq_lustre_type ctx ty (LA.Int (LH.pos_of_expr e)))
(** Checks if the expr is of type Int. This will be useful 
 * in evaluating array sizes that we need to have as constant integers
 * while declaring the array type *)

and is_expr_of_consts: tc_context -> LA.expr -> bool = fun ctx e ->
  List.fold_left (&&) true (List.map (member_val ctx) (LA.SI.elements (LH.vars e)))
(** checks if all the variables in the expression are constants *)

and check_expr_of_consts: tc_context -> LA.expr -> unit tc_result = fun ctx e ->
  match e with
  | Ident (pos, i) -> if member_val ctx i
                      then R.ok ()
                      else type_error pos ("Expression " ^ i ^ " is not a constant")
  | RecordProject (_, e, _) -> check_expr_of_consts ctx e
  | TupleProject (_, e1, e2) -> check_expr_of_consts ctx e1 >> check_expr_of_consts ctx e2
  (* Values *)
  | Const _ -> R.ok ()
  (* Operators *)
  | UnaryOp (_, _, e) -> check_expr_of_consts ctx e
  | BinaryOp (_, _, e1, e2) -> check_expr_of_consts ctx e1
                               >> check_expr_of_consts ctx e2
  | TernaryOp (_, _, e1, e2, e3) -> check_expr_of_consts ctx e1
                                    >> check_expr_of_consts ctx e2
                                    >> check_expr_of_consts ctx e3
  | ConvOp (_, _, e) -> check_expr_of_consts ctx e
  | CompOp (_, _, e1, e2) -> check_expr_of_consts ctx e1
                               >> check_expr_of_consts ctx e2
  (* Structured expressions *)
  | RecordExpr (_, _, id_exprs) -> R.seq_ (List.map (fun (_, e) -> check_expr_of_consts ctx e) id_exprs)
  | GroupExpr (_, _, es) -> R.seq_ (List.map (check_expr_of_consts ctx) es)
  (* Update of structured expressions *)
  | StructUpdate (_, e1, _, e2)
    | ArrayConcat (_, e1, e2)
    | ArrayConstr (_, e1, e2)  -> check_expr_of_consts ctx e1
                                  >> check_expr_of_consts ctx e2
  | ArraySlice (_, e, _) -> check_expr_of_consts ctx e
  | ArrayIndex (_, e, _) -> check_expr_of_consts ctx e
  | e -> type_error (LH.pos_of_expr e)
           ("Expression " ^ (Lib.string_of_t LA.pp_print_expr e) ^ " is not a constant expression")  
(** checks if all the variables in the expression are constants *)
  
and is_expr_term_zero: LA.expr -> bool = function
  | LA.Const (_, (Num "0"))
    | LA.Const (_, (Dec "0.0")) -> true
  (* TODO: use regex to check if it is of the format 0\.[0]* *)
  | _ -> false
                                                            
  
and eq_typed_ident: tc_context -> LA.typed_ident -> LA.typed_ident -> bool tc_result =
  fun ctx (_, i1, ty1) (_, i2, ty2) -> eq_lustre_type ctx ty1 ty2
(** Compute type equality for [LA.typed_ident] *)

and eq_type_array: tc_context -> (LA.lustre_type * LA.expr) -> (LA.lustre_type * LA.expr) -> bool tc_result
  = fun ctx (ty1, e1) (ty2, e2) -> eq_lustre_type ctx ty1 ty2
(** Compute equality for [LA.ArrayType]
 * For now, we do not check the bounds for arrays. This introduces bugs similar to Issue #566. 
 *   https://github.com/kind2-mc/kind2/issues/566. 
 *   Backend should handle such cases as it can talk to a powerful solver. *)

                                 
let rec type_check_group: tc_context -> LA.t ->  unit tc_result list
  = fun global_ctx
  -> function
  | [] -> [R.ok ()]
  (* skip over type declarations and const_decls*)
  | (LA.TypeDecl _ :: rest) 
    | LA.ConstDecl _ :: rest -> type_check_group global_ctx rest  
  | LA.NodeDecl (_, ((i, _,_, _, _, _, _, _) as node_decl)) :: rest ->
     (check_type_node_decl global_ctx node_decl (lookup_ty global_ctx i))
     :: type_check_group global_ctx rest
  | LA.FuncDecl (_, ((i, _,_, _, _, _, _, _) as node_decl)):: rest ->
     (check_type_node_decl global_ctx node_decl (lookup_ty global_ctx i))
     :: type_check_group global_ctx rest
  | LA.ContractNodeDecl (_, ((i, _, _, _, _) as contract_decl)) :: rest ->
     (check_type_contract_decl global_ctx contract_decl)
     :: type_check_group global_ctx rest
  | LA.NodeParamInst  _ :: rest -> Lib.todo __LOC__
(** By this point, all the circularity should be resolved,
 * the top most declaration should be able to access 
 * the types of all the forward referenced indentifiers from the context*)       

let type_check_decl_grps: tc_context -> LA.t list -> unit tc_result list
  = fun ctx decls ->
      Log.log L_trace ("===============================================\n"
                       ^^ "Phase 2: Type checking declaration Groups\n"
                       ^^"===============================================\n");  
  List.concat (List.map (type_check_group ctx) decls)               
(** Typecheck a list of independent groups using a global context*)

let rec report_tc_result: unit tc_result list -> unit tc_result
  =  function
     | [] -> R.ok () 
     | Error (pos,err) :: _ -> LC.fail_at_position pos err
     | Ok () :: tl -> report_tc_result tl
(** Get the first error *)

(****************************************************************
 * The main function of the file that kicks off type checking flow  *
 ****************************************************************)  

let is_type_or_const_decl: LA.declaration -> bool = fun d ->
  match d with
  | TypeDecl _
    | ConstDecl _ -> true
  | _ -> false

let split_program: LA.t -> (LA.t * LA.t)
  = List.fold_left
      (fun (ds, ds') d ->
        if is_type_or_const_decl d then (d::ds, ds')
        else (ds, d::ds')) ([], [])  

let type_check_program: LA.t -> LA.t tc_result = fun prg ->
  Log.log L_trace ("===============================================\n"
                   ^^ "Phase 1: Building TC Global Context\n"
                   ^^"===============================================\n")
  ; let (ty_and_const_decls, node_and_contract_decls) = split_program prg in
    (* circularity check and reordering for types and constants *)
    GA.sort_decls ty_and_const_decls >>= fun sorted_tys_consts ->
    Log.log L_trace "Sorted consts and type decls:\n%a" LA.pp_print_program sorted_tys_consts
    (* build the base context from the type and const decls *)
    ; build_type_and_const_context empty_context sorted_tys_consts >>= fun global_ctx ->
      GA.sort_decls node_and_contract_decls >>= fun sorted_node_and_contract_decls ->
    (* type check the nodes and contract decls using this base typing context  *)
    tc_context_of global_ctx sorted_node_and_contract_decls >>= fun tc_ctx ->
    
    Log.log L_trace ("===============================================\n"
                     ^^ "Phase 1: Completed Building TC Global Context\n"
                     ^^ "TC Context\n%a\n"
                     ^^"===============================================\n")
      pp_print_tc_context tc_ctx
    ; let tc_res = (type_check_decl_grps tc_ctx [prg]) in
      Log.log L_trace ("===============================================\n"
                       ^^ "Phase 2: Type checking declaration Groups Done\n"
                       ^^"===============================================\n")  
      
      ; report_tc_result tc_res >>
          (Log.log L_trace "Reordered Declarations:\n--------------\n%a "
            LA.pp_print_program (sorted_tys_consts @ sorted_node_and_contract_decls) 
            ; R.ok (sorted_tys_consts @ sorted_node_and_contract_decls)) 

(** Typechecks the [LA.declaration list] or the lustre program Ast and returns 
 *  a [Ok ()] if it succeeds or and [Error of String] if the typechecker fails*)
           
(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
