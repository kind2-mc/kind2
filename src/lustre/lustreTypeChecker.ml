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

(* @author Apoorv Ingle *)

(* TODO: Find strongly connected components, put them in a group *)
(* TODO: This also checks if we have co-dependent types or values *)
(* TODO: UserType if they are alias of any other type, then flatten them out *)

module LA = LustreAst
module LC = LustreContext
module R = Res
           
(* exception Type_error of Lib.position * string           
 * let throwTypeError pos string = raise (Type_error (pos, string)) *)
           
(** Returns [ok] if the typecheck/typeinference runs fine 
 * or reports an error at position with the error *)
type 'a tcResult = ('a, Lib.position * string) result


(* Get the first error *)
let rec reportTcResult: unit tcResult list -> unit tcResult = function
  | [] -> R.ok () 
  | Error (pos,err) :: _ -> LC.fail_at_position pos err
  | Ok () :: tl -> reportTcResult tl
                 
(** Simplified view of [LA.lustre_type]
 * This does not appear in the the interface file as we do not want it to escape the
 * typechecking phase  *)
type tcType  = LA.lustre_type
(* and lustre_kind =
 *   | KVar of LA.ident
 *   | KStar
 *   | KNat
 *   | KArr of lustre_kind * lustre_kind *)
  
(* This is different from [LA.pp_print_lustre_type] because we do not want position value to 
 * pollute the logs *)
let rec pp_print_tcType: Format.formatter -> tcType -> unit
  = fun ppf ty ->
  match ty with
  | TVar (_, i) -> Format.fprintf ppf "@[%a@]" LA.pp_print_ident i
  | Int _ -> Format.fprintf ppf "@[int@]"
  | Bool _ -> Format.fprintf ppf "@[bool@]"
  | UInt8 _ -> Format.fprintf ppf "@[uint8@]"
  | UInt16 _ -> Format.fprintf ppf "@[uint16@]"
  | UInt32 _ -> Format.fprintf ppf "@[uint32@]"
  | UInt64 _ -> Format.fprintf ppf "@[uint64@]"
  | Int8 _ -> Format.fprintf ppf "@[int8@]"
  | Int16 _ -> Format.fprintf ppf "@[int16@]"
  | Int32 _ -> Format.fprintf ppf "@[int32@]"
  | Int64 _ -> Format.fprintf ppf "@[int64@]"
  | Real _ -> Format.fprintf ppf "@[real@]"
  (* Function type of argument and return *)
  | TArr (_, argTy, retTy) -> Format.fprintf ppf "@[%a->@,%a@]" pp_print_tcType argTy pp_print_tcType retTy 
  (* Arrays Tuples, ranges *)
  | IntRange (_, mi, ma) -> Format.fprintf ppf "intRange (%a, %a)" LA.pp_print_expr mi LA.pp_print_expr ma
  | UserType (_, i) -> Format.fprintf ppf "userType %a" LA.pp_print_ident i
  | TupleType (_, tys) -> Format.fprintf ppf "[%a]" (Lib.pp_print_list pp_print_tcType ",") tys
  (* lustre V6 types *)
  | AbstractType (_,i) -> Format.fprintf ppf "abstractType %a" LA.pp_print_ident i 
  | RecordType (_, fs) -> let pp_print_field ppf = fun (_, i, ty) ->
                     Format.fprintf ppf "@[%a:%a@]" LA.pp_print_ident i pp_print_tcType ty in
                   Format.fprintf ppf "@[recordType {@ %a@ }@]" (Lib.pp_print_list pp_print_field ";@ @,") fs
  | ArrayType (_, (ty, e)) -> Format.fprintf ppf "@[[%a]^%a@]" pp_print_tcType ty LA.pp_print_expr e
  | EnumType (_, n, ids) ->
     let pp_print_enumname ppf = function
       | Some name -> LA.pp_print_ident ppf name
       | None -> () in
     Format.fprintf ppf "enumType %a {@ %a@ }"
       pp_print_enumname n
       (Lib.pp_print_list LA.pp_print_ident ";@ @,") ids
     
let string_of_tcType t = Lib.string_of_t pp_print_tcType t
                       
(** Module for identifier Map *)
module OrdIdent = struct
  type t = LA.ident
  let compare i1 i2 = Stdlib.compare i1 i2
end

(** Map for types with identifiers as keys *)
module IMap = struct

  (** everything that [Stdlib.Map] gives us  *)
  include Map.Make(OrdIdent)

  (** Pretty print type synonyms*)
  let pp_print_type_binding ppf = fun i ty -> 
    Format.fprintf ppf "(%a<->%a), " LA.pp_print_ident i pp_print_tcType ty

  (** Pretty print type bindings*)
  let pp_print_type_binding ppf = fun i ty -> 
    Format.fprintf ppf "(%a:%a), " LA.pp_print_ident i pp_print_tcType ty

  (** Pretty print value bindings (used for constants)*)
  let pp_print_val_binding ppf = fun i (v, ty) ->
    Format.fprintf ppf "(%a:%a :-> %a), " LA.pp_print_ident i pp_print_tcType ty LA.pp_print_expr v

  (** Pretty print type context *)
  let pp_print_tySyns ppf = iter (pp_print_type_binding ppf)   

  (** Pretty print type context *)
  let pp_print_tymap ppf = iter (pp_print_type_binding ppf)   

  (** Pretty print value store *)
  let pp_print_vstore ppf = iter (pp_print_val_binding ppf)
end

let sortTypedIdent: LA.typed_ident list -> LA.typed_ident list = fun tyIdents ->
  List.sort (fun (_,i1,_) (_,i2,_) -> Stdlib.compare i1 i2) tyIdents

let sortIdents: LA.ident list -> LA.ident list = fun ids ->
  List.sort (fun i1 i2 -> Stdlib.compare i1 i2) ids

type tyAliasStore = tcType IMap.t
(** A store of type Aliases, i.e. for user defined types  *)

type tyStore = tcType IMap.t
(** A store of identifier and their types*)

type constStore = (LA.expr * tcType) IMap.t 
(** A Store of constant identifier and their (const) values with types. 
 *  The values of the associated identifiers should be evaluated to a 
 * Bool or an Int at constant propogation phase of type checking *)
            
(** Type Checker context is a pair type store and a value store with identifier as its key *)
type tcContext = { tySyns: tyAliasStore; tyCtx:tyStore; vlCtx: constStore}

let emptyContext: tcContext = {tySyns = IMap.empty; tyCtx= IMap.empty; vlCtx=IMap.empty}

(** Pretty print the complete type checker context*)
let pp_print_tcContext ppf ctx
  = Format.fprintf ppf
      "TypeSynonyms={%a}\nTypeContext={%a}\nConstValueContext={%a}"
      IMap.pp_print_tySyns (ctx.tySyns)
      IMap.pp_print_tymap (ctx.tyCtx)
      IMap.pp_print_vstore (ctx.vlCtx)


                            
(** [typeError] returns an [Error] of [tcResult] *)
let typeError pos err = R.error (pos, "Type error: " ^ err)

let memberTySyn: tcContext -> LA.ident -> bool
  = fun ctx i -> IMap.mem i (ctx.tySyns)
           
let memberTy: tcContext -> LA.ident -> bool
  = fun ctx i -> IMap.mem i (ctx.tyCtx)

let memberVal: tcContext -> LA.ident -> bool
  = fun ctx i -> IMap.mem i (ctx.vlCtx)

                      
let lookupTySyn: tcContext -> LA.ident -> tcType =
  fun ctx i -> IMap.find i (ctx.tySyns)
                      
let lookupTy: tcContext -> LA.ident -> tcType =
  fun ctx i -> let ty = IMap.find i (ctx.tyCtx) in
               match ty with
               | LA.UserType (_, uid) -> if (memberTySyn ctx uid) then (lookupTySyn ctx uid) else ty
               | _ ->  ty

let lookupConst: tcContext -> LA.ident -> (LA.expr * tcType) =
  fun ctx i -> IMap.find i (ctx.vlCtx)

let addTySyn: tcContext -> LA.ident -> tcType -> tcContext = 
  fun ctx i ty -> {ctx with tySyns=IMap.add i ty (ctx.tySyns)}

let addTy: tcContext -> LA.ident -> tcType -> tcContext
  = fun ctx i ty -> {ctx with tyCtx=IMap.add i ty (ctx.tyCtx)}

let addConst: tcContext -> LA.ident -> LA.expr -> tcType -> tcContext
  = fun ctx i e ty -> {ctx with vlCtx=IMap.add i (e, ty) ctx.vlCtx} 

let union: tcContext -> tcContext -> tcContext
  = fun ctx1 ctx2 -> { tySyns = (IMap.union (fun k v1 v2 -> Some v1) (ctx1.tySyns) (ctx2.tySyns))
                     ; tyCtx = (IMap.union (fun k v1 v2 -> Some v1) (ctx1.tyCtx) (ctx2.tyCtx))
                     ; vlCtx = (IMap.union (fun k v1 v2 -> Some v1) (ctx1.vlCtx) (ctx2.vlCtx))
                     }

let singletonTy: LA.ident -> tcType -> tcContext =
  fun i ty -> addTy emptyContext i ty

let singletonConst: LA.ident -> LA.expr -> tcType -> tcContext =
  fun i e ty -> addConst emptyContext i e ty

let inferTypeConst: Lib.position -> LA.constant -> tcType
  = fun pos -> function
  | Num _ -> Int pos
  | Dec _ -> Real pos
  | _ -> Bool pos

       
let inferTypeUnaryOp: Lib.position -> LA.unary_operator -> tcType tcResult =
  fun pos -> function
  | LA.Not -> R.ok (LA.TArr (pos ,Bool pos , Bool pos))
  | LA.BVNot
  | LA.Uminus -> R.ok (LA.TArr (pos, Int pos, Int pos))

let inferTypeBinaryOp: Lib.position -> LA.binary_operator -> tcType tcResult = fun pos ->
  function
  | LA.And | LA.Or | LA.Xor | LA.Impl
    -> R.ok (LA.TArr (pos, Bool pos, TArr(pos, Bool pos, Bool pos)))
  | LA.Mod | LA. Minus | LA.Plus | LA. Div | LA.Times | LA.IntDiv
    | LA.BVAnd | LA.BVOr | LA.BVShiftL | LA.BVShiftR
    -> R.ok (LA.TArr (pos, Int pos, TArr(pos, Int pos, Int pos))) 
     

let inferTypeTernaryOp: LA.ternary_operator -> tcType tcResult = function | _ -> Lib.todo __LOC__

let inferTypeNaryOp: LA.n_arity_operator -> tcType tcResult  = function | _ -> Lib.todo __LOC__

let inferTypeConvOp: Lib.position -> LA.conversion_operator -> tcType tcResult = fun pos ->
  function
  | _ -> R.ok (LA.TArr (pos, Int pos, Int pos))

let inferTypeCompOp: Lib.position -> LA.comparison_operator -> tcType tcResult = fun pos ->
  function
  | _ -> R.ok (LA.TArr (pos, Int pos, LA.TArr (pos, Int pos, Bool pos))) 

let inferTypeGrpExpr: LA.expr -> tcType = function | _ -> Lib.todo __LOC__
                                                        
(** Infer the type of a [LA.expr] with the types of free variables given in [tcContext] *)
let rec inferTypeExpr: tcContext -> LA.expr -> tcType tcResult
  = fun ctx expr ->
  match expr with
  (* Identifiers *)
  | LA.Ident (pos, i) ->
     (try R.ok (lookupTy ctx i) with
      | Not_found -> typeError pos ("Unbound Variable: << " ^ i ^ " >>")) 
  | LA.ModeRef (pos, ids) -> Lib.todo __LOC__
  | LA.RecordProject _  -> Lib.todo __LOC__
  | LA.TupleProject (pos, e1, e2) -> Lib.todo __LOC__ 

  (* Values *)
  | LA.Const (pos, c) -> R.ok (inferTypeConst pos c)

  (* Operator applications *)
  | LA.UnaryOp (pos, op, e) ->
     R.bind (inferTypeUnaryOp pos op) (fun ty ->
         match ty with
         | TArr (_,argTy, resTy) ->
            R.bind (checkTypeExpr ctx e argTy) (fun _ ->
                R.ok resTy)
         | fty -> typeError pos ("Unexpected unary operator type: "
                                 ^ string_of_tcType fty))
  | LA.BinaryOp (pos, bop, e1, e2) ->
     R.bind (inferTypeBinaryOp pos bop) (fun ty ->
         match ty with
         | TArr (_,argTy1, TArr (_,argTy2, resTy)) ->
            (R.bind (checkTypeExpr ctx e1 argTy1) (fun _ ->
                 R.bind (checkTypeExpr ctx e2 argTy2) (fun _ ->
                     R.ok resTy)))
         | fty -> typeError pos ("Unexpected binary operator type: "
                                 ^ string_of_tcType fty))
  | LA.TernaryOp (pos, top, con, e1, e2) ->
     R.bind (inferTypeExpr ctx con) (fun cTy ->
         match cTy with
         | Bool _ ->  R.bind (inferTypeExpr ctx e1) (fun e1Ty->
                          R.bind (checkTypeExpr ctx e1 e1Ty) (fun _ ->
                              R.ok e1Ty))
         | _   ->  typeError pos ("Expected a boolean expression but found "
                                  ^ string_of_tcType cTy))
  | LA.NArityOp _ -> Lib.todo __LOC__          (* One hot expression is not supported *)    
  | LA.ConvOp (pos, cop, e) -> 
     R.bind (inferTypeConvOp pos cop) (fun ty ->
         match ty with
         | TArr (_,argTy, resTy) ->
            R.bind (checkTypeExpr ctx e argTy) (fun _ ->
                R.ok resTy)
         | fty -> typeError pos ("Unexpected conversion operator type: "
                                 ^ string_of_tcType fty))
  | LA.CompOp (pos, cop, e1, e2) ->
     R.bind (inferTypeCompOp pos cop) (fun ty ->
         match ty with
         | TArr (_,argTy1, TArr (_,argTy2, resTy)) ->
            (R.bind (checkTypeExpr ctx e1 argTy1) (fun _ ->
                 R.bind (checkTypeExpr ctx e2 argTy2) (fun _ -> 
                     R.ok resTy)))
         | fty -> typeError pos ("Unexpected comparison operator type: "
                                 ^ string_of_tcType fty))
    
  (* Structured expressions *)
  | LA.RecordExpr (pos, _, flds) ->
     let inferField: tcContext -> (LA.ident * LA.expr) -> (LA.typed_ident) tcResult
       = fun ctx (i, e) ->
       R.bind (inferTypeExpr ctx e) (fun ty ->
           R.ok (LustreAstHelpers.pos_of_expr e, i, ty))       
     in R.bind (R.seq (List.map (inferField ctx) flds)) (fun fldTys -> 
            R.ok (LA.RecordType (pos, fldTys)))
    
  | LA.GroupExpr (pos, structType, exprs)  ->
     ( match structType with
       | LA.ExprList 
         | LA.TupleExpr -> R.bind (R.seq (List.map (inferTypeExpr ctx) exprs)) (fun tys ->
                               R.ok (LA.TupleType (pos, tys)))
       | LA.ArrayExpr -> R.bind (R.seq (List.map (inferTypeExpr ctx) exprs)) (fun tys ->
                             Log.log L_debug "Array elements: [%a]\n Array types: [%a]"
                               (Lib.pp_print_list LA.pp_print_expr ",") exprs
                               (Lib.pp_print_list pp_print_tcType ",") tys
                            ; let elty = List.hd tys in
                              R.bind(R.seqM (&&) true (List.map (eqLustreType ctx elty) tys)) (fun isEq->
                                  if isEq
                                  then let arrTy = List.hd tys in
                                       let arrExp = LA.Const (pos, Num (string_of_int (List.length tys))) in
                                       R.ok (LA.ArrayType (pos, (arrTy, arrExp)))
                                  else typeError pos "All expressions must be of the same type in an Array")))
    
  (* Update of structured expressions *)
  | ArrayConstr (pos, bExpr, supExpr) ->
     R.bind (inferTypeExpr ctx bExpr) (fun bTy ->
         R.bind (inferTypeExpr ctx supExpr) (fun supTy ->
             R.bind (eqLustreType ctx supTy (Int pos)) (fun isBoundInt ->
                 if isBoundInt 
                 then R.ok(LA.ArrayType (pos, (bTy, supExpr)))
                 else typeError pos "Array cannot have non numeral type as its bounds")))
  | StructUpdate _ -> Lib.todo __LOC__
  | ArraySlice (pos, e1, (il, iu)) ->
     if isExprIntType ctx il && isExprIntType ctx iu
     then R.bind (inferTypeExpr ctx e1) (fun ty ->
               match ty with
               | ArrayType (_, (bTy, s)) -> Lib.todo __LOC__
               | _ -> typeError pos ("Slicing can only be done on an type Array "
                                       ^ "but found type "
                                       ^ Lib.string_of_t pp_print_tcType ty))
     else typeError pos ("Slicing should have integer types")        
  | ArrayConcat  _ -> Lib.todo __LOC__
  (* Quantified expressions *)
  (* | Quantifier of position * quantifier * typed_ident list * expr *)
  (* Clock operators *)
  (* | When of position * expr * clock_expr
   * | Current of position * expr
   * | Condact of position * expr * expr * ident * expr list * expr list
   * | Activate of position * ident * expr * expr * expr list
   * | Merge of position * ident * (ident * expr) list
   * | RestartEvery of position * ident * expr list * expr *)
  (* Temporal operators *)
  | Pre (pos, e) -> inferTypeExpr ctx e
  (* | Last of position * ident
   * | Fby of position * expr * int * expr*)
  | Arrow (pos, e1, e2) -> R.bind (inferTypeExpr ctx e1) (fun ty1 ->
                               R.bind (inferTypeExpr ctx e2) (fun ty2 ->
                                   if ty1 == ty2 then R.ok ty1 else
                                     typeError pos
                                       ("Arrow types do not match "
                                        ^ string_of_tcType ty1
                                        ^ " and " ^ string_of_tcType ty2))) 
  (* Node calls *)
  | Call (pos, i, argExprs) ->
     Log.log L_debug "Inferring type for node call %a" LA.pp_print_ident i  
    ; let rec inferTypeNodeArgs: tcContext -> LA.expr list -> tcType tcResult
        = fun ctx args ->
        R.bind (R.seq (List.map (inferTypeExpr ctx) args)) (fun argTys ->
            R.ok (LA.TupleType (pos, argTys)))
      in
      (match (lookupTy ctx i) with 
       | TArr (_, expArgTys, expRetTys) ->
          R.bind (inferTypeNodeArgs ctx argExprs) (fun givenArgTys ->
              R.bind (eqLustreType ctx expArgTys givenArgTys) (fun isArgTyOk ->
                  if isArgTyOk
                  then R.ok expRetTys
                  else typeError pos ("Node arguments expected to have type "
                                      ^ string_of_tcType expArgTys
                                      ^ " but found type "
                                      ^ string_of_tcType givenArgTys)))
       | ty -> typeError pos
                 ("Expected node type to be a function type, but found type"
                  ^ string_of_tcType ty)) 
      
  (* | CallParam of position * ident * lustre_type list * expr list *)
  | _ -> Lib.todo __LOC__

(** Type checks an expression and returns [ok] 
 * if the expected is the given type [tcType]  
 * returns an [Error of string] otherwise *)
and checkTypeExpr: tcContext -> LA.expr -> tcType -> unit tcResult
  = fun ctx expr expTy ->
  match expr with
  (* Identifiers *)
  | Ident (pos, i) as ident ->
     R.bind (inferTypeExpr ctx ident) (fun ty ->
         R.bind (eqLustreType ctx ty expTy) (fun isEq ->
             if isEq
             then R.ok ()
             else typeError pos ("Indentifier " ^ i
                                 ^ " does not match expected type "
                                 ^ string_of_tcType expTy
                                 ^ " with infered type "
                                 ^ string_of_tcType ty)))
  | ModeRef (pos, ids) -> Lib.todo __LOC__
  | RecordProject (pos, expr, idx) -> checkTypeRecordProj pos ctx expr idx expTy
  | TupleProject (pos, e1, e2) -> Lib.todo __LOC__ 
  (* Operators *)
  | UnaryOp (pos, op, e) ->
     R.bind (inferTypeUnaryOp pos op) (fun ty ->
         R.bind (inferTypeExpr ctx e) (fun argTy ->
             R.bind (eqLustreType ctx ty (TArr(pos,argTy, expTy))) (fun isEq ->
                 if isEq
                 then R.ok ()
                 else typeError pos ("Cannot apply argument of type "
                                     ^ string_of_tcType argTy
                                     ^ " to operator of type "
                                     ^ string_of_tcType ty))))
  | BinaryOp (pos, op, e1, e2) ->
     R.bind (inferTypeBinaryOp pos op) (fun ty ->
         R.bind (inferTypeExpr ctx e1) (fun argTy1 ->
             R.bind (inferTypeExpr ctx e2) (fun argTy2 ->
                 R.bind (eqLustreType ctx ty (TArr (pos,argTy1, TArr (pos, argTy2, expTy)))) (fun isEq ->
                     if isEq 
                     then R.ok ()
                     else typeError pos (" Cannot apply arguments of type "
                                         ^ string_of_tcType argTy1
                                         ^ " and type " ^ string_of_tcType argTy2
                                         ^ " to operator of type " ^ string_of_tcType ty)))))
  | LA.TernaryOp (pos, op, con, e1, e2) ->
     R.bind (inferTypeExpr ctx con) (fun ty ->
         match ty with
         | Bool _ -> R.bind (inferTypeExpr ctx e1) (fun ty1 ->
                         R.bind (inferTypeExpr ctx e2) (fun ty2 ->
                             R.bind (eqLustreType ctx ty1 ty2)(fun isEq ->
                                 if isEq
                                 then R.ok ()
                                 else typeError pos
                                        ("Cannot unify type "
                                         ^ string_of_tcType ty1
                                         ^ "with type "
                                         ^ string_of_tcType ty2))))
         | _ -> typeError pos ("ITE condition expression "
                               ^ "Expected: " ^ string_of_tcType (Bool pos)
                               ^ "Found: " ^ string_of_tcType ty))
  | NArityOp _ -> Lib.todo __LOC__          (* One hot expression is not supported? *)    
  | ConvOp (pos, cvop, e) ->
     R.bind (inferTypeConvOp pos cvop) (fun cvopTy ->
         R.bind (inferTypeExpr ctx e) (fun exprTy ->
             R.bind (eqLustreType ctx cvopTy (TArr (pos,exprTy, expTy)))(fun isEq ->
                 if isEq
                 then R.ok ()
                 else typeError pos ("Cannot apply argument of type "
                                     ^ string_of_tcType exprTy
                                     ^ " to operator of type "
                                     ^ string_of_tcType cvopTy))))
  | CompOp (pos, cop, e1, e2) ->
     R.bind (inferTypeCompOp pos cop) (fun ty ->
         R.bind (inferTypeExpr ctx e1) (fun argTy1 ->
             R.bind (inferTypeExpr ctx e2) (fun argTy2 ->
                 R.bind (eqLustreType ctx ty (TArr (pos,argTy1, TArr (pos,argTy2, expTy)))) (fun isEq ->
                     if isEq 
                     then R.ok()
                     else typeError pos
                            ("Cannot apply arguments of type "
                             ^ string_of_tcType argTy1
                             ^ " and " ^ string_of_tcType argTy2
                             ^ " to operator of type "
                             ^ string_of_tcType ty)))))
  (* Values/Constants *)
  | Const (pos, c) -> R.ok ()

  (* Structured expressions *)
  | RecordExpr (pos, _, flds) ->
     let (ids, es) = List.split flds in
     let mkTyIdent p i t = (p, i, t) in    
     R.bind (R.seq (List.map (inferTypeExpr ctx) es)) (fun infTys ->
         let infRTy = LA.RecordType (pos, (List.map2 (mkTyIdent pos) ids infTys)) in
         R.bind (eqLustreType ctx expTy infRTy) (fun isEq ->
             if isEq then R.ok ()
             else typeError pos
                    ("RecordType mismatch expected "
                     ^ string_of_tcType expTy
                     ^ " but found "
                     ^ string_of_tcType infRTy)))
     
  | GroupExpr _ -> Lib.todo __LOC__
  (* Update of structured expressions *)
  | StructUpdate _ -> Lib.todo __LOC__
  | ArrayConstr (pos, bExp, supExp) ->
     R.bind (inferTypeExpr ctx bExp) (fun bTy ->
         R.bind (inferTypeExpr ctx supExp) (fun supTy ->
             R.bind (eqLustreType ctx expTy (LA.ArrayType (pos, (bTy, bExp)))) (fun isEq ->
                 if isEq
                 then R.ok()
                 else typeError pos ("Expecting array type "
                                     ^ string_of_tcType expTy
                                     ^ " but found "
                                     ^ string_of_tcType (LA.ArrayType (pos, (bTy, bExp)))))))
  | ArraySlice _ -> Lib.todo __LOC__
  | ArrayConcat _ -> Lib.todo __LOC__
  (* Quantified expressions *)
  (* | Quantifier of position * quantifier * typed_ident list * expr *)
  (* Clock operators *)
  (* | When of position * expr * clock_expr
   * | Current of position * expr
   * | Condact of position * expr * expr * ident * expr list * expr list
   * | Activate of position * ident * expr * expr * expr list
   * | Merge of position * ident * (ident * expr) list
   * | RestartEvery of position * ident * expr list * expr *)
  (* Temporal operators *)
  | Pre (pos, e) -> checkTypeExpr ctx e expTy
  (* | Last of position * ident
   * | Fby of position * expr * int * expr*)
  | Arrow (pos, e1, e2) -> R.bind(inferTypeExpr ctx e1) (fun ty1 ->
                               R.bind(inferTypeExpr ctx e2) (fun ty2 ->
                                   R.bind (eqLustreType ctx ty1 ty2)(fun isEq ->
                                       if isEq 
                                       then R.ok ()
                                       else typeError pos (" Cannot match expected type "
                                                           ^ string_of_tcType ty1
                                                           ^ " with " ^ string_of_tcType ty2))))
  (* Node calls *)
  | Call (pos, i, args) as ncall -> R.bind (inferTypeExpr ctx ncall) (fun ty ->
                                        R.bind (eqLustreType ctx ty expTy) (fun isEq ->
                                            if isEq
                                            then R.ok ()
                                            else typeError pos (" Cannot match expected type "
                                                           ^ string_of_tcType ty
                                                           ^ " with " ^ string_of_tcType expTy)))  
  | CallParam _ -> Lib.todo __LOC__
  | _ -> Lib.todo __LOC__ 
and checkTypeRecordProj: Lib.position -> tcContext -> LA.expr -> LA.index -> tcType -> unit tcResult =
  fun pos ctx expr idx expTy -> 
  R.bind(inferTypeExpr ctx expr) (fun recTy ->
         match recTy with
         | RecordType (_, flds) ->
            R.bind (try R.ok (List.find (fun (_, i, _) -> i = idx) flds) with
            | Not_found -> typeError pos ("Cannot project field " ^ idx
                                          ^ " from given record type "
                                          ^ Lib.string_of_t pp_print_tcType recTy)) (fun (_, _, fty) -> 
                R.bind (eqLustreType ctx fty expTy) (fun isEq ->
                    if isEq
                    then R.ok ()
                    else typeError pos ("Cannot match expected type "
                                        ^ Lib.string_of_t pp_print_tcType expTy
                                        ^ " with infered type "
                                        ^ Lib.string_of_t pp_print_tcType fty)))
         | _ -> typeError pos ("Cannot project field " ^ idx
                               ^ " from a non record type "
                               ^ Lib.string_of_t pp_print_tcType recTy))       
and checkTypeConstDecl: tcContext -> LA.const_decl -> tcType -> unit tcResult =
  fun ctx constDecl expTy ->
  match constDecl with
  | FreeConst (pos, i, lusTy) ->
     let infTy = (lookupTy ctx i) in
     if infTy != expTy
     then typeError pos
            ("Identifier "
             ^ i
             ^ " expected to have type " ^ string_of_tcType infTy
             ^ " but found type " ^ string_of_tcType expTy)
     else R.ok ()
  | UntypedConst (pos, i, exp) ->
     R.bind (inferTypeExpr ctx exp) (fun ty ->
         if expTy != ty
         then typeError pos
                ("Identifier "
                 ^ i
                 ^ " expected to have type " ^ string_of_tcType expTy
                 ^ " but found type " ^ string_of_tcType ty)
         else R.ok ()) 
    
  | TypedConst (pos, i, exp, lusTy) ->
     R.bind (inferTypeExpr ctx exp) (fun infTy ->
         if expTy != infTy
         then typeError pos
                ("Identifier "
                 ^ i
                 ^ " expects type " ^ string_of_tcType expTy
                 ^ " but expression is of type " ^ string_of_tcType infTy)
         else R.ok ())  

and checkTypeNodeDecl: tcContext -> LA.node_decl -> tcType -> unit tcResult
  = fun ctx
        (nodeName, isExtern, params, cclktydecls, clktydecls, localdecls, items, contract)
        expTy ->
  Log.log L_debug "TC declaration node: %a {" LA.pp_print_ident nodeName
  ; let extractArg: LA.const_clocked_typed_decl -> tcContext
      = fun  (_, i,ty, _, _) -> singletonTy i ty in
    let extractRet: LA.clocked_typed_decl -> tcContext
      = fun (_, i, ty, _) -> singletonTy i ty in
    let localVarBinding: tcContext -> LA.node_local_decl -> tcContext tcResult = fun ctx -> function
      | LA.NodeConstDecl (pos, constDecls) -> tcCtxConstDecl ctx constDecls 
      | LA.NodeVarDecl (pos, (_, v, ty, _)) ->
         if isTypeWellFormed ctx ty then R.ok (addTy ctx v ty)
         else typeError pos ("Node's local variable "
                             ^ v
                             ^ " type should be well formed")
                                               
    in

    (* if the node is extern, we will not have any body to typecheck so skip it *)
    if isExtern
    then ( Log.log L_debug "External Node, skipping type check"
         ; R.ok ())
    else (
      Log.log L_debug "Params: %a" LA.pp_print_node_param_list params

      (* These are inputs to the node *)
      ; let ips = List.fold_left union emptyContext (List.map extractArg cclktydecls) in
      Log.log L_debug "Const clocked typed decls: %a\nips:%a"
        (Lib.pp_print_list LA.pp_print_const_clocked_typed_ident ",@,") cclktydecls
        pp_print_tcContext ips
      
      (* These are outputs of the node *)
      ; let ops = List.fold_left union emptyContext (List.map extractRet clktydecls) in
        Log.log L_debug "Clocked typed decls: %a\nops:%a"
          (Lib.pp_print_list LA.pp_print_clocked_typed_ident ",@,") clktydecls
          pp_print_tcContext ops
        ; Log.log L_debug "Local decls: %a" LA.pp_print_node_local_decl localdecls
        ; R.bind (R.seq (List.map (localVarBinding ctx) localdecls)) (fun localVarCtxts ->
              let localDecls = List.fold_left union ctx localVarCtxts in
              Log.log L_debug "Extracted local consts and vars: %a" pp_print_tcContext localDecls
              ; let localCtx = union localDecls       (* declared local variables and constants *)
                                  (union ips ops)     (* input and output type vars *)
              in
              Log.log L_debug "Local Typing Context {%a}" pp_print_tcContext localCtx
              ; let doNodeEqn ctx eqn = match eqn with
                  | LA.Assert (pos, e) ->
                     R.bind
                       ( Log.log L_debug "checking assertion"
                       ; checkTypeExpr ctx e (Bool pos)) (fun _ -> R.ok ())
                  | LA.Equation (_, lhs, expr) ->
                     R.bind
                       (inferTypeExpr ctx expr) (fun ty ->
                         checkTypeStructDef ctx lhs ty)
                  | LA.Automaton (pos, _, _, _) ->
                     Lib.todo ("Unsupported feature Automation." ^ __LOC__)
                in
                let rec doItems: tcContext -> LA.node_item list -> unit tcResult =
                  fun ctx its -> match its with
                                 | [] -> R.ok ()
                                 | (LA.Body eqn as body) :: rest ->
                                    R.bind ( Log.log L_debug "Node Item (Equation): %a" LA.pp_print_node_item body
                                           ; doNodeEqn ctx eqn) (fun _ ->
                                        doItems ctx rest)
                                 | (LA.AnnotMain _ as ann) :: rest ->
                                    Log.log L_debug "Node Item Skipped (Main Annotation): %a" LA.pp_print_node_item ann
                                   ; doItems ctx rest
                                 | (LA.AnnotProperty _ as ann) :: rest ->
                                    Log.log L_debug "Node Item Skipped (Annotation Property): %a" LA.pp_print_node_item ann
                                   ; doItems ctx rest 
                in
                let r = doItems localCtx items in
                Log.log L_debug "TC declaration node %a done }" LA.pp_print_ident nodeName
                ; r)
    )

and checkTypeStructItem: tcContext -> LA.struct_item -> tcType -> unit tcResult
  = fun ctx st expTy ->
  match st with
  | SingleIdent (pos, i) ->
     let infTy = lookupTy ctx i in
     R.bind (eqLustreType ctx expTy infTy) (fun isEq ->
         if isEq
         then R.ok ()
         (*This is an ugly fix to try and see if the RHS was instead a function return call *)
         else R.bind (eqLustreType ctx expTy (TupleType (pos, (infTy::[])))) (fun isEq' ->
                  if isEq'
                  then R.ok()
                  else typeError pos ("Expected type "
                                      ^ string_of_tcType expTy
                                      ^ " but found type "
                                      ^ string_of_tcType infTy)))
  | _ -> Lib.todo __LOC__
(** The structure of the left hand side of the equation 
 * should match the type of the right hand side expression *)
and checkTypeStructDef: tcContext -> LA.eq_lhs -> tcType -> unit tcResult
  = fun ctx (StructDef (pos, lhss)) expTy ->
  (* This is a structured type, and we would want the expected type expTy to be a tuple type *)
    (Log.log L_debug "TypeStructDef checking if %a has type %a"
       (Lib.pp_print_list LA.pp_print_struct_item ",")
       lhss pp_print_tcType expTy
    ; match expTy with
      | TupleType (_, expTyLst) ->
         if List.length lhss = List.length expTyLst
         then R.seq_ (List.map2 (checkTypeStructItem ctx) lhss expTyLst)
         else typeError pos ("Term structure on left hand side of the equation"
                             ^ " does not match expected type "
                             ^ Lib.string_of_t pp_print_tcType expTy 
                             ^ " on right hand side of the node equation")
      (* We are dealing with simple types, so lhs has to be a singleton list *)
      | _ -> if (List.length lhss != 1)
             then typeError pos ("Term structure on left hand side of the equation"
                                 ^ " does not match expected type structure "
                                 ^ Lib.string_of_t pp_print_tcType expTy 
                                 ^ " on right hand side of the node equation")
             else let lhs = List.hd lhss in
                  checkTypeStructItem ctx lhs expTy)

(** Obtain a global typing context, get contatnts and function decls*)
and tcContextOf: tcContext -> LA.t -> tcContext tcResult = fun ctx ->
  let tcContextOf': tcContext -> LA.declaration -> tcContext tcResult
    = fun ctx decl ->
    match decl with
    | LA.TypeDecl (_, tyDecl)     -> tcCtxOfTyDecl ctx tyDecl 
    | LA.ConstDecl (_, constDecl) -> tcCtxConstDecl ctx constDecl
    | LA.NodeDecl (pos, nodeDecl) -> tcCtxOfNodeDecl pos ctx nodeDecl
    | LA.FuncDecl (pos, nodeDecl) -> tcCtxOfNodeDecl pos ctx nodeDecl
    | _ -> R.ok ctx

  in function
  (* TODO: make this into a sequence and then fold? *)
  | [] -> R.ok ctx
  | d :: tl ->
     R.bind ( Log.log L_debug
                "Extracting typing context from declaration: %a"
                LA.pp_print_declaration d
            ; tcContextOf' ctx d) (fun ctx' ->
         R.bind (tcContextOf (union ctx' ctx) tl) (fun c -> 
             R.ok c))

and tcCtxOfTyDecl: tcContext -> LA.type_decl -> tcContext tcResult = fun ctx ->
  function
  | LA.AliasType (_, i, ty) -> R.ok (addTySyn ctx i ty)
  | LA.FreeType _ -> R.ok ctx
(** Does it make sense to have this type i.e. is it inhabited? We do not want types such as int^true *)
and isTypeWellFormed: tcContext -> tcType -> bool = fun ctx ty ->
  match ty with
  | LA.TArr (_, argTy, resTy) -> isTypeWellFormed ctx argTy && isTypeWellFormed ctx resTy
  | LA.RecordType (_, idTys) -> List.fold_left (&&) true (List.map (fun (_, _, ty) -> isTypeWellFormed ctx ty) idTys)
  | LA.ArrayType (_, (_, s)) -> isExprIntType ctx s && isExprOfConts ctx s
  | LA.TupleType (_, tys) -> List.fold_left (&&) true (List.map (isTypeWellFormed ctx) tys)
  | _ -> true
                   
(** Shadow the old binding with the new const decl *)
and tcCtxConstDecl: tcContext -> LA.const_decl -> tcContext tcResult
  = fun ctx decl ->
  Log.log L_debug
    "Extracting typing context from const declaration: %a"
    LA.pp_print_const_decl decl
  ; match decl with
    | LA.FreeConst (pos, i, ty) ->
       if (isTypeWellFormed ctx ty)
       then R.ok (addTy ctx i ty)
       else typeError pos "Constant should be of a well formed type"
    | LA.UntypedConst (_, i, e) ->
       R.bind (inferTypeExpr ctx e) (fun ty -> 
           R.ok (addTy (addConst ctx i e ty) i ty))
    | LA.TypedConst (pos, i, expr, ty)
      ->  let expTy = ty in
          R.bind (checkTypeExpr ctx expr expTy) (fun _ ->
              R.ok (addTy (addConst ctx i expr expTy) i expTy))

(** get the type signature of node or a function *)
and tcCtxOfNodeDecl: Lib.position -> tcContext -> LA.node_decl -> tcContext tcResult
  = fun pos ctx (i, _, _ , ip, op,_ ,_ ,_) ->
  if (memberTy ctx i)
  then typeError pos ("Duplicate node detected with name: " ^ i)
  else let funTy = buildFunTy pos ip op in
       if isTypeWellFormed ctx funTy
       then R.ok (addTy ctx i funTy)
       else typeError pos "Arguments and return types of the node should be well formed."
  
(** Function type for nodes will be (TupleTy ips) -> (tuple outputs)  *)
and buildFunTy: Lib.position -> LA.const_clocked_typed_decl list -> LA.clocked_typed_decl list -> tcType
  = fun pos args rets -> 
  let extractIp (_, _, ty, _, _) =  ty in
  let extractOp (_, _, ty, _) = ty in
  let ips =  List.map extractIp args in
  let ops = List.map extractOp rets in
  TArr (pos, TupleType (pos, ips), TupleType (pos, ops))

(** Compute Equality for lustre types  *)
and eqLustreType : tcContext -> LA.lustre_type -> LA.lustre_type -> bool tcResult = fun ctx t1 t2 ->
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
  (* Lustre V6 features *)
  | UserType (_, i1), UserType (_, i2) -> R.ok (i1 = i2)
  | AbstractType (_, i1), AbstractType (_, i2) -> R.ok (i1 = i2)
  | TupleType (_, tys1), TupleType (_, tys2) ->
     if List.length tys1 = List.length tys2
     then R.bind (R.seq (List.map2 (eqLustreType ctx) tys1 tys2)) (fun isEqs ->
              R.ok (List.fold_left (&&) true isEqs))
     else R.ok false
  | RecordType (_, tys1), RecordType (_, tys2) ->
     R.bind (R.seq (List.map2 (eqTypedIdent ctx)
                      (sortTypedIdent tys1)
                      (sortTypedIdent tys2))) (fun isEqs ->
        R.ok (List.fold_left (&&) true isEqs))
  | ArrayType (pos1, arr1), ArrayType (pos2, arr2) -> eqTypeArray ctx arr1 arr2 
  | EnumType (_, n1, is1), EnumType (_, n2, is2) ->
     R.ok (n1 = n2 && (List.fold_left (&&) true (List.map2 (=) (sortIdents is1) (sortIdents is2))))
  (* node/function type *)
  | TArr (_, argTy1, retTy1), TArr (_, argTy2, retTy2) ->
     R.bind (eqLustreType ctx argTy1 argTy2) (fun isEqArgTy ->
         if isEqArgTy
         then eqLustreType ctx retTy1 retTy2
         else R.ok false )
  (* special case for type synonyms *)
  | UserType (_, u), ty
    | ty, UserType (_, u) ->
     if memberTySyn ctx u
     then let tyAlias  = lookupTySyn ctx u in 
          eqLustreType ctx ty tyAlias
     else R.ok false
  | _, _ -> R.ok false

(** Checks if the constant is of type Int. This will be useful 
 * in evaluating array sizes that we need to have as constant integers
 * while declaring the array type *)
and isExprIntType: tcContext -> LA.expr -> bool  = fun ctx e ->
  R.safe_unwrap false (
      R.bind (inferTypeExpr ctx e) (fun ty -> 
          eqLustreType ctx ty (LA.Int (LustreAstHelpers.pos_of_expr e))))

and isExprArrayType: tcContext -> LA.expr -> bool  = fun ctx e ->
  R.safe_unwrap false
    (R.bind (inferTypeExpr ctx e) (fun ty ->
         match ty with
         | ArrayType _ -> R.ok true
         | _ -> R.ok false))
(** checks if all the variables in the expression are constants *)
and isExprOfConts: tcContext -> LA.expr -> bool = fun ctx e ->
  List.fold_left (&&) true (List.map (memberVal ctx) (LA.SI.elements (LustreAstHelpers.vars e)))
  
(** Compute type equality for [LA.typed_ident] *)
and eqTypedIdent: tcContext -> LA.typed_ident -> LA.typed_ident -> bool tcResult =
  fun ctx (_, i1, ty1) (_, i2, ty2) -> eqLustreType ctx ty1 ty2

(** Compute equality for [LA.ArrayType] *)
(** For now, we do not check the bounds for arrays. This introduces bugs similar to Issue #566. 
    https://github.com/kind2-mc/kind2/issues/566 *)
and eqTypeArray: tcContext -> (LA.lustre_type * LA.expr) -> (LA.lustre_type * LA.expr) -> bool tcResult
  = fun ctx (ty1, e1) (ty2, e2) -> eqLustreType ctx ty1 ty2

  
(** Evalute const expressions to an integer value.*)
(** TODO Make sure constant expressions do not have a cyclic dependency*)
and evalConstExpr: tcContext -> LA.expr -> int tcResult = fun ctx e ->
  match e with
  (* identifier and constants *)
  | Ident (pos, i) -> (try (evalConstExpr ctx (fst (lookupConst ctx i))) with
                    | Not_found -> typeError pos ("Identifier " ^ i ^ " does not have a bounded value"))  
                      
  | Const (pos, c) -> (match c with
                    | Num n -> R.ok (int_of_string n)
                    | _ -> typeError pos ("Constant " ^ Lib.string_of_t LA.pp_print_expr e
                                          ^ " is expected to have type type " ^ string_of_tcType (Int pos))) 
  (* more complex operations *)
  (* | UnaryOp of position * unary_operator * expr
   * | BinaryOp of position * binary_operator * expr * expr
   * | TernaryOp of position * ternary_operator * expr * expr * expr
   * | NArityOp of position * n_arity_operator * expr list
   * | ConvOp of position * conversion_operator * expr
   * | CompOp of position * comparison_operator * expr * expr
   * |  *)
  | _ -> typeError (LustreAstHelpers.pos_of_expr e)
           ("Cannot evaluate expression"
            ^ Lib.string_of_t LA.pp_print_expr e ^" to constant")
       
(* Compute the strongly connected components for type checking *)
let scc: LA.t -> LA.t list
  = fun decls -> [decls]
               
(* By this point, all the circularity should be resolved,
 * the top most declaration should be able to access 
 * the types of all the forward referenced indentifiers from the context*)
let rec typeCheckGroup: tcContext -> LA.t ->  unit tcResult list
  = fun ctx
  -> function
  | [] -> [R.ok ()]
  (* skip over type declarations and constDecls*)
  | (LA.TypeDecl _ :: rest) 
    | LA.ConstDecl _ :: rest -> typeCheckGroup ctx rest  
  | LA.NodeDecl (pos, ((i, _,_, _, _, _, _, _) as nodeDecl)) :: rest ->
     (checkTypeNodeDecl ctx nodeDecl (lookupTy ctx i)) :: typeCheckGroup ctx rest
  | LA.FuncDecl (pos, ((i, _,_, _, _, _, _, _) as nodeDecl)):: rest ->
     (checkTypeNodeDecl ctx nodeDecl (lookupTy ctx i)) :: typeCheckGroup ctx rest
  (* 
   * | 
   * | ContractNodeDecl of position * contract_node_decl
   * | NodeParamInst of position * node_param_inst *)
  | _ -> Lib.todo __LOC__
       
       
(* typecheck a list of independent groups using a global context*)
let typeCheckDeclGrps: tcContext -> LA.t list -> unit tcResult list = fun ctx decls -> 
  List.concat (List.map (typeCheckGroup ctx) decls)               

let typeCheckProgram: LA.t -> unit tcResult = fun prg ->
  R.bind (Log.log L_debug ("===============================================\n"
                           ^^ "Phase 1: Building TC Global Context\n"
                           ^^"===============================================\n")
        ; tcContextOf emptyContext prg) (fun tcCtx ->
      Log.log L_debug ("===============================================\n"
                       ^^ "Phase 1: Completed Building TC Global Context\n"
                       ^^ "TC Context\n%a\n"
                       ^^"===============================================\n")
        pp_print_tcContext  tcCtx
      ; prg |> scc |> typeCheckDeclGrps tcCtx |> reportTcResult)
    
    
(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)

