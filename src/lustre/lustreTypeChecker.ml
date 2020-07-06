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

module LA = LustreAst
module LC = LustreContext
module LAH = LustreAstHelpers
           
let todo = failwith "Unsupported"

exception Type_error of Lib.position * string           
let throwTypeError pos string = raise (Type_error (pos, string))
                      
(** Returns [Ok] if the typecheck/typeinference runs fine 
 * or reports an error at position with the error *)
type tcResult = Ok | Error of Lib.position * string

(** Module for identifier Map *)
module OrdIdent = struct
  type t = LA.ident
  let compare i1 i2 = Stdlib.compare i1 i2
end

(** Map for types with identifiers as keys *)
module TyMap = Map.Make(OrdIdent)

(** Simplified view of [LA.lustre_type]
 * This does not appear in the the interface file as we do not want it to escape the
 * typechecking phase  *)
type tcType  =
  (* Simple Types *)
  | Bool
  | Num    (* Num acts as an Int and Real also acts as a BV for approximating *)
  (* Function type of argument and return *)
  | Fun of tcType * tcType
  (* Arrays Tuples, ranges *)
  | IntRange of int * int
  | UserTy of LA.ident
  | TupleTy of tcType list
  (* lustre V6 types *)
  | AbstractTy of LA.ident
  | RecordTy of (LA.ident * tcType) list
  | ArrayTy of tcType * int
  | EnumTy of LA.ident option * (LA.ident list)

(** A constant should be evaluated to an integer *)
let evalToConstExp: LA.expr -> int = todo

(** Converts a [LA.lustre_type] to tcType *)
let rec toTcType: LA.lustre_type -> tcType
  = function
  | LA.Bool _ -> Bool
  | LA.Int _ 
  | LA.UInt8 _  
  | LA.UInt16 _ 
  | LA.UInt32 _  
  | LA.UInt64 _ 
  | LA.Int8 _ 
  | LA.Int16 _  
  | LA.Int32 _ 
  | LA.Int64 _ -> Num
  | LA.IntRange (_, e1, e2) -> IntRange (evalToConstExp e1, evalToConstExp e2)
  | LA.Real _-> Num
  | LA.UserType (_, i) -> UserTy i
  | LA.AbstractType (_, i) -> AbstractTy i
  | LA.TupleType (_, ids) -> TupleTy (List.map toTcType ids)
  | LA.RecordType (_, typedIds) -> RecordTy (List.map typedIdentToTcTuple typedIds) 
  | LA.ArrayType (_, (ty, e)) -> ArrayTy (toTcType ty, evalToConstExp e)
  | LA.EnumType (_, n, ids) -> EnumTy (n, ids) 
and typedIdentToTcTuple: LA.typed_ident -> (LA.ident * tcType) = function
    (_, i, ty) -> (i, toTcType ty) 

(** Typing context is nothing but a mapping of indentifier to its type *)
type tcContext = tcType TyMap.t
                            
let emptyContext = TyMap.empty

(* [typeerror] returns an [Error] of [tcResult] *)
let typeError pos err = Error (pos, err)

let lookup: tcContext -> LA.ident -> tcType =
  fun ctx i -> TyMap.find i ctx

let add: tcContext -> LA.ident -> tcType -> tcContext
  = fun ctx i ty -> TyMap.add i ty ctx 
             
let inferConstType: LA.constant -> tcType
  = function
     | Num _ -> Num
     | Dec _ -> Num
     | _ -> Bool

let inferUnaryOpType: LA.unary_operator -> tcType = function
  | LA.Not -> Fun (Bool, Bool)
  | LA.BVNot
  | LA.Uminus -> Fun (Num, Num)

let inferBinaryOp: LA.binary_operator -> tcType = function
  | LA.And | LA.Or | LA.Xor | LA.Impl
    -> Fun (Bool, Bool)
  | LA.Mod | LA. Minus | LA.Plus | LA. Div | LA.Times | LA.IntDiv
    | LA.BVAnd | LA.BVOr | LA.BVShiftL | LA.BVShiftR
    -> Fun (Num, Num) 
  

let inferTernaryOp: LA.ternary_operator -> tcType = todo

let inferNaryOp: LA.n_arity_operator -> tcType = todo

let inferTypeFun: tcContext -> LA.expr -> tcType = fun ctx e ->
  match e with
  | _ -> todo
  
(** Check if the function type of the [LA.expr] is the same as the exptected [tcType] 
  * where the free variables are given in [tcContext] *)
let rec checkTypeFun: tcContext -> LA.expr -> tcType -> tcResult
  = fun ctx f expTy ->
  match f with
  | UnaryOp (_, op, e) ->  todo
  | BinaryOp (_, op, e1, e2) -> todo
  | TernaryOp (_, op, e1, e2, e3) -> todo
  | NArityOp (_, op, es) -> todo
  | _ -> Error (LAH.pos_of_expr f, "Operator is not a funtion type")
  and
(** Infer the type of a [LA.expr] with the types of free variables given in [tcContext] *)
  inferTypeExpr: tcContext -> LA.expr -> tcType
  = fun ctx expr ->
  match expr with
  (* Identifiers *)
  | Ident (pos, i) ->
     (try(lookup ctx i) with
     | Not_found -> throwTypeError  pos ("Unbound Variable: " ^ i)) 
  | ModeRef (pos, ids) -> TupleTy (List.map (lookup ctx) ids)
  (* | RecordProject _ -> *) 
  (* | TupleProject of position * expr * expr *)
  (* Values *)
  | Const (pos, c) -> inferConstType c 
  (* Operators *)
  | UnaryOp _ 
  | BinaryOp _ 
  | TernaryOp _
  | NArityOp _ as op -> (inferTypeFun ctx op) 
    
         
   (* | ConvOp of position * conversion_operator * expr
   * | CompOp of position * comparison_operator * expr * expr
   * (\* Structured expressions *\)
   * | RecordExpr of position * ident * (ident * expr) list
   * | GroupExpr of position * group_expr * expr list
   * (\* Update of structured expressions *\)
   * | StructUpdate of position * expr * label_or_index list * expr
   * | ArrayConstr of position * expr * expr 
   * | ArraySlice of position * expr * (expr * expr) 
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
  | _ -> todo
(** Type checks an expression and returns [Ok] 
 * if the expected is the given type [tcType]  
 * returns an [Error] otherwise *)
and checkTypeExpr: tcContext -> LA.expr -> tcType -> tcResult
  = fun ctx expr expTy ->
  match expr with
  | Ident (pos, i) as ident ->
     if (inferTypeExpr ctx ident) = expTy
     then Ok else todo
  | _ -> Ok                                
       
             
let typingContextOfTyDecl: LA.type_decl -> tcContext
  = fun _ -> emptyContext

let typingContextOfConstDecl:  tcContext -> LA.const_decl -> (tcContext, tcResult) result
  = fun ctx -> function
  | LA.FreeConst (_, i, ty) -> Ok (add ctx i (toTcType ty))
  | LA.UntypedConst (_, i, expr) -> Ok (ctx)
  | LA.TypedConst (pos, i, expr, ty)
    ->  let expTy = toTcType ty in
        match (checkTypeExpr ctx expr expTy) with
        | Ok -> Ok(add ctx i expTy)
        | Error (pos, err) ->
           Error (typeError pos ("Declared type does not match the expression: " ^ err))
  
(* Compute the strongly connected components for type checking *)
(* TODO: Find strongly connected components, put them in a group *)
let scc: LA.t -> LA.t list
  = fun decls -> [decls]

let typingContextOf: LA.t -> tcContext
  = fun decls -> 
  let typingContextOf': tcContext -> LA.declaration -> tcContext
    = fun ctx decl ->
    match decl with
      | LA.TypeDecl  (_, tyDecl) -> typingContextOfTyDecl tyDecl
      | LA.ConstDecl (_, tyDecl) -> emptyContext
      | LA.NodeDecl  (_, nodeDecl) -> emptyContext
      | LA.FuncDecl  (_, nodeDecl) -> emptyContext
      | LA.ContractNodeDecl (_, cnrtNodeDecl) -> emptyContext
      | LA.NodeParamInst (_, nodeParamLst) -> emptyContext
    in List.fold_left typingContextOf' emptyContext decls 

let typeCheckGroup: (tcContext * LA.t) list -> tcResult list =
  fun ctxGrpPair -> List.map (fun _ -> Ok) ctxGrpPair 

let staticTypeAnalize: LustreAst.t -> tcResult list =
  fun decls ->
  (* Setup type checking contexts by first breaking the program 
   * into typing groups (strongly connected components) *)
  let typingGroups = scc decls in
  (* compute the base typing contexts of each typing group *)
  let tyGrpsCtxs = List.map typingContextOf typingGroups in
  let ctxAndDeclPair = List.combine tyGrpsCtxs typingGroups in
  typeCheckGroup ctxAndDeclPair  

(* Get the first error *)
let rec reportAnalysisResult: tcResult list -> tcResult = function
  | Error (pos,err) :: _ -> LC.fail_at_position pos err
  | Ok :: tl -> reportAnalysisResult tl
  | _ -> Ok


let typeCheckProgram: LA.t -> tcResult = fun prg ->
  prg |> staticTypeAnalize |> reportAnalysisResult 
    

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
