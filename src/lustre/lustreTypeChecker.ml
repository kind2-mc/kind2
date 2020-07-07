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
module R =  Stdlib.Result
(* module LAH = LustreAstHelpers *)
           
let todo s = failwith ("Unsupported operation at " ^ s)

(* exception Type_error of Lib.position * string           
 * let throwTypeError pos string = raise (Type_error (pos, string)) *)
                      
(** Returns [ok] if the typecheck/typeinference runs fine 
 * or reports an error at position with the error *)
type 'a tcResult = ('a, Lib.position * string) result

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

let rec to_string: tcType -> string = function
  | Bool -> "Bool"
  | Num  -> "Num"
  (* Function type of argument and return *)
  | Fun (argTy, retTy) -> to_string argTy ^ " -> " ^ to_string retTy
  (* Arrays Tuples, ranges *)
  | IntRange (mi, ma) -> "IntRange(" ^ string_of_int mi ^ "," ^ string_of_int ma ^ ")" 
  | UserTy i -> "UserType " ^ i
  | TupleTy tyLst ->
     (List.fold_left (fun s ty -> s ^ ", " ^ (to_string ty)) "Tuple (" tyLst) ^ ")"
  (* lustre V6 types *)
  | AbstractTy i -> "AbstractType " ^ i 
  | RecordTy fs ->
     (List.fold_left (fun s (i, ty) -> s ^ ", " ^ i ^";"^ (to_string ty))
        "RecordType (" fs) ^ ")"
  | ArrayTy (ty, size) -> "["^ to_string ty ^ "^" ^ string_of_int size ^"]"
  | EnumTy (n, ids) -> "EnumType "
                       ^ (match n with
                        | Some n' -> n'
                        | None -> "" )
                       ^ "{"
                       ^ List.fold_left (fun s i -> s ^ ", " ^ i) "" ids
                       ^ "}" 
                     
  
(** A constant should be evaluated to an integer *)
let evalToConstExp: LA.expr -> int = function _  -> todo __LOC__

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
let typeError pos err = R.error (pos, err)

let lookup: tcContext -> LA.ident -> tcType =
  fun ctx i -> TyMap.find i ctx

let add: tcContext -> LA.ident -> tcType -> tcContext
  = fun ctx i ty -> TyMap.add i ty ctx 

let union: tcContext -> tcContext -> tcContext
  = fun ctx1 ctx2 -> TyMap.merge (fun k v1 v2 -> v1) ctx1 ctx2
                  
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
  

let inferTernaryOp: LA.ternary_operator -> tcType = function | _ -> todo __LOC__

let inferNaryOp: LA.n_arity_operator -> tcType = function | _ -> todo __LOC__

let inferTypeConvOp: LA.conversion_operator -> tcType = function
  | _ -> Fun (Num, Num)

let inferTypeCompOp: LA.comparison_operator -> tcType = function
  | _ -> Fun (Num, Fun (Num, Bool)) 

let inferTypeGrpExpr: LA.expr -> tcType = function | _ -> todo __LOC__
                                        
(** Infer the type of a [LA.expr] with the types of free variables given in [tcContext] *)
let rec inferTypeExpr: tcContext -> LA.expr -> tcType tcResult
  = fun ctx expr ->
  match expr with
  (* Identifiers *)
  | Ident (pos, i) ->
     (try (Ok (lookup ctx i)) with
      | Not_found -> typeError pos ("Unbound Variable: " ^ i)) 
  (* | ModeRef (pos, ids) -> ok (TupleTy (List.map (lookup ctx) ids)) *)
  (* | RecordProject _ -> *) 
  (* | TupleProject of position * expr * expr *)

  (* Values *)
  | Const (_, c) -> R.ok (inferConstType c)

  (* Operator applications *)
  | UnaryOp (pos, op, e) ->
     (match (inferUnaryOpType op) with
      | Fun (argTy, resTy) ->
         R.bind (checkTypeExpr ctx e argTy) (fun _ ->
             R.ok resTy)
      | fty -> typeError pos ("Unexpected unary operator type: " ^ to_string fty))
  | BinaryOp (pos, bop, e1, e2) ->
     (match (inferBinaryOp bop) with
      | Fun (argTy1, Fun (argTy2, resTy)) ->
         (R.bind (checkTypeExpr ctx e1 argTy1) (fun _ ->
              R.bind (checkTypeExpr ctx e2 argTy2) (fun _ ->
                  R.ok resTy)))
      | fty -> typeError pos ("Unexpected binary operator type: " ^ to_string fty))
  | TernaryOp (pos, top, e1, e2, e3) ->
     (match (inferTernaryOp top) with
      | Fun (argTy1, Fun (argTy2, (Fun (argTy3, resTy)))) -> 
         (R.bind (checkTypeExpr ctx e1 argTy1) (fun _ ->
              R.bind (checkTypeExpr ctx e2 argTy2) (fun _ ->
                  R.bind (checkTypeExpr ctx e3 argTy3) (fun _ ->
                      R.ok resTy))))
      | fty -> typeError pos ("Unexpected ternary operator type: " ^ to_string fty))
  | NArityOp _ -> todo __LOC__          (* One hot expression is not supported? *)    
  | ConvOp (pos, cop, e) ->
     (match (inferTypeConvOp cop) with
      | Fun (argTy, resTy) ->
         R.bind (checkTypeExpr ctx e argTy) (fun _ ->
             R.ok resTy)
      | fty -> typeError pos ("Unexpected conversion operator type: " ^ to_string fty))
  | CompOp (pos, cop, e1, e2) ->
     (match (inferTypeCompOp cop) with
      | Fun (argTy1, Fun (argTy2, resTy)) ->
         (R.bind (checkTypeExpr ctx e1 argTy1) (fun _ ->
              R.bind (checkTypeExpr ctx e2 argTy2) (fun _ -> 
                  R.ok resTy)))
      | fty -> typeError pos ("Unexpected comparison operator type: " ^ to_string fty))
                            
  (* Structured expressions *)
  | RecordExpr (pos, _, flds) ->
     (let rec inferFields = function
        | [] -> R.ok []
        | (i, e):: tl -> R.bind (inferFields tl) (fun tl' -> 
                               R.bind (inferTypeExpr ctx e) (fun ty -> 
                                   R.ok ((i, ty) :: tl')))
    in match inferFields flds with
    | R.Ok fldTys -> R.ok (RecordTy fldTys)
    | Error _ as err -> err)
      
   | GroupExpr _ as ge -> R.ok (inferTypeGrpExpr ge)
  (* Update of structured expressions *)
  (* | StructUpdate of position * expr * label_or_index list * expr
   * | ArrayConstr of position * expr * expr 
   * | ArraySlice of position * expr * (expr * expr) 
   * | ArrayConcat of position * expr * expr *)
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
  (* | Pre of position * expr
   * | Last of position * ident
   * | Fby of position * expr * int * expr
   * | Arrow of position * expr * expr *)
  (* Node calls *)
  (* | Call of position * ident * expr list
   * | CallParam of position * ident * lustre_type list * expr list *)
  | _ -> todo __LOC__

  (** Type checks an expression and returns [ok] 
   * if the expected is the given type [tcType]  
   * returns an [Error] otherwise *)
  and checkTypeExpr: tcContext -> LA.expr -> tcType -> unit tcResult
    = fun ctx expr expTy ->
    match expr with
    | Ident (pos, i) as ident ->
       (match (inferTypeExpr ctx ident) with
        | Ok ty -> (if (ty = expTy)
                    then R.ok ()
                    else typeError pos ("Indentifier " ^ i
                                        ^ " does not match expected type"
                                        ^ to_string expTy))
        | Error _ as err -> err)
    | UnaryOp (pos, op, _) ->
       (match (inferUnaryOpType op) with
        | Fun (argTy, retTy) ->
           if expTy = argTy then R.ok ()
           else typeError pos ("Expected type " ^ to_string expTy ^ " but found type " ^ to_string argTy)
        | _ -> typeError pos ("Unexpted Operator type"))
    | _ -> todo __LOC__
       
             
let typingContextOfTyDecl: LA.type_decl -> tcContext
  = function
  | _ -> emptyContext

(** Shadow the old binding with the new type *)
let typingContextOfConstDecl:  tcContext -> LA.const_decl -> tcContext tcResult
  = fun ctx -> function
  | LA.FreeConst (_, i, ty) -> R.ok (add ctx i (toTcType ty))
  | LA.UntypedConst (_, i, expr) -> R.ok ctx
  | LA.TypedConst (pos, i, expr, ty)
    ->  let expTy = toTcType ty in
        R.bind (checkTypeExpr ctx expr expTy) (fun _ ->
            R.ok (add ctx i expTy))
  
(* Compute the strongly connected components for type checking *)
(* TODO: Find strongly connected components, put them in a group *)
let scc: LA.t -> LA.t list
  = fun decls -> [decls]

let rec typingContextOf: LA.t -> tcContext tcResult
  = let typingContextOf': tcContext -> LA.declaration -> tcContext tcResult
    = fun ctx decl ->
    match decl with
      | LA.ConstDecl (_, tyDecl) -> typingContextOfConstDecl ctx tyDecl
      | _ -> R.ok emptyContext
    in function 
    | [] -> R.ok emptyContext
    | d :: tl -> R.bind (typingContextOf tl) (fun ctx' ->
                     R.bind (typingContextOf' ctx' d) (fun ctx -> 
                         R.ok ctx))

let typeCheckGroup: tcContext -> LA.t ->  unit tcResult
  = fun ctx grp -> 
  R.ok ()
               
(* typecheck a list of groups *)
let rec typeCheckDeclGrps: LA.t list -> unit tcResult list =
  function
  | [] -> []
  | grp :: grps ->
     R.bind (typingContextOf grp) (fun ctx ->
         typeCheckGroup ctx grp) :: typeCheckDeclGrps grps
                 
(* Get the first error *)
let rec reportTcResult: unit tcResult list -> unit tcResult = function
  | Error (pos,err) :: _ -> LC.fail_at_position pos err
  | R.Ok () :: tl -> reportTcResult tl
  | _ -> R.ok () 


let typeCheckProgram: LA.t -> unit tcResult = fun prg ->
  prg |> scc |> typeCheckDeclGrps |> reportTcResult 
    

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
