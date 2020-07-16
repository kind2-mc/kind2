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
module R = Res

let todo s = failwith ("Unsupported operation at " ^ s)

           
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
type tcType  =
  (* Named typed is identifier: type *)
  | TyVar of LA.ident
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

let rec pp_print_tcType: Format.formatter -> tcType -> unit
  = fun ppf ty ->
  match ty with
  | TyVar i -> Format.fprintf ppf "@[%a@]" LA.pp_print_ident i 
  | Bool -> Format.fprintf ppf "@[Bool@]"
  | Num  -> Format.fprintf ppf "@[Num@]"
  (* Function type of argument and return *)
  | Fun (argTy, retTy) -> Format.fprintf ppf "@[ @[%a@] @, -> @[%a@] @]" pp_print_tcType argTy pp_print_tcType retTy 
  (* Arrays Tuples, ranges *)
  | IntRange (mi, ma) -> Format.fprintf ppf "IntRange(%a, %a)" Format.pp_print_int mi Format.pp_print_int ma
  | UserTy i -> Format.fprintf ppf "UserType %a" LA.pp_print_ident i
  | TupleTy tys -> Format.fprintf ppf "@[TupleTy (%a)@]" (Lib.pp_print_list pp_print_tcType "*") tys
  (* lustre V6 types *)
  | AbstractTy i -> Format.fprintf ppf "AbstractType %a" LA.pp_print_ident i 
  | RecordTy fs -> let pp_print_field ppf = fun (i, ty) ->
                     Format.fprintf ppf "@[%a: %a@]" LA.pp_print_ident i pp_print_tcType ty in
                   Format.fprintf ppf "@[RecordTy {@ %a@ }@]" (Lib.pp_print_list pp_print_field ";@,") fs
  | ArrayTy (ty, size) -> Format.fprintf ppf "[@ %a ^ %a@ ]" pp_print_tcType ty Format.pp_print_int size
  | EnumTy (n, ids) ->
     let pp_print_enumname ppf = function
       | Some name -> LA.pp_print_ident ppf name
       | None -> () in
     Format.fprintf ppf "EnumType %a {@ %a@ }"
       pp_print_enumname n
       (Lib.pp_print_list LA.pp_print_ident ",@,") ids
     
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

  (** Monadic map operation *)
  let mapM: ('a -> 'b tcResult) -> 'a t -> 'b t tcResult =   
    fun m f -> todo __LOC__

  (** Pretty print type bindings*)
  let pp_print_type_binding ppf = fun i ty -> 
    Format.fprintf ppf "(%a:%a),@, " LA.pp_print_ident i pp_print_tcType ty

  (** Pretty print value bindings (used for constants)*)
  let pp_print_val_binding ppf = fun i v ->
    Format.fprintf ppf "(%a:->%a)" LA.pp_print_ident i LA.pp_print_expr v

  (** Pretty print type context *)
  let pp_print_tymap ppf = iter (pp_print_type_binding ppf)   
  (** Pretty print value store *)
  let pp_print_vstore ppf = iter (pp_print_val_binding ppf)

  (** Pretty print the complete type checker context*)
  let pp_print_tcContext ppf ctx
    = Format.fprintf ppf
        "TypeContext: {@ %a@ }\nValuecontext{@ %a @ }"
        pp_print_tymap (fst ctx)
        pp_print_vstore (snd ctx)

end

type tyStore = tcType IMap.t
type vStore = LA.expr IMap.t 

(** Type Checker context is a pair type store and a value store with identifier as its key *)
type tcContext = tyStore * vStore 
               

let emptyContext = (IMap.empty, IMap.empty)
                 

(** A constant should be evaluated to an integer *)
let rec evalToConstExp: LA.expr -> int
  = function
  | LA.Const (_, c) ->
     (match c with
      | LA.Num n -> int_of_string n
      | _ -> todo __LOC__)
  | LA.Ident (_, i) -> todo __LOC__
  | _  -> todo __LOC__

and toTcType: LA.lustre_type -> tcType
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
(** Converts a [LA.lustre_type] to tcType *)
                
(** [typeError] returns an [Error] of [tcResult] *)
let typeError pos err = R.error (pos, err)

let lookupTy: tcContext -> LA.ident -> tcType =
  fun ctx i -> IMap.find i (fst ctx)

let lookupVal: tcContext -> LA.ident -> LA.expr =
  fun ctx i -> IMap.find i (snd ctx)

let addTy: tcContext -> LA.ident -> tcType -> tcContext
  = fun ctx i ty -> (IMap.add i ty (fst ctx), snd ctx) 

let addVal: tcContext -> LA.ident -> LA.expr -> tcContext
  = fun ctx i e -> ((fst ctx), IMap.add i e (snd ctx)) 

let union: tcContext -> tcContext -> tcContext
  = fun ctx1 ctx2 -> ( IMap.union (fun k v1 v2 -> Some v1) (fst ctx1) (fst ctx2)
                     , IMap.union (fun k v1 v2 -> Some v1) (snd ctx1) (snd ctx2))

let singletonTy: LA.ident -> tcType -> tcContext =
  fun i ty -> addTy emptyContext i ty

let singletonVal: LA.ident -> LA.expr -> tcContext =
  fun i e -> addVal emptyContext i e
           
let memberTy: tcContext -> LA.ident -> bool
  = fun ctx i -> IMap.mem i (fst ctx)

let memberVal: tcContext -> LA.ident -> bool
  = fun ctx i -> IMap.mem i (snd ctx)

let inferTypeConst: LA.constant -> tcType
  = function
  | Num _ -> Num
  | Dec _ -> Num
  | _ -> Bool

       
let inferTypeUnaryOp: LA.unary_operator -> tcType tcResult = function
  | LA.Not -> R.ok (Fun (Bool, Bool))
  | LA.BVNot
    | LA.Uminus -> R.ok (Fun (Num, Num))

let inferTypeBinaryOp: LA.binary_operator -> tcType tcResult = function
  | LA.And | LA.Or | LA.Xor | LA.Impl
    -> R.ok (Fun (Bool, Fun(Bool, Bool)))
  | LA.Mod | LA. Minus | LA.Plus | LA. Div | LA.Times | LA.IntDiv
    | LA.BVAnd | LA.BVOr | LA.BVShiftL | LA.BVShiftR
    -> R.ok (Fun (Num, Fun(Num, Num))) 
     

let inferTypeTernaryOp: LA.ternary_operator -> tcType tcResult = function | _ -> todo __LOC__

let inferTypeNaryOp: LA.n_arity_operator -> tcType tcResult  = function | _ -> todo __LOC__

let inferTypeConvOp: LA.conversion_operator -> tcType tcResult = function
  | _ -> R.ok (Fun (Num, Num))

let inferTypeCompOp: LA.comparison_operator -> tcType tcResult = function
  | _ -> R.ok (Fun (Num, Fun (Num, Bool))) 

let inferTypeGrpExpr: LA.expr -> tcType = function | _ -> todo __LOC__
                                                        
(** Infer the type of a [LA.expr] with the types of free variables given in [tcContext] *)
let rec inferTypeExpr: tcContext -> LA.expr -> tcType tcResult
  = fun ctx expr ->
  match expr with
  (* Identifiers *)
  | LA.Ident (pos, i) ->
     (try (Ok (lookupTy ctx i)) with
      | Not_found -> typeError pos ("Unbound Variable: << " ^ i ^ " >>")) 
  | LA.ModeRef (pos, ids) -> todo __LOC__
  | LA.RecordProject _  -> todo __LOC__
  | LA.TupleProject (pos, e1, e2) -> todo __LOC__ 

  (* Values *)
  | LA.Const (_, c) -> R.ok (inferTypeConst c)

  (* Operator applications *)
  | LA.UnaryOp (pos, op, e) ->
     R.bind (inferTypeUnaryOp op) (fun ty ->
         match ty with
         | Fun (argTy, resTy) ->
            R.bind (checkTypeExpr ctx e argTy) (fun _ ->
                R.ok resTy)
         | fty -> typeError pos ("Unexpected unary operator type: "
                                 ^ string_of_tcType fty))
  | LA.BinaryOp (pos, bop, e1, e2) ->
     R.bind (inferTypeBinaryOp bop) (fun ty ->
         match ty with
         | Fun (argTy1, Fun (argTy2, resTy)) ->
            (R.bind (checkTypeExpr ctx e1 argTy1) (fun _ ->
                 R.bind (checkTypeExpr ctx e2 argTy2) (fun _ ->
                     R.ok resTy)))
         | fty -> typeError pos ("Unexpected binary operator type: "
                                 ^ string_of_tcType fty))
  | LA.TernaryOp (pos, top, con, e1, e2) ->
     R.bind (inferTypeExpr ctx con) (fun cTy ->
         if cTy != Bool
         then typeError pos ("Expected a boolean expression but found "
                             ^ string_of_tcType cTy)
         else R.bind (inferTypeExpr ctx e1) (fun e1Ty->
                  R.bind (checkTypeExpr ctx e1 e1Ty) (fun _ ->
                      R.ok e1Ty)))
  | LA.NArityOp _ -> todo __LOC__          (* One hot expression is not supported? *)    
  | LA.ConvOp (pos, cop, e) -> 
     R.bind (inferTypeConvOp cop) (fun ty ->
         match ty with
         | Fun (argTy, resTy) ->
            R.bind (checkTypeExpr ctx e argTy) (fun _ ->
                R.ok resTy)
         | fty -> typeError pos ("Unexpected conversion operator type: "
                                 ^ string_of_tcType fty))
  | LA.CompOp (pos, cop, e1, e2) ->
     R.bind (inferTypeCompOp cop) (fun ty ->
         match ty with
         | Fun (argTy1, Fun (argTy2, resTy)) ->
            (R.bind (checkTypeExpr ctx e1 argTy1) (fun _ ->
                 R.bind (checkTypeExpr ctx e2 argTy2) (fun _ -> 
                     R.ok resTy)))
         | fty -> typeError pos ("Unexpected comparison operator type: "
                                 ^ string_of_tcType fty))
    
  (* Structured expressions *)
  | LA.RecordExpr (pos, _, flds) ->
     (let rec inferFields = function
        | [] -> R.ok []
        | (i, e):: tl -> R.bind (inferFields tl) (fun tl' -> 
                             R.bind (inferTypeExpr ctx e) (fun ty -> 
                                 R.ok ((i, ty) :: tl')))
      in match inferFields flds with
         | Ok fldTys -> R.ok (RecordTy fldTys)
         | Error _ as err -> err)
    
  | LA.GroupExpr (pos, structType, exprs)  ->
     ( match structType with
       | LA.ExprList 
         | LA.TupleExpr -> R.bind (R.seq (List.map (inferTypeExpr ctx) exprs)) (fun tys ->
                               R.ok (TupleTy tys))
       | LA.ArrayExpr -> R.bind (R.seq (List.map (inferTypeExpr ctx) exprs)) (fun tys ->
                             if List.length tys > 0
                             then if List.for_all (fun t -> t = (List.hd tys)) tys 
                                  then R.ok (ArrayTy (List.hd tys, List.length tys))
                                  else typeError pos "All expressions must be of the same type in an Array"
                             else typeError pos "Array cannot be of size zero"))
    
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
  | Call (pos, i, args) ->
     let ty = lookupTy ctx i in
     let rec inferTypeNodeArgs: tcContext -> LA.expr list -> tcType -> tcType tcResult
       = fun ctx args ty -> 
       match (args, ty) with
       | arg :: [], Fun (argTy, resTy) ->
          R.bind (checkTypeExpr ctx arg argTy) (fun _ ->
              R.ok resTy)
       | arg :: [], ty' -> typeError pos "Arguments type mismatch"
       | arg :: args', Fun(argTy, resTy) ->
          R.bind (checkTypeExpr ctx arg argTy) (fun _ ->
              inferTypeNodeArgs ctx args' resTy)
       | _ -> typeError pos "panic while checking arguments"
     in
     inferTypeNodeArgs ctx args ty 
     
  (* | CallParam of position * ident * lustre_type list * expr list *)
  | _ -> todo __LOC__
(** Type checks an expression and returns [ok] 
 * if the expected is the given type [tcType]  
 * returns an [Error] otherwise *)
and checkTypeExpr: tcContext -> LA.expr -> tcType -> unit tcResult
  = fun ctx expr expTy ->
  match expr with
  (* Identifiers *)
  | Ident (pos, i) as ident ->
     R.bind (inferTypeExpr ctx ident) (fun ty ->
         if (ty = expTy)
         then R.ok ()
         else typeError pos ("Type mismatch: Indentifier " ^ i
                             ^ " does not match expected type "
                             ^ string_of_tcType expTy))
  | ModeRef (pos, ids) -> todo __LOC__
  | RecordProject _  -> todo __LOC__
  | TupleProject (pos, e1, e2) -> todo __LOC__ 
  (* Operators *)
  | UnaryOp (pos, op, e) ->
     R.bind (inferTypeUnaryOp op) (fun ty ->
         R.bind (inferTypeExpr ctx e) (fun argTy ->
             if ty = Fun (argTy, expTy)
             then R.ok ()
             else typeError pos ("Type mismatch: Cannot apply argument of type "
                                 ^ string_of_tcType argTy
                                 ^ " to operator of type "
                                 ^ string_of_tcType ty)))
  | BinaryOp (pos, op, e1, e2) ->
     R.bind (inferTypeBinaryOp op) (fun ty ->
         R.bind (inferTypeExpr ctx e1) (fun argTy1 ->
             R.bind (inferTypeExpr ctx e2) (fun argTy2 ->
                 if ty = Fun (argTy1, Fun (argTy2, expTy))
                 then R.ok ()
                 else typeError pos ("Type mismatch: Cannot apply arguments of type "
                                     ^ string_of_tcType argTy1
                                     ^ " and type " ^ string_of_tcType argTy2
                                     ^ " to operator of type " ^ string_of_tcType ty))))
    
  | LA.TernaryOp (pos, op, con, e1, e2) ->
     R.bind (inferTypeExpr ctx con) (fun ty ->
         if ty = Bool
         then R.bind (inferTypeExpr ctx e1) (fun ty1 ->
                  R.bind (inferTypeExpr ctx e2) (fun ty2 ->
                      if (ty1 = ty2)
                      then R.ok ()
                      else typeError pos
                             ("Type mismatch: "
                              ^ "Cannot unify type "
                              ^ string_of_tcType ty1
                              ^ "with type "
                              ^ string_of_tcType ty2)))
         else
           typeError pos ("Type mismatch: ITE condition expression "
                          ^ "Expected: " ^ string_of_tcType Bool
                          ^ "Found: " ^ string_of_tcType ty))
  | NArityOp _ -> todo __LOC__          (* One hot expression is not supported? *)    
  | ConvOp (pos, cvop, e) ->
     R.bind (inferTypeConvOp cvop) (fun cvopTy ->
         R.bind (inferTypeExpr ctx e) (fun exprTy ->
             if cvopTy = Fun (exprTy, expTy)
             then R.ok ()
             else typeError pos ("Type mismatch: cannot apply argument of type "
                                 ^ string_of_tcType exprTy
                                 ^ " to operator of type "
                                 ^ string_of_tcType cvopTy)))
  | CompOp (pos, cop, e1, e2) ->
     R.bind (inferTypeCompOp cop) (fun ty ->
         R.bind (inferTypeExpr ctx e1) (fun argTy1 ->
             R.bind (inferTypeExpr ctx e2) (fun argTy2 ->
                 if ty = Fun (argTy1, Fun (argTy2, expTy))
                 then R.ok()
                 else typeError pos
                        ("Type mismatch: cannot apply arguments of type "
                         ^ string_of_tcType argTy1
                         ^ " and " ^ string_of_tcType argTy2
                         ^ " to operator of type "
                         ^ string_of_tcType ty))))
  (* Values/Constants *)
  | Const (pos, c) -> R.ok ()

  (* Structured expressions *)
  | RecordExpr (pos, _, flds) -> todo __LOC__
  | GroupExpr _ -> todo __LOC__
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
  | Pre (pos, e) -> todo __LOC__
  (* | Last of position * ident
   * | Fby of position * expr * int * expr*)
  | Arrow (pos, e1, e2) -> R.bind(inferTypeExpr ctx e1) (fun ty1 ->
                               R.bind(inferTypeExpr ctx e2) (fun ty2 ->
                                   if ty1 = ty2
                                   then R.ok ()
                                   else typeError pos ("Type mismatch: Cannot unify "
                                                       ^ string_of_tcType ty1
                                                       ^ " and " ^ string_of_tcType ty2)))
  | _ -> todo __LOC__
       
and checkTypeConstDecl: tcContext -> LA.const_decl -> tcType -> unit tcResult =
  fun ctx constDecl expTy ->
  match constDecl with
  | FreeConst (pos, i, lusTy) -> let infTy = (lookupTy ctx i) in
                                 if infTy != expTy
                                 then typeError pos
                                        ("Type mismatch: Identifier "
                                         ^ i
                                         ^ " expected to have type " ^ string_of_tcType infTy
                                         ^ " but found type " ^ string_of_tcType expTy)
                                 else R.ok ()
  | UntypedConst (pos, i, exp) -> R.bind (inferTypeExpr ctx exp) (fun ty ->
                                      if expTy != ty
                                      then typeError pos
                                             ("Type mismatch: Identifier "
                                              ^ i
                                              ^ " expected to have type " ^ string_of_tcType expTy
                                              ^ " but found type " ^ string_of_tcType ty)
                                      else R.ok ()) 
                                
  | TypedConst (pos, i, exp, lusTy) -> R.bind (inferTypeExpr ctx exp) (fun infTy ->
                                           if expTy != infTy
                                           then typeError pos
                                                  ("Type mismatch: Identifier "
                                                   ^ i
                                                   ^ " expects type " ^ string_of_tcType expTy
                                                   ^ " but expression is of type " ^ string_of_tcType infTy)
                                           else R.ok ())  

and checkTypeNodeDecl: tcContext -> LA.node_decl -> tcType -> unit tcResult
  = fun ctx
        (i, isExtern, params, cclktydecls, clktydecls, localdecls, items, contract)
        expTy ->
  Log.log L_debug "TC node declaration{\n %a" LA.pp_print_ident i
  ; let extractArg: LA.const_clocked_typed_decl -> tcContext
      = fun  (_, i,ty, _, _) -> singletonTy i (toTcType ty) in
    let extractRet: LA.clocked_typed_decl -> tcContext
      = fun (_, i, ty, _) -> singletonTy i (toTcType ty) in
    let localVarTyBinding: LA.node_local_decl -> tcContext = function
      | LA.NodeConstDecl (pos, constDecls) ->
         (match constDecls with
          | FreeConst (pos, i, ty) -> singletonTy i (toTcType ty)
          | _ -> todo __LOC__)
      | LA.NodeVarDecl (pos, (_, i, ty, _)) -> singletonTy i (toTcType ty) 
    in

    (* if the node is extren, we will not have any body to typecheck so skip it *)
    if isExtern
    then ( Log.log L_debug "External Node, skipping type check"
         ; R.ok ())
    else (
      Log.log L_debug "Params: %a" LA.pp_print_node_param_list params
    ; Log.log L_debug "Local decls: %a" LA.pp_print_node_local_decl localdecls
    ; let localVars = List.fold_left union emptyContext (List.map localVarTyBinding localdecls) in

      (* These are inputs to the node *)
      let ips = List.fold_left union emptyContext (List.map extractArg cclktydecls) in
      Log.log L_debug "Const clocked typed decls: %a\nips:%a"
        (Lib.pp_print_list LA.pp_print_const_clocked_typed_ident ",@,") cclktydecls
        IMap.pp_print_tcContext ips
      
      (* These are outputs of the node *)
      ; let ops = List.fold_left union emptyContext (List.map extractRet clktydecls) in
        Log.log L_debug "Clocked typed decls: %a\nops:%a"
          (Lib.pp_print_list LA.pp_print_clocked_typed_ident ",@,") clktydecls
          IMap.pp_print_tcContext ops

        ; let localCtx = union ctx               (* global context *)
                           (union localVars      (* declared local variables *)
                              (union ips ops))   (* input and output type vars *)
          in
          Log.log L_debug "Local Typing Context {%a}" IMap.pp_print_tcContext localCtx
          ; let doNodeEqn ctx eqn = match eqn with
              | LA.Assert (_, e) ->
                 R.bind
                   ( Log.log L_debug "Assertion (skipped)"
                   ; inferTypeExpr ctx e) (fun _ -> R.ok ())
              | LA.Equation (_, lhs, expr) as eqn ->
                 R.bind
                   ( Log.log L_debug "Node Equation: %a" LA.pp_print_node_body eqn
                   ; inferTypeExpr ctx expr) (fun ty ->
                     checkTypeStructDef ctx lhs ty)
              | LA.Automaton (pos, _, _, _) ->
                 typeError pos "Typechecker failed. Unsupported feature Automation."
            in
            let rec doItems: tcContext -> LA.node_item list -> unit tcResult =
              fun ctx its -> match its with
                             | [] -> R.ok ()
                             | (LA.Body eqn as body) :: rest ->
                                R.bind ( Log.log L_debug "Node Item: %a" LA.pp_print_node_item body
                                       ; doNodeEqn ctx eqn) (fun _ ->
                                    doItems ctx rest)
                             | (LA.AnnotMain _ as ann) :: rest ->
                                Log.log L_debug "Node Item (skipped): %a" LA.pp_print_node_item ann
                               ; doItems ctx rest
                             | (LA.AnnotProperty _ as ann) :: rest ->
                                Log.log L_debug "Node Item (skipped): %a" LA.pp_print_node_item ann
                               ; doItems ctx rest 
            in

            let r = doItems localCtx items in
            Log.log L_debug "Node TC done }"
            ; r
    )
    
(* The structure of the left hand side of the equation 
 * should match the type of the right hand side expression *)
and checkTypeStructDef: tcContext -> LA.eq_lhs -> tcType -> unit tcResult
  = fun ctx (StructDef (pos, lhss)) ty ->
  if (List.length lhss) > 1
  then todo __LOC__
  else
    assert (List.length lhss = 1)
  ; let lhs = List.hd lhss in
    match lhs with
    | SingleIdent (pos, i) -> let expTy = lookupTy ctx i in
                              if expTy = ty
                              then R.ok()
                              else typeError pos ("Type mismatch. Expected type"
                                                  ^ string_of_tcType expTy
                                                  ^ " but found type "
                                                  ^ string_of_tcType ty)
    | _ -> todo __LOC__
         

(** Obtain a global typing context *)
and tcContextOf: tcContext -> LA.t -> tcContext tcResult = fun ctx ->
  let tcContextOf': tcContext -> LA.declaration -> tcContext tcResult
    = fun ctx decl ->
    match decl with
    | LA.ConstDecl (_, tyDecl) -> tcCtxConstDecl ctx tyDecl
    | LA.NodeDecl (pos, nodeDecl) -> tcCtxOfNodeDecl pos ctx nodeDecl 
    | _ -> R.ok ctx

  in function 
  | [] -> R.ok ctx
  | d :: tl -> R.bind ( Log.log L_debug
                          "Extracting typing context from declaration: %a"
                          LA.pp_print_declaration d
                      ; tcContextOf' ctx d) (fun ctx' ->
                   R.bind (
                       Log.log L_debug "%a" IMap.pp_print_tcContext (union ctx' ctx)
                     ; tcContextOf (union ctx' ctx) tl) (fun c -> 
                       R.ok c))
and tcCtxTyDecl: tcContext -> LA.type_decl -> tcContext
  = fun ctx _ -> ctx
(** Shadow the old binding with the new decl *)
and tcCtxConstDecl: tcContext -> LA.const_decl -> tcContext tcResult
  = fun ctx -> function
            | LA.FreeConst (_, i, ty) ->
               R.ok (addTy ctx i (toTcType ty))
            | LA.UntypedConst (_, i, expr) ->
               R.ok (addVal ctx i expr)
            | LA.TypedConst (pos, i, expr, ty)
              ->  let expTy = toTcType ty in
                  R.bind (checkTypeExpr ctx expr expTy) (fun _ ->
                      R.ok (addTy ctx i expTy))

(** get the type signature of node or a function *)
and tcCtxOfNodeDecl: Lib.position -> tcContext -> LA.node_decl -> tcContext tcResult
  = fun pos ctx (i, _, _ , ip, op,_ ,_ ,_) ->
  if (memberTy ctx i)
  then typeError pos ("Duplicate node detected with name: " ^ i)
  else R.ok (addTy ctx i (buildFunTy ip op))
  
(** Function type for nodes will be (TupleTy ips) -> (tuple outputs)  *)
and  buildFunTy: LA.const_clocked_typed_decl list -> LA.clocked_typed_decl list -> tcType
  = fun args rets -> 
  let extractIp (_, _, ty, _, _) = (toTcType ty) in
  let extractOp (_, _, ty, _) = (toTcType ty) in
  let ips =  List.map extractIp args in
  let ops = List.map extractOp rets in
  Fun (TupleTy ips, TupleTy ops)

(** Evalute const expressions to a value *)
and evalConstExpr: LA.expr IMap.t -> LA.expr -> LA.expr tcResult = fun ctx ->
  function
  (* identifier and constants *)
  | Ident (_, i) -> R.ok (IMap.find i ctx)
  | Const _ as c -> R.ok c
  (* more complex operations *)
  (* | UnaryOp of position * unary_operator * expr
   * | BinaryOp of position * binary_operator * expr * expr
   * | TernaryOp of position * ternary_operator * expr * expr * expr
   * | NArityOp of position * n_arity_operator * expr list
   * | ConvOp of position * conversion_operator * expr
   * | CompOp of position * comparison_operator * expr * expr
   * 
   * |  *)
  | _ -> todo __LOC__
       
and evalConstExprs: LA.expr IMap.t -> (LA.expr IMap.t) tcResult = fun vstore
  ->  IMap.mapM (fun e -> evalConstExpr vstore e) vstore

and propogateConsts: tcContext -> tcContext tcResult = fun (tyCtx, valCtx) ->
  R.bind (evalConstExprs valCtx) (fun vctx' ->
      R.ok (tyCtx, vctx'))

(* Compute the strongly connected components for type checking *)
(* TODO: Find strongly connected components, put them in a group *)
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
  (*    match dec with
   * | FuncDecl of position * node_decl
   * | ContractNodeDecl of position * contract_node_decl
   * | NodeParamInst of position * node_param_inst *)
  | _ -> todo __LOC__
       
       
(* typecheck a list of independent groups using a global context*)
let typeCheckDeclGrps: tcContext -> LA.t list -> unit tcResult list = fun ctx decls -> 
  List.concat (List.map (typeCheckGroup ctx) decls)               

let typeCheckProgram: LA.t -> unit tcResult = fun prg ->
  R.bind (tcContextOf emptyContext prg) (fun tcCtx ->
      Log.log L_debug "Type Checker Context\n====\n%a\n====\n" IMap.pp_print_tcContext  tcCtx
                                         ; R.bind (propogateConsts tcCtx) (fun p ->
                                               Log.log L_debug "Global Context\n====\n%a\n====\n" IMap.pp_print_tcContext p; 
                                               prg |> scc |> typeCheckDeclGrps p |> reportTcResult)) 
    
    
(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)

