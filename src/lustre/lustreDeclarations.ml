(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

open Lib
open Lib.ReservedIds
open LustreReporting

module A = LustreAst
module H = LustreAstHelpers
         
module I = LustreIdent

module D = LustreIndex

module E = LustreExpr

module N = LustreNode
module Contract = LustreContract

module C = LustreContext

module S = LustreSimplify
module G = LustreGlobals

module SVS = StateVar.StateVarSet

module Deps = LustreDependencies
module QId = LustreAstIdent

(*********************************************)
(* Auxiliary functions for automata encoding *)
(*********************************************)

(* Useful information for encoding automata *)
type automaton_info = {
  (* Name of the automaton *)
  auto_name : string;

  (* Inputs of the node in which the automaton appears *)
  node_inputs : A.const_clocked_typed_decl list;

  (* Outputs of the automaton (declared with returns) *)
  auto_outputs : A.clocked_typed_decl list;

  (* Other node variables *)
  other_vars : A.const_clocked_typed_decl list;

  (* Memories for [last] expressions, passed as inputs to the automaton
     states *)
  lasts_inputs : A.const_clocked_typed_decl list;

  (* Enumerated datatype to represent states *)
  states_lustre_type : A.lustre_type;

  (* Local variables used to encode the internal state of the automaton *)
  i_state_selected : A.ident;
  i_restart_selected : A.ident;
  i_state : A.ident;
  i_restart : A.ident;
}


exception Found_auto_out of A.clocked_typed_decl
exception Found_last_ty of A.lustre_type


let fail_or_warn =
  if Flags.lus_strict () then
    fail_at_position else warn_at_position


(* Create a new name for anonymous automata *)
let fresh_automaton_name =
  let cpt = ref 0 in
  fun scope ->
    incr cpt;
    String.concat "." (scope @ ["automaton" ^ string_of_int !cpt])


let rec replace_lasts_branch allowed name acc = function
  | A.Target _ as t -> t, acc
  | A.TransIf (pos, e, br, None) as t ->
    let e', acc = H.replace_lasts allowed name acc e in
    let br', acc = replace_lasts_branch allowed name acc br in
    if e' == e && br' == br then t, acc
    else A.TransIf (pos, e', br', None), acc
  | A.TransIf (pos, e, br, Some br2) as t ->
    let e', acc = H.replace_lasts allowed name acc e in
    let br', acc = replace_lasts_branch allowed name acc br in
    let br2', acc = replace_lasts_branch allowed name acc br2 in
    if e' == e && br' == br && br2' = br2 then t, acc
    else A.TransIf (pos, e', br', Some br2'), acc

let replace_lasts_transition allowed name acc = function
  | None -> None, acc
  | Some (pos, br) ->
    let br, acc = replace_lasts_branch allowed name acc br in
    Some (pos, br), acc

let rec replace_lasts_state allowed name acc = function
  | A.State (pos, state_c, init, locals, eqs, unless_tr, until_tr) ->
    let unless_tr, acc = replace_lasts_transition allowed name acc unless_tr in
    let until_tr, acc = replace_lasts_transition allowed name acc until_tr in
    let eqs, acc = List.fold_left (fun (eqs, acc) -> function
        | A.Assert (pos, e) as eq ->
          let e', acc' = H.replace_lasts allowed name acc e in
          if e == e' then eq :: eqs, acc
          else A.Assert (pos, e') :: eqs, acc'
        | A.Equation (pos, lhs, e) as eq ->
          let e', acc' = H.replace_lasts allowed name acc e in
          if e == e' then eq :: eqs, acc
          else A.Equation (pos, lhs, e') :: eqs, acc'
        | A.Automaton (pos, aname, states, returns) ->
          let rstates, acc = List.fold_left (fun (rstates, acc) st ->
              let st, acc = replace_lasts_state allowed name acc st in
              st :: rstates, acc
            ) ([], acc) states in
          A.Automaton (pos, aname, List.rev rstates, returns) :: eqs, acc
      ) ([], acc) eqs
    in
    let eqs = List.rev eqs in
    A.State (pos, state_c, init, locals, eqs, unless_tr, until_tr), acc


let type_of_last inputs outputs locals l =
  try
    List.iter (fun (_, i, ty, _, _) ->
        if i = l then raise (Found_last_ty ty)
      ) inputs;
    List.iter (fun (_, i, ty, _) ->
        if i = l then raise (Found_last_ty ty)
      ) outputs;
    List.iter (function
        | A.NodeConstDecl (_, (A.FreeConst (_, i, ty) |
                               A.TypedConst (_, i, _, ty))) ->
          if i = l then raise (Found_last_ty ty)
        | A.NodeConstDecl (_, A.UntypedConst (pos, i, e)) ->
          fail_at_position pos ("Please add type of "^ QId.to_string i)
        | A.NodeVarDecl (_, (_, i, ty, _)) ->
          if i = l then raise (Found_last_ty ty)
      ) locals;
    raise Not_found
  with Found_last_ty ty -> ty


let allowed_lasts inputs outputs locals =
  List.map (fun (_, i, _, _, _) -> i) inputs
  @ List.map (fun (_, i, _, _) -> i) outputs
  @ List.map (function
      | A.NodeConstDecl (_,
                         (A.FreeConst (_, i, _) |
                          A.TypedConst (_, i, _, _) |
                          A.UntypedConst (_, i, _))) -> i
      | A.NodeVarDecl (_, (_, i, _, _)) -> i
    ) locals


(* Infer defined streams of an automaton *)


let in_locals i' locals = List.exists (function
    | A.NodeConstDecl (_,
                       (A.FreeConst (_, i, _) |
                        A.TypedConst (_, i, _, _) |
                        A.UntypedConst (_, i, _)))
    | A.NodeVarDecl (_, (_, i, _, _)) -> i = i'
  ) locals
  

let rec defined_vars_struct_item locals acc = function
  | A.SingleIdent (_, i)
  | A.ArrayDef (_, i, _)
  | A.TupleSelection (_, i, _)
  | A.FieldSelection (_, i, _)
  | A.ArraySliceStructItem (_, i, _) ->
    if in_locals i locals then acc else QId.IdentSet.add i acc
  | A.TupleStructItem (_, l) ->
    List.fold_left (defined_vars_struct_item locals) acc l

let defined_vars_lhs locals acc = function
  | A.StructDef (_, l) ->
    List.fold_left (defined_vars_struct_item locals) acc l


let rec defined_vars_equation locals acc = function
  | A.Assert _ -> acc
  | A.Automaton (_, _, _, A.Given returns) ->
    List.fold_left (fun acc i -> QId.IdentSet.add i acc) acc returns
  | A.Automaton (_, _, states, A.Inferred) ->
    List.fold_left (fun acc (A.State (_, _, _, l', eqs, _, _)) ->
        List.fold_left
          (defined_vars_equation (List.rev_append l' locals)) acc eqs
      ) acc states
  | A.Equation (_, lhs, _) -> defined_vars_lhs locals acc lhs
  

let defined_vars_eqs eqs =
  List.fold_left (defined_vars_equation []) QId.IdentSet.empty eqs
  |> QId.IdentSet.elements


(* Collect inputs used in equaltions and automatons. This is to create
   auxiliary nodes for states with a minimal number of inputs *)
  
let rec used_inputs_expr inputs acc =
  let open A in
  function
  | Const _ | ModeRef _ -> acc

  | Ident (_, i) | Last (_, i) -> QId.IdentSet.add i acc

  | TupleProject (_, e, _) | RecordProject (_, e, _) | ConvOp (_,_,e) | UnaryOp (_, _, e)
  | Current (_, e) | When (_, e, _) | Quantifier (_, _, _, e) ->
    used_inputs_expr inputs acc e

  | BinaryOp (_, _, e1, e2) | CompOp (_, _, e1, e2)
  | ArrayConstr (_, e1, e2) | ArrayConcat (_, e1, e2) | ArrayIndex (_, e1, e2) ->
    used_inputs_expr inputs (used_inputs_expr inputs acc e2) e1
    
  | TernaryOp (_, _, e1, e2, e3) | ArraySlice (_, e1, (e2, e3)) ->
    used_inputs_expr inputs
      (used_inputs_expr inputs (used_inputs_expr inputs acc e1) e2) e3
  
  | GroupExpr (_, _, l) | NArityOp (_, _, l)
  | Call (_, _, l) | CallParam (_, _, _, l) ->
    List.fold_left (used_inputs_expr inputs) acc l

  | Merge (_, _, l) ->
    List.fold_left (fun acc (_, e) -> used_inputs_expr inputs acc e) acc l

  | RestartEvery (_, _, l, e) ->
    List.fold_left (used_inputs_expr inputs) acc (e :: l)

  | Activate (_, _, e, r, l) ->
    List.fold_left (used_inputs_expr inputs) acc (e :: r :: l)

  | Condact (_, e, r, _, l1, l2) ->
    List.fold_left (used_inputs_expr inputs) acc (e :: r :: l1 @ l2)

  | RecordExpr (_, _, ie) ->
    List.fold_left (fun acc (_, e) -> used_inputs_expr inputs acc e) acc ie

  | StructUpdate (_, e1, li, e2) ->
    let acc = used_inputs_expr inputs (used_inputs_expr inputs acc e1) e2 in
    List.fold_left (fun acc -> function
        | Label _ -> acc
        | Index (_, e) -> used_inputs_expr inputs acc e
      ) acc li
    
  | Fby (_, e1, _, e2) ->
    used_inputs_expr inputs (used_inputs_expr inputs acc e1) e2

  | Pre (pos, e) -> used_inputs_expr inputs acc e

  | Arrow (pos, e1, e2) ->
    used_inputs_expr inputs (used_inputs_expr inputs acc e1) e2

let rec used_inputs_equation inputs acc = function
  | A.Assert (_, e) | A.Equation (_, _, e) -> used_inputs_expr inputs acc e
  | A.Automaton (_, _, states, _) ->
    List.fold_left (used_inputs_state inputs) acc states

and used_inputs_transbr inputs acc = function
  | A.Target _ -> acc
  | A.TransIf (_, e, br, t) ->
    used_inputs_trans inputs
      (used_inputs_transbr inputs
         (used_inputs_expr inputs acc e)
         br)
      t

and used_inputs_trans inputs acc = function
  | None -> acc
  | Some br -> used_inputs_transbr inputs acc br

and used_inputs_trans' inputs acc = function
  | None -> acc
  | Some (_, br) -> used_inputs_transbr inputs acc br

and used_inputs_state inputs acc = function
  | A.State (_, _, _, _, eqs, unl, uti) ->
    used_inputs_trans' inputs
      (used_inputs_trans' inputs
         (used_inputs_eqs inputs acc eqs) unl)
      uti

and used_inputs_eqs inputs acc eqs =
  List.fold_left (used_inputs_equation inputs) acc eqs


(* Collect inputs used in equaltions and automatons. This is to create
   auxiliary nodes for states with a minimal number of inputs *)
let used_inputs inputs eqs =
  let u = used_inputs_eqs inputs QId.IdentSet.empty eqs in
  List.filter (fun (_, i, _, _, _) -> QId.IdentSet.mem i u) inputs


(*************************************)
(* Auxiliary functions for contracts *)
(*************************************)


(** Returns an option of the output state variables mentioned in the current
state of a lustre expression. *)
let contract_check_no_output ctx pos expr =
  let outputs =
    LustreContext.outputs_of_current_node ctx
  in
  let outputs =
    D.fold ( fun _ elm set -> SVS.add elm set ) outputs SVS.empty
  in
  match C.trace_svars_of ctx expr with
  | Some coi -> SVS.inter outputs coi |> SVS.elements
  | None -> failwith "unreachable"


(* ********************************************************************** *)
(* Parse constants                                                        *)
(* ********************************************************************** *)

(* Add declaration of constant to context *)
let eval_const_decl ?(ghost = false) ctx = function

  (* Declaration of a free constant *)
  | A.FreeConst (pos, i, ty) ->

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident (QId.to_string i) in

    (* Evaluate type expression *)
    let tyd = S.eval_ast_type ctx ty in 

    let vt, ctx = 
      D.fold 
        (fun i ty (vt, ctx) ->
           let state_var, ctx = 
             C.mk_state_var 
               ?is_input:(Some false)
               ?is_const:(Some true)
               ?for_inv_gen:(Some true)
               ~shadow:ghost
               ctx
               (C.scope_of_context ctx @ I.user_scope)
               ident
               i
               ty
               None
           in
           let v = Var.mk_const_state_var state_var in
           D.add i v vt, ctx)
        tyd
        (D.empty, ctx)
    in

    C.add_free_constant ctx ident vt;

    ctx
    
  (* Declaration of a typed or untyped constant *)
  | A.UntypedConst (pos, i, expr) 
  | A.TypedConst (pos, i, expr, _) as const_decl ->

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident (QId.to_string i) in

    if
      
      (try 

         (* Identifier must not be declared, unless it is a ghost
            constant which shadows declared constants *)
         not ghost && C.expr_in_context ctx ident 

       (* Fail if reserved identifier used *)
       with Invalid_argument e -> fail_at_position pos e)

    then

      (* Fail if identifier already declared *)
      fail_at_position 
        pos 
        (Format.asprintf 
           "Identifier %a is redeclared as constant" 
           (I.pp_print_ident false) ident);      
    
    (* Evaluate constant expression *)
    let res, _ = 
      S.eval_ast_expr
        []
        (C.fail_on_new_definition
           ctx
           pos
           "Invalid constant expression")
        expr
    in
    
    (* Distinguish typed and untyped constant here *)
    (match const_decl with 

      (* Need to type check constant against given type *)
      | A.TypedConst (_, _, _, type_expr) -> 

        (try 

           (* Evaluate type expression. Flatten any arrays so that we check
            * each element against its expected type *)
           let type_expr' = S.eval_ast_type_flatten true ctx type_expr in

           (* Check if type of expression is a subtype of the defined
              type at each index *)
           D.iter2
             (fun _ def_type { E.expr_type; E.expr_init = e } ->
                (* let e = (e :> Term.t) in *)
                (* let open Type in *)
                (* match node_of_type def_type with *)
                (* | IntRange (l, u) when Term.is_numeral e -> *)
                (*   let en = Term.numeral_of_term e in *)
                (*   if not (Numeral.(l >= en) && Numeral.(en <= u)) then *)
                (*       raise E.Type_mismatch *)
                (* | _ -> *)
                  if not (Type.check_type expr_type def_type) then
                    raise E.Type_mismatch
             ) type_expr' res

         with Invalid_argument _ | E.Type_mismatch ->
           (fail_at_position
              pos
              "Type mismatch in constant declaration"))

      (* No type check for untyped or free constant *)
      | _ -> ());

    
    D.iter
      (fun _ e ->
         if not (E.is_const e) then
           fail_at_position
             pos
             (Format.asprintf
                "Invalid constant expression for %a"
                (I.pp_print_ident false) ident);
      ) res;


    (* Return context with new mapping of identifier to expression *)
    C.add_expr_for_ident ~shadow:ghost ctx ident res


(* ********************************************************************** *)
(* Parse node                                                             *)
(* ********************************************************************** *)

(* Add all node inputs to contexts *)
let rec eval_node_inputs ctx = function

  (* All inputs parsed *)
  | [] -> ctx

  (* Input on the base clock *)
  | (pos, i, ast_type, A.ClockTrue, is_const) :: tl -> 

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident (QId.to_string i) in

    if 
      
      try 
        C.expr_in_context ctx ident 
      with Invalid_argument e -> 
        fail_at_position pos e
      
    then
      
      fail_at_position 
        pos
        (Format.asprintf 
           "Node input %a already declared" 
           (I.pp_print_ident false) ident);
    
    (* Evaluate type expression *)
    let index_types = S.eval_ast_type ctx ast_type in
  
    (* Add declaration of possibly indexed type to contexts *)
    let ctx = 
      C.add_node_input
        ~is_const
        ctx
        ident
        index_types
    in

    (* Continue with following inputs *)
    eval_node_inputs ctx tl

  | (pos, _, _, _, _) :: _ -> 

    fail_at_position pos "Clocked node inputs not supported"


(* Add all node inputs to contexts *)
let rec eval_node_outputs ?is_single ctx = function

  (* All outputs parsed *)
  | [] -> ctx

  (* Output on the base clock *)
  | (pos, i, ast_type, A.ClockTrue) :: tl -> 

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident (QId.to_string i) in

    if 
      
      try 
        C.expr_in_context ctx ident 
      with Invalid_argument e -> 
        fail_at_position pos e
      
    then
      
      fail_at_position 
        pos
        (Format.asprintf 
           "Node output %a already declared" 
           (I.pp_print_ident false) ident);
    
    (* Evaluate type expression *)
    let ident_types = S.eval_ast_type ctx ast_type in
  
    (* Add declaration of possibly indexed type to contexts *)
    let ctx = C.add_node_output ?is_single ctx ident pos ident_types in

    (* Continue with following inputs *)
    eval_node_outputs ctx tl

  | (pos, _, _, _) :: _ -> 

    fail_at_position pos "Clocked node outputs not supported"


(* Add all node local declarations to contexts *)
let rec eval_node_locals ?(ghost = false) ctx = function

  (* All local declarations parsed *)
  | [] -> ctx


  (* Identifier must not be declared *)
  | A.NodeVarDecl (pos, (_, i, _, _)) :: _ 
  | A.NodeConstDecl (pos, A.FreeConst (_, i, _)) :: _
  | A.NodeConstDecl (pos, A.UntypedConst (_, i, _)) :: _
  | A.NodeConstDecl (pos, A.TypedConst (_, i, _, _)) :: _ when 

      (* Ghost variables shadow already declared variables *)
      (not ghost &&
       (
         
         (* Identifier of AST identifier *)
         let ident = I.mk_string_ident (QId.to_string i) in
         
         try 
           C.expr_in_context ctx ident 
         with Invalid_argument e -> 
           fail_at_position pos e
             
       )) -> 
    
    fail_at_position 
      pos
      (Format.asprintf 
         "Node local variable or constant %a already declared" 
         A.pp_print_ident i)


  (* Local variable on the base clock *)
  | A.NodeVarDecl (_, (pos, i, var_type, A.ClockTrue)) :: tl -> 

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident (QId.to_string i) in

    (* Evaluate type expression *)
    let index_types = S.eval_ast_type ctx var_type in

    (* Add declaration of possibly indexed type to contexts *)
    let ctx = C.add_node_local ~ghost ctx ident pos index_types in

    (* Continue with following outputs *)
    eval_node_locals ~ghost ctx tl

  (* Local variable not on the base clock *)
  |  A.NodeVarDecl (_, (pos, i, _, _)) :: _ -> 

    fail_at_position 
      pos 
      (Format.asprintf 
         "Clocked node local variables not supported for %a" 
         A.pp_print_ident i)

  (* Local constant *)
  | A.NodeConstDecl (pos, const_decl) :: tl -> 

    (* Add mapping of identifier to value to context *)
    let ctx = eval_const_decl ~ghost ctx const_decl in

    (* Continue with following outputs *)
    eval_node_locals ~ghost ctx tl


(* ********************************************************************** *)
(* Parse equations                                                        *)
(* ********************************************************************** *)

(* Return trie of state variables from a structural assignment *)
let eval_struct_item ctx pos = function

  (* Single identifier *)
  | A.SingleIdent (pos, i) ->  

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident (QId.to_string i) in

    (* Get expression of identifier *)
    let res = 

      try

        (* Get trie of local or output state variables *)
        C.assignable_state_var_of_ident ctx ident
          
      with 
        
        (* Identifier cannot be assigned to *)
        | Invalid_argument _ -> 
          
          fail_at_position 
            pos 
            ("Assignment to identifier not possible " ^ QId.to_string i)

        (* Identifier not declared *)
        | Not_found -> 
          
          fail_at_position 
            pos 
            ("Assignment to undeclared identifier " ^ QId.to_string i)

    in

    (* Return trie of state variables and context unchanged *)
    (res, 0, ctx)

  (* Recursive array definition *)
  | A.ArrayDef (pos, i, l) -> 
    
    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident (QId.to_string i) in

    (* Get expression of identifier *)
    let res = 

      try

        (* Get trie of local or output state variables *)
        C.assignable_state_var_of_ident ctx ident
          
      with 
        
        (* Identifier cannot be assigned to *)
        | Invalid_argument _ -> 
          
          fail_at_position 
            pos 
            "Assignment to identifier not possible"

        (* Identifier not declared *)
        | Not_found -> 
          
          fail_at_position 
            pos 
            "Assignment to undeclared identifier"

    in

    
    (* Fail if the index in the second argument does not start with
       the same number of D.VarIndex keys as the length of list in the
       first argument. *)
    let check l1 =
      let d1 = List.length l1 in
      fun l2 ->
        let d2 =
          l2
          |> List.filter (function D.ArrayVarIndex _ -> true | _ -> false)
          |> List.length in
        if d1 <> d2 then
          fail_at_position pos "Index mismatch for array definition"
    in

    (* let rec aux = function  *)
    (*   | [] -> (function _ -> ()) *)
    (*   | h :: tl1 ->  *)
    (*     (function  *)
    (*       | D.ArrayVarIndex _ :: tl2 -> aux tl1 tl2 *)
    (*       | _ ->  *)
    (*         fail_at_position  *)
    (*           pos  *)
    (*           "Index mismatch for array") *)
    (* in *)

    (* Check that the variable has at least as many indexes as
       variables given *)
    List.iter (check l) (D.keys res);

    (* Must have at least one element in the trie *)
    assert 
      (try D.choose res |> ignore; true with Not_found -> false);
    
    let indexes = List.length l in
    
    (* Add bindings for the running variables to the context *)
    let _, ctx = 
      List.fold_left 
        (fun (i, ctx) v -> 

           (* Get an expression for the i-th index variable *)
           let expr = E.mk_index_var i in

           (* Bind identifier to the index variable, shadow previous
              bindings *)
           let ctx = 
             C.add_expr_for_ident
               ~shadow:true
               ctx
               (I.mk_string_ident (QId.to_string v))
               (D.singleton D.empty_index expr)
           in
           (succ i, ctx))
        (0, ctx)
        l
    in

    res, indexes, ctx


  | A.TupleStructItem (pos, _)  
  | A.TupleSelection (pos, _, _) 
  | A.FieldSelection (pos, _, _) 
  | A.ArraySliceStructItem (pos, _, _) ->     

    fail_at_position 
      pos 
      "Assignment not supported" 


let uneval_struct_item ctx = function

  (* Remove index variables in recursive array definitions *)
  | A.ArrayDef (pos, _, l) -> 

    (* Remove bindings for the running variables from the context in
       reverse order *)
    let ctx = 
      List.fold_left 
        (fun ctx v -> 

           (* Bind identifier to the index variable, shadow previous
              bindings *)
           let ctx = 
             C.remove_expr_for_ident
               ctx
               (I.mk_string_ident (QId.to_string v))
           in
           ctx)
        ctx
        (List.rev l)
    in
           
    ctx

  | _ -> ctx


(* Remove elements of the left-hand side from the scope *)
let uneval_eq_lhs ctx = function

  (* Nothing added from structrural assignments *)
  | A.StructDef (pos, l) -> List.fold_left uneval_struct_item ctx l


(* Return a trie of state variables from the left-hand side of an
   equation *)
let eval_eq_lhs ctx pos = function

  (* Empty list for node calls without returns *)
  | A.StructDef (pos, []) -> (D.empty, 0, ctx)

  (* Single item *)
  | A.StructDef (pos, [e]) -> eval_struct_item ctx pos e 

  (* List of items *)
  | A.StructDef (pos, l) -> 

    (* Combine by adding index for position on left-hand side *)
    let ctx, i, res = 
      List.fold_left
        (fun (ctx, i, accum) e -> 

           (* Get state variables of item *)
           let t, _, ctx = eval_struct_item ctx pos e in 

           (* Changed context *)
           (ctx,

            (* Go forwards through list *)
            i + 1,

            (* Add index of item on left-hand side to indexes *)
            D.fold
              (fun j e a -> D.add (D.ListIndex i :: j) e a)
              t
              accum))

        (* Add to empty trie with first index zero *)
        (ctx, 0, D.empty)

        (* Iterate over list *)
        l

    in

    (* Return types of indexes, no array bounds and unchanged
       context *)
    res, 0, ctx

(* Match bindings from a trie of state variables and bindings for a
   trie of expressions and produce a list of equations *)
let rec expand_tuple' pos accum bounds lhs rhs = match lhs, rhs with 

  (* No more equations, return in original order *)
  | [], [] -> accum

  (* Indexes are not of equal length *)
  | _, []
  | [], _ ->         

    fail_at_position pos "Type mismatch in equation: indexes not of equal length"

    (* All indexes consumed *)
  | ([], state_var) :: lhs_tl, 
    ([], expr) :: rhs_tl -> 

    expand_tuple'
      pos
      (((state_var, List.rev bounds), expr) :: accum)
      []
      lhs_tl
      rhs_tl

  (* Only array indexes may be left at head of indexes *)
  | (D.ArrayVarIndex b :: lhs_index_tl, state_var) :: lhs_tl,
    ([], expr) :: rhs_tl ->

    expand_tuple' 
      pos
      accum
      (E.Bound b :: bounds)
      ((lhs_index_tl, state_var) :: lhs_tl)
      (([], expr) :: rhs_tl)

  (* Array variable on left-hand side, fixed index on right-hand side *)
  | (D.ArrayVarIndex b :: lhs_index_tl, state_var) :: lhs_tl,
    (D.ArrayIntIndex i :: rhs_index_tl, expr) :: rhs_tl -> 

    (* Recurse to produce equations with this index *)
    let accum' = 
      expand_tuple' 
        pos
        accum
        (E.Fixed (E.mk_int_expr (Numeral.of_int i)) :: bounds)
        [(lhs_index_tl, state_var)]
        [(rhs_index_tl, expr)]
    in

    (* Return of no fixed indexes on right-hand side left *)
    if rhs_tl = [] then accum' else

      (* Continue with next fixed index on right-hand side and
         variable index on left-hand side *)
      expand_tuple'
        pos
        accum'
        bounds
        lhs
        rhs_tl

  (* Array index on left-hand and right-hand side *)
  | (D.ArrayVarIndex b :: lhs_index_tl, state_var) :: lhs_tl,
    (D.ArrayVarIndex br :: rhs_index_tl, expr) :: rhs_tl -> 

    (* We cannot compare expressions for array bounds syntactically,
       because that may give too many false negatives. Evaluating both
       bounds to find if they are equal would be too complicated,
       therefore accept some false positives here. *)

    (* Take the smaller bound when it is known statically otherwise keep the
       one from the left-hand side *)
    let b = 
      if E.is_numeral b && E.is_numeral br &&
         Numeral.(E.(numeral_of_expr b > numeral_of_expr br)) then
        br
      else b
    in
    
    
    (* Count number of variable indexes *)
    (* let i =  *)
    (*   List.fold_left  *)
    (*     (fun a -> function  *)
    (*        | D.ArrayVarIndex _ -> succ a *)
    (*        | _ -> a) *)
    (*     0 *)
    (*     lhs_index_tl *)
    (* in *)
    
    (* Is every variable in the expression necessarily of array type? 

       Need to skip the index expression of a select operator: A[k] *)
    
    let expr' = expr in
    (*   E.map (fun _ e -> *)
    (*       if E.is_var e && (E.type_of_lustre_expr e |> Type.is_array) then *)
    (*          E.mk_select e (E.mk_index_var i) *)
    (*       else e) *)
    (*     expr *)
    (* in *)

    expand_tuple' 
      pos
      accum
      (E.Bound b :: bounds)
      ((lhs_index_tl, state_var) :: lhs_tl)
      ((rhs_index_tl, expr') :: rhs_tl)

  (* Tuple index on left-hand and right-hand side *)
  | ((D.TupleIndex i :: lhs_index_tl, state_var) :: lhs_tl,
     (D.TupleIndex j :: rhs_index_tl, expr) :: rhs_tl) 

  | ((D.ListIndex i :: lhs_index_tl, state_var) :: lhs_tl,
     (D.ListIndex j :: rhs_index_tl, expr) :: rhs_tl) 

  | ((D.ArrayIntIndex i :: lhs_index_tl, state_var) :: lhs_tl,
     (D.ArrayIntIndex j :: rhs_index_tl, expr) :: rhs_tl) -> 

    (* Indexes are sorted, must match *)
    if i = j then 

      expand_tuple'
        pos
        accum
        bounds
        ((lhs_index_tl, state_var) :: lhs_tl)
        ((rhs_index_tl, expr) :: rhs_tl)

    else

      fail_at_position pos "Type mismatch in equation: indexes do not match"

  (* Tuple index on left-hand and array index on right-hand side *)
  | ((D.TupleIndex i :: lhs_index_tl, state_var) :: lhs_tl,
     (D.ArrayIntIndex j :: rhs_index_tl, expr) :: rhs_tl) ->

    (* Indexes are sorted, must match *)
    if i = j then 

      (* Use tuple index instead of array index on right-hand side *)
      expand_tuple'
        pos
        accum
        bounds
        ((lhs_index_tl, state_var) :: lhs_tl)
        ((lhs_index_tl, expr) :: rhs_tl)

    else

      fail_at_position pos "Type mismatch in equation: indexes do not match"


  (* Record index on left-hand and right-hand side *)
  | (D.RecordIndex i :: lhs_index_tl, state_var) :: lhs_tl,
    (D.RecordIndex j :: rhs_index_tl, expr) :: rhs_tl
  (* Abstract type index works like record except program cannot project field *)
  | (D.AbstractTypeIndex i :: lhs_index_tl, state_var) :: lhs_tl,
    (D.AbstractTypeIndex j :: rhs_index_tl, expr) :: rhs_tl -> 

    (* Indexes are sorted, must match *)
    if i = j then 

      expand_tuple'
        pos
        accum
        bounds
        ((lhs_index_tl, state_var) :: lhs_tl)
        ((rhs_index_tl, expr) :: rhs_tl)

    else

      fail_at_position pos "Type mismatch in equation: record indexes do not match"

  (* Mismatched indexes on left-hand and right-hand sides *)
  | (D.RecordIndex _ :: _, _) :: _, (D.TupleIndex _ :: _, _) :: _
  | (D.RecordIndex _ :: _, _) :: _, (D.ListIndex _ :: _, _) :: _
  | (D.RecordIndex _ :: _, _) :: _, (D.ArrayIntIndex _ :: _, _) :: _
  | (D.RecordIndex _ :: _, _) :: _, (D.ArrayVarIndex _ :: _, _) :: _
  | (D.RecordIndex _ :: _, _) :: _, (D.AbstractTypeIndex _ :: _, _) :: _

  | (D.TupleIndex _ :: _, _) :: _, (D.RecordIndex _ :: _, _) :: _
  | (D.TupleIndex _ :: _, _) :: _, (D.ListIndex _ :: _, _) :: _
  | (D.TupleIndex _ :: _, _) :: _, (D.ArrayVarIndex _ :: _, _) :: _
  | (D.TupleIndex _ :: _, _) :: _, (D.AbstractTypeIndex _ :: _, _) :: _

  | (D.ListIndex _ :: _, _) :: _, (D.RecordIndex _ :: _, _) :: _
  | (D.ListIndex _ :: _, _) :: _, (D.TupleIndex _ :: _, _) :: _
  | (D.ListIndex _ :: _, _) :: _, (D.ArrayIntIndex _ :: _, _) :: _
  | (D.ListIndex _ :: _, _) :: _, (D.ArrayVarIndex _ :: _, _) :: _
  | (D.ListIndex _ :: _, _) :: _, (D.AbstractTypeIndex _ :: _, _) :: _

  | (D.ArrayIntIndex _ :: _, _) :: _, (D.RecordIndex _ :: _, _) :: _
  | (D.ArrayIntIndex _ :: _, _) :: _, (D.TupleIndex _ :: _, _) :: _
  | (D.ArrayIntIndex _ :: _, _) :: _, (D.ListIndex _ :: _, _) :: _
  | (D.ArrayIntIndex _ :: _, _) :: _, (D.ArrayVarIndex _ :: _, _) :: _
  | (D.ArrayIntIndex _ :: _, _) :: _, (D.AbstractTypeIndex _ :: _, _) :: _

  | (D.ArrayVarIndex _ :: _, _) :: _, (D.RecordIndex _ :: _, _) :: _
  | (D.ArrayVarIndex _ :: _, _) :: _, (D.TupleIndex _ :: _, _) :: _
  | (D.ArrayVarIndex _ :: _, _) :: _, (D.ListIndex _ :: _, _) :: _
  | (D.ArrayVarIndex _ :: _, _) :: _, (D.AbstractTypeIndex _ :: _, _) :: _

  | (D.AbstractTypeIndex _ :: _, _) :: _, (D.RecordIndex _ :: _, _) :: _
  | (D.AbstractTypeIndex _ :: _, _) :: _, (D.TupleIndex _ :: _, _) :: _
  | (D.AbstractTypeIndex _ :: _, _) :: _, (D.ListIndex _ :: _, _) :: _
  | (D.AbstractTypeIndex _ :: _, _) :: _, (D.ArrayIntIndex _ :: _, _) :: _
  | (D.AbstractTypeIndex _ :: _, _) :: _, (D.ArrayVarIndex _ :: _, _) :: _

  | (_ :: _, _) :: _, ([], _) :: _ 
  | ([], _) :: _, (_ :: _, _) :: _ ->

    fail_at_position pos "Type mismatch in equation: head indexes do not match"


(* Return a list of equations from a trie of state variables and a
   trie of expressions *)
let expand_tuple pos lhs rhs = 

  (* Format.eprintf *)
  (*   "@[<v>expand_tuple lhs:@,%a@]@." *)
  (*   (pp_print_list *)
  (*      (fun ppf (i, sv) -> *)
  (*         Format.fprintf ppf "%a: %a " *)
  (*           (D.pp_print_index true) i *)
  (*           StateVar.pp_print_state_var sv) *)
  (*      "@,") *)
  (*   (List.map (fun (i, e) -> (List.rev i, e)) (D.bindings lhs)); *)

  (* Format.eprintf *)
  (*   "@[<v>expand_tuple rhs:@,%a@]@." *)
  (*   (pp_print_list *)
  (*      (fun ppf (i, e) -> *)
  (*         Format.fprintf ppf "%a: %a " *)
  (*           (D.pp_print_index true) i *)
  (*           (E.pp_print_lustre_expr false) e) *)
  (*      "@,") *)
  (*   (List.map (fun (i, e) -> (List.rev i, e)) (D.bindings rhs)); *)
  
  expand_tuple' 
    pos
    []
    []
    (List.map (fun (i, e) -> ((* List.rev *) i, e)) (D.bindings lhs))
    (List.map (fun (i, e) -> ((* List.rev *) i, e)) (D.bindings rhs))


let rec eval_node_equation inputs outputs locals ctx = function
  
  | A.Assert (pos, ast_expr) -> 
    (* report unguarded pre *)
    let ctx = C.set_guard_flag ctx (H.has_unguarded_pre ast_expr) in

    (* Evaluate Boolean expression and guard all pre operators *)
    let expr, ctx = 
      S.eval_bool_ast_expr [] ctx pos ast_expr 
      |> C.close_expr ~original:ast_expr pos
    in

    let ctx = C.reset_guard_flag ctx in

    (* Add assertion to node *)
    let (svar, _), ctx = C.mk_local_for_expr ~is_ghost:true pos ctx expr in
    N.add_state_var_def svar (N.Assertion pos) ;
    C.add_node_assert ctx pos svar
      

  (* Equations with possibly more than one variable on the left-hand side

     The expression is without node calls, those have been
     abstracted *)
  | A.Equation (pos, lhs, ast_expr) -> 

    (* Trie of state variables on left-hand side and extended context
       for right-hand side *)
    let eq_lhs, indexes, ctx = eval_eq_lhs ctx pos lhs in

    (* array bounds. TODO: check that the order is correct *)
    let rm_array_var_index lst =
      List.filter (function
      | D.ArrayVarIndex _ -> false
      | _ -> true
      ) lst
    in
    let lhs_bounds =
      List.fold_left (fun acc (i, sv) ->
          N.add_state_var_def sv
            (N.ProperEq (H.pos_of_expr ast_expr, rm_array_var_index i)) ;
          List.fold_left (fun (acc, cpt) -> function
              | D.ArrayVarIndex b ->
                if cpt < indexes then E.Bound b :: acc, succ cpt
                else acc, cpt
              | _ -> acc, cpt
            ) (acc, 0) i
          |> fst
        ) [] (D.bindings eq_lhs)
      (* |> List.rev *) in

    (* report unguarded pre *)
    let ctx = C.set_guard_flag ctx (H.has_unguarded_pre ast_expr) in

    (* Evaluate expression on right-hand side in extended context *)
    let eq_rhs, ctx = S.eval_ast_expr lhs_bounds ctx ast_expr in

    let ctx = C.reset_guard_flag ctx in

    (* Close each expression by guarding all pre operators separately *)
    let eq_rhs, ctx = 
      D.fold 
        (fun i e (t, c) -> 
           let e', c = C.close_expr ~original:ast_expr pos (e, c) in 
           let t' = D.add i e' t in
           (t', c))
        eq_rhs
        (D.empty, ctx)

    in 
    
    (* Remove local definitions for equation from context

       We add local definitions from the left-hand side to the
       context, then evaluate the right-hand side, which may modify
       this context with new abstractions. We need to keep the
       definitions from the right-hand side, but remove the local
       definitions that we made before. *)
    let ctx = uneval_eq_lhs ctx lhs in

    let equations = expand_tuple pos eq_lhs eq_rhs in

    (* Add equations for each index *)
      List.fold_left (
        fun ctx ((sv, b), e) ->
          (* Is [e] a state variable in the current state? *)
          let ctx =
            if E.is_var e then (
              let alias = E.state_var_of_expr e in
              (* Format.printf "%a is an alias for %a@.@."
                StateVar.pp_print_state_var alias
                StateVar.pp_print_state_var sv ; *)
              C.current_node_map ctx (
                fun node -> N.set_state_var_alias node alias sv
              )
            ) else ctx
          in
          C.add_node_equation ctx pos sv b indexes e
      ) ctx equations

  | A.Automaton (pos, aname, states, _) as e ->
    let auto_outputs = defined_vars_eqs [e] in
    eval_automaton pos aname states auto_outputs inputs outputs locals ctx



(* ********************************************************************** *)
(* Parse contracts                                                        *)
(* ********************************************************************** *)

(* Parse a ghost variable declaration and evaluate continuation 

   This function is shared between nodes and functions, each has a
   different way to deal with ghost variables. *)
and eval_ghost_var
  ?(no_defs = false) is_postponed inputs outputs locals ctx
= function

  (* Declaration of a free variable *)
  | A.FreeConst (pos, _, _) ->

    fail_at_position pos "Free ghost variables not supported"

  (* Declaration of a typed or untyped variable *)
  | A.UntypedConst (pos, i, expr) 
  | A.TypedConst (pos, i, expr, _) as const_decl ->


    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident (QId.to_string i) in

    if (
      try 
        (* Identifier must not be declared *)
        C.expr_in_context ctx ident && not is_postponed
      with Invalid_argument e ->
       (* Fail if reserved identifier used *)
       fail_at_position pos e
    ) then (
      (* Fail if identifier already declared *)
      fail_at_position pos (
        Format.asprintf 
          "Identifier %a is redeclared as ghost" 
          (I.pp_print_ident false) ident
      )
    ) ;

    if H.has_unguarded_pre expr then (
      fail_or_warn
        pos
        "Illegal unguarded pre in ghost variable definition."
    ) ;

    match const_decl with 
    (* Distinguish typed and untyped constant here *)

    (* Need to type check constant against given type *)
    | A.TypedConst (_, _, _, type_expr) -> (

      try (
        (* Evaluate type expression *)
        let type_expr = S.eval_ast_type ctx type_expr in
        (* Add ghost to context. *)
        let ctx = C.add_node_local ~ghost:true ctx ident pos type_expr in

        let ctx =
          eval_node_equation inputs outputs locals ctx (
            A.Equation (pos, A.StructDef (pos, [A.SingleIdent (pos, i)]), expr)
          )
        in

        ctx

      ) with
      | E.Type_mismatch -> fail_at_position pos (
        Format.sprintf "Type mismatch in declaration of ghost variable %s" (QId.to_string i)
      )
      (* Propagate unknown declarations to handle forward referencing. *)
      | Deps.Unknown_decl (_, _, _) as e -> raise e
      | e -> fail_at_position pos (
        Format.asprintf
          "unexpected error in treatment of ghost variable %s: %s"
          (QId.to_string i)
          (Printexc.to_string e)
      )
    )

    (* No type check for untyped or free constant *)
    | _ -> (
      (* Evaluate ghost expression *)
      let expr, ctx' =
        S.eval_ast_expr [] (
          (* Change context to fail on new definitions *)
          if no_defs then
            C.fail_on_new_definition
              ctx pos "Invalid expression for variable"
          else ctx
        ) expr
      in
      let ctx = if no_defs then ctx else ctx' in
      
      let type_expr = D.map (fun { E.expr_type } -> expr_type) expr in
      (* Add ghost to context. *)
      let ctx = C.add_node_local ~ghost:true ctx ident pos type_expr in
      let ctx =
        C.add_expr_for_ident ~shadow:true ctx ident expr
      in

      ctx
    )

(* Evaluates a generic contract item: assume, guarantee, require or ensure. *)
and eval_contract_item check ~typ scope (ctx, accum, count) (pos, iname, expr) =
  (* Check for unguarded pre-s. *)
  if H.has_unguarded_pre expr then (
    fail_or_warn pos "Illegal unguarded pre in contract item."
  ) ;
  (* Scope is created backwards. *)
  let scope = List.rev scope in
  (* Evaluate expression to a Boolean expression, may change context. *)
  let expr, ctx =
    S.eval_bool_ast_expr [] ctx pos expr
    |> C.close_expr pos
  in
  (* Check the expression if asked to. *)
    ( match check with
    | None -> ()
    | Some desc -> (
      match contract_check_no_output ctx pos expr with
      | [] -> ()
      | svars ->
        assert (List.length svars > 0) ;
        let s = if List.length svars > 1 then "s" else "" in
        let pref = match C.current_node_name ctx with
          | None -> ""
          | Some name ->
            Format.asprintf " of node %a" (I.pp_print_ident false) name
        in
        let suff = match scope with
          | [] -> ""
          | _ ->
            List.rev scope
            |> Format.asprintf " (via call%s: %a)"
              (if List.length scope > 1 then "s" else "") (
                pp_print_list (
                  fun fmt (pos, name) ->
                    Format.fprintf fmt "%s%a" name pp_print_pos pos
                ) ", "
              )
        in
        (* It triggers a warning instead of an error because current check is more restrictive
           than it should be: it should trigger an error only if the final streams depend on
           a current output value (an output stream passed as an argument in a node call is not
           an error if only the previous value of the stream is used)
        *)
        warn_at_position pos (
          Format.asprintf
            "@[<v>%s mentions output%s%s %a%s@]"
              desc s pref (
                pp_print_list (
                  fun fmt sv ->
                    Format.fprintf fmt "'%s'" (StateVar.name_of_state_var sv)
                ) ", "
              ) svars suff
        )
    )
  ) ;
  (* Define expression with a state variable *)
  let (svar, _), ctx = C.mk_local_for_expr ~reuse:false ~is_ghost:true pos ctx expr in
  let contract_svar = Contract.mk_svar pos count iname svar scope in
  N.add_state_var_def svar (N.ContractItem (pos, contract_svar, typ)) ;
  (* Add state variable to accumulator, continue with possibly modified
  context. *)
  ctx, contract_svar :: accum, count + 1


(* Fail if a contract node input is incompatible with a node input *)
and check_node_and_contract_inputs call_pos ctx node_inputs = function 

  (* All contract inputs are consistent with node inputs *)
  | [] -> ()

  (* Input to contract, must not have a clock *)
  | ( pos, 
      ident, 
      contract_input_lustre_type, 
      A.ClockTrue, 
      contract_input_const ) :: tl -> 

    let 

      (* Node input corresponding to contract input *)
      (_, 
       _, 
       node_input_lustre_type, 
       node_input_clock, 
       node_input_const) = 

      try 

        (* Find node input with the same identifier *)
        List.find
          (fun (_, i, _, _, _) -> i = ident)
          node_inputs

      with Not_found -> 

        fail_at_position 
          call_pos 
          "Illegal contract call: node does not have input"

    in

    (* Input must not have a clock *)
    (match node_input_clock with 
      | A.ClockTrue -> ()
      | _ -> 
        fail_at_position 
          pos 
          "Clocked inputs not supported");

    (* Node input must be constant iff contract input is *)
    if contract_input_const <> node_input_const then 

      fail_at_position 
        pos 
        "Illegal contract call: node does not have input";

    (try 

       (* Evaluate defined types of contract and node, and fail if not
          compatible *)
       D.iter2
         (fun _ t s -> 
            if not (Type.check_type s t) then raise E.Type_mismatch)
         (S.eval_ast_type ctx contract_input_lustre_type)
         (S.eval_ast_type ctx node_input_lustre_type)

     with Invalid_argument _ | E.Type_mismatch -> 

       (fail_at_position
          pos
          "Type mismatch in constant declaration"));

    (* Continue with remaining inputs *)
    check_node_and_contract_inputs call_pos ctx node_inputs tl

  | (pos, _, _, _, _) :: tl -> 

    fail_at_position 
      pos 
      "Clocked inputs not supported"


(* Fail if a contract node output is incompatible with a node output *)
and check_node_and_contract_outputs call_pos ctx node_outputs = function 

  (* All contract outputs are consistent with node outputs *)
  | [] -> ()

  (* Output of contract, must not have a clock *)
  | (pos, 
     ident, 
     contract_output_lustre_type, 
     A.ClockTrue) :: tl -> 

    let 

      (* Node output corresponding to contract output *)
      (_, 
       _,
       node_output_lustre_type, 
       node_output_clock) = 

      try 

        (* Find node output with the same identifier *)
        List.find
          (fun (_, i, _, _) -> i = ident)
          node_outputs

      with Not_found -> 

        fail_at_position 
          call_pos 
          "Illegal contract call: node does not have output"

    in

    (* Output must not have a clock *)
    (match node_output_clock with 
      | A.ClockTrue -> ()
      | _ -> 
        fail_at_position 
          pos 
          "Clocked outputs not supported");

    (try 

       (* Evaluate defined types of contract and node, and fail if not
          compatible *)
       D.iter2
         (fun _ t s -> if not (Type.check_type s t) then raise E.Type_mismatch)
         (S.eval_ast_type ctx contract_output_lustre_type)
         (S.eval_ast_type ctx node_output_lustre_type)

     with Invalid_argument _ | E.Type_mismatch -> 

       (fail_at_position
          pos
          "Type mismatch in constant declaration"));

    (* Continue with remaining inputs *)
    check_node_and_contract_outputs call_pos ctx node_outputs tl

  | (pos, _, _, _) :: tl -> 

    fail_at_position 
      pos 
      "Clocked outputs not supported"


(* Evaluates a mode for a node. *)
and eval_node_mode scope ctx is_candidate (pos, id, reqs, enss) =
  (* Evaluate requires. *)
  let ctx, reqs, _ =
    reqs
    |> List.fold_left (eval_contract_item (Some "require") ~typ:N.Require scope)
       (ctx, [], 1) in
  (* Evaluate ensures. *)
  let ctx, enss, _ =
    enss |> List.fold_left (eval_contract_item None ~typ:N.Ensure scope) (ctx, [], 1) in
  let path =
    scope |> List.fold_left (fun l (_, name) -> name :: l) (QId.to_list id)
  in
  (* Done. *)
  Contract.mk_mode (I.mk_string_ident (QId.to_string id)) pos path reqs enss is_candidate
  |> C.add_node_mode ctx


(* (* Checks whether some node calls have contracts, recursively. *)
let rec check_no_contract_in_node_calls ctx = function
(* No call left, done. *)
| [] -> ()
(* Let's do this. *)
| { N.call_node_name ; N.call_pos } :: calls -> (
  match
    try C.node_of_name ctx call_node_name
    with Not_found -> fail_at_position call_pos (
      Format.asprintf "call to unknown node '%a'"
        (LustreIdent.pp_print_ident false) call_node_name
    )
  with
  | Some contract ->
  | None -> 
)
 *)

(* Evaluates contract calls. *)
and eval_node_contract_call 
  known ctx scope inputs outputs locals is_candidate (
    call_pos, id, in_params, out_params
  ) = 
  let ident = I.mk_string_ident (QId.to_string id) in

  if I.Set.mem ident known then (
    Format.asprintf
      "circular dependency between following contracts: @[<hov>%a@]"
      (pp_print_list (I.pp_print_ident false) ", ")
      (I.Set.elements known)
    |> fail_at_position call_pos
  ) ;

  let known = I.Set.add ident known in

  (* Check for unguarded pre-s. *)
  in_params |> List.iter (
    fun expr -> if H.has_unguarded_pre expr then (
      fail_or_warn
        call_pos "Illegal unguarded pre in input parameters of contract call."
    )
  ) ;

  (* Push scope for contract svars. *)
  let svar_scope = (call_pos, (QId.to_string id)) :: scope in
  (* Push scope for contract call. *)
  let ctx = C.push_contract_scope ctx (QId.to_string id) in
  (* Retrieve contract node from context. *)
  let pos, (id, params, in_formals, out_formals, contract) =
    try C.contract_node_decl_of_ident ctx id
    with Not_found ->
      (* Contract might be forward referenced. *)
      Deps.Unknown_decl (Deps.Contract, ident, call_pos) |> raise
  in

  (* Failing for unsupported features. *)
  ( match params with
    | [] -> ()
    | _ -> fail_at_position pos (
      "type parameters in contract node is not supported"
    )
  ) ;
  in_formals |> List.iter (
    function
    | pos, id, typ, A.ClockTrue, is_const -> () (* pos, id, typ, is_const *)
    | _ -> fail_at_position pos (
        "clocks in contract node signature are not supported"
      )
  ) ;
  out_formals |> List.iter (
    function
    | pos, id, typ, A.ClockTrue -> () (* pos, id, typ *)
    | _ -> fail_at_position pos (
        "clocks in contract node signature are not supported"
      )
  ) ;

  (* Add substitution from formal inputs to actual one before we evaluate
     everything. *)
  let ctx = try
    List.fold_left2 (
        fun ctx expr (_, in_id, typ, _, _) ->
          let expr, ctx = S.eval_ast_expr [] ctx expr in

          (* Fail if type mismatch. *)
          (
            try
              (* Evaluate type expression. *)
              let expected = S.eval_ast_type ctx typ in
              (* Check if subtype. *)
              D.iter2 (
                fun _ expected { E.expr_type } ->
                  if not (Type.check_type expr_type expected) then
                    raise E.Type_mismatch
              ) expected expr
            with
            | Invalid_argument _
            | E.Type_mismatch -> fail_at_position call_pos (
                Format.asprintf
                  "type mismatch in import of contract %s for formal input %s"
                  (QId.to_string id) (QId.to_string in_id)
              )
          ) ;

          (* Fail if expression mentions an output in the current state. *)
          (
            D.iter (
              fun _ expr -> match contract_check_no_output ctx pos expr with
                | [] -> ()
                | svars ->
                  assert (List.length svars > 0) ;
                  let s = if List.length svars > 1 then "s" else "" in
                  let pref = match C.current_node_name ctx with
                    | None -> ""
                    | Some name ->
                      Format.asprintf " in node %a" (I.pp_print_ident false) name
                  in
                  let suff = match scope with
                    | [] -> ""
                    | _ ->
                      List.rev scope
                      |> Format.asprintf " (contract call trace: %a)" (
                        pp_print_list (
                          fun fmt (pos, name) ->
                            Format.fprintf fmt "%s%a" name pp_print_pos pos
                        ) ", "
                      )
                  in
                  fail_at_position pos (
                    Format.asprintf
                      "@[<v>input parameter in contract import%s mentions \
                       output%s %a%s@]"
                      pref s (
                      pp_print_list (
                        fun fmt sv ->
                          Format.fprintf fmt "'%s'"
                            (StateVar.name_of_state_var sv)
                      ) ", "
                    ) svars
                      suff
                  )
            ) expr
          ) ;

          C.add_expr_for_ident
            ~shadow:true ctx (LustreIdent.mk_string_ident (QId.to_string in_id)) expr

    ) ctx in_params in_formals
    with
    | Invalid_argument _ ->  fail_at_position call_pos (
        Format.asprintf
          "arity mismatch for the input parameters of import of contract %s: \
           expected %d but got %d"
          (QId.to_string id)
          (List.length in_formals)
          (List.length in_params)
      )
  in

  (* Add substitution from formal outputs to actual one before we evaluate
     everything. *)
  let ctx = try
      List.fold_left2 (
        fun ctx expr (pos, in_id, typ, _) ->
          let expr, ctx = S.eval_ast_expr [] ctx expr in

          (* Fail if type mismatch. *)
          (
            try
              (* Evaluate type expression. *)
              let expected = S.eval_ast_type ctx typ in
              (* Check if subtype. *)
              D.iter2 (
                fun _ expected { E.expr_type } ->
                  if not (Type.check_type expr_type expected) then
                    raise E.Type_mismatch
              ) expected expr
            with
            | Invalid_argument _
            | E.Type_mismatch -> fail_at_position call_pos (
                Format.asprintf
                  "type mismatch in import of contract %s for formal output %s"
                  (QId.to_string id) (QId.to_string in_id)
              )
          ) ;

          C.add_expr_for_ident
            ~shadow:true ctx (LustreIdent.mk_string_ident (QId.to_string in_id)) expr
      ) ctx (List.map (fun i -> LustreAst.Ident (pos, i))out_params) out_formals
    with
    | Invalid_argument _ ->  fail_at_position call_pos (
        Format.asprintf
          "arity mismatch for the output parameters of import of contract %s: \
           expected %d but got %d"
          (QId.to_string id)
          (List.length in_formals)
          (List.length in_params)
      )
  in

  (* If node's actually a function, check that contract is not stateful. *)
  (* Format.printf "current_node: %a@.@."
    (I.pp_print_ident false) (
      match C.current_node_name ctx with
      | Some id -> id
      | None -> assert false
    ) ; *)
  ( if C.get_node_function_flag ctx then (
    (* Format.printf "checking contract %s@.@." id ; *)
    match H.contract_has_pre_or_arrow contract with
    | Some _ -> fail_at_position call_pos (
      Format.asprintf
        "@[<v>in contract of function %a@ \
        illegal import of stateful contract %s@ \
        functions can only be specified by stateless contracts@]"
        (I.pp_print_ident false) (
          match C.current_node_name ctx with
          | Some id -> id
          | None -> assert false
        )
        (QId.to_string id)
    )
    | None -> ()
  ) ) ;

  (* Evaluate node as usual, it will merge with the current contract. *)
  let ctx =
    contract |> List.map (fun item -> item, is_candidate)
    |> eval_node_contract_spec known ctx call_pos svar_scope
      inputs outputs locals
  in

  (* Pop scope for contract call. *)
  C.pop_contract_scope ctx
  

(* Add declaration and equation for ghost stream *)
and add_ghost inputs outputs locals ctx pos ident type_expr ast_expr expr = 

  (* Add local declaration for ghost stream *)
  let ctx = C.add_node_local ~ghost:true ctx ident pos type_expr in

  (* Add equation for ghost stream *)
  eval_node_equation inputs outputs locals ctx (
    A.Equation (
      pos, (
        A.StructDef (
          pos,
          [A.SingleIdent (pos, QId.from_string (I.string_of_ident false ident))]
        )
      ),
      ast_expr
    )
  )

(* Add all node contracts to contexts *)
and eval_node_contract_item
  known scope inputs outputs locals is_candidate is_postponed
  (ctx, cpt_a, cpt_g)
= function

  (* Add constants to context *)
  | A.GhostConst c -> eval_const_decl ~ghost:true ctx c, cpt_a, cpt_g

  (* Add ghost variables to context *)
  | A.GhostVar v ->
    eval_ghost_var is_postponed inputs outputs locals ctx v, cpt_a, cpt_g

  (* Evaluate assumption *)
  | A.Assume (pos, name, soft, expr) ->
    let ctx, assumes, cpt_a =
      eval_contract_item (Some (if soft then "weakly assume" else "assume"))
        ~typ:(if soft then N.WeakAssumption else N.Assumption) scope (ctx, [], cpt_a)
        (pos, name, expr) in
    C.add_node_ass ctx assumes,
    cpt_a, cpt_g

  (* Evaluate guarantee *)
  | A.Guarantee (pos, name, soft, expr) ->
    let ctx, guarantees, cpt_g =
      eval_contract_item None ~typ:(if soft then N.WeakGuarantee else N.Guarantee)
      scope (ctx, [], cpt_g) (pos, name, expr) in
    List.map (fun g -> g, is_candidate) guarantees |> C.add_node_gua ctx,
    cpt_a, cpt_g

  (* Evaluate modes. *)
  | A.Mode m -> eval_node_mode scope ctx is_candidate m, cpt_a, cpt_g

  (* Evaluate imports. *)
  | A.ContractCall call ->
    eval_node_contract_call
      known ctx scope inputs outputs locals is_candidate call,
    cpt_a, cpt_g


(* Add all node contracts to contexts *)
and eval_node_contract_spec
  known ctx pos scope inputs outputs locals contract
=
  (* Handles declarations, allows forward reference. *)
  let rec loop acc prev_postponed_size postponed = function
    | (head, is_candidate, is_postponed) :: tail -> (
      let acc, postponed =
        try
          eval_node_contract_item
            known scope inputs outputs locals
            is_candidate is_postponed acc head,
          postponed
        with
        | Deps.Unknown_decl _ ->
          acc, (head, is_candidate, true) :: postponed
      in
      loop acc prev_postponed_size postponed tail
    )
    | [] -> (
      match postponed with
      | [] -> acc
      | (head, is_candidate, is_postponed) :: _
        when prev_postponed_size = List.length postponed ->
      (
        try (* eval_node_contract_item is expected to fail with Deps.Unknown_decl *)
          eval_node_contract_item
            known scope inputs outputs locals
            is_candidate is_postponed acc head
        with
        | Deps.Unknown_decl (s_type, s_ident, s_pos) ->
          let sc = List.map snd scope in
          let pp_print_type = fun ppf -> function
            (* If it's an unknown constant, it's more generally an unknown
            identifier. *)
            | Deps.Const -> Format.fprintf ppf "identifier"
            | typ -> Deps.pp_print_decl ppf typ
          in
          let msg = if sc = [] then
            Format.asprintf
              "unknown %a '%a'"
              pp_print_type s_type (I.pp_print_ident false) s_ident
          else
            Format.asprintf
              "unknown %a '%a' referenced in contract '%a'"
              pp_print_type s_type (I.pp_print_ident false) s_ident
              Scope.pp_print_scope sc
          in
          fail_at_position s_pos msg
      )
      | _ -> loop acc (List.length postponed) [] postponed
    )
  in
  let ctx, _, _ =
    contract
    |> List.map (fun (f,s) -> (f,s,false))
    |> loop (ctx, 1, 1) (1 + List.length contract) []
    (* List.fold_left
      (eval_node_contract_item known scope inputs outputs locals)
      (ctx, 1, 1) contract *)
  in

  (* What follows are checks over the contract. We know the contract is parsed
  before the body of the node, so whatever's currently in the node just comes
  from the contract itself. *)
  ( match C.get_node ctx with
    | None -> failwith "unreachable, no current node after parsing contract"
    | Some { N.oracles ; N.calls } -> (
      (* Checking whether the contract we just parsed introduced any oracles.
      If it did, then it means there was unguarded pre-s below the contract.
      They a priori come from node calls in the contract since unguarded pre-s
      in contract items and contract imports fail immediately. *)
      ( match oracles with
        | [] -> () (* No oracles introduced, we're fine. *)
        | _ -> (* PEBCAK. *)
          fail_or_warn
            pos "Illegal unguarded pre under a node call in this contract."
      ) ;
      (* Checking that no subsystem of the current node has contracts. If one
      of them does, it means there is a call to a node with a contract in the
      cone of influence of the contract we just parsed. *)
      let node_of_name ctx name =
        try C.node_of_name ctx name with Not_found -> Format.asprintf "\
          unreachable, node %a called in contract undefined\
        " (I.pp_print_ident false) name
        |> failwith
      in
      let rec loop known = function
        | [] -> ()
        | { N.name ; N.calls ; N.contract = None } :: tail ->
          (* No contract, is ok. Preparing recursive call. *)
          let known = I.Set.add name known in
          calls |> List.fold_left (
            fun acc { N.call_node_name = sub_name } -> 
              if I.Set.mem sub_name known then acc
              else (node_of_name ctx sub_name) :: acc
          ) tail
          |> loop known
        | { N.name } :: _ -> (* PEBCAK. *)
          Format.asprintf "\
            Illegal call to node '%a' in the cone of influence of this \
            contract: node %a has a contract.\
          " (I.pp_print_ident false) name (I.pp_print_ident false) name
          |> fail_at_position pos
      in
      let subs, known =
        calls |> List.fold_left (
          fun (subs, known) { N.call_node_name = sub_name } ->
            if I.Set.mem sub_name known then subs, known
            else (node_of_name ctx sub_name) :: subs, I.Set.add sub_name known
        ) ([], I.Set.empty)
      in
      loop known subs
    )
  ) ;

  ctx
  
(* Evaluate a hierarchical automaton by recursively encoding states as nodes
   and evaluating those *)
and eval_automaton pos aname states auto_outputs inputs outputs locals ctx =

    let ctx = C.set_in_automaton ctx true in

    (* Create a new automaton name if anonymous *)
    let name = match aname with
      | Some name -> QId.to_string name
      | None -> fresh_automaton_name []
    in

    (* Only variables direcltly visible in the node are allowed under a last
       operator in a state *)
    let allowed_l = allowed_lasts inputs outputs locals in

    (* Eliminate [last] applications in state equations *)
    let states, lasts =
      List.fold_left (fun (states, lasts) s ->
          let s, lasts = replace_lasts_state allowed_l name lasts s in
          s :: states, lasts
        ) ([], QId.IdentSet.empty) states in
    let states = List.rev states in
    let lasts = (List.map QId.to_string (QId.IdentSet.elements lasts)) in

    (* Construct new inputs for the handler nodes for values of [last]
       applications on the base clock (i.e. outside the state) *)
    let lasts_inputs, lasts_args = List.map (fun l ->
        try
          let i = QId.from_string (name ^ ".last." ^ l) in
          (pos, i ,
             type_of_last inputs outputs locals (QId.from_string l),
             A.ClockTrue, false),
          (i, fun pos -> A.Last (pos, QId.from_string l)) (* Last replaced after parsing *)
        with Not_found ->
          fail_at_position pos ("Last type for "^l^" could not be inferred")
      ) lasts
      |> List.split
    in

    let argify_inputs pos =
      List.map (fun (_, i, _, _, _) ->
          try (List.assoc i lasts_args) pos
          with Not_found -> A.Ident (pos, i))
    in
    
    (* Pass [pre .] as arguments for the [last .] in the handler and unless of
       the state *)
    (* let lasts_args pos = List.map (fun l -> *)
    (*     A.Pre (pos, (A.Ident (pos, l))) *)
    (*   ) lasts in *)
    
    (* Create enumerated datatype for states *)
    let states_enum =
      List.map (function A.State (_, s, _, _, _, _, _) -> s) states in
    let states_type = A.EnumType (pos, QId.from_string name, states_enum) in
    (* Evaluate states type expression *)
    let states_ty = S.eval_ast_type ctx states_type in
    let bool_ty = S.eval_ast_type ctx (A.Bool pos) in

    (* look for automaton outputs in local variables and outputs *)
    let auto_outputs_dl = List.map (fun o ->
        try List.find (fun (_, o', _, _) -> QId.equal o o') outputs
        with Not_found ->
          try List.iter (function
              | A.NodeVarDecl (_, ((_, l, _, _) as ld)) when QId.equal o l ->
                raise (Found_auto_out ld)
              | _ -> ()) locals;
            fail_at_position pos ("Could not find automaton output "^ QId.to_string o)
          with Found_auto_out ld -> ld
      ) auto_outputs in

    (* let auto_outputs_idents = *)
    (*   List.map (fun o -> A.Ident (pos,o)) auto_outputs in *)
    
    (* Gather other node variables which are neither inputs nor outputs of the
       automaton *)
    let other_vars_dl = List.fold_left (fun acc (p, o, t, c) ->
        if not (List.exists (fun o' -> o = o') auto_outputs) then
          (p, o, t, c, false) :: acc
        else acc
      ) [] outputs in
    let other_vars_dl = List.fold_left (fun acc -> function
        | A.NodeVarDecl (_, (p, l, t, c)) ->
          if not (List.exists (fun o' -> l = o') auto_outputs) then
            (p, l, t, c, false) :: acc
          else acc
        | _ -> acc
      ) other_vars_dl locals in
    let other_vars_dl = List.rev other_vars_dl in
    (* let other_vars_idents = *)
    (*   List.map (fun (p, i, _, _, _) -> A.Ident (p,i)) other_vars_dl in *)
    
    (* find initial state *)
    let initial_state =
      let inits = List.find_all
          (function A.State (_, _, init, _, _, _, _) -> init) states in
      match inits, states with
      (* no initial states, take first *)
      | [], A.State (_, s, _, _, _, _, _) :: _ -> s
      (* one initial state *)
      | [A.State (_, s, _, _, _, _, _)], _ -> s
      (* no states *)
      | _, [] -> fail_at_position pos "No states in automaton"
      (* more thatn one initial state *)
      | _ :: _, _ ->
        fail_at_position pos "More than one initial state in automaton"
    in
    
    (* Node local variables used to encode the automaton *)
    let i_state = QId.from_string (String.concat "." [name; state_string]) in
    let i_restart = QId.from_string (String.concat "." [name; restart_string]) in
    let i_state_selected = QId.from_string (String.concat "." [name; state_selected_string]) in
    let i_restart_selected =
     QId.from_string( String.concat "." [name; restart_selected_string]) in
    let i_state_selected_next =
      QId.from_string (String.concat "." [name; state_selected_next_string]) in
    let i_restart_selected_next =
      QId.from_string(String.concat "." [name; restart_selected_next_string]) in
    (* Add them to the local variables of the current node *)
    let add_auto_local i ty ctx =
      let ident = I.mk_string_ident (QId.to_string i) in
      C.add_node_local ctx ident pos ty
    in
    let ctx = ctx
              |> add_auto_local i_state states_ty
              |> add_auto_local i_restart bool_ty
              |> add_auto_local i_state_selected states_ty
              |> add_auto_local i_restart_selected bool_ty
              |> add_auto_local i_state_selected_next states_ty
              |> add_auto_local i_restart_selected_next bool_ty
    in

    let info = {
      auto_name = name;
      node_inputs = inputs;
      auto_outputs = auto_outputs_dl;
      other_vars = other_vars_dl;
      lasts_inputs;
      states_lustre_type = states_type;
      i_state_selected;
      i_restart_selected;
      i_state;
      i_restart;
    } in

    (* Encode/evaluate automaton states and get the names of the corresponding
       new auxiliary nodes *)
    let ctx, aux_nodes =
      List.fold_left (fun (ctx, aux_nodes) s ->
          let ctx, n = encode_automaton_state info ctx s in
          ctx, (n :: aux_nodes)
        ) (ctx, []) states in
    
    let aux_nodes = List.rev aux_nodes in
    
    let handlers, unlesses = List.split aux_nodes in 

    (* state_selected = initial_state -> pre state_selected_next; *)
    let state_selected_eq =
      A.Equation
        (pos,
         A.StructDef (pos, [A.SingleIdent (pos, i_state_selected)]),
         A.Arrow (pos, A.Ident (pos, initial_state),
                  A.Pre (pos, A.Ident (pos, i_state_selected_next)))) in

    (* restart_selected = false -> pre restart_selected_next; *)
    let restart_selected_eq =
      A.Equation
        (pos,
         A.StructDef (pos, [A.SingleIdent (pos, i_restart_selected)]),
         A.Arrow (pos, A.Const (pos, A.False),
                  A.Pre (pos, A.Ident (pos, i_restart_selected_next)))) in

    (* let inputs_idents = *)
    (*   List.map (fun (_, i, _, _, _) -> A.Ident (pos, i)) inputs in *)
    
    let handlers_activate_calls =
      List.map2 (fun (handler, actual_inputs)
                  (A.State (pos, state_c, _, _, _, _, _)) ->
        state_c,
        (* activate handler every state = state_c restart every <restart> *)
        A.Activate
          (pos, QId.from_string handler,
           (* clock *)
           A.CompOp (pos, A.Eq, A.Ident (pos, i_state), A.Ident (pos, state_c)),
           (* restart *)
           A.Ident (pos, i_restart),
           (* arguments to the call = inputs of the node + others + lasts *)
           (* inputs_idents @ other_vars_idents @ (lasts_args pos) *)
           argify_inputs pos actual_inputs
          )
      ) handlers states in

    (* merge handlers calls:
       (state.in.next, restart.in.next, outputs ...) =
         merge state
           (S1 -> activate handler.S1 every state = S1 restart ...)
           (S2 -> activate handler.S1 every state = S2 restart ...)
    *)
    let handlers_eq =
      A.Equation (pos,
        A.StructDef (pos,
         List.map (fun i -> A.SingleIdent (pos, i))
           (i_state_selected_next :: i_restart_selected_next :: auto_outputs)),
        A.Merge (pos, i_state, handlers_activate_calls)) in

    let unlesses_activate_calls =
      List.map2 (fun (unless, actual_inputs)
                  (A.State (pos, state_c, _, _, _, _, _)) ->
        state_c,
        (* activate unless every state_selected =
           state_c restart every restart_selected *)
        A.Activate
          (pos, QId.from_string unless, 
           (* clock *)
           A.CompOp (pos, A.Eq, A.Ident (pos, i_state_selected), A.Ident (pos, state_c)),
           (* restart *)
           A.Ident (pos, i_restart_selected),
           (* arguments = state_selected + restart_selected +
              inputs of the node + outputs of the automaton + others*)
           (* A.Ident (pos, i_state_selected) :: *)
           (* A.Ident (pos, i_restart_selected) :: *)
           (* inputs_idents @ auto_outputs_idents @ other_vars_idents @ *)
           (* (lasts_args pos) *)
           argify_inputs pos actual_inputs
          )
      ) unlesses states in

    (* merge unlesses calls: 
       (state, restart) =
         merge state.in
           (S1 -> activate unless.S1 every state.in = S1 restart ...)
           (S2 -> activate unless.S1 every state.in = S2 restart ...)
    *)
    let unlesses_eq =
      A.Equation (pos,
        A.StructDef (pos,
         List.map (fun i -> A.SingleIdent (pos, i)) [i_state; i_restart]),
        A.Merge (pos, i_state_selected, unlesses_activate_calls)) in
    
    (* add equations to the node *)
    let ctx = eval_node_equation inputs outputs locals ctx state_selected_eq in
    let ctx =
      eval_node_equation inputs outputs locals ctx restart_selected_eq in
    let ctx = eval_node_equation inputs outputs locals ctx handlers_eq in
    let ctx = eval_node_equation inputs outputs locals ctx unlesses_eq in

    (* Format.eprintf "(\* Automaton equations *\)@.%a@.%a@.%a@.%a@.@." *)
    (*   A.pp_print_node_item (A.Body state_selected_eq) *)
    (*   A.pp_print_node_item (A.Body restart_selected_eq) *)
    (*   A.pp_print_node_item (A.Body handlers_eq) *)
    (*   A.pp_print_node_item (A.Body unlesses_eq); *)
    
    C.reset_in_automaton ctx


(* Encode branching conditions for transitions as an expression *)
and encode_transition_branch pos state_c default = function
  (* restart t *)
  | A.Target (A.TransRestart (pos_t, (pos_s, s))) ->
    A.GroupExpr (pos_t, A.ExprList, [A.Ident (pos_s, s); A.Const (pos_t,A.True)])
  (* resume t *)
  | A.Target (A.TransResume (pos_t, (pos_s, s))) ->
    A.GroupExpr (pos_t, A.ExprList, [A.Ident (pos_s, s); A.Const (pos_t,A.False)])
  (* if cond then_br; *)
  | A.TransIf (posif, cond, then_br, None) ->
    A.TernaryOp (posif, A.Ite, cond,
           encode_transition_branch pos state_c default then_br,
           (* else default *)
           default)
  (* if cond then then_br else/elsif else_br end; *)
  | A.TransIf (posif, cond, then_br, Some else_br) ->
    A.TernaryOp (posif, A.Ite, cond,
           encode_transition_branch pos state_c default then_br,
           encode_transition_branch pos state_c default else_br)

(* Encode body and until transition of state as a node *)
and encode_until_handler pos
    { auto_name; states_lustre_type;
      auto_outputs; other_vars; lasts_inputs;
      i_state_selected; i_restart_selected; node_inputs }
    state_c locals eqs until_tr ctx =
  let stay = A.GroupExpr (pos, A.ExprList, [A.Ident (pos, QId.from_string state_c); A.Const (pos, A.False)]) in
  let e = match until_tr with
    | None -> stay
    | Some (posb, br) -> encode_transition_branch posb state_c stay br
  in
  let eq =
    A.Equation
      (pos, A.StructDef
         (pos, List.map (fun i -> A.SingleIdent (pos, i))
            [i_state_selected; i_restart_selected]),
       e)
  in
  let name = String.concat "." [auto_name; handler_string; state_c] in
  let outputs =
    (pos, i_state_selected, states_lustre_type, A.ClockTrue) ::
    (pos, i_restart_selected, A.Bool pos, A.ClockTrue) ::
    auto_outputs
  in

  let ident = I.mk_string_ident name in
  (* Identifier must not be declared *)
  if C.node_in_context (C.prev ctx) ident then fail_at_position pos (
    Format.asprintf 
      "Auxiliary node %a is redeclared" 
      (I.pp_print_ident false) ident
  ) ;

  let allowed_inputs = node_inputs @ other_vars @ lasts_inputs in
  let actual_inputs = used_inputs allowed_inputs (eq :: eqs) in

  (* Create separate auxiliary context for node (not external) *)
  let node_ctx = C.create_node (C.prev ctx) ident false in
  let node_ctx =
    eval_node_decl node_ctx pos
      actual_inputs
      outputs
      locals
      (List.map (fun e -> A.Body e) (eq :: eqs)) None
  in

  (* Format.eprintf "%a@.@." *)
  (*   A.pp_print_declaration *)
  (*   (A.NodeDecl (pos, (name, false, [], actual_inputs, outputs, locals, *)
  (*                      (List.map (fun e -> A.Body e) (eq :: eqs)), None))); *)

  let ctx = C.add_node_to_context ctx node_ctx in
  
  (name, actual_inputs), ctx


(* encoding of unless condition for strong transition as an auxiliary node *)
and encode_unless pos
    {auto_name; states_lustre_type;
     node_inputs; auto_outputs; other_vars; lasts_inputs;
     i_state_selected; i_restart_selected; i_state; i_restart }
    state_c unless_tr ctx =
  let skip = A.GroupExpr (pos, A.ExprList, [A.Ident (pos, i_state_selected);
                               A.Ident (pos, i_restart_selected)]) in
  let e = match unless_tr with
    | None -> skip
    | Some (posb, br) -> encode_transition_branch posb state_c skip br
  in
  let eq =
      A.Equation (pos,
        A.StructDef (pos,
         List.map (fun i -> A.SingleIdent (pos, i)) [i_state; i_restart]),
         e)
  in
  let name = String.concat "." [auto_name; unless_string; state_c] in
  let auto_out_inputs =
    List.map (fun (p, o, t, c) -> (p, o, t, c, false)) auto_outputs in
  let inputs =
    (pos, i_state_selected, states_lustre_type, A.ClockTrue, false) ::
    (pos, i_restart_selected, A.Bool pos, A.ClockTrue, false) ::
    node_inputs @ auto_out_inputs @ other_vars @ lasts_inputs
  in
  let outputs = [
    pos, i_state, states_lustre_type, A.ClockTrue;
    pos, i_restart, A.Bool pos, A.ClockTrue;
  ] in

  let actual_inputs = used_inputs inputs [eq] in

  let ident = I.mk_string_ident name in
  (* Identifier must not be declared *)
  if C.node_in_context (C.prev ctx) ident then fail_at_position pos (
    Format.asprintf 
      "Auxiliary node %a is redeclared" 
      (I.pp_print_ident false) ident
  ) ;

  (* Create separate context for node (not external) *)
  let node_ctx = C.create_node (C.prev ctx) ident false in
  let node_ctx =
    eval_node_decl node_ctx pos actual_inputs outputs [] [A.Body eq] None
  in
  (* Format.eprintf "%a@.@." *)
  (*   A.pp_print_declaration *)
  (*   (A.NodeDecl (pos, (name, false, [], actual_inputs, outputs, [], *)
  (*                      [A.Body eq], None))); *)

  let ctx = C.add_node_to_context ctx node_ctx in

  (name, actual_inputs), ctx
  

(* Encode a state of an automaton. 
   Returns the name of the node to handle body/until and the name of the node
   for the unless transition, as well as a modified context.*)
and encode_automaton_state info ctx = function
  | A.State (pos, state_c, _, locals, eqs, unless_tr, until_tr) ->
    let handler, ctx =
      encode_until_handler pos info (QId.to_string state_c) locals eqs until_tr ctx in
    let unless, ctx = encode_unless pos info (QId.to_string state_c) unless_tr ctx in
    ctx, (handler, unless)




(* Evaluate node statements and add to context  *)
and eval_node_items inputs outputs locals ctx = function

  (* No more statements *)
  | [] -> ctx

  (* Assertion or equation *)
  | A.Body e :: tl -> 

    let ctx = eval_node_equation inputs outputs locals ctx e in
    
    (* Continue with next node statements *)
    eval_node_items inputs outputs locals ctx tl

  (* Property annotation *)
  | A.AnnotProperty (pos, name_opt, ast_expr) :: tl -> 
    (* report unguarded pre *)
    let ctx = C.set_guard_flag ctx (H.has_unguarded_pre ast_expr) in

    (* Evaluate Boolean expression and guard all pre operators *)
    let expr, ctx = 
      S.eval_bool_ast_expr [] ctx pos ast_expr 
      |> C.close_expr ~original:ast_expr pos
    in

    let ctx = C.reset_guard_flag ctx in
    
    let name = match name_opt with
      | Some n -> (
        if C.prop_name_in_context ctx n then
          fail_at_position pos
            (Format.asprintf "Name '%s' already used by another property" n)
        else n
      )
      | None -> Format.asprintf "@[<h>%a@]" A.pp_print_expr ast_expr
    in
    
    (* Add property to node *)
    let ctx = C.add_node_property ctx (Property.PropAnnot pos) name expr in

    (* Continue with next node statements *)
    eval_node_items inputs outputs locals ctx tl

  (* Annotation for main node *)
  | (A.AnnotMain true) :: tl -> 

    eval_node_items inputs outputs locals
      (C.set_node_main ctx)
      tl

  (* Annotation for main node *)
  | (A.AnnotMain false) :: tl -> 

    eval_node_items inputs outputs locals ctx tl


(** Try to parse a contract and add it as candidate to an optional contract.

Failure's silent. *)
and parse_implicit_contract scope inputs outputs ctx file contract_name = try (
  let in_ch = open_in file in

  (* Create lexing buffer *)
  let lexbuf = Lexing.from_function LustreLexer.read_from_lexbuf_stack in

  (* Initialize lexing buffer with channel *)
  LustreLexer.lexbuf_init 
    in_ch
    (try Filename.dirname (Flags.input_file ())
     with Failure _ -> Sys.getcwd ()) ;

  let ast = LustreParser.main LustreLexer.token lexbuf in
  (* Format.printf
    "contract: @[<v>%a@]@.@."
    (pp_print_list A.pp_print_declaration "@ ")  ast ; *)

  let call =
    (* Find the contract and build the call. *)
    ast |> List.fold_left (
      fun call -> function
      | A.ContractNodeDecl (
        pos, (id, _, cont_in, cont_out, _)
      ) when QId.equal id (QId.from_string contract_name) -> (
        (* Verify signatures match and construct call. *)
        try (
          let ok, ins =
            List.fold_left2 (
              fun (ok, ins) (
                pos, node_in, node_in_ty, _, _
              ) (
                _, cont_in, cont_in_ty, _, _
              ) ->
                ok && (node_in = cont_in),
                (A.Ident (pos, node_in)) :: ins
            ) (true, []) inputs cont_in
            |> fun (ok, ins) -> ok, List.rev ins
          in
          let ok, outs =
            List.fold_left2 (
              fun (ok, outs) (
                pos, node_out, node_out_ty, _
              ) (
                _, cont_out, cont_out_ty, _
              ) ->
                ok && (node_out = cont_out),
                (node_out) :: outs
            ) (ok, []) outputs cont_out
            |> fun (ok, outs) -> ok, List.rev outs
          in
          if ok then Some (
            A.ContractCall (pos, id, ins, outs)
          ) else call
        ) with _ -> call
      )
      | _ -> call
    ) None
  in
  match call with
  | Some _ ->
    let ctx = C.push_contract_scope ctx contract_name in
    let ctx = List.fold_left declaration_to_context ctx ast in
    let ctx = C.pop_contract_scope ctx in
    ctx, call
  | None -> raise Not_found
) with e -> (
  (* Printexc.to_string e
  |> Format.printf
    "[eval_node_decl] \
    @[<v>Could not load Kind 2 contract from `%s`:@ %s@]@.@." file ; *)
  ctx, None
)


(* Add declarations of node to context *)
and eval_node_decl
  ctx pos inputs outputs locals items contract_spec
=

  (* Add inputs to context: as state variable to ident_expr_map, and
     to inputs *)
  let ctx = eval_node_inputs ctx inputs in

  (* Add outputs to context: as state variable to ident_expr_map, and
     to outputs *)
  let ctx =
    eval_node_outputs ~is_single:(List.length outputs = 1) ctx outputs
  in

  (* |===| Contract stuff. *)

  (* Try to find a contract previously dumped by Kind 2. *)
  let scope =
    match C.current_node_name ctx with
    | Some name -> I.to_scope name
    | None -> failwith "[eval_node_decl] No current node in context."
  in
  let dir = Flags.subdir_for scope in

  (* Setting candidate flag for explicit contract. *)
  let contract_spec =
    match contract_spec with
    | None -> None
    | Some spec -> Some (
      spec |> List.map (fun item -> item, false)
    )
  in

  (* Augments an optional contract with a candidate declaration. *)
  let augment_contract contract decl =
    match contract with
    | Some contract -> Some ( (decl, true) :: contract )
    | None -> Some [ decl, true ]
  in

  (* Attempt to parse invariants logged in previous runs. *)
  let ctx, contract_spec =
    let target = Filename.concat dir Names.inv_log_file in
    match
      Names.inv_log_contract_name scope
      |> parse_implicit_contract scope inputs outputs ctx target
    with
    | ctx, None -> ctx, contract_spec
    | ctx, Some call ->
      let ctx =
        C.current_node_map ctx (
          fun ({ N.silent_contracts } as node) -> {
            node with N.silent_contracts = target :: silent_contracts
          }
        )
      in
      ctx, augment_contract contract_spec call
  in


  (* Attempt to parse contract logged in previous runs. *)
  let ctx, contract_spec =
    let target = Filename.concat dir Names.contract_gen_file in
    match
      Names.contract_name scope
      |> parse_implicit_contract scope inputs outputs ctx target
    with
    | ctx, None -> ctx, contract_spec
    | ctx, Some call ->
      let ctx =
        C.current_node_map ctx (
          fun ({ N.silent_contracts } as node) -> {
            node with N.silent_contracts = target :: silent_contracts
          }
        )
      in
      ctx, augment_contract contract_spec call
  in

  (* Parse contracts and add to context *)
  let ctx = match contract_spec with
    | None -> ctx
    | Some contract ->
      ( match C.current_node_name ctx with
        | None -> Format.printf "[contracts] no node in context@.@."
        | Some _ -> ()
      ) ;
      (* New scope for local declarations in contracts *)
      let ctx = C.push_scope ctx "contract" in
      (* Eval contracts. *)
      let ctx =
        eval_node_contract_spec I.Set.empty ctx pos []
          inputs outputs locals contract
      in
      let ctx = C.add_node_sofar_assumption ctx in
      (* Remove scope for local declarations in contract *)
      C.pop_scope ctx
  in

  (* New scope for local declarations in implementation *)
  let ctx = C.push_scope ctx "impl" in

  (* Add locals to context: as state variable to ident_expr_map, and
     to inputs *)
  let ctx = eval_node_locals ctx locals in

  (* Parse equations, assertions, properties, automata, etc. *)
  let ctx =
    eval_node_items inputs outputs locals ctx items in

  C.check_vars_defined ctx;
  
  (* Remove scope for local declarations in implementation *)
  let ctx = C.pop_scope ctx in

  (* Create node from current context and return *)
  ctx


(* ********************************************************************** *)
(* Parse declarations                                                     *)
(* ********************************************************************** *)

(** Handle declaration and return context. *)
and declaration_to_context ctx = function
(* Declaration of a type as alias or free *)
| A.TypeDecl (pos, type_rhs) ->

  let (i, type_expr) = match type_rhs with
    (* Replace type aliases with their right-hand-side *)
    | A.AliasType (_, i, type_expr) -> (i, type_expr)
    (* Replace free types with an abstract type with no user-accessible
     * representation. *)
    | A.FreeType (_, i) -> (i, A.AbstractType (pos, i))
  in

  (* Identifier of AST identifier *)
  let ident = I.mk_string_ident (QId.to_string i) in

  (* Type t must not be declared *)
  if C.type_in_context ctx ident then fail_at_position pos (
    Format.asprintf
      "Type %a is redeclared" (I.pp_print_ident false) ident
  ) ;

  (* Add all indexes of type to identifier and add to trie *)
  let res = S.eval_ast_type ctx type_expr in

  (* Return changed context and unchanged declarations *)
  C.add_type_for_ident ctx ident res

(* Declaration of a typed or untyped constant *)
| A.ConstDecl (_, const_decl) ->

  (* Add mapping of identifier to value to context *)
  eval_const_decl ctx const_decl

(* Function declaration without parameters *)
| A.FuncDecl (
  pos, (i, ext, [], inputs, outputs, locals, items, contracts)
) -> (

  (* Identifier of AST identifier *)
  let ident = I.mk_string_ident (QId.to_string i) in

  (* Identifier must not be declared *)
  if C.node_in_context ctx ident then fail_at_position pos (
    Format.asprintf 
      "Function %a is redeclared" 
      (I.pp_print_ident false) ident
  ) ;

  let pre_or_arrow_fail desc = function
    | Some illegal_pos -> fail_at_position pos (
      Format.asprintf
        "@[<v>in declaration of function %a:@ \
        in %s at %a:@ \
        illegal pre or arrow in function declaration@ \
        functions cannot have any state@]"
        (I.pp_print_ident false) ident
        desc
        pp_print_position illegal_pos
    )
    | None -> ()
  in

  (* No pre or arrow in locals, equations or contracts. *)
  ( locals
    |> List.iter (
      fun decl ->
        H.node_local_decl_has_pre_or_arrow decl
        |> pre_or_arrow_fail "local declaration"
    ) ;
    items
    |> List.iter (
      fun item ->
        H.node_item_has_pre_or_arrow item
        |> pre_or_arrow_fail "item"
    ) ;
    match contracts with
    | Some contract ->
      H.contract_has_pre_or_arrow contract
      |> pre_or_arrow_fail "contract item"
    | None -> ()
  ) ;

  (* Create separate context for function *)
  let fun_ctx = C.create_node ctx ident ext in
  (* Mark node as function. *)
  let fun_ctx = C.set_node_function fun_ctx in

  (* Evaluate function declaration in separate context *)
  let fun_ctx = 
    eval_node_decl
      fun_ctx pos inputs outputs locals items contracts
  in

  (* Check that all there's no (non-function) node call. *)
  ( C.current_node_calls fun_ctx
    |> List.iter (
      fun { N.call_pos ; N.call_node_name } ->
        let node = C.node_of_name fun_ctx call_node_name in
        if not node.N.is_function then fail_at_position call_pos (
          Format.asprintf
            "@[<v>in function %a@ \
            illegal call to node %a@ \
            functions can only call other functions, not nodes@]"
            (I.pp_print_ident false) ident
            (I.pp_print_ident false) call_node_name
        )
    )
  ) ;

  (* Add function to context *)
  C.add_node_to_context ctx fun_ctx
)

(* Node declaration without parameters *)
| A.NodeDecl (
  pos, (i, ext, [], inputs, outputs, locals, items, contracts)
) -> (

  (* Identifier of AST identifier *)
  let ident = I.mk_string_ident (QId.to_string i) in

  (* Identifier must not be declared *)
  if C.node_in_context ctx ident then fail_at_position pos (
    Format.asprintf 
      "Node %a is redeclared" 
      (I.pp_print_ident false) ident
  ) ;

  (* Create separate context for node *)
  let node_ctx = C.create_node ctx ident ext in

  (* Evaluate node declaration in separate context *)
  let node_ctx = 
    eval_node_decl
      node_ctx pos inputs outputs locals items contracts
  in
  
  (* Add node to context *)
  C.add_node_to_context ctx node_ctx
)

  (* try (
    (* Create separate context for node *)
    let node_ctx = C.create_node ctx ident in

    (* Evaluate node declaration in separate context *)
    let node_ctx = 
      eval_node_decl
        node_ctx pos inputs outputs locals equations contracts
    in

    (* Add node to context *)
    C.add_node_to_context ctx node_ctx

  (* Node may be forward referenced *)
  with C.Node_or_function_not_found (called_ident, pos) -> 
         
     if 

       (* Is the referenced node declared later? *)
       List.exists 
         (function 
           | A.NodeDecl (_, (i, _, _, _, _, _, _)) 
           | A.FuncDecl (_, (i, _, _, _)) 
             when i = (I.string_of_ident false) called_ident -> true 
           | _ -> false)
         decls

     then

       (

         (* Check circularity *)
         (try

            (* Get nodes that this forward references *)
            let called_deps = C.deps_of_node ctx called_ident in

            (* Is the reference circular? *)
            if I.Set.mem ident called_deps then 

              fail_at_position
                pos
                (Format.asprintf 
                   "Circular dependecy between nodes %a and %a" 
                   (I.pp_print_ident false) ident
                   (I.pp_print_ident false) called_ident)

          with Not_found -> ());

         (* Add new dependency *)
         let ctx = C.add_dep ctx ident called_ident in

         (* Move declaration to correct position.  

            Inefficient: might be better to do a topological sort
            beforehand *)
         let decls =
           List.fold_left 
             (fun acc d -> match d with 
                | A.NodeDecl (_, (i, _, _, _, _, _, _)) 
                | A.FuncDecl (_, (i, _, _, _)) 
                  when i = (I.string_of_ident false) called_ident ->
                  curr_decl :: d :: acc
                | _ -> d :: acc)
             [] 
             decls
           |> List.rev
         in

         (* Continue *)
         declarations_to_context ctx decls

       )

     else

       fail_at_position
         pos
         (Format.asprintf 
            "Node or function %a is not defined" 
            (I.pp_print_ident false) called_ident)) *)

(* Declaration of a contract node *)
| A.ContractNodeDecl (pos, node_decl) ->

  (* Add to context for later inlining *)
  C.add_contract_node_decl_to_context ctx (pos, node_decl)
(* 

(* Uninterpreted function declaration *)
| A.FuncDecl (pos, (i, inputs, outputs, contracts)) -> (

  (* Identifier of AST identifier *)
  let ident = I.mk_string_ident i in

  (* Identifier must not be declared *)
  if C.node_or_function_in_context ctx ident then (
    fail_at_position pos (
      Format.asprintf
         "Function %a is redeclared"
         (I.pp_print_ident false) ident
    )
  ) ;

  (* Create separate context for function *)
  let func_ctx = C.create_function ctx ident in

  (* Evaluate node declaration in separate context *)
  let func_ctx = eval_func_decl func_ctx inputs outputs contracts in

  (* Add node to context *)
  C.add_function_to_context ctx func_ctx
) *)



  (* (try

     (* Create separate context for function *)
     let func_ctx = C.create_function ctx ident in

     (* Evaluate node declaration in separate context *)
     let func_ctx = 
       eval_func_decl
         func_ctx
         inputs
         outputs
         contracts 
     in  

     (* Add node to context *)
     let ctx = C.add_function_to_context ctx func_ctx in

     (* Recurse for next declarations *)
     declarations_to_context ctx decls

   (* No references in function, since node or function calls not
      allowed *)
   with C.Node_or_function_not_found (called_ident, pos) -> 

       fail_at_position
         pos
         (Format.asprintf 
            "Node or function %a is not defined" 
            (I.pp_print_ident false) called_ident)) *)

(* ******************************************************************** *)
(* Unsupported below                                                    *)
(* ******************************************************************** *)


(* Parametric node declaration *)
| A.NodeParamInst (pos, _)
| A.NodeDecl (pos, _) ->
  fail_at_position pos "Parametric nodes are not supported"
(* Parametric function declaration *)
| A.FuncDecl (pos, _) ->
  fail_at_position pos "Parametric functions are not supported"

(* Add declarations of program to context *)
let rec declarations_to_context ctx = function

(* All declarations processed, return new context. *)
| [] -> ctx

(* Some declarations left. *)
| decl :: tail ->
  (* Getting next context and tail. *)
  let ctx, tail =
    (* Try to handle this declaration. If successful, the tail is unchanged. *)
    try declaration_to_context ctx decl, tail
    (* Otherwise, something unknown was found. Let's check if this something is
    forward referenced. *)
    with
    | Deps.Unknown_decl (typ, ident, pos) ->
      ctx, C.solve_fref ctx decl (typ, ident, pos) tail
  in
  (* Looping with (potentially) new context and tail. *)
  declarations_to_context ctx tail




(* ********************************************************************** *)
(* Main enty point                                                        *)
(* ********************************************************************** *)

(* Iterate over the declarations and return the nodes *)
let declarations_to_nodes decls = 

  (* Create fresh context with empty scope and no nodes *)
  let ctx = C.mk_empty_context () in

  (* Add declarations to context *)
  let ctx = declarations_to_context ctx decls in

  (* Return nodes in context *)
  C.get_nodes ctx, { G.free_constants = C.get_free_constants ctx;
                     G.state_var_bounds = C.get_state_var_bounds ctx }


(*

(* ********************************************************************** *)
(* Testing functions                                                      *)
(* ********************************************************************** *)

(* Entry point for standalone simplifier *)
let main () = 

  let in_ch = open_in Sys.argv.(1) in

  (* Create lexing buffer *)
  let lexbuf = Lexing.from_function LustreLexer.read_from_lexbuf_stack in
  
  (* Initialize lexing buffer with channel *)
  LustreLexer.lexbuf_init in_ch (Filename.dirname (Sys.argv.(1)));

  let nodes = 
    try 
      LustreParser.main LustreLexer.token lexbuf
      |> declarations_to_nodes 
    with LustreParser.Error -> 

      let pos = 
        Lexing.lexeme_start_p lexbuf |> position_of_lexing 
      in
      
      fail_at_position pos "Syntax error"

  in

  Format.printf 
    "@[<v>*** After LustreDeclarations:@,%a@]"
    (pp_print_list (N.pp_print_node false) "@,")
    nodes

;;


main ()

*)

(* 
   Local Variables:
   compile-command: "make -k -C ../.."
   indent-tabs-mode: nil
   End: 
*)
  
