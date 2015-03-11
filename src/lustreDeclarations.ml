(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

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

module A = LustreAst

module I = LustreIdent
module IT = LustreIdent.LustreIdentHashtbl

module D = LustreIndex

module E = LustreExpr
module ET = E.LustreExprHashtbl

module N = LustreNode

module C = LustreContext

module S = LustreSimplify



let pp_print_trie pp_i pp_e ppf t = 
  D.bindings t |> 
  pp_print_list
    (fun ppf (i, e) -> 
       if i = D.empty_index then 
         pp_e ppf e
       else
         Format.fprintf 
           ppf
           "%a: %a"
           pp_i i
           pp_e e)
    ";@ "
    ppf


(* ********************************************************************** *)
(* Parse constants                                                        *)
(* ********************************************************************** *)

(* Add declaration of constant to context *)
let eval_const_decl ctx = function

  (* Declaration of a free constant *)
  | A.FreeConst (pos, _, _) ->

    C.fail_at_position pos "Free constants not supported"

  (* Declaration of a typed or untyped constant *)
  | A.UntypedConst (pos, i, expr) 
  | A.TypedConst (pos, i, expr, _) as const_decl ->

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident i in

    if

      (try 

         (* Identifier must not be declared *)
         C.expr_in_context ctx ident 

       (* Fail if reserved identifier used *)
       with Invalid_argument e -> C.fail_at_position pos e)

    then

      (* Fail if identifier already declared *)
      C.fail_at_position 
        pos 
        (Format.asprintf 
           "Identifier %a is redeclared as constant" 
           (I.pp_print_ident false) ident);

    (* Evaluate constant expression *)
    let res, _ = 
      S.eval_ast_expr
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

           (* Evaluate type expression *)
           let type_expr' = S.eval_ast_type ctx type_expr in 

           (* Check if type of expression is a subtype of the defined
              type at each index *)
           D.iter2
             (fun _ def_type { E.expr_type } ->
                if not (Type.check_type expr_type def_type) then
                  raise E.Type_mismatch)
             type_expr'
             res

         with Invalid_argument _ | E.Type_mismatch -> 

           (C.fail_at_position
              pos
              "Type mismatch in constant declaration"))

      (* No type check for untyped or free constant *)
      | _ -> ());


    (* Return context with new mapping of identifier to expression *)
    C.add_expr_for_ident ctx ident res


(* ********************************************************************** *)
(* Parse signature                                                        *)
(* ********************************************************************** *)

(* Add all node inputs to contexts *)
let rec eval_node_inputs ctx = function

  (* All inputs parsed *)
  | [] -> ctx

  (* Input on the base clock *)
  | (pos, i, ast_type, A.ClockTrue, is_const) :: tl -> 

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident i in

    if 
      
      try 
        C.expr_in_context ctx ident 
      with Invalid_argument e -> 
        C.fail_at_position pos e
      
    then
      
      C.fail_at_position 
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

    C.fail_at_position pos "Clocked node inputs not supported"


(* Add all node inputs to contexts *)
let rec eval_node_outputs ?is_single ctx = function

  (* All outputs parsed *)
  | [] -> ctx

  (* Output on the base clock *)
  | (pos, i, ast_type, A.ClockTrue) :: tl -> 

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident i in

    if 
      
      try 
        C.expr_in_context ctx ident 
      with Invalid_argument e -> 
        C.fail_at_position pos e
      
    then
      
      C.fail_at_position 
        pos
        (Format.asprintf 
           "Node output %a already declared" 
           (I.pp_print_ident false) ident);
    
    (* Evaluate type expression *)
    let ident_types = S.eval_ast_type ctx ast_type in
  
    (* Add declaration of possibly indexed type to contexts *)
    let ctx = C.add_node_output ?is_single ctx ident ident_types in

    (* Continue with following inputs *)
    eval_node_outputs ctx tl

  | (pos, _, _, _) :: _ -> 

    C.fail_at_position pos "Clocked node outputs not supported"


(* Add all node local declarations to contexts *)
let rec eval_node_locals ctx = function

  (* All local declarations parsed *)
  | [] -> ctx


  (* Identifier must not be declared *)
  | A.NodeVarDecl (pos, (_, i, _, _)) :: _ 
  | A.NodeConstDecl (pos, A.FreeConst (_, i, _)) :: _
  | A.NodeConstDecl (pos, A.UntypedConst (_, i, _)) :: _
  | A.NodeConstDecl (pos, A.TypedConst (_, i, _, _)) :: _ when 

      (

        (* Identifier of AST identifier *)
        let ident = I.mk_string_ident i in

        try 
          C.expr_in_context ctx ident 
        with Invalid_argument e -> 
          C.fail_at_position pos e

      ) -> 

    C.fail_at_position 
      pos
      (Format.asprintf 
         "Node local variable or constant %a already declared" 
         A.pp_print_ident i)


  (* Local variable on the base clock *)
  | A.NodeVarDecl (pos, (_, i, var_type, A.ClockTrue)) :: tl -> 

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident i in

    (* Evaluate type expression *)
    let index_types = S.eval_ast_type ctx var_type in

    (* Add declaration of possibly indexed type to contexts *)
    let ctx = C.add_node_local ctx ident index_types in

    (* Continue with following outputs *)
    eval_node_locals ctx tl

  (* Local variable not on the base clock *)
  |  A.NodeVarDecl (pos, (_, i, _, _)) :: _ -> 

    C.fail_at_position 
      pos 
      (Format.asprintf 
         "Clocked node local variables not supported for %a" 
         A.pp_print_ident i)

  (* Local constant *)
  | A.NodeConstDecl (pos, const_decl) :: tl -> 

    (* Add mapping of identifier to value to context *)
    let ctx = eval_const_decl ctx const_decl in

    (* Continue with following outputs *)
    eval_node_locals ctx tl


(* ********************************************************************** *)
(* Parse contracts                                                        *)
(* ********************************************************************** *)

(* Add all node contracts to contexts *)
let rec eval_node_contracts ctx = function

  (* No more contract clauses *)
  | [] -> ctx

  (* Contract *)
  | (source, name, requires, ensures) :: tl ->

    (* Evaluate Boolean expression and guard all pre operators *)
    let aux (accum, ctx) (pos, expr) =

      (* Evaluate expression to a Boolean expression, may change
         context *)
      let expr', ctx = 
        S.eval_bool_ast_expr ctx pos expr
        |> C.close_expr pos
      in

      (* Add expression to accumulator, continue with possibly
         modified context *)
      expr' :: accum, ctx

    in

    (* Evaluate requirements *)
    let requires', ctx =
      List.fold_left aux ([], ctx) requires
    in

    (* Evaluate ensures *)
    let ensures', ctx =
      List.fold_left aux ([], ctx) ensures
    in

    (* Add contract to node *)
    let ctx = 
      C.add_node_contract ctx (name, source, requires', ensures')
    in

    (* Continue with next contract clauses *)
    eval_node_contracts ctx tl


(* ********************************************************************** *)
(* Parse equations                                                        *)
(* ********************************************************************** *)

(* Return trie of state variables from a structural assignment *)
let eval_struct_item ctx pos = function

  (* Single identifier *)
  | A.SingleIdent (pos, i) ->  

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident i in

    (* Get expression of identifier *)
    let res = 

      try

        C.assignable_state_var_of_ident ctx ident

      with 
        
        | Invalid_argument _ -> 
          
          C.fail_at_position 
            pos 
            "Assignment to identifier not possible"

        | Not_found -> 
          
          C.fail_at_position 
            pos 
            "Assignment to undeclared identifier"

    in

    (* Return trie of state variables and context unchanged *)
    (res, ctx)

  | A.TupleStructItem (pos, _)  
  | A.TupleSelection (pos, _, _) 
  | A.FieldSelection (pos, _, _) 
  | A.ArraySliceStructItem (pos, _, _) ->     

    C.fail_at_position 
      pos 
      "Assignment not supported" 


(* Remove elements of the left-hand side from the scope *)
let uneval_eq_lhs ctx = function

  (* Nothing added from structrural assignments *)
  | A.StructDef (pos, _) -> ctx

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
               (I.mk_string_ident v)
           in
           ctx)
        ctx
        (List.rev l)
    in
           
    ctx


(* Return a trie of state variables from the left-hand side of an
   equation *)
let rec eval_eq_lhs ctx pos = function

  (* Empty list for node calls without returns *)
  | A.StructDef (pos, []) -> (D.empty, ctx)

  (* Single item *)
  | A.StructDef (pos, [e]) -> 

    (* Get types of item *)
    let t, ctx = eval_struct_item ctx pos e in 

    (* Return types of indexes, no array bounds and unchanged
       context *)
    t, ctx

  (* List of items *)
  | A.StructDef (pos, l) -> 

    (* Combine by adding index for position on left-hand side *)
    let ctx, _, res = 
      List.fold_left
        (fun (ctx, i, accum) e -> 

           (* Get state variables of item *)
           let t, ctx = eval_struct_item ctx pos e in 

           (* Changed context *)
           (ctx,

            (* Go forwards through list *)
            succ i,

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
    res, ctx

  (* Recursive array definition *)
  | A.ArrayDef (pos, i, l) -> 

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident i in

    (* Get expression of identifier *)
    let expr = 
      try 

        C.expr_of_ident ctx ident 

      with Not_found -> 

        C.fail_at_position 
          pos 
          "Undeclared identifer on left-hand side"

    in

    let res = 
      D.map
        (fun e -> 
           if E.is_var e then E.state_var_of_expr e else
             C.fail_at_position 
               pos 
               "Invalid identifer on left-hand side")
        expr
    in

    (* Fail if the index in the second argument does not start with
       the same number of D.VarIndex keys as the length of list in the
       first argument. *)
    let rec aux = function 
      | [] -> (function _ -> ())
      | h :: tl1 -> 
        (function 
          | D.ArrayVarIndex _ :: tl2 -> aux tl1 tl2
          | _ -> 
            C.fail_at_position 
              pos 
              "Index mismatch for array")
    in

    (* Check that the variable has at least as many indexes as
       variables given *)
    List.iter (fun (i, _) -> aux l i) (D.bindings expr);

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
               (I.mk_string_ident v)
               (D.singleton D.empty_index expr)
           in
           (succ i, ctx))
        (0, ctx)
        l
    in

    res, ctx


(* Match bindings from a trie of state variables and bindings for a
   trie of expressions and produce a list of equations *)
let rec expand_tuple' pos accum bounds lhs rhs = match lhs, rhs with 

  (* No more equations, return in original order *)
  | [], [] -> accum

  (* Indexes are not of equal length *)
  | _, []
  | [], _ ->         

    C.fail_at_position pos "Type mismatch in equation: indexes not of equal length"

  (* All indexes consumed *)
  | ([], state_var) :: lhs_tl, ([], expr) :: rhs_tl -> 

    expand_tuple' 
      pos
      ((state_var, bounds, expr) :: accum)
      []
      lhs_tl
      rhs_tl

  (* Only array indexes may be left at head of indexes *)
  | (D.ArrayVarIndex b :: lhs_index_tl, state_var) :: lhs_tl, ([], expr) :: rhs_tl ->

    expand_tuple'
      pos
      accum
      (N.Bound b :: bounds)
      ((lhs_index_tl, state_var) :: lhs_tl)
      (([], expr) :: rhs_tl)

  (* Array variable on left-hand side, fixed index on right-hand side *)
  | ((D.ArrayVarIndex b :: lhs_index_tl as lhs_index), state_var) :: lhs_tl,
    (D.ArrayIntIndex i :: rhs_index_tl, expr) :: rhs_tl -> 

    (* TODO: Check if the bounds are equal. Not as easy as it sounds
       like, because the bounds may be computed. *)
    expand_tuple'
      pos
      accum
      (N.Fixed (E.mk_int_expr (Numeral.of_int i)) :: bounds)
      ((lhs_index_tl, state_var) :: 

       (* Replicate array index until all indexes on right-hand side
          covered *)
       (match rhs_tl with 
         | [] -> lhs_tl
         | _ -> (lhs_index, state_var) :: lhs_tl))

      ((rhs_index_tl, expr) :: rhs_tl)

  (* Array index on left-hand and right-hand side *)
  | (D.ArrayVarIndex b :: lhs_index_tl, state_var) :: lhs_tl,
    (D.ArrayVarIndex _ :: rhs_index_tl, expr) :: rhs_tl -> 

    (* TODO: Check if the bounds are equal. Not as easy as it sounds
       like, because the bounds may be computed. *)
    let i = 
      List.filter
        (function D.ArrayVarIndex _ -> true | _ -> false) 
        rhs_index_tl
      |> List.length
    in

    let expr' =
      E.mk_select
        expr
        (E.mk_index_var i)
    in

    expand_tuple'
      pos
      accum
      ((N.Bound b) :: bounds) 
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

      C.fail_at_position pos "Type mismatch in equation: indexes do not match"

  (* Record index on left-hand and right-hand side *)
  | (D.RecordIndex i :: lhs_index_tl, state_var) :: lhs_tl,
    (D.RecordIndex j :: rhs_index_tl, expr) :: rhs_tl -> 

    (* Indexes are sorted, must match *)
    if i = j then 

      expand_tuple'
        pos
        accum
        bounds
        ((lhs_index_tl, state_var) :: lhs_tl)
        ((rhs_index_tl, expr) :: rhs_tl)

    else

      C.fail_at_position pos "Type mismatch in equation: record indexes do not match"

  (* Mismatched indexes on left-hand and right-hand sides *)
  | (D.RecordIndex _ :: _, _) :: _, (D.TupleIndex _ :: _, _) :: _
  | (D.RecordIndex _ :: _, _) :: _, (D.ListIndex _ :: _, _) :: _
  | (D.RecordIndex _ :: _, _) :: _, (D.ArrayIntIndex _ :: _, _) :: _
  | (D.RecordIndex _ :: _, _) :: _, (D.ArrayVarIndex _ :: _, _) :: _

  | (D.TupleIndex _ :: _, _) :: _, (D.RecordIndex _ :: _, _) :: _
  | (D.TupleIndex _ :: _, _) :: _, (D.ListIndex _ :: _, _) :: _
  | (D.TupleIndex _ :: _, _) :: _, (D.ArrayIntIndex _ :: _, _) :: _
  | (D.TupleIndex _ :: _, _) :: _, (D.ArrayVarIndex _ :: _, _) :: _

  | (D.ListIndex _ :: _, _) :: _, (D.RecordIndex _ :: _, _) :: _
  | (D.ListIndex _ :: _, _) :: _, (D.TupleIndex _ :: _, _) :: _
  | (D.ListIndex _ :: _, _) :: _, (D.ArrayIntIndex _ :: _, _) :: _
  | (D.ListIndex _ :: _, _) :: _, (D.ArrayVarIndex _ :: _, _) :: _

  | (D.ArrayIntIndex _ :: _, _) :: _, (D.RecordIndex _ :: _, _) :: _
  | (D.ArrayIntIndex _ :: _, _) :: _, (D.TupleIndex _ :: _, _) :: _
  | (D.ArrayIntIndex _ :: _, _) :: _, (D.ListIndex _ :: _, _) :: _
  | (D.ArrayIntIndex _ :: _, _) :: _, (D.ArrayVarIndex _ :: _, _) :: _

  | (D.ArrayVarIndex _ :: _, _) :: _, (D.RecordIndex _ :: _, _) :: _
  | (D.ArrayVarIndex _ :: _, _) :: _, (D.TupleIndex _ :: _, _) :: _
  | (D.ArrayVarIndex _ :: _, _) :: _, (D.ListIndex _ :: _, _) :: _

  | (_ :: _, _) :: _, ([], _) :: _ 
  | ([], _) :: _, (_ :: _, _) :: _ ->

    C.fail_at_position pos "Type mismatch in equation: head indexes do not match"

    
(* Return a list of equations from a trie of state variables and a
   trie of expressions *)
let expand_tuple pos lhs rhs = 
  
  Format.printf
    "@[<v>lhs:@ %a@,rhs:@ %a@]@."
    (pp_print_trie (D.pp_print_index false) StateVar.pp_print_state_var) lhs
    (pp_print_trie 
       (D.pp_print_index false) 
       (E.pp_print_lustre_expr false)) 
    rhs;

  expand_tuple' 
    pos
    []
    []
    (List.map (fun (i, e) -> (List.rev i, e)) (D.bindings lhs))
    (List.map (fun (i, e) -> (List.rev i, e)) (D.bindings rhs))


(* Evaluate node statements and add to context  *)
let rec eval_node_equations ctx = function

  (* No more statements *)
  | [] -> ctx

  (* Assertion *)
  | A.Assert (pos, ast_expr) :: tl -> 

    (* Evaluate Boolean expression and guard all pre operators *)
    let expr, ctx = 
      S.eval_bool_ast_expr ctx pos ast_expr 
      |> C.close_expr pos
    in

    (* Add assertion to node *)
    let ctx = C.add_node_assert ctx expr in

    (* Continue with next node statements *)
    eval_node_equations ctx tl

  (* Property annotation *)
  | A.AnnotProperty (pos, ast_expr) :: tl -> 

    (* Evaluate Boolean expression and guard all pre operators *)
    let expr, ctx = 
      S.eval_bool_ast_expr ctx pos ast_expr 
      |> C.close_expr pos
    in

    (* Add property to node *)
    let ctx = C.add_node_property ctx (TermLib.PropAnnot pos) expr in

    (* Continue with next node statements *)
    eval_node_equations ctx tl

  (* Annotation for main node *)
  | A.AnnotMain :: tl -> 

    eval_node_equations 
      (C.set_node_main ctx)
      tl

  (* Equations with possibly more than one variable on the left-hand side

     The expression is without node calls, those have been
     abstracted *)
  | A.Equation (pos, lhs, ast_expr) :: tl -> 

    (* Trie of state variables on left-hand side and extended context
       for right-hand side *)
    let eq_lhs, ctx = eval_eq_lhs ctx pos lhs in

    (* Evaluate Boolean expression and guard all pre operators *)
    let eq_rhs, ctx = 

      (* Evaluate in extended context *)
      S.eval_ast_expr ctx ast_expr 

      (* Close each expression separately *)
      |> D.fold 
        (fun i e (t, c) -> 
           let e', c = C.close_expr pos (e, c) in 
           let t' = D.add i e' t in
           (t', c))
        D.empty

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
    let ctx =
      List.fold_left
        (fun ctx (sv, b, e) -> C.add_node_equation ctx pos sv b e)
        ctx
        equations
    in

    (* Continue with next node statements *)
    eval_node_equations ctx tl


(* Add declarations of node to context *)
let eval_node_decl
    ctx
    inputs
    outputs
    locals
    equations
    contracts = 

  (* Add inputs to context: as state variable to ident_expr_map, and
     to inputs *)
  let ctx = eval_node_inputs ctx inputs in

  (* Add outputs to context: as state variable to ident_expr_map, and
     to outputs *)
  let ctx = eval_node_outputs ~is_single:(List.length outputs = 1) ctx outputs in

(*
  (* Parse contracts and add to context in contracts *)
  let ctx = eval_node_contracts ctx contracts in
*)

  (* Add locals to context: as state variable to ident_expr_map, and
     to inputs *)
  let ctx = eval_node_locals ctx locals in

  (* Parse equations, assertions, properties *)
  let ctx = eval_node_equations ctx equations in

  Format.printf
    "%a@."
    N.pp_print_node_debug (C.node_of_context ctx);

  (* Create node from current context and return *)
  ctx 
  

(* ********************************************************************** *)
(* Parse declarations                                                     *)
(* ********************************************************************** *)

(* Add declarations of program to context *)
let rec declarations_to_context ctx = function 

  (* All declarations processed, return result *)
  | [] -> ctx

  (* Declaration of a type as alias or free *)
  | (A.TypeDecl (pos, A.AliasType (_, i, type_expr))) :: decls ->

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident i in

    if       

      (* Type t must not be declared *)
      C.type_in_context ctx ident

    then

      C.fail_at_position 
        pos
        (Format.asprintf 
           "Type %a is redeclared" 
           (I.pp_print_ident false) ident);

    (* Add all indexes of type to identifier and add to trie *)
    let res = S.eval_ast_type ctx type_expr in

    (* Return changed context and unchanged declarations *)
    let ctx = C.add_type_for_ident ctx ident res in

    (* Recurse for next declarations *)
    declarations_to_context ctx decls

  (* Declaration of a typed or untyped constant *)
  | (A.ConstDecl (_, const_decl)) :: decls ->

    (* Add mapping of identifier to value to context *)
    let ctx = eval_const_decl ctx const_decl in

    (* Recurse for next declarations *)
    declarations_to_context ctx decls

  (* Node declaration without parameters *)
  | (A.NodeDecl 
       (pos, 
        (i, 
         [], 
         inputs, 
         outputs, 
         locals, 
         equations, 
         contracts))) :: decls -> 

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident i in

    (* Identifier must not be declared *)
    if C.node_in_context ctx ident then

      (* Fail if identifier already declared *)
      C.fail_at_position 
        pos 
        (Format.asprintf 
           "Node %a is redeclared" 
           (I.pp_print_ident false) ident);

    (* Create separate context for node *)
    let node_ctx = C.create_node ctx ident in

    (* Evaluate node declaration in separate context *)
    let node_ctx = 
      eval_node_decl
        node_ctx
        inputs
        outputs
        locals
        equations
        contracts
    in  

    (* Add node to context *)
    let ctx = C.add_node_to_context ctx node_ctx in

    (* Recurse for next declarations *)
    declarations_to_context ctx decls

  (* Declaration of a contract node *)
  | A.ContractNodeDecl (pos, node_decl) :: decls -> 

    (* Add to context for later inlining *)
    let ctx = C.add_contract_node_decl_to_context ctx (pos, node_decl) in

    (* Recurse for next declarations *)
    declarations_to_context ctx decls

  (* ******************************************************************** *)
  (* Unsupported below                                                    *)
  (* ******************************************************************** *)

  (* Identifier is a free type *)
  | (A.TypeDecl (pos, (A.FreeType _))) :: decls -> 

    C.fail_at_position pos "Free types not supported"

  (* External function declaration *)
  | (A.FuncDecl (pos, _)) :: _ ->

    C.fail_at_position pos "Functions not supported"

  (* Parametric node declaration *)
  | (A.NodeParamInst (pos, _)) :: _
  | (A.NodeDecl (pos, _)) :: _ ->

    C.fail_at_position pos "Parametric nodes not supported" 


(* ********************************************************************** *)
(* Main enty point                                                        *)
(* ********************************************************************** *)

(* Iterate over the declarations and return the nodes *)
let declarations_to_nodes decls = 

  try

    (* Create fresh context with empty scope and no nodes *)
    let ctx = C.mk_empty_context () in

    (* Add declarations to context *)
    let ctx = declarations_to_context ctx decls in

    (* Return nodes in context *)
    C.get_nodes ctx

  (* Node may be forward referenced *)
  with C.Node_not_found (ident, pos) -> 

    if 

      (* Is the referenced node declared later? *)
      List.exists 
        (function 
          | A.NodeDecl (_, (i, _, _, _, _, _, _)) 
            when i = (I.string_of_ident false) ident -> true 
          | _ -> false)
        decls

    then

      C.fail_at_position 
        pos 
        (Format.asprintf 
           "Node %a is forward referenced" 
           (I.pp_print_ident false) ident)

    else

      C.fail_at_position
        pos
        (Format.asprintf 
           "Node %a is not defined" 
           (I.pp_print_ident false) ident)


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
      
      C.fail_at_position pos "Syntax error"

  in

  Format.printf 
    "@[<v>*** After LustreDeclarations:@,%a@]"
    (pp_print_list (N.pp_print_node false) "@,")
    nodes

;;


main ()

(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
