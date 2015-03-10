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


(* Return trie of state variables to assign to *)
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

let uneval_struct_item ctx = function

  (* Nothing added to context in single identifier *)
  | A.SingleIdent (pos, i) -> ctx

  | A.TupleStructItem (pos, _)  
  | A.TupleSelection (pos, _, _) 
  | A.FieldSelection (pos, _, _) 
  | A.ArraySliceStructItem (pos, _, _) ->     

    C.fail_at_position 
      pos 
      "Assignment not supported" 


let uneval_eq_lhs ctx = function

  (* Empty list for node calls without returns *)
  | A.StructDef (pos, []) -> ctx

  | A.StructDef (pos, _) -> ctx

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

(*    

      




(*
      debug lustreSimplify
          "parse_node_equation %a"
          A.pp_print_node_equation (A.Equation (pos, lhs, ast_expr))
      in
*)

    (* State variables and types of their assigned expressions *)
    let eq_lhs, indexes, context' = match lhs with 

      | A.StructDef (pos, struct_items) -> 

        let eq_lhs = 

          List.fold_left
            (function eq_lhs -> function 

               (* Left-hand side is a single identifier *)
               | A.SingleIdent (pos, ident) -> 

                 (* Trie of expressions for indexes of identifier *)
                 let ident_exprs = 

                   try 

                     (* Get expressions for each index of identifier *)
                     ITrie.find_prefix
                       ident
                       expr_of_ident

                   with Not_found -> 

                     fail_at_position 
                       pos 
                       "Undefined variable in assignment" 

                 in

                 (* Get next top index of accumulator, use empty
                    index if left-hand side contains only one
                    variable *)
                 let top_index =
                   match struct_items with 
                     | [] -> assert false
                     | [_] -> I.empty_index
                     | _ -> next_top_index_of_idx_trie eq_lhs
                 in

                 (* Add types of indexes to accumulator *)
                 let eq_lhs' = 
                   IdxTrie.fold
                     (fun i e a -> 

                        (* Expression must be a variable *)
                        if not (E.is_var e) then 

                          fail_at_position 
                            pos 
                            "Not assigning to variable";

                        (* Get state variable from expression *)
                        let state_var = 
                          E.state_var_of_expr e
                        in

                        if 

                          (* State variable must be an output *)
                          IdxTrie.exists 
                            (fun _ sv -> 
                               StateVar.equal_state_vars sv state_var)
                            node_outputs

                          || 

                          (* Or state variable must be a local variable *)
                          List.exists 
                            (fun sv -> 
                               StateVar.equal_state_vars sv state_var)
                            node_locals

                        then


                          (* Add type of state variable to accumulator *)
                          IdxTrie.add
                            (I.push_back_index_to_index top_index i)
                            state_var
                            a

                        else

                          fail_at_position 
                            pos 
                            "Assignment to neither output nor \
                             local variable")
                     ident_exprs
                     eq_lhs
                 in

                 (* Return state variables on left-hand side *)
                 eq_lhs'

               (* TODO: Structural assignments *)
               | _ -> 
                 fail_at_position
                   pos
                   "Structural assignments not supported")
            IdxTrie.empty
            struct_items

        in

        (eq_lhs, [], context)

      | A.ArrayDef (pos, ident, indexes) -> 

        let indexes', context' = 
          List.fold_left 
            (fun (indexes', context') index_ident -> 

               (* Fresh state variable for index *)
               let state_var = 
                 mk_fresh_state_var 
                   false 
                   Type.t_int
               in

               (* Associate index identifier with state variable *)
               let expr_of_ident' = 
                 ITrie.add
                   ident
                   (E.mk_var state_var E.base_clock)
                   expr_of_ident
               in

               (* Get array size from trie *)
               let array_size = 

                 try 

                   top_int_index_of_idx_trie

                     (try 

                        ITrie.find_prefix 
                          index_ident 
                          expr_of_ident

                      with Not_found ->

                        fail_at_position
                          pos
                          "Undefined variable in assignment")

                 with _ -> 

                   fail_at_position
                     pos
                     "Variable is not an array in assignment"

               in

               (indexes))

            indexes
        in

        eq_lhs, indexes', context'

    in

    (* Evaluate expression and guard all pre operators *)
    let eq_rhs, abstractions = 
      close_indexed_ast_expr
        pos
        (eval_ast_expr 
           abstractions
           context' 
           ast_expr)

    in

(*
          debug lustreSimplify
              "@[<v>abstractions:@,%a@]"
              pp_print_abstraction_context abstractions
          in
*)


    (* Add all equations to node *)
    let abstractions', context', node' = 

      try 

        IdxTrie.fold2
          (fun _ state_var expr (abstractions, context, node) -> 

             (* Add equation to node *)
             equation_to_node 
               abstractions

               (* Use previous with indexes removed *)
               context 

               node
               pos
               state_var
               indexes
               expr)

          eq_lhs
          eq_rhs

          (abstractions, context, node)

      with Invalid_argument _ -> 

        fail_at_position 
          pos
          "Type mismatch in equation"

    in

    (* Continue, and restart with previous empty abstractions *)
    parse_node_equations 
      abstractions'
      context'
      node'
      tl

*)

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

 (* Parse contracts and add to context in contracts *)
  let ctx = eval_node_contracts ctx contracts in

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




(*
  (* Declaration of a typed, untyped or free constant *)
  | (A.ConstDecl (pos, (A.UntypedConst (_, ident, _) as const_decl))) :: decls 
  | (A.ConstDecl (pos, (A.TypedConst (_, ident, _, _) as const_decl))) :: decls ->

    if

      (try 

         (* Identifier must not be declared *)
         ident_in_context global_context ident 

       (* Fail if reserved identifier used *)
       with Invalid_argument e -> fail_at_position pos e)

    then

      (* Fail if identifier already declared *)
      fail_at_position 
        pos 
        (Format.asprintf 
           "Identifier %a is redeclared as constant" 
           (I.pp_print_ident false) ident);

    (* Change context with constant declaration *)
    let global_context' = 
      add_const_decl global_context const_decl 
    in

    (* Recurse for next declarations *)
    declarations_to_nodes' global_context' decls


  (* Node declaration without parameters *)
  | (A.NodeDecl 
       (pos, 
        (node_ident, 
         [], 
         inputs, 
         outputs, 
         locals, 
         <<<<<<< HEAD
           equations, 
         contracts))) :: decls ->
    =======
    equations))) :: decls ->
>>>>>>> refs/remotes/origin/scade6-arrays

          (try 

             (* Add node declaration to global context *)
             let node_context = 
               parse_node
                 node_ident
                 global_context 
                 inputs 
                 outputs
                 locals
                 equations 
               <<<<<<< HEAD
                 contracts
               =======
               >>>>>>> refs/remotes/origin/scade6-arrays
             in

             (* Recurse for next declarations *)
             declarations_to_nodes' 
               { global_context with 
                   nodes = node_context :: nodes }
               decls

           (* Node may be forward referenced *)
           with Node_not_found (ident, pos) -> 

             if 

               (* Is the referenced node declared later? *)
               List.exists 
                 (function 
                   | A.NodeDecl (_, (i, _, _, _, _, _)) when i = ident -> true 
                   | _ -> false)
                 decls

             then

               fail_at_position 
                 pos 
                 (Format.asprintf 
                    "Node %a is forward referenced" 
                    (I.pp_print_ident false) ident)

             else

               fail_at_position
                 pos
                 (Format.asprintf 
                    "Node %a is not defined" 
                    (I.pp_print_ident false) ident))


               (* Node declaration without parameters *)
               | (A.FuncDecl (pos, _)) :: _ ->

                 fail_at_position pos "Functions not supported"


               (* Node declaration without parameters *)
               | (A.NodeParamInst (pos, _)) :: _
               | (A.NodeDecl (pos, _)) :: _ ->

                 fail_at_position pos "Parametric nodes not supported" 


*)

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


(* Add type declaration for an alias type to a context *)
let add_alias_type_decl 
    ({ type_of_ident } as context) 
    pos
    ident
    ident_type =

  (* Add all indexes of type to identifier and add to trie *)
  let type_of_ident' = 
    IdxTrie.fold
      (fun i t a -> ITrie.add (I.push_index i ident) t a)
      (eval_ast_type context ident_type)
      type_of_ident
  in

  (* Add association of type identifier with indexes to types *)
  { context with type_of_ident = type_of_ident' }


(* ******************************************************************** *)
(* Constant declarations                                                *)
(* ******************************************************************** *)


(* Add a typed or untyped constant declaration to the context *)
let add_typed_const_decl
    ident 
    ({ type_of_ident; expr_of_ident } as context) 
    pos
    expr 
    type_expr =

  try 

    (* Evaluate expression, must not generate new abstractions from
       node calls *)
    let expr', abstractions = 
      eval_ast_expr 
        (no_abstraction pos)
        context 
        expr 
    in

    (* Type check if type of constant given *)
    (match type_expr with 

      (* No type given *)
      | None -> ()

      (* Check if type of expression matches given type *)
      | Some t -> 

        (* Evaluate type expression *)
        let type_expr' = eval_ast_type context t in 

        (* Check if type of expression is a subtype of the defined
           type at each index *)
        IdxTrie.iter2
          (fun _ (def_type, _) { E.expr_type } ->
             if not (Type.check_type expr_type def_type) then
               raise E.Type_mismatch)
          type_expr'
          expr');

w    (* Add expression to constants *)
    let expr_of_ident' = 
      IdxTrie.fold
        (fun i e a ->

           (* Add index to identifier for constant *)
           let i' = I.push_index i ident in 

           (* Ensure we don't overwrite an already defined constant *)
           if ITrie.mem i' a then 
             fail_at_position pos "Identifier already declared"


           else
             
             (* Add expression as constant *)
             ITrie.add i' e a)

        expr'
        expr_of_ident
    in

    (* Return withe new constant in context *)
    { context with expr_of_ident = expr_of_ident' }


  (* Type mismatch if sets indexes are not equal *)
  with Invalid_argument _ | E.Type_mismatch ->

    fail_at_position pos "Type mismatch for expressions"


(* Add declaration of constant to context *)
let add_const_decl context = function 

  (* Free constant *)
  | A.FreeConst (pos, ident, _) -> 
    fail_at_position pos "Free constants not supported"


  (* Constant without type *)
  | A.UntypedConst (pos, ident, expr) -> 
    add_typed_const_decl ident context pos expr None

  (* Constant with given type *)
  | A.TypedConst (pos, ident, expr, type_expr) -> 
    add_typed_const_decl ident context pos expr (Some type_expr)
  

(* ******************************************************************** *)
(* Node declarations                                                    *)
(* ******************************************************************** *)


(* Add declaration of an identifier to trie and to context 

   Helper function for add_node_input_decl, add_node_output_decl *)
let add_node_decl_to_trie
    ({ expr_of_ident } as context)
    state_var_trie
    state_var_source
    scope
    ident
    ?is_const
    ?is_input
    ident_types =

  (* Get next index at root of trie *)
  let next_top_idx = next_top_index_of_idx_trie state_var_trie in

  (* Create state variable, add as expression with index to map of
     identifiers and as state variable to node inputs *)
  let expr_of_ident', state_var_trie' = 

    IdxTrie.fold

      (fun index t (expr_of_ident, state_var_trie) ->
         
         (* Add index to identifier *)
         let ident' = I.push_back_index index ident in

         (* Add index to highest index of inputs *)
         let index' = 
           I.push_back_index_to_index
             index
             next_top_idx
         in

         (* Create state variable as input and contant *)
         let state_var = 
           E.mk_state_var_of_ident
             ?is_input
             ?is_const
             scope
             ident' 
             t
         in

         (* State variable is an input *)
         E.set_state_var_source state_var state_var_source;

         (* Add expression to trie of identifier *)
         (ITrie.add ident' (E.mk_var state_var E.base_clock) expr_of_ident,

          (* Add state variable to trie of inputs *)
          IdxTrie.add index' state_var state_var_trie))
      
      ident_types
      (expr_of_ident, state_var_trie)

  in
  
  ({ context with expr_of_ident = expr_of_ident' }, 
   state_var_trie')
     

(* Add declaration of an identifier to list and to context

   Helper function for add_node_var_decl, add_node_oracle_decl *)
let add_node_decl_to_list
    ({ expr_of_ident } as context)
    state_var_list
    state_var_source
    scope
    ident
    ?is_const
    ?is_input
    ident_types =

  (* Create state variable, add as expression with index to map of
     identifiers and as state variable to node inputs *)
  let expr_of_ident', state_var_list' = 

    IdxTrie.fold

      (fun index t (expr_of_ident, state_var_list) ->
         
         (* Add index to identifier *)
         let ident' = I.push_back_index index ident in

         (* Create state variable as input and contant *)
         let state_var = 
           E.mk_state_var_of_ident
             ?is_input
             ?is_const
             scope
             ident' 
             t
         in

         (* State variable is an input *)
         E.set_state_var_source state_var state_var_source;

         (* Add expression to trie of identifier *)
         (ITrie.add ident' (E.mk_var state_var E.base_clock) expr_of_ident,

          (* Add state variable to list *)
          state_var :: state_var_list))
      
      ident_types
      (expr_of_ident, state_var_list)

  in
  
  ({ context with expr_of_ident = expr_of_ident' }, 
   state_var_list')
     

(* Add declaration of a node input to contexts *)
let add_node_input_decl
    context
    ({ N.inputs = node_inputs; N.name = node_ident } as node)
    pos
    ident
    ?is_const
    ident_types =

  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Add declaration of input to trie and context *)
  let context', node_inputs' = 
    add_node_decl_to_trie
      context
      node_inputs
      E.Input
      scope
      ident
      ?is_const
      ~is_input:true
      ident_types
  in

  (* Return context and node with declaration *)
  (context', { node with N.inputs = node_inputs' })
     

(* Add declaration of a node input to contexts *)
let add_node_output_decl
    context
    ({ N.outputs = node_outputs; N.name = node_ident } as node)
    pos
    ident
    ident_types =

  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Add declaration of output to trie and context *)
  let context', node_outputs' = 
    add_node_decl_to_trie
      context
      node_outputs
      E.Output
      scope
      ident
      ~is_input:false
      ~is_const:false
      ident_types
  in

  (* Return context and node with declaration *)
  (context', { node with N.outputs = node_outputs' })


(* Add declaration of a node local variable to contexts *)
let add_node_var_decl
    context
    ({ N.name = node_ident; N.locals = node_locals } as node)
    pos
    ident
    ident_types =
     
  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Add declaration of local variable to list and context *)
  let context', node_locals' = 
    add_node_decl_to_list
      context
      node_locals
      (if is_dummy_pos pos then E.Abstract else E.Local)
      scope
      ident
      ~is_input:false
      ~is_const:false
      ident_types
  in

  (* Return context and node with declaration *)
  (context', { node with N.locals = node_locals' })

    
(* Add declaration of an oracle input to contexts *)
let add_node_oracle_decl
    context
    ({ N.name = node_ident; N.oracles = node_oracles } as node)
    pos
    ident
    ident_types =
     
  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Add declaration of oracle to list and context *)
  let context', node_oracles' = 
    add_node_decl_to_list
      context
      node_oracles
      E.Oracle
      scope
      ident
      ~is_input:true
      ~is_const:true
      ident_types
  in

  (* Return context and node with declaration *)
  (context', { node with N.oracles = node_oracles' })


(* Add declaration of an observer output to contexts *)
let add_node_observer_decl
    ({ expr_of_ident } as context)
    ({ N.observers = node_observers; 
       N.name = node_ident } as node)
    ident
    ident_types =

  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Add declaration of observer to list and context *)
  let context', node_observers' = 
    add_node_decl_to_list
      context
      node_observers
      E.Observer
      scope
      ident
      ~is_input:false
      ~is_const:false
      ident_types
  in

  (* Return context and node with declaration *)
  (context', { node with N.observers = node_observers' })
  

(* Add all node inputs to contexts *)
let rec parse_node_inputs context node = function

  (* All inputs parsed, return in original order *)
  | [] -> (context, node)

  (* Identifier must not be declared *)
  | (pos, ident, _, _, _) :: _ when 

      (try 
         ident_in_context context ident 
       with Invalid_argument e -> 
         fail_at_position pos e) -> 

    fail_at_position 
      pos
      (Format.asprintf 
         "Node input %a already declared" 
         (I.pp_print_ident false) ident)

  (* Input on the base clock *)
  | (pos, ident, ast_type, A.ClockTrue, is_const) :: tl -> 

    (* Evaluate type expression *)
    let ident_types = eval_ast_type context ast_type in
  
    (* Add declaration of possibly indexed type to contexts *)
    let context', node' = 
      add_node_input_decl
        context
        node
        pos
        ident
        ~is_const
        ident_types
    in

    (* Continue with following inputs *)
    parse_node_inputs context' node' tl

  | (pos, _, _, _, _) :: _ -> 

    fail_at_position pos "Clocked node inputs not supported"


(* Add all node outputs to contexts *)
let rec parse_node_outputs context node = function

  (* All outputs parsed, return in original order *)
  | [] -> (context, node)

  (* Identifier must not be declared *)
  | (pos, ident, _, _) :: _ when       
      
      (try 
         ident_in_context context ident 
       with Invalid_argument e -> 
         fail_at_position pos e) -> 
    
    fail_at_position 
      pos
      (Format.asprintf 
         "Node output %a already declared" 
         (I.pp_print_ident false) ident)

  (* Output on the base clock *)
  | (pos, ident, ast_type, A.ClockTrue) :: tl -> 

    (* Evaluate type expression *)
    let ident_types = eval_ast_type context ast_type in

    (* Add declaration of possibly indexed type to contexts *)
    let context', node' = 
      add_node_output_decl
        context
        node
        pos
        ident
        ident_types
    in

    (* Continue with following outputs *)
    parse_node_outputs context' node' tl

  | (pos, _, _, _) :: _ -> 

    fail_at_position pos "Clocked node outputs not supported" 


(* Add all node local declarations to contexts *)
let rec parse_node_locals context node = function

  (* All local declarations parsed, order does not matter *)
  | [] -> (context, node)


  (* Identifier must not be declared *)
  | A.NodeVarDecl (pos, (_, ident, _, _)) :: _ 
  | A.NodeConstDecl (pos, A.FreeConst (_, ident, _)) :: _
  | A.NodeConstDecl (pos, A.UntypedConst (_, ident, _)) :: _
  | A.NodeConstDecl (pos, A.TypedConst (_, ident, _, _)) :: _ when 

      (try 
         ident_in_context context ident 
       with Invalid_argument e -> 
         fail_at_position pos e) -> 
    
    fail_at_position 
      pos
      (Format.asprintf 
         "Node local variable or constant %a already declared" 
         (I.pp_print_ident false) ident)


  (* Local variable on the base clock *)
  | A.NodeVarDecl (pos, (_, ident, var_type, A.ClockTrue)) :: tl -> 

    (* Evaluate type expression *)
    let ident_types = eval_ast_type context var_type in

    (* Add declaration of possibly indexed type to contexts *)
    let context', node' = 
      add_node_var_decl
        context
        node
        pos
        ident
        ident_types
    in
    
    (* Continue with following outputs *)
    parse_node_locals 
      context'
      node'
      tl

  (* Local variable not on the base clock *)
  |  A.NodeVarDecl (pos, (_, ident, _, _)) :: _ -> 

    fail_at_position 
      pos 
      (Format.asprintf 
         "Clocked node local variables not supported for %a" 
         (I.pp_print_ident false) ident)


  (* Local constant *)
  | A.NodeConstDecl (pos, const_decl) :: tl -> 

    (* Add declaration of constant to context *)
    let context' = add_const_decl context const_decl in

    (* Continue with following outputs *)
    parse_node_locals context' node tl


(* Add an expression as a property *)
let rec property_to_node 
    ({ mk_state_var_for_expr; new_vars } as abstractions)
    context
    node
    pos
    source
    expr =

  (* State variable for property and changed environment *)
  let abstractions', state_var =

    if 

      (* Property is a state variable at current offset? *)
      E.is_var expr

    then 

      (* State variable of expression *)
      let state_var = E.state_var_of_expr expr in

      (* No abstraction necessary *)
      (abstractions, state_var)

    else

      (* State variable of abstraction variable *)
      let state_var, new_vars' = 
        mk_state_var_for_expr false new_vars expr 
      in
      
      (* State variable is a locally abstracted variable *)
      E.set_state_var_source state_var E.Abstract;

      (* Property is new state variable *)
      ({ abstractions with new_vars = new_vars' }, state_var)
      
  in

  (* Add declatation of variable to observers *)
  let node_observers' = node.N.observers @ [state_var] in

  (* Remove declaration of variable from locals *)
  let node_locals' = 
    List.filter
      (fun sv -> not (StateVar.equal_state_vars sv state_var))
      node.N.locals
  in

  (* Remove declaration of variable from outputs *)
  let node_outputs' = 
    IdxTrie.filter
      (fun _ sv -> not (StateVar.equal_state_vars sv state_var))
      node.N.outputs
  in

  (* Add property to node *)
  (abstractions',
   context, 
   { node with 
       N.props = (state_var :: node.N.props); 
       N.observers = node_observers';
       N.locals = node_locals';
       N.outputs = node_outputs' }
   )


(* Add an expression as an assertion *)
and assertion_to_node abstractions context node pos expr = 

  let node' = { node with N.asserts = expr :: node.N.asserts } in

  (abstractions, context, node')

(* Add a contract to a node. *)
and contract_to_node context node abstractions contract =

<<<<<<< HEAD
  let node' =
    { node with N.contracts = contract :: node.N.contracts }
  in

  context, node', abstractions
=======
(* Add an expression as a contact clause *)
and assumption_to_node abstractions context node pos ident expr =

  let node' = 
    { node with N.assumptions = (ident, expr) :: node.N.assumptions } 
  in

  (abstractions, context, node')


(* Add an expression as a contact clause *)
and guarantee_to_node abstractions context node pos ident expr =

  let node' = 
    { node with N.guarantees = (ident, expr) :: node.N.guarantees } 
  in

  (abstractions, context, node')
>>>>>>> refs/remotes/origin/scade6-arrays


(* Add equational definition of a variable *)
and equation_to_node 
    abstractions
    context 
    node 
    pos
    state_var
    indexes
    ({ E.expr_type } as expr) = 

  (* Replace unguarded pre with oracle constants *)
  let expr', oracles' = 
    E.oracles_for_unguarded_pres
      pos
      abstractions.mk_oracle_pre_of_for_state_var
      warn_at_position
      abstractions.new_oracles
      expr
  in

  (* Type of state variable defined by expression *)
  let state_var_type = StateVar.type_of_state_var state_var in 

  (* Node with property added if subtyping cannot be inferred *)
  let abstractions', context', node' =

    if 

      (* Type must be a subtype of declared type *)
      Type.check_type expr_type state_var_type 

    then

      (* Nothing to add *)
      abstractions, context, node

    else

      (* Type of expression may not be subtype of declared type *)
      (match state_var_type, expr_type with 

        (* Declared type is integer range, expression is of type
           integer *)
        | t, s 
          when Type.is_int_range t && (Type.is_int s || Type.is_int_range s) -> 

          let (lbound, ubound) = Type.bounds_of_int_range t in

          (* Value of expression is in range of declared type: 
             lbound <= expr and expr <= ubound *)
          let range_expr = 
            (E.mk_and 
               (E.mk_lte (E.mk_int lbound) expr) 
               (E.mk_lte expr (E.mk_int ubound)))
          in

          let msg =
            Format.sprintf
              "Cannot determine correctness of subrange type, \
               adding constraint as property and reverting to type int for
               variable %s." (StateVar.string_of_state_var state_var) in

          warn_at_position pos msg;

          (* Expanding type of state variable to int *)
          StateVar.change_type_of_state_var state_var (Type.mk_int ());
          
          (* Add property to node *)
          property_to_node 
            abstractions 
            context 
            node
            A.dummy_pos 
            range_expr

        | t, s -> 

          fail_at_position
            pos
            (Format.asprintf 
               "Type mismatch between variable of type %a and expression of type %a"
               (E.pp_print_lustre_type false) state_var_type
               (E.pp_print_lustre_type false) expr_type))

  in

  (* Add oracle constants to abstraction *)
  let abstractions' = 
    { abstractions' with new_oracles = oracles' } 
  in

  (* Add equation and abstractions *)
  (abstractions',
   context', 
   { node' with 
       N.equations = (state_var, (indexes, expr')) :: node'.N.equations })


(* Parse a statement (equation, assert or annotation) in a node *)
let rec parse_node_equations 
    ({ mk_fresh_state_var } as abstractions)
    ({ expr_of_ident } as context) 
    ({ N.name = node_ident;
       N.outputs = node_outputs;
       N.locals = node_locals } as node ) = 

  function

    (* No more statements *)
    | [] -> abstractions, context, node 

    (* Assertion *)
    | A.Assert (pos, ast_expr) :: tl -> 

      (* Evaluate Boolean expression and guard all pre operators *)
      let expr', abstractions = 
        close_ast_expr
          pos
          (bool_expr_of_ast_expr 
             abstractions
             context 
             pos
             ast_expr)
      in

      (* Add assertion to node *)
      let abstractions', context', node' = 
        assertion_to_node abstractions context node pos expr'
      in

      (* Continue with next node statements, and restart with previous
         empty abstractions *)
      parse_node_equations 
        abstractions'
        context'
        node' 
        tl

    (* Property annotation *)
    | A.AnnotProperty (pos, ast_expr) :: tl -> 

      (* Evaluate Boolean expression and guard all pre operators *)
      let expr', abstractions = 
        close_ast_expr
          pos
          (bool_expr_of_ast_expr 
             abstractions
             context 
             pos
             ast_expr)
      in

      (* Add assertion to node *)
      let abstractions', context', node' = 
        property_to_node abstractions context node pos expr'
      in

      (* Continue with next node statements, and restart with previous
         empty abstractions *)
      parse_node_equations 
        abstractions'
        context'
        node' 
        tl


    (* Equations with possibly more than one variable on the left-hand side

       The expression is without node calls, those have been
       abstracted *)
    | A.Equation (pos, lhs, ast_expr) :: tl -> 

(*
      debug lustreSimplify
          "parse_node_equation %a"
          A.pp_print_node_equation (A.Equation (pos, lhs, ast_expr))
      in
*)

      (* State variables and types of their assigned expressions *)
      let eq_lhs, indexes, context' = match lhs with 

        | A.StructDef (pos, struct_items) -> 

          let eq_lhs = 

            List.fold_left
              (function eq_lhs -> function 

                 (* Left-hand side is a single identifier *)
                 | A.SingleIdent (pos, ident) -> 

                   (* Trie of expressions for indexes of identifier *)
                   let ident_exprs = 

                     try 

                       (* Get expressions for each index of identifier *)
                       ITrie.find_prefix
                         ident
                         expr_of_ident

                     with Not_found -> 

                       fail_at_position 
                         pos 
                         "Undefined variable in assignment" 

                   in

                   (* Get next top index of accumulator, use empty
                      index if left-hand side contains only one
                      variable *)
                   let top_index =
                     match struct_items with 
                       | [] -> assert false
                       | [_] -> I.empty_index
                       | _ -> next_top_index_of_idx_trie eq_lhs
                   in

                   (* Add types of indexes to accumulator *)
                   let eq_lhs' = 
                     IdxTrie.fold
                       (fun i e a -> 

                          (* Expression must be a variable *)
                          if not (E.is_var e) then 

                            fail_at_position 
                              pos 
                              "Not assigning to variable";

                          (* Get state variable from expression *)
                          let state_var = 
                            E.state_var_of_expr e
                          in

                          if 

                            (* State variable must be an output *)
                            IdxTrie.exists 
                              (fun _ sv -> 
                                 StateVar.equal_state_vars sv state_var)
                              node_outputs

                            || 

                            (* Or state variable must be a local variable *)
                            List.exists 
                              (fun sv -> 
                                 StateVar.equal_state_vars sv state_var)
                              node_locals

                          then


                            (* Add type of state variable to accumulator *)
                            IdxTrie.add
                              (I.push_back_index_to_index top_index i)
                              state_var
                              a

                          else

                            fail_at_position 
                              pos 
                              "Assignment to neither output nor \
                               local variable")
                       ident_exprs
                       eq_lhs
                   in

                   (* Return state variables on left-hand side *)
                   eq_lhs'

                 (* TODO: Structural assignments *)
                 | _ -> 
                   fail_at_position
                     pos
                     "Structural assignments not supported")
              IdxTrie.empty
              struct_items

          in

          (eq_lhs, [], context)

        | A.ArrayDef (pos, ident, indexes) -> 

          let indexes', context' = 
            List.fold_left 
              (fun (indexes', context') index_ident -> 

                 (* Fresh state variable for index *)
                 let state_var = 
                   mk_fresh_state_var 
                     false 
                     Type.t_int
                 in

                 (* Associate index identifier with state variable *)
                 let expr_of_ident' = 
                   ITrie.add
                     ident
                     (E.mk_var state_var E.base_clock)
                     expr_of_ident
                 in

                 (* Get array size from trie *)
                 let array_size = 

                   try 

                     top_int_index_of_idx_trie

                       (try 

                          ITrie.find_prefix 
                            index_ident 
                            expr_of_ident

                        with Not_found ->

                          fail_at_position
                            pos
                            "Undefined variable in assignment")

                   with _ -> 

                     fail_at_position
                       pos
                       "Variable is not an array in assignment"

                 in

                 (indexes))

                 indexes
          in

          eq_lhs, indexes', context'

      in

      (* Evaluate expression and guard all pre operators *)
      let eq_rhs, abstractions = 
        close_indexed_ast_expr
          pos
          (eval_ast_expr 
             abstractions
             context' 
             ast_expr)

      in

(*
          debug lustreSimplify
              "@[<v>abstractions:@,%a@]"
              pp_print_abstraction_context abstractions
          in
*)


      (* Add all equations to node *)
      let abstractions', context', node' = 

        try 

          IdxTrie.fold2
            (fun _ state_var expr (abstractions, context, node) -> 

               (* Add equation to node *)
               equation_to_node 
                 abstractions

                 (* Use previous with indexes removed *)
                 context 

                 node
                 pos
                 state_var
                 indexes
                 expr)

            eq_lhs
            eq_rhs

            (abstractions, context, node)

        with Invalid_argument _ -> 

          fail_at_position 
            pos
            "Type mismatch in equation"

      in

      (* Continue, and restart with previous empty abstractions *)
      parse_node_equations 
        abstractions'
        context'
        node'
        tl


    (* Annotation for main node *)
    | A.AnnotMain :: tl -> 

      parse_node_equations 
        abstractions
        context 
        { node with N.is_main = true }
        tl

    (* Assumption *)
    | A.Assume (pos, ident, expr) :: tl -> 

      (* Evaluate Boolean expression and guard all pre operators *)
      let expr', abstractions = 
        close_ast_expr
          pos
          (bool_expr_of_ast_expr 
             abstractions
             context 
             pos
             expr)
      in

      (* Add assertion to node *)
      let abstractions', context', node' = 
        assumption_to_node abstractions context node pos ident expr'
      in

      (* Continue with next contract clauses, and restart with
         previous empty abstractions *)
      parse_node_equations
        abstractions'
        context' 
        node'
        tl


    (* Guarantee *)
    | A.Guarantee (pos, ident, expr) :: tl -> 

      (* Evaluate Boolean expression and guard all pre operators *)
      let expr', abstractions = 
        close_ast_expr
          pos
          (bool_expr_of_ast_expr 
             abstractions
             context 
             pos
             expr)
      in

      (* Add assertion to node *)
      let abstractions', context', node' = 
        guarantee_to_node abstractions context node pos ident expr'
      in

      (* Continue with next contract clauses, and restart with
         previous empty abstractions *)
      parse_node_equations
        abstractions'
        context' 
        node'
        tl


(* Add abstracted variables and node calls to context *)
let abstractions_to_context_and_node 
    ({ new_vars } as abstractions)
    context 
    node =

  (* Add declaration of variables to context

     Must add variables first, this may generate new abstractions from
     unguarded pres. *)
  let ({ new_oracles } as abstractions'), context', node' = 

    List.fold_left 
      (fun (abstractions, context, node) (state_var, expr) -> 

         (* Split scope from name of variable *)
         let ident, scope = 
           E.ident_of_state_var state_var
         in

         (* Add variable declaration to context *)
         let context', node' =
           add_node_var_decl
             context
             node
             A.dummy_pos
             ident
             (IdxTrie.add
                I.empty_index
                (StateVar.type_of_state_var state_var)
                IdxTrie.empty)
         in

         (* Add equation to node *)
         let abstractions', context', node' = 
           equation_to_node 
             abstractions context'
             node'
             A.dummy_pos 
             state_var 
             []
             expr 
         in

         (abstractions', context', node'))

      (abstractions, context, node)
      new_vars

  in

  (* Add declaration of oracle inputs to context *)
  let ({ new_calls } as abstractions'),  context', node' = 

    List.fold_left 
      (fun (abstractions, context, node) (state_var) -> 

         (* Split scope from name of variable *)
         let (ident, scope) = 
           E.ident_of_state_var state_var
         in

         (* Add oracle declaration to context *)
         let context', node' = 
           add_node_oracle_decl
             context
             node
             A.dummy_pos
             ident
             (IdxTrie.add
                I.empty_index
                (StateVar.type_of_state_var state_var)
                IdxTrie.empty)
         in
         
         (abstractions, context', node'))

      (abstractions', context', node')
      new_oracles

  in

  (* Add declaration of return variables of calls to context

     No need to iterate over observers, they will become observers of
     the calling node *)
  let ({ new_observers } as abstractions'), context', node' = 

    List.fold_left
      (fun 
        accum
        ({ N.call_returns = outputs;
           N.call_observers = observers;
           N.call_node_name = node_call_ident } as call) ->

         let abstractions', context', node' = 
           IdxTrie.fold
             (fun _ state_var (abstractions, context, node) -> 
                
                (* Split scope from name of variable *)
                let (ident, scope) = 
                  E.ident_of_state_var state_var
                in
                
                (* Add variable declaration to context *)
                let context', node' = 

                  if 

                    (* Variable is already declared as output or
                       local? *)
                    (IdxTrie.exists 
                       (fun _ sv -> 
                          StateVar.equal_state_vars sv state_var)
                       node.N.outputs)

                    || (List.exists 
                          (fun sv -> 
                             StateVar.equal_state_vars sv state_var)
                          node.N.locals)

                  then

                    (* Return context and node unchanged *)
                    (context, node)

                  else

                    (* Add new local variable to node *)
                    add_node_var_decl
                      context
                      node
                      A.dummy_pos
                      ident
                      (IdxTrie.add
                         I.empty_index
                         (StateVar.type_of_state_var state_var)
                         IdxTrie.empty)

                in

                abstractions, context', node')
             outputs
             accum
         in 
 
         (abstractions',
          context', 
          { node' with N.calls = call :: node'.N.calls }))

      (abstractions', context', node')
      new_calls

  in

  (* Add declaration of observer outputs to context *)
  let abstractions', context', node' = 

    List.fold_left 
      (fun (abstractions, context, node) (state_var) -> 

         (* Split scope from name of variable *)
         let (ident, scope) = 
           E.ident_of_state_var state_var
         in

         (* Add variable declaration to context and oracle input to node *)
         let context', node' = 
           add_node_observer_decl
             context
             node
             ident
             (IdxTrie.add
                I.empty_index
                (StateVar.type_of_state_var state_var)
                IdxTrie.empty)
         in

         (abstractions, context', node'))

      (abstractions', context', node')
      new_observers

  in

<<<<<<< HEAD
  context', node', abstractions' 


(* Parse a statement (equation, assert or annotation) in a node *)
let rec parse_node_equations 
    context 
    abstractions 
    ({ N.name = node_ident } as node ) = 

  function

    (* No more statements *)
    | [] -> abstractions, context, node 

    (* Assertion *)
    | A.Assert (pos, ast_expr) :: tl -> 

      (* Evaluate Boolean expression and guard all pre operators *)
      let expr', abstractions' = 
        close_ast_expr
          pos
          (bool_expr_of_ast_expr 
             context 
             abstractions
             pos
             ast_expr)
      in
      
      (* Add assertion to node *)
      let context', node', abstractions' = 
        assertion_to_node context node abstractions' pos expr'
      in
      
      (* Continue with next node statements *)
      parse_node_equations 
        context'
        abstractions'
        node' 
        tl

    (* Property annotation *)
    | A.AnnotProperty (pos, ast_expr) :: tl -> 

      (* Evaluate Boolean expression and guard all pre operators *)
      let expr', abstractions' = 
        close_ast_expr
          pos
          (bool_expr_of_ast_expr 
             context 
             abstractions
             pos
             ast_expr)
      in
      
      (* Add assertion to node *)
      let context', node', abstractions' = 
        property_to_node 
          context 
          node
          abstractions'
          pos
          (TermLib.PropAnnot pos) 
          expr'
      in
      
      (* Continue with next node statements *)
      parse_node_equations 
        context'
        abstractions'
        node' 
        tl


    (* Equations with possibly more than one variable on the left-hand side

       The expression is without node calls, those have been
       abstracted *)
    | A.Equation (pos, struct_items, ast_expr) :: tl -> 

      debug lustreSimplify
        "parse_node_equation %a"
        A.pp_print_node_equation (A.Equation (pos, struct_items, ast_expr))
      in
      
      (* Evaluate expression and guard all pre operators *)
      let expr', abstractions = 
        close_indexed_ast_expr
          pos
          (eval_ast_expr 
             context 
             abstractions
             ast_expr)

      in

      debug lustreSimplify
        "@{<hv>expr' is @[<v>%a@]@]"
        (pp_print_list 
           (fun ppf (i, e) -> 
              Format.fprintf ppf "%a: %a" 
                (I.pp_print_index false) i
                (E.pp_print_lustre_expr false) e)
           "@,")
           expr'
      in
      
      debug lustreSimplify
        "@[<v>abstractions:@,%a@]"
        pp_print_abstraction_context abstractions
      in

      (* State variables and types of their assigned expressions *)
      let eq_types = 
        List.rev
          (List.fold_left
             (function accum -> function
                
                (* Left-hand side is a single identifier *)
                | A.SingleIdent (pos, ident) -> 

                  (* Find identifier of left-hand side in outputs *)
                  let accum' =
                    List.fold_left
                      (fun a (v, _) -> 
                         try 
                           (ignore 
                              (I.get_suffix
                                 ident
                                 (fst (E.ident_of_state_var v))); 
                            v) :: a
                         with Not_found ->
                           a)
                      accum
                      node.N.outputs
                  in

                  (* Identifier not found in outputs *)
                  if accum' = accum then

                    (* Find identifier of left-hand side in local variables *)
                    let accum'' = 
                      List.fold_left
                        (fun a (v, _) -> 
                           try 
                             (ignore 
                                (I.get_suffix
                                   ident
                                   (fst (E.ident_of_state_var v)));
                              (* Format.printf
                                "found in locals %a@." 
                                StateVar.pp_print_state_var v; *)
                              v) :: a
                           with Not_found ->
                             a)
                        accum
                        node.N.locals
                    in

                    (* Identifier not found in outputs and local variables *)
                    if accum'' = accum' then 
                      
                      fail_at_position 
                        pos 
                        "Assignment to neither output nor local variable" 

                    else

                      (* Return *)
                      accum''

                  else

                    (* Return *)
                    accum'

                (* TODO: Recursive assignments to indexed variables 

                   Need to add to scope of expression per definition
                   from variable on the left-hand side

                   For possibly recursive definitions use define-fun
                   to either unroll definitions or quantify. *)
                | A.IndexedIdent (pos, ident, index) -> 
              
                  fail_at_position
                    pos
                    "Indexed definitions not supported"

                (* TODO: Structural assignments *)
                | _ -> 
                  fail_at_position
                    pos
                    "Structural assignments not supported")

             []
             struct_items)
      in

      (* Add all equations to node *)
      let context', node', abstractions' = 

        try 

          List.fold_right2
            
            (fun state_var (_, expr) (context, node, abstractions) -> 
               
               (* Do not check for matching indexes here, the best thing
                  possible is to compare suffixes, but it is not obvious, where
                  to start suffix at *)
               let eq = (state_var, expr) in
               
               (* Add assertion to node *)
               equation_to_node context node abstractions pos eq)
            
            eq_types
            expr'
            (context, node, abstractions)

        with Invalid_argument "List.fold_right2" -> 

          fail_at_position 
            pos
            "Type mismatch in equation"

      in

      (* Continue *)
      parse_node_equations 
        context'
        abstractions'
        node'
        tl


    (* Annotation for main node *)
    | A.AnnotMain :: tl -> 

      parse_node_equations 
        context 
        abstractions
        { node with N.is_main = true }
        tl


(* Parse a contract annotation of a node *)
let rec parse_node_contracts
    context 
    abstractions
    ({ N.name = node_ident } as node) = function

  (* No more contract clauses *)
  | [] -> (abstractions, context, node)


  (* Assumption *)
  | (source, name, requires, ensures) :: tail ->

     let requires', abstractions' =
       requires
       |> List.fold_left
            ( fun (list,abs) (pos, req) ->

              (* Evaluate Boolean expression and guard all pre
                 operators *)
              let expr', abs' = 
                close_ast_expr
                  pos
                  (bool_expr_of_ast_expr 
                     context 
                     abs
                     pos
                     req)
              in

              expr' :: list, abs' )
            ([], abstractions)
     in

     let ensures', abstractions' =
       ensures
       |> List.fold_left
            ( fun (list,abs) (pos, ens) ->

              (* Evaluate Boolean expression and guard all pre
                 operators *)
              let expr', abs' = 
                close_ast_expr
                  pos
                  (bool_expr_of_ast_expr 
                     context 
                     abs
                     pos
                     ens)
              in

              expr' :: list, abs' )
            ([], abstractions')
     in

     (* Add contract to node *)
     let context', node', abstractions' = 
       contract_to_node context node abstractions' (name, source, requires', ensures')
     in

     (* Continue with next contract clauses *)
     parse_node_contracts
       context' 
       abstractions'
       node'
       tail
=======
  abstractions', context', node'
>>>>>>> refs/remotes/origin/scade6-arrays


(* Return a LustreNode.t from a node LustreAst.node_decl *)
let parse_node  
    node_ident
    global_context
    inputs 
    outputs 
    locals 
<<<<<<< HEAD
    equations 
    contracts =
=======
    equations =
>>>>>>> refs/remotes/origin/scade6-arrays

  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Empty node *)
  let node = N.empty_node node_ident in

  (* Create a new state variable for abstractions *)
  let mk_fresh_state_var 
      ?is_const
      ?is_input
      ?for_inv_gen
      state_var_type = 

    E.mk_fresh_state_var
      ?is_input
      ?is_const
      ?for_inv_gen
      scope
      I.abs_ident
      state_var_type
      node.N.fresh_state_var_index
  in

  (* Create a new state variable for abstractions *)
  let mk_state_var_for_expr 
      ?is_const
      ?is_input
      ?for_inv_gen
      new_vars
      ({ E.expr_type } as expr) = 

    try 

      (* Find previous definition of expression *)
      let state_var =
        E.LustreExprHashtbl.find
          node.N.expr_state_var_map
          expr
      in

      (* Return state variable and no new defintiion *)
      (state_var, new_vars)

    with Not_found ->

      (* Create a fresh state variable for definition *)
      let state_var =
        E.mk_fresh_state_var
          ?is_const
          ?is_input
          ?for_inv_gen
          scope
          I.abs_ident
          expr_type
          node.N.fresh_state_var_index
      in

      (* Record definition of expression by state variable *)
      E.LustreExprHashtbl.add
        node.N.expr_state_var_map
        expr
        state_var;

      (* Return variable and add definition *)
      (state_var, ((state_var, expr) :: new_vars))

  in

  (* Create a new constant to guard pre operator on state variable *)
  let mk_oracle_for_pre_of_state_var state_var = 

    try 

      (* Return oracle previously created *)
      StateVar.StateVarHashtbl.find  
        node.N.state_var_oracle_map
        state_var

    (* No oracle for state variable *)
    with Not_found -> 

      (* Create a fresh oracle *)
      let oracle = 
        E.mk_fresh_state_var
          ~is_input:true
          ~is_const:true
          scope
          I.oracle_ident
          (StateVar.type_of_state_var state_var)
          node.N.fresh_oracle_index
      in

      (* Map state variable to oracle *)
      StateVar.StateVarHashtbl.add
        node.N.state_var_oracle_map
        state_var
        oracle;

      (* Return fresh oracle *)
      oracle

  in

  (* Create a new oracle of type *)
  let mk_new_oracle oracle_type = 
    E.mk_fresh_state_var
      ~is_input:true
      ~is_const:true
      scope
      I.oracle_ident
      oracle_type
      node.N.fresh_oracle_index
  in

  (* Create a new variable observing a property of subnode *)
  let mk_new_observer = 
    let r = ref Numeral.(- one) in
    fun observer_type ->
      Numeral.incr r;
      E.mk_state_var_of_ident
        ~is_input:false
        ~is_const:false
        scope
        (I.push_int_index !r I.observer_ident)
        observer_type
  in

  (* Initial, empty abstraction context *)
  let empty_abstractions = 
    { scope;
      mk_fresh_state_var = mk_fresh_state_var;
      mk_state_var_for_expr = mk_state_var_for_expr;
      mk_oracle_for_pre_of_state_var = mk_oracle_for_pre_of_state_var;
      mk_new_oracle = mk_new_oracle;
      mk_new_observer = mk_new_observer;
      new_vars = [];
      new_calls = [];
      new_oracles = [];
      new_observers = [] }
  in

  (* Parse inputs, add to global context and node context *)
  let context', node' = 
    parse_node_inputs global_context node inputs
  in

  (* Parse outputs, add to local context and node context *)
  let context', node' = 
    parse_node_outputs
      context' 
      node' 
      outputs
  in

<<<<<<< HEAD
  (* Parse contract

     Must check before adding local variable to context, may not use
     local variables *)
  let abstractions, local_context, node = 
    parse_node_contracts
      local_context 
      empty_abstractions
      node 
      contracts
  in

=======
>>>>>>> refs/remotes/origin/scade6-arrays
  (* Parse local declarations, add to local context and node context *)
  let context', node' = 
    parse_node_locals context' node' locals
  in

  (* Parse equations and assertions, add to node context, local
     context is not modified *)
  let abstractions', context', node' = 
    parse_node_equations 
<<<<<<< HEAD
      local_context 
      abstractions
      node 
=======
      empty_abstractions
      context' 
      node' 
>>>>>>> refs/remotes/origin/scade6-arrays
      equations
  in

  (* Add abstractions to context and node *)
  let _, _, node' =
    abstractions_to_context_and_node 
      abstractions' 
      context' 
      node' 
  in

  (* Simplify by substituting variables that are aliases *)
  N.solve_eqs_node_calls node'


(* ******************************************************************** *)
(* Main                                                                 *)
(* ******************************************************************** *)

(* Iterate over a list of declarations and return a context *)
let rec declarations_to_nodes'
    ({ type_of_ident; expr_of_ident; nodes } as global_context) = 

  function

    (* All declarations processed, return result *)
    | [] -> global_context


    (* Declaration of a type as alias or free *)
    | (A.TypeDecl (pos, (A.AliasType (_, ident, _) as type_decl))) :: decls
    | (A.TypeDecl (pos, (A.FreeType (_, ident) as type_decl))) :: decls -> 

      if       

        (* Type t must not be declared *)
        type_in_context global_context ident

      then

        fail_at_position 
          pos
          (Format.asprintf 
             "Type %a is redeclared" 
             (I.pp_print_ident false) ident);

      (* Change context with alias type declaration *)
      let global_context' = match type_decl with 

        (* Identifier is an alias for a type *)
        | A.AliasType (_, ident, type_expr) -> 

          (* Add alias type declarations for the possibly indexed
             type expression *)
          let global_context' = 
            add_alias_type_decl
              global_context
              pos
              ident
              type_expr
          in

          (* Return changed context and unchanged declarations *)
          global_context'

        (* Identifier is a free type *)
        | A.FreeType (_, ident) -> 

          fail_at_position pos "Free types not supported"

      in

      (* Recurse for next declarations *)
      declarations_to_nodes' global_context' decls


    (* Declaration of a typed, untyped or free constant *)
    | (A.ConstDecl (pos, (A.FreeConst (_, ident, _) as const_decl))) :: decls 
    | (A.ConstDecl (pos, (A.UntypedConst (_, ident, _) as const_decl))) :: decls 
    | (A.ConstDecl (pos, (A.TypedConst (_, ident, _, _) as const_decl))) :: decls ->

      if

        (try 

           (* Identifier must not be declared *)
           ident_in_context global_context ident 

         (* Fail if reserved identifier used *)
         with Invalid_argument e -> fail_at_position pos e)

      then

        (* Fail if identifier already declared *)
        fail_at_position 
          pos 
          (Format.asprintf 
             "Identifier %a is redeclared as constant" 
             (I.pp_print_ident false) ident);

      (* Change context with constant declaration *)
      let global_context' = 
        add_const_decl global_context const_decl 
      in

      (* Recurse for next declarations *)
      declarations_to_nodes' global_context' decls


    (* Node declaration without parameters *)
    | (A.NodeDecl 
         (pos, 
          (node_ident, 
           [], 
           inputs, 
           outputs, 
           locals, 
<<<<<<< HEAD
           equations, 
           contracts))) :: decls ->
=======
           equations))) :: decls ->
>>>>>>> refs/remotes/origin/scade6-arrays

      (try 

        (* Add node declaration to global context *)
        let node_context = 
          parse_node
            node_ident
            global_context 
            inputs 
            outputs
            locals
            equations 
<<<<<<< HEAD
            contracts
=======
>>>>>>> refs/remotes/origin/scade6-arrays
        in
        
        (* Recurse for next declarations *)
        declarations_to_nodes' 
          { global_context with 
              nodes = node_context :: nodes }
          decls

       (* Node may be forward referenced *)
       with Node_not_found (ident, pos) -> 

        if 

          (* Is the referenced node declared later? *)
          List.exists 
            (function 
              | A.NodeDecl (_, (i, _, _, _, _, _)) when i = ident -> true 
              | _ -> false)
            decls

        then

          fail_at_position 
            pos 
            (Format.asprintf 
               "Node %a is forward referenced" 
               (I.pp_print_ident false) ident)
      
        else
          
          fail_at_position
            pos
            (Format.asprintf 
               "Node %a is not defined" 
               (I.pp_print_ident false) ident))


    (* Node declaration without parameters *)
    | (A.FuncDecl (pos, _)) :: _ ->

      fail_at_position pos "Functions not supported"


    (* Node declaration without parameters *)
    | (A.NodeParamInst (pos, _)) :: _
    | (A.NodeDecl (pos, _)) :: _ ->

      fail_at_position pos "Parametric nodes not supported" 



*)


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
