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

module A = LustreAst

module I = LustreIdent
module IT = LustreIdent.Hashtbl

module D = LustreIndex

module E = LustreExpr
module ET = E.LustreExprHashtbl

module N = LustreNode
module F = LustreFunction
module G = LustreGlobals

module C = LustreContext

module S = LustreSimplify



(* ********************************************************************** *)
(* Parse constants                                                        *)
(* ********************************************************************** *)

(* Add declaration of constant to context *)
let eval_const_decl ?(ghost = false) ctx = function

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

         (* Identifier must not be declared, unless it is a ghost
            constant which shadows declared constants *)
         not ghost && C.expr_in_context ctx ident 

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

    (* Ensure expression is constant *)
    D.iter 
      (fun _ e -> 
         if not (E.is_const e) then 
           (C.fail_at_position
              pos
              "Invalid constant expression"))
      res;


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
         let ident = I.mk_string_ident i in
         
         try 
           C.expr_in_context ctx ident 
         with Invalid_argument e -> 
           C.fail_at_position pos e
             
       )) -> 
    
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

    Format.eprintf "of TYPE %a@." A.pp_print_lustre_type var_type;

    Format.eprintf
      "IE @[<hv>%a@]@."
      (D.pp_print_trie
         (fun ppf (i, e) ->
            Format.fprintf ppf
              "@[<hv 2>%a:@ %a@]"
              (D.pp_print_index false) i
              (Type.pp_print_type) e)
         ";@ ")
      index_types;
    

    
    (* Add declaration of possibly indexed type to contexts *)
    let ctx = C.add_node_local ~ghost ctx ident index_types in

    (* Continue with following outputs *)
    eval_node_locals ~ghost ctx tl

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
    let ident = I.mk_string_ident i in

    (* Get expression of identifier *)
    let res = 

      try

        (* Get trie of local or output state variables *)
        C.assignable_state_var_of_ident ctx ident
          
      with 
        
        (* Identifier cannot be assigned to *)
        | Invalid_argument _ -> 
          
          C.fail_at_position 
            pos 
            "Assignment to identifier not possible"

        (* Identifier not declared *)
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
  | A.StructDef (pos, []) -> (D.empty, 0, ctx)

  (* Single item *)
  | A.StructDef (pos, [e]) -> 

    (* Get types of item *)
    let t, ctx = eval_struct_item ctx pos e in 

    (* Return types of indexes, no array bounds and unchanged
       context *)
    t, 0, ctx

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
    res, 0, ctx

  (* Recursive array definition *)
  | A.ArrayDef (pos, i, l) -> 

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident i in

    (* Get expression of identifier *)
    let res = 

      try

        (* Get trie of local or output state variables *)
        C.assignable_state_var_of_ident ctx ident
          
      with 
        
        (* Identifier cannot be assigned to *)
        | Invalid_argument _ -> 
          
          C.fail_at_position 
            pos 
            "Assignment to identifier not possible"

        (* Identifier not declared *)
        | Not_found -> 
          
          C.fail_at_position 
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
        if d1 <> d2 then C.fail_at_position pos "Index mismatch for cacaarray"
    in

    (* let rec aux = function  *)
    (*   | [] -> (function _ -> ()) *)
    (*   | h :: tl1 ->  *)
    (*     (function  *)
    (*       | D.ArrayVarIndex _ :: tl2 -> aux tl1 tl2 *)
    (*       | _ ->  *)
    (*         C.fail_at_position  *)
    (*           pos  *)
    (*           "Index mismatch for array") *)
    (* in *)

    Format.eprintf "checking 1: %a and 2:@."
      (pp_print_list A.pp_print_ident ",, ") l;

    Format.printf
      "  @[<hv>%a@]@."
      (D.pp_print_trie
         (fun ppf (i, e) ->
            Format.fprintf ppf
              "@[<hv 2>%a:@ %a@]"
              (D.pp_print_index false) i
              (StateVar.pp_print_state_var) e)
         ";@ ")
      res;
        
    (* Check that the variable has at least as many indexes as
       variables given *)
    List.iter (check l) (D.keys res);

    (* Must have at least one element in the trie *)
    assert 
      (try D.choose res |> ignore; true with Not_found -> false);

    (* Convert array bounds to indexes for equation *)
    let convert l2 =
      List.fold_left (fun acc -> function
          | D.ArrayVarIndex _ -> succ acc
          | _ -> acc) 0 l2 in
    
    let indexes = (D.keys res |> List.hd) |> convert in
    
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

    res, indexes, ctx


(* Match bindings from a trie of state variables and bindings for a
   trie of expressions and produce a list of equations *)
let rec expand_tuple' pos accum bounds lhs rhs = match lhs, rhs with 

  (* No more equations, return in original order *)
  | [], [] -> accum

  (* Indexes are not of equal length *)
  | _, []
  | [], _ ->         

    C.fail_at_position pos "Type mismatch in equation: indexes not of equal length"

  | _ -> 
    Format.eprintf "LHS : <%a> RHS : <%a> @."
      (D.pp_print_index false) (List.hd lhs |> fst)
      (D.pp_print_index false) (List.hd rhs |> fst);
    match lhs, rhs with
  | [], []   | _, [] | [], _ ->         assert false

    (* All indexes consumed *)
  | ([], state_var) :: lhs_tl, 
    ([], expr) :: rhs_tl -> 

    expand_tuple'
      pos
      (((state_var, bounds), expr) :: accum)
      []
      lhs_tl
      rhs_tl

  (* Only array indexes may be left at head of indexes *)
  | (D.ArrayVarIndex b :: lhs_index_tl, state_var) :: lhs_tl,
    ([], expr) :: rhs_tl ->

    expand_tuple' 
      pos
      accum
      (N.Bound b :: bounds)
      ((lhs_index_tl, state_var) :: lhs_tl)
      (([], expr) :: rhs_tl)

  (* Array variable on left-hand side, fixed index on right-hand side *)
  | (D.ArrayVarIndex b :: lhs_index_tl, state_var) :: lhs_tl,
    (D.ArrayIntIndex i :: rhs_index_tl, expr) :: rhs_tl -> 
Format.eprintf "ici@.@.";

    (* Recurse to produce equations with this index *)
    let accum' = 
      expand_tuple' 
        pos
        accum
        (N.Fixed (E.mk_int_expr (Numeral.of_int i)) :: bounds)
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
    (D.ArrayVarIndex _ :: rhs_index_tl, expr) :: rhs_tl -> 

    (* We cannot compare expressions for array bounds syntactically,
       because that may give too many false negatives. Evaluating both
       bounds to find if they are equal would be too complicated,
       therefore accept some false positives here. *)
    
    (* Count number of variable indexes *)
    let i = 
      List.fold_left 
        (fun a -> function 
           | D.ArrayVarIndex _ -> succ a
           | _ -> a)
        0
        lhs_index_tl
    in

    (* Is every variable in the expression necessarily of array type? 

       Need to skip the index expression of a select operator: A[k] *)
    
    let expr' =
      E.map
        (fun _ e -> 
           if E.is_var e then 
             (assert (E.type_of_lustre_expr e |> Type.is_array);
              E.mk_select e (E.mk_index_var i))
           else e)
        expr
    in
      
    expand_tuple' 
      pos
      accum
      (N.Bound b :: bounds)
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

(*
  Format.printf
    "@[<v>expand_tuple lhs:@,%a@]@."
    (pp_print_list
       (fun ppf (i, sv) -> 
          Format.fprintf ppf "%a: %a "
            (D.pp_print_index false) i
            StateVar.pp_print_state_var sv)
       "@,")
    (List.map (fun (i, e) -> (List.rev i, e)) (D.bindings lhs));

  Format.printf
    "@[<v>expand_tuple rhs:@,%a@]@."
    (pp_print_list
       (fun ppf (i, e) -> 
          Format.fprintf ppf "%a: %a "
            (D.pp_print_index false) i
            (E.pp_print_lustre_expr false) e)
       "@,")
    (List.map (fun (i, e) -> (List.rev i, e)) (D.bindings rhs));
  *)
  
  (* TODO check with Christoph why they were reversed *)
  expand_tuple' 
    pos
    []
    []
    (List.map (fun (i, e) -> ((* List.rev  *)i, e)) (D.bindings lhs))
    (List.map (fun (i, e) -> ((* List.rev  *)i, e)) (D.bindings rhs))


(* Evaluate node statements and add to context  *)
let rec eval_node_equations ctx = function

  (* No more statements *)
  | [] -> ctx

  (* Assertion *)
  | A.Assert (pos, ast_expr) :: tl -> 

    (* Evaluate Boolean expression and guard all pre operators *)
    let expr, ctx = 
      S.eval_bool_ast_expr [] ctx pos ast_expr 
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
      S.eval_bool_ast_expr [] ctx pos ast_expr 
      |> C.close_expr pos
    in

    let name = 
      Format.asprintf
        "@[<h>%a@]"
        A.pp_print_expr ast_expr
    in
    
    (* Add property to node *)
    let ctx = C.add_node_property ctx (Property.PropAnnot pos) name expr in

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
    let eq_lhs, indexes, ctx = eval_eq_lhs ctx pos lhs in

    (* array bounds. TODO: check that the order is correct *)
    let lhs_bounds =
      List.fold_left (fun acc (i, _) ->
          List.fold_left (fun acc -> function
              | D.ArrayVarIndex b -> N.Bound b :: acc
              | _ -> acc
            ) acc i
        ) [] (D.bindings eq_lhs) in
    
    
    (* Evaluate expression on right-hand side *)
    let eq_rhs, ctx = 

      (* Evaluate in extended context *)
      S.eval_ast_expr lhs_bounds ctx ast_expr 

    in

    (* Close each expression by guarding all pre operators separately *)
    let eq_rhs, ctx = 
      D.fold 
        (fun i e (t, c) -> 
           let e', c = C.close_expr pos (e, c) in 
           let t' = D.add i e' t in
           (t', c))
        eq_rhs
        (D.empty, ctx)

    in 
(*
    Format.printf
      "@[<hv>%a@]@."
      (D.pp_print_trie
         (fun ppf (i, e) ->
            Format.fprintf ppf
              "@[<hv 2>%a:@ %a@]"
              (D.pp_print_index false) i
              (E.pp_print_lustre_expr false) e)
         ";@ ")
      eq_rhs;
*)
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
        (fun ctx ((sv, b), e) -> C.add_node_equation ctx pos sv b indexes e)
        ctx
        equations
    in

    (* Continue with next node statements *)
    eval_node_equations ctx tl


(* ********************************************************************** *)
(* Parse contracts                                                        *)
(* ********************************************************************** *)

(* Parse a ghost variable declaration and evaluate continuation 

   This function is shared between nodes and functions, each has a
   different way to deal with ghost variables. *)
let eval_ghost_var ?(no_defs = false) f ctx = function

  (* Declaration of a free variable *)
  | A.FreeConst (pos, _, _) ->

    C.fail_at_position pos "Free ghost variables not supported"

  (* Declaration of a typed or untyped variable *)
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
           "Identifier %a is redeclared as ghost" 
           (I.pp_print_ident false) ident);

    (* Evaluate ghost expression *)
    let expr', ctx = 
      S.eval_ast_expr
        []
        (* Change context to fail on new definitions *)
        (if no_defs then 
           C.fail_on_new_definition
             ctx
             pos
             "Invalid expression for variable"
         else 
           ctx)
        expr
    in

    let type_expr' = 

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
               expr';

             type_expr'

           with Invalid_argument _ | E.Type_mismatch -> 

             (C.fail_at_position
                pos
                "Type mismatch in ghost variable declaration"))

        (* No type check for untyped or free constant *)
        | _ -> D.map (fun { E.expr_type } -> expr_type) expr')

    in

    (* Pass to continuation *)
    f ctx pos ident type_expr' expr expr' 


(* Introduce fresh state variable for a require expression *)
let eval_req (accum, ctx) (pos, expr) = 

  (* Evaluate expression to a Boolean expression, may change
     context *)
  let expr', ctx = 
    S.eval_bool_ast_expr [] ctx pos expr |> C.close_expr pos
  in

  (* Define expression with a state variable *)
  let (state_var, _), ctx = 
    C.mk_local_for_expr pos ctx expr' 
  in

  (* Add state variable to accumulator, continue with possibly
     modified context *)
  (pos, state_var) :: accum, ctx
  

(* Introduce fresh state variable for an ensure expression *)
let eval_ens (accum, ctx) (pos, expr) = 

  (* Evaluate expression to a Boolean expression, may change
     context *)
  let expr', ctx = 
    S.eval_bool_ast_expr [] ctx pos expr |> C.close_expr pos
  in

  (* Define expression with a state variable *)
  let (state_var, _), ctx = 
    C.mk_local_for_expr pos ctx expr' 
  in

  (* Add state variable to accumulator, continue with possibly
     modified context *)
  (pos, state_var) :: accum, ctx


(* Declare and define ghost streams, requires and ensures expressions
   and return contract *)
let eval_node_contract ctx contract_pos contract_name reqs enss =

  (* Evaluate require clauses separately. *)
  let contract_reqs, ctx = List.fold_left eval_req ([], ctx) reqs in
  
  (* Evaluate ensure clauses separately. *)
  let contract_enss, ctx = List.fold_left eval_ens ([], ctx) enss in

  (* Return a contract *)
  ({ N.contract_name;
     N.contract_pos; 
     N.contract_reqs; 
     N.contract_enss },
   ctx)


(* Fail if a contract node input is incompatible with a node input *)
let rec check_node_and_contract_inputs call_pos ctx node_inputs = function 

  (* All contract inputs are consistent with node inputs *)
  | [] -> ()

  (* Input to contract, must not have a clock *)
  | (pos, 
     ident, 
     contract_input_lustre_type, 
     A.ClockTrue, 
     contract_input_const) :: tl -> 

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

        C.fail_at_position 
          call_pos 
          "Illegal contract call: node does not have input"

    in

    (* Input must not have a clock *)
    (match node_input_clock with 
      | A.ClockTrue -> ()
      | _ -> 
        C.fail_at_position 
          pos 
          "Clocked inputs not supported");

    (* Node input must be constant iff contract input is *)
    if contract_input_const <> node_input_const then 

      C.fail_at_position 
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

       (C.fail_at_position
          pos
          "Type mismatch in constant declaration"));

    (* Continue with remaining inputs *)
    check_node_and_contract_inputs call_pos ctx node_inputs tl

  | (pos, _, _, _, _) :: tl -> 

    C.fail_at_position 
      pos 
      "Clocked inputs not supported"


(* Fail if a contract node output is incompatible with a node output *)
let rec check_node_and_contract_outputs call_pos ctx node_outputs = function 

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

        C.fail_at_position 
          call_pos 
          "Illegal contract call: node does not have output"

    in

    (* Output must not have a clock *)
    (match node_output_clock with 
      | A.ClockTrue -> ()
      | _ -> 
        C.fail_at_position 
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

       (C.fail_at_position
          pos
          "Type mismatch in constant declaration"));

    (* Continue with remaining inputs *)
    check_node_and_contract_outputs call_pos ctx node_outputs tl

  | (pos, _, _, _) :: tl -> 

    C.fail_at_position 
      pos 
      "Clocked outputs not supported"


let rec inline_contract_of_contract_node
    ctx
    (contract_pos, 
     contract_ident, 
     contract_reqs, 
     contract_enss)
    contract_locals = 

  function 

    (* No more contract equations, return inline contract *)
    | [] -> 

      (ctx,
       contract_pos, 
       contract_ident, 
       contract_reqs, 
       contract_enss)

    (* Ghost equation *)
    | A.GhostEquation (eq_pos, ident, expr) :: tl -> 

      (try 

         (match 

            (* Find declaration of ghost variable *)
            List.find
              (function 
                | A.NodeConstDecl _ -> false
                | A.NodeVarDecl (_, (_, i, _, _)) -> i = ident)
              contract_locals

          with 

            (* Constant declarations have been filtered out *)
            | A.NodeConstDecl (pos, _) -> assert false

            (* Ghost variable on the base clock *)
            | A.NodeVarDecl (_, (_, _, lustre_type, A.ClockTrue)) -> ()

            (* Ghost variable not on the base clock *)
            | A.NodeVarDecl (_, (_, _, _, _)) -> 

              C.fail_at_position 
                contract_pos 
                "Clocked ghost variables not supported")

       (* Ghost variable undeclared *)
       with Not_found ->           

         C.fail_at_position 
           contract_pos 
           "Assignment to undeclared ghost variable");

      (* Add equation for ghost stream *)
      let ctx = 
        eval_node_equations 
          ctx
          [A.Equation
             (eq_pos,
              (A.StructDef
                 (eq_pos, [A.SingleIdent (eq_pos, ident)])), expr)]
      in


      inline_contract_of_contract_node
        ctx
        (contract_pos, 
         contract_ident, 
         contract_reqs, 
         contract_enss)
        contract_locals
        tl

    (* Requires clause *)
    | A.Require req :: tl ->

      inline_contract_of_contract_node
        ctx
        (contract_pos, 
         contract_ident, 
         req :: contract_reqs, 
         contract_enss)
        contract_locals
        tl

    (* Ensures clause *)
    | A.Ensure ens :: tl -> 

      inline_contract_of_contract_node
        ctx
        (contract_pos, 
         contract_ident, 
         contract_reqs, 
         ens :: contract_enss)
        contract_locals
        tl
    

(* Lookup definition of contract from contract node, or return inline contract *)
let resolve_contract node_inputs node_outputs ctx = function 

  (* Inline contract *)
  | A.InlinedContract (pos, ident, reqs, enss) -> 

    (ctx, pos, ident, reqs, enss)

  (* Contract from a spec node *)
  | A.ContractCall (call_pos, ident) -> 

    (* Lookup contract node spec from context *)
    let pos, 
        (_,
         contract_node_params, 
         contract_inputs, 
         contract_outputs, 
         contract_locals, 
         contract_equations) = 
      C.contract_node_decl_of_ident ctx ident 
    in

    (* We do not support parametric nodes *)
    assert (contract_node_params = []);

    (* Fail if node inputs are incompatible with contract inputs *)
    check_node_and_contract_inputs call_pos ctx node_inputs contract_inputs;

    (* Fail if node outputs are incompatible with contract outputs *)
    check_node_and_contract_outputs call_pos ctx node_outputs contract_outputs;

    (* Declare and define all ghost constants *)
    let ctx = eval_node_locals ~ghost:true ctx contract_locals in 

    (* Inline definitions of ghost variables *)
    inline_contract_of_contract_node
      ctx
      (pos, ident, [], []) 
      contract_locals 
      contract_equations


(* Add mode contracts from list to context *)
let rec eval_node_mode_contracts resolve_contract ctx = function 

  (* No more mode contracts, return *)
  | [] -> ctx

  (* Take the first contract *)
  | mode_contract :: tl -> 

    (* Peek at contract to get identifier for scoping *)
    let ident = match mode_contract with
      | A.InlinedContract (_, ident, _, _) 
      | A.ContractCall (_, ident) -> ident
    in

    (* New scope for local declarations *)
    let ctx = C.push_scope ctx ident in

    (* Inline if necessary *)
    let (ctx, pos, ident, reqs, enss) = 
      resolve_contract ctx mode_contract 
    in

    (* Evaluate *)
    let (contract, ctx) = 
      eval_node_contract
        ctx
        pos
        (I.mk_string_ident ident)
        reqs
        enss 
    in

    (* Add to context *)
    let ctx = 
      C.add_node_mode_contract ctx pos ident contract
    in

    (* Remove scope for local declarations *)
    let ctx = C.pop_scope ctx in

    (* Continue with next contracts *)
    eval_node_mode_contracts resolve_contract ctx tl 


(* Add all node contracts to contexts *)
let eval_node_contract_spec 
  resolve_contract
    ctx
    (ghost_consts,
     ghost_vars,
     global_contract,
     mode_contracts) =

  (* Add constants to context *)
  let ctx = List.fold_left (eval_const_decl ~ghost:true) ctx ghost_consts in

  (* Add declaration and equation for ghost stream *)
  let f ctx pos ident type_expr ast_expr expr = 
    
    (* Add local declaration for ghost stream *)
    let ctx = C.add_node_local ~ghost:true ctx ident type_expr in

    (* Add equation for ghost stream *)
    eval_node_equations 
      ctx
      [A.Equation
         (pos, 
          (A.StructDef 
             (pos,
              [A.SingleIdent (pos, I.string_of_ident false ident)])), 
          ast_expr)]
      
  in

  (* Add ghost variables to context *)
  let ctx = List.fold_left (eval_ghost_var f) ctx ghost_vars in

  (* Add global contract to context *)

  let ctx = match global_contract with
    
    (* No global contract for nodex *)
    | None -> ctx

    (* Global contract for node *)
    | Some c -> 
      
      (* New scope for local declarations in contract *)
      let ctx = C.push_scope ctx "__global" in
      
      (* Inline if necessary *)
      let (ctx, pos, ident, reqs, enss) = 
        resolve_contract ctx c
      in
      
      (* Evaluate *)
      let (contract, ctx) = 
        eval_node_contract 
          ctx
          pos
          (I.mk_string_ident ident)
          reqs
          enss 
      in
      
      (* Add to context *)
      let ctx = 
        C.add_node_global_contract ctx pos contract
      in
      
      (* Remove scope for local declarations in contract *)
      C.pop_scope ctx
      
  in
  
  (* Continue with mode contracts *)
  eval_node_mode_contracts resolve_contract ctx mode_contracts


(* Add declarations of node to context *)
let eval_node_decl
    ctx
    inputs
    outputs
    locals
    equations
    contract_spec = 

  (* Add inputs to context: as state variable to ident_expr_map, and
     to inputs *)
  let ctx = eval_node_inputs ctx inputs in

  (* Add outputs to context: as state variable to ident_expr_map, and
     to outputs *)
  let ctx = eval_node_outputs ~is_single:(List.length outputs = 1) ctx outputs in

  (* New scope for local declarations in contracts *)
  let ctx = C.push_scope ctx "contract" in

  (* Parse contracts and add to context in contracts *)
  let ctx = 
    eval_node_contract_spec (resolve_contract inputs outputs) ctx contract_spec 
  in

  (* Remove scope for local declarations in implementation *)
  let ctx = C.pop_scope ctx in

  (* New scope for local declarations in implementation *)
  let ctx = C.push_scope ctx "impl" in

  (* Add locals to context: as state variable to ident_expr_map, and
     to inputs *)
  let ctx = eval_node_locals ctx locals in

  (* Parse equations, assertions, properties *)
  let ctx = eval_node_equations ctx equations in

  (* Remove scope for local declarations in implementation *)
  let ctx = C.pop_scope ctx in

  (* Create node from current context and return *)
  ctx 
  

(* ********************************************************************** *)
(* Parse function declarations                                            *)
(* ********************************************************************** *)

(* Return true if the expression is functional, i.e. without temporal
   operators *)
let is_function_expr ({ E.expr_init; E.expr_step } as expr) =

  (* Must not have a variable at the previous state *)
  not (E.has_pre_var E.cur_offset expr) &&

  (* Expressions must be equal *)
  (E.equal_expr expr_init expr_step)
  

(* Return an expression for a stateless function from an expression *)
let function_expr_of_expr ({ E.expr_init; E.expr_step } as expr) =

  if 

    (* Check if expression does not contain temporal operators *)
    is_function_expr expr
  
  then

    (* Return one of the two (equal) expressions *)
    expr_step

  else
    
    (* Fail *)
    raise (Invalid_argument "func_expr_of_expr")



(* Add all node inputs to contexts *)
let rec eval_func_inputs ctx = function

  (* All inputs parsed *)
  | [] -> ctx

  (* Input on the base clock *)
  | (pos, i, ast_type) :: tl -> 

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
           "Function input %a already declared" 
           (I.pp_print_ident false) ident);
    
    (* Evaluate type expression *)
    let index_types = S.eval_ast_type ctx ast_type in
  
    (* Add declaration of possibly indexed type to contexts *)
    let ctx = 
      C.add_function_input
        ctx
        ident
        index_types
    in

    (* Continue with following inputs *)
    eval_func_inputs ctx tl


(* Add all function inputs to contexts *)
let rec eval_func_outputs ?is_single ctx = function

  (* All outputs parsed *)
  | [] -> ctx

  (* Output on the base clock *)
  | (pos, i, ast_type) :: tl -> 

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
           "Function output %a already declared" 
           (I.pp_print_ident false) ident);
    
    (* Evaluate type expression *)
    let ident_types = S.eval_ast_type ctx ast_type in
  
    (* Add declaration of possibly indexed type to contexts *)
    let ctx = C.add_function_output ?is_single ctx ident ident_types in

    (* Continue with following inputs *)
    eval_func_outputs ctx tl


(* Form conjunction of requires expressions *)
let eval_func_req_ens (accum, ctx) (pos, expr) =

  (* Evaluate expression to a Boolean expression, may change
     context *)
  let expr', ctx = 
    S.eval_bool_ast_expr
      []
      (C.fail_on_new_definition
         ctx
         pos
         "Invalid expression in contract for function")
      pos 
      expr 
    |> C.close_expr pos
  in

  if not (is_function_expr expr') then
    C.fail_at_position
      pos
      "Invalid temporal expression in contract of function";

  (* Add to conjunction of requirements *)
  (E.mk_and accum expr' , ctx)


(* Declare and define ghost streams, requires and ensures expressions
   and return contract *)
let eval_func_contract ctx contract_pos contract_name reqs enss =

  (* Evaluate require clauses to a conjunction *)
  let reqs', ctx =
    List.fold_left eval_func_req_ens (E.t_true, ctx) reqs 
  in

  (* Introduce state variable for conjunction of requirements *)
  let contract_req = function_expr_of_expr reqs' in
  
  (* Evaluate require clauses to a conjunction *)
  let ens', ctx =
    List.fold_left eval_func_req_ens (E.t_true, ctx) enss
  in

  (* Introduce state variable for conjunction of requirements *)
  let contract_ens = function_expr_of_expr ens' in
  
  (* Return a contract *)
  ({ F.contract_name;
     F.contract_pos; 
     F.contract_req; 
     F.contract_ens },
   ctx)


(* Add mode contracts from list to context *)
let rec eval_func_mode_contracts resolve_contract ctx = function 

  (* No more mode contracts, return *)
  | [] -> ctx

  (* Take the first contract *)
  | mode_contract :: tl -> 

    (* Peek at contract to get identifier for scoping *)
    let ident = match mode_contract with
      | A.InlinedContract (_, ident, _, _) 
      | A.ContractCall (_, ident) -> ident
    in

    (* New scope for local declarations *)
    let ctx = C.push_scope ctx ident in

    (* Inline if necessary *)
    let (ctx, pos, ident, reqs, enss) = 
      resolve_contract ctx mode_contract 
    in

    (* Evaluate *)
    let (contract, ctx) = 
      eval_func_contract
        ctx
        pos
        (I.mk_string_ident ident)
        reqs
        enss 
    in

    (* Add to context *)
    let ctx = 
      C.add_function_mode_contract ctx pos ident contract
    in

    (* Remove scope for local declarations *)
    let ctx = C.pop_scope ctx in

    (* Continue with next contracts *)
    eval_func_mode_contracts resolve_contract ctx tl 


(* Add all node contracts to contexts *)
let eval_func_contract_spec 
    ctx
    func_inputs
    func_outputs
    (ghost_consts,
     ghost_vars,
     global_contract,
     mode_contracts) =

  (* Add constants to context *)
  let ctx = 
    List.fold_left
      (eval_const_decl ~ghost:true)
      ctx
      ghost_consts 
  in

  (* Add expresson for identifier for ghost stream *)
  let f ctx pos ident _ _ expr = 

    (* Check expressions for all indexes *)
    D.iter
      (fun _ e -> 
         if not (is_function_expr e) then 
           C.fail_at_position
             pos
             "Invalid temporal expression in contract of function")
      expr;

    (* Bind identifier to expression in context *)
    C.add_expr_for_ident ctx ident expr

  in

  (* Fail on contract calls *)
  let inlined_contract_only ctx = function 

    (* Return paramters of inline contract *)
    | A.InlinedContract (pos, ident, reqs, enss) -> 
      (ctx, pos, ident, reqs, enss)
      
    (* Contract must be inlined *)
    | A.ContractCall (pos, _) -> 
      C.fail_at_position 
        pos
        "Only inline contracts supported for functions" 

  in

  (* Add ghost variables to context *)
  let ctx = 
    List.fold_left
      (eval_ghost_var ~no_defs:true f)
      ctx
      ghost_vars 
  in

  (* Add global contract to context *)
  let ctx = match global_contract with
    
    (* No global contract for nodex *)
    | None -> ctx

    (* Global contract for node *)
    | Some c -> 
      
      (* New scope for local declarations in contract *)
      let ctx = C.push_scope ctx "__global" in
      
      (* Inline if necessary *)
      let (ctx, pos, ident, reqs, enss) = inlined_contract_only ctx c in
      
      (* Evaluate *)
      let (contract, ctx) = 
        eval_func_contract 
          ctx
          pos
          (I.mk_string_ident ident)
          reqs
          enss 
      in
      
      (* Add to context *)
      let ctx = 
        C.add_function_global_contract ctx pos contract
      in
      
      (* Remove scope for local declarations in contract *)
      C.pop_scope ctx
      
  in
  
  (* Continue with mode contracts *)
  eval_func_mode_contracts inlined_contract_only ctx mode_contracts


(* Add declarations of node to context *)
let eval_func_decl
    ctx
    inputs
    outputs
    contract_spec = 

  (* Add inputs to context: as state variable to ident_expr_map, and
     to inputs *)
  let ctx = eval_func_inputs ctx inputs in

  (* Add outputs to context: as state variable to ident_expr_map, and
     to outputs *)
  let ctx = eval_func_outputs ~is_single:(List.length outputs = 1) ctx outputs in

  (* New scope for local declarations in contracts *)
  let ctx = C.push_scope ctx "contract" in

  (* Parse contracts and add to context in contracts *)
  let ctx = eval_func_contract_spec ctx inputs outputs contract_spec in

  (* Remove scope for local declarations in implementation *)
  let ctx = C.pop_scope ctx in

  (* New scope for local declarations in implementation *)
  let ctx = C.push_scope ctx "impl" in

  (* Remove scope for local declarations in implementation *)
  let ctx = C.pop_scope ctx in

  (* Create node from current context and return *)
  ctx 


(* ********************************************************************** *)
(* Parse declarations                                                     *)
(* ********************************************************************** *)

(* Add declarations of program to context *)
let rec declarations_to_context ctx = 

  function 

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
           contracts))) as curr_decl :: decls -> 

      (* Identifier of AST identifier *)
      let ident = I.mk_string_ident i in

      (* Identifier must not be declared *)
      if C.node_or_function_in_context ctx ident then

        (* Fail if identifier already declared *)
        C.fail_at_position 
          pos 
          (Format.asprintf 
             "Node %a is redeclared" 
             (I.pp_print_ident false) ident);

      (try

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

                  C.fail_at_position
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

           C.fail_at_position
             pos
             (Format.asprintf 
                "Node or function %a is not defined" 
                (I.pp_print_ident false) called_ident))

    (* Declaration of a contract node *)
    | A.ContractNodeDecl (pos, node_decl) :: decls -> 

      (* Add to context for later inlining *)
      let ctx = C.add_contract_node_decl_to_context ctx (pos, node_decl) in

      (* Recurse for next declarations *)
      declarations_to_context ctx decls


    (* Uninterpreted function declaration *)
    | (A.FuncDecl 
         (pos, 
          (i, 
           inputs, 
           outputs,
           contracts))) :: decls ->

      (* Identifier of AST identifier *)
      let ident = I.mk_string_ident i in

      (* Identifier must not be declared *)
      if C.node_or_function_in_context ctx ident then

        (* Fail if identifier already declared *)
        C.fail_at_position 
          pos 
          (Format.asprintf 
             "Function %a is redeclared" 
             (I.pp_print_ident false) ident);

      (try

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

           C.fail_at_position
             pos
             (Format.asprintf 
                "Node or function %a is not defined" 
                (I.pp_print_ident false) called_ident))

    (* ******************************************************************** *)
    (* Unsupported below                                                    *)
    (* ******************************************************************** *)

    (* Identifier is a free type *)
    | (A.TypeDecl (pos, (A.FreeType _))) :: decls -> 

      C.fail_at_position pos "Free types not supported"


    (* Parametric node declaration *)
    | (A.NodeParamInst (pos, _)) :: _
    | (A.NodeDecl (pos, _)) :: _ ->

      C.fail_at_position pos "Parametric nodes not supported" 



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
  C.get_nodes ctx, { G.functions = C.get_functions ctx }



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
      
      C.fail_at_position pos "Syntax error"

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
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
