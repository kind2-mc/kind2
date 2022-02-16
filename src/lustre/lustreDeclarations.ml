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


let fail_or_warn =
  if Flags.lus_strict () then
    fail_at_position else warn_at_position

(*************************************)
(* Auxiliary functions for contracts *)
(*************************************)


(** Returns an option of the output state variables mentioned in the current
state of a lustre expression. *)
let [@ocaml.warning "-27"] contract_check_no_output ctx pos expr =
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
  | A.FreeConst (_, i, ty) ->

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident (HString.string_of_hstring i) in

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
    let ident = I.mk_string_ident (HString.string_of_hstring i) in

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
             (fun _ def_type { E.expr_type; (* E.expr_init = e *) } ->
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
    let ident = I.mk_string_ident i in

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
        pos
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
    let ident = I.mk_string_ident (HString.string_of_hstring i) in

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
         let ident = I.mk_string_ident (HString.string_of_hstring i) in
         
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
    let ident = I.mk_string_ident (HString.string_of_hstring i) in

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
  | A.NodeConstDecl (_, const_decl) :: tl -> 

    (* Add mapping of identifier to value to context *)
    let ctx = eval_const_decl ~ghost ctx const_decl in

    (* Continue with following outputs *)
    eval_node_locals ~ghost ctx tl


(* ********************************************************************** *)
(* Parse equations                                                        *)
(* ********************************************************************** *)

(* Return trie of state variables from a structural assignment *)
let [@ocaml.warning "-27"] eval_struct_item ctx pos = function

  (* Single identifier *)
  | A.SingleIdent (pos, i) ->  

    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident (HString.string_of_hstring i) in

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
            ("Assignment to identifier not possible " ^ (HString.string_of_hstring i))

        (* Identifier not declared *)
        | Not_found -> 
          
          fail_at_position 
            pos 
            ("Assignment to undeclared identifier " ^ (HString.string_of_hstring i))

    in

    (* Return trie of state variables and context unchanged *)
    (res, 0, ctx)

  (* Recursive array definition *)
  | A.ArrayDef (pos, i, l) -> 
    
    (* Identifier of AST identifier *)
    let ident = I.mk_string_ident (HString.string_of_hstring i) in

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
               (I.mk_string_ident v)
               (D.singleton D.empty_index expr)
           in
           (succ i, ctx))
        (0, ctx)
        (List.map HString.string_of_hstring l)
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
  | A.ArrayDef (_, _, l) -> 

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
        (List.rev (List.map HString.string_of_hstring l))
    in
           
    ctx

  | _ -> ctx


(* Remove elements of the left-hand side from the scope *)
let uneval_eq_lhs ctx = function

  (* Nothing added from structrural assignments *)
  | A.StructDef (_, l) -> List.fold_left uneval_struct_item ctx l


(* Return a trie of state variables from the left-hand side of an
   equation *)
let [@ocaml.warning "-27"] eval_eq_lhs ctx pos = function

  (* Empty list for node calls without returns *)
  | A.StructDef (_, []) -> (D.empty, 0, ctx)

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
  | (D.ArrayVarIndex _ :: lhs_index_tl, state_var) :: _,
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
     (D.ArrayIntIndex j :: _, expr) :: rhs_tl) ->

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


let rec eval_node_equation _inputs _outputs _locals ctx = function
  
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
          (*
          let ctx =
            (* Is [e] a state variable in the current state? *)
            if E.is_var e && b = [] then (
              let alias = E.state_var_of_expr e in
              (* Format.printf "%a is an alias for %a@.@."
                StateVar.pp_print_state_var alias
                StateVar.pp_print_state_var sv ; *)
              C.current_node_map ctx (
                fun node -> N.set_state_var_alias node alias sv
              )
            ) else ctx
          in*)
          C.add_node_equation ctx pos sv b indexes e
      ) ctx equations



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
    let ident = I.mk_string_ident (HString.string_of_hstring i) in

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
        Format.sprintf "Type mismatch in declaration of ghost variable %s" (HString.string_of_hstring i)
      )
      (* Propagate unknown declarations to handle forward referencing. *)
      | Deps.Unknown_decl (_, _, _) as e -> raise e
      | e -> fail_at_position pos (
        Format.asprintf
          "unexpected error in treatment of ghost variable %s: %s"
          (HString.string_of_hstring i)
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
  let iname = match iname with
    | Some s -> Some (HString.string_of_hstring s)
    | None -> None
  in
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
                    Format.fprintf fmt "%s%a"
                      name pp_print_line_and_column pos
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
(*and check_node_and_contract_inputs call_pos ctx node_inputs = function 

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
      "Clocked inputs not supported"*)


(* Fail if a contract node output is incompatible with a node output *)
(*and check_node_and_contract_outputs call_pos ctx node_outputs = function 

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
      "Clocked outputs not supported"*)


(* Evaluates a mode for a node. *)
and eval_node_mode scope ctx is_candidate (pos, id, reqs, enss) =
  let id = HString.string_of_hstring id in
  (* Evaluate requires. *)
  let ctx, reqs, _ =
    reqs
    |> List.fold_left
         (* (eval_contract_item (Some "require") ~typ:N.Require scope) *)
         (eval_contract_item None ~typ:N.Require scope)
         (ctx, [], 1)
  in
  (* Evaluate ensures. *)
  let ctx, enss, _ =
    enss |> List.fold_left (eval_contract_item None ~typ:N.Ensure scope) (ctx, [], 1) in
  let path =
    scope |> List.fold_left (fun l (_, name) -> name :: l) [id]
  in
  (* Done. *)
  Contract.mk_mode (I.mk_string_ident id) pos path reqs enss is_candidate
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
  let id' = HString.string_of_hstring id in
  let ident = I.mk_string_ident id' in

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
  let svar_scope = (call_pos, id) :: scope in
  (* Push scope for contract call. *)
  let ctx = C.push_contract_scope ctx id' in
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
    | _ (* pos *), _ (* id *), _ (* typ *), A.ClockTrue, _ (* is_const *) -> () (* pos, id, typ, is_const *)
    | _ -> fail_at_position pos (
        "clocks in contract node signature are not supported"
      )
  ) ;
  out_formals |> List.iter (
    function
    | _ (* pos *), _ (* id *), _ (* typ *), A.ClockTrue -> () (* pos, id, typ *)
    | _ -> fail_at_position pos (
        "clocks in contract node signature are not supported"
      )
  ) ;

  (* Add substitution from formal inputs to actual one before we evaluate
     everything. *)
  let ctx = try
    List.fold_left2 (
        fun ctx expr (_, in_id, typ, _, _) ->
          let in_id = HString.string_of_hstring in_id in
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
                  (HString.string_of_hstring id) in_id
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
                            Format.fprintf fmt "%a%a"
                              HString.pp_print_hstring name
                              pp_print_line_and_column pos
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
            ~shadow:true ctx (LustreIdent.mk_string_ident in_id) expr

    ) ctx in_params in_formals
    with
    | Invalid_argument _ ->  fail_at_position call_pos (
        Format.asprintf
          "arity mismatch for the input parameters of import of contract %s: \
           expected %d but got %d"
          (HString.string_of_hstring id)
          (List.length in_formals)
          (List.length in_params)
      )
  in

  (* Add substitution from formal outputs to actual one before we evaluate
     everything. *)
  let ctx = try
      List.fold_left2 (
        fun ctx expr (_, in_id, typ, _) ->
          let in_id = HString.string_of_hstring in_id in
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
                  (HString.string_of_hstring id) in_id
              )
          ) ;

          C.add_expr_for_ident
            ~shadow:true ctx (LustreIdent.mk_string_ident in_id) expr
      ) ctx (List.map (fun i -> LustreAst.Ident (pos, i))out_params) out_formals
    with
    | Invalid_argument _ ->  fail_at_position call_pos (
        Format.asprintf
          "arity mismatch for the output parameters of import of contract %s: \
           expected %d but got %d"
          (HString.string_of_hstring id)
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
        (HString.string_of_hstring id)
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
(*and add_ghost inputs outputs locals ctx pos ident type_expr ast_expr expr = 

  (* Add local declaration for ghost stream *)
  let ctx = C.add_node_local ~ghost:true ctx ident pos type_expr in

  (* Add equation for ghost stream *)
  eval_node_equation inputs outputs locals ctx (
    A.Equation (
      pos, (
        A.StructDef (
          pos,
          [A.SingleIdent (pos, I.string_of_ident false ident)]
        )
      ),
      ast_expr
    )
  )*)

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
    let scope = List.map (fun (a, b) -> a, HString.mk_hstring b) scope in
    eval_node_contract_call
      known ctx scope inputs outputs locals is_candidate call,
    cpt_a, cpt_g

  | A.AssumptionVars (_, vars) ->
    let ctx =
      List.fold_left
        (fun ctx (pos, id) ->
          let ident = I.mk_string_ident (HString.string_of_hstring id) in
          C.add_assumption_variable ctx (pos, ident)
        )
        ctx
        vars
    in
    ctx, cpt_a, cpt_g


(* Add all node contracts to contexts *)
and eval_node_contract_spec
  known ctx pos scope inputs outputs locals contract
=
  let scope = List.map (fun (a, b) -> a, HString.string_of_hstring b) scope in
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
        | ({ N.name ; N.calls ; N.is_extern } as node) :: tail when
            is_extern || not (N.has_effective_contract node) ->
          (* Imported node or node without an effective contract is ok.
             Preparing recursive call. *)
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
        if C.prop_name_in_context ctx (HString.string_of_hstring n) then
          fail_at_position pos
            (Format.asprintf "Name '%s' already used by another property" (HString.string_of_hstring n))
        else n
      )
      | None -> HString.mk_hstring (Format.asprintf "@[<h>%a@]" A.pp_print_expr ast_expr)
    in
    
    (* Add property to node *)
    let ctx = C.add_node_property ctx (Property.PropAnnot pos) (HString.string_of_hstring name) expr in

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


(* Add declarations of node to context *)
and eval_node_decl
  ctx pos inputs outputs locals items contract_spec
=

  (* Add inputs to context: as state variable to ident_expr_map, and
     to inputs *)
  let inputs' = List.map (fun (a, b, c, d, e) -> a, HString.string_of_hstring b, c, d, e) inputs in
  let ctx = eval_node_inputs ctx inputs' in

  (* Add outputs to context: as state variable to ident_expr_map, and
     to outputs *)
  let ctx =
    eval_node_outputs ~is_single:(List.length outputs = 1) ctx outputs
  in

  (* |===| Contract stuff. *)

  (* Setting candidate flag for explicit contract. *)
  let contract_spec =
    match contract_spec with
    | None -> None
    | Some spec -> Some (
      spec |> List.map (fun item -> item, false)
    )
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
      (* Remove scope for local declarations in contract *)
      C.pop_scope ctx
  in

  (* New scope for local declarations in implementation *)
  let ctx = C.push_scope ctx "impl" in

  (* Add locals to context: as state variable to ident_expr_map, and
     to inputs *)
  let ctx = eval_node_locals ctx locals in

  (* Parse equations, assertions, properties, etc. *)
  let ctx =
    eval_node_items inputs outputs locals ctx items in

  C.check_vars_defined ctx;
  
  (* Remove scope for local declarations in implementation *)
  let ctx = C.pop_scope ctx in

  (* Add assumptions, guarantees, and properties to check the values of
     state variables are in range of the declared type (subrange).
     This must be run after input, output, ghost, and local variables
     have been processed.

     We group state variables based on the kind of constraint
     used to check it. E.g. inputs go to [assume_svars] because
     we use assumptions to check their bounds.
  *)

  let assume_svars, guarantee_svars, prop_svars =
    match C.get_node ctx with
    | None -> failwith "[eval_node_decl] No current node in context."
    | Some ({ N.is_extern ; N.state_var_source_map } as node) -> (
      let assume_svars, others =
        StateVar.StateVarMap.filter
          (fun sv src ->
            let sv_type = StateVar.type_of_state_var sv in
            (match src with
             | N.Input | N.Output | N.Ghost | N.Local -> true
             | _ -> false
            ) &&
            (
              Type.is_int_range sv_type
              ||
              ((Type.is_array sv_type) &&
               Type.is_int_range (Type.last_elem_type_of_array sv_type)
              )
            )
          )
          state_var_source_map
        |> StateVar.StateVarMap.partition
          (fun _ src -> match src with N.Input -> true | _ -> false)
      in
      let prop_svars, guarantee_svars =
        if is_extern then
          StateVar.StateVarMap.empty, others
        else (
          StateVar.StateVarMap.partition
          (fun svar src ->
            let converted =
              match C.original_int_type ctx svar with
              | None -> false
              | Some ty when Type.is_int ty -> true
              | _ -> assert false
                    (* This should not happen if conversion from
                       subrange type to subrange type is not enabled
                       in LustreContext. *)
            in
            if converted then true
            else
              match src with
            | N.Local -> true
            | N.Output -> not (N.has_effective_contract node)
            | _ -> false
          )
          others
        )
      in
      StateVar.StateVarMap.bindings assume_svars |> List.map fst,
      StateVar.StateVarMap.bindings guarantee_svars |> List.map fst,
      StateVar.StateVarMap.bindings prop_svars |> List.map fst
    )
  in

  let create_constraint_name svar =
    Format.asprintf "%a._bounds" (E.pp_print_lustre_var false) svar
  in

  let create_range_expr svar =
    let svar_type = StateVar.type_of_state_var svar in
    if Type.is_array svar_type then (
      let base_type = Type.last_elem_type_of_array svar_type in
      let indices =
        Type.all_index_types_of_array svar_type
        |> List.map (fun ty -> ty, Var.mk_fresh_var Type.t_int)
      in
      let array_var = E.mk_var svar in
      let select_term =
        List.fold_left
          (fun acc (_, iv) -> E.mk_select acc (E.mk_free_var iv))
          array_var
          indices
      in
      let lbound, ubound = Type.bounds_of_int_range base_type in
      let ct =
        (E.mk_and
          (E.mk_lte (E.mk_int lbound) select_term)
          (E.mk_lte select_term (E.mk_int ubound)))
      in
      let qct =
        List.fold_left
          (fun acc (ty, iv) ->
             match Type.node_of_type ty with
             | Type.IntRange (i, j, Type.Range) -> (
               let bounds =
                 E.mk_and
                   (E.mk_lte (E.mk_int i) (E.mk_free_var iv))
                   (E.mk_lt (E.mk_free_var iv) (E.mk_int j))
               in
               E.mk_forall [iv] (E.mk_impl bounds acc)
             )
             | _ ->
               E.mk_forall [iv] acc)
          ct
          indices
      in
      qct
    )
    else (
      let lbound, ubound = Type.bounds_of_int_range svar_type in
      let lus_var = E.mk_var svar in
      (* Value of state variable is in range of declared type:
        lbound <= svar and svar <= ubound *)
      (E.mk_and
        (E.mk_lte (E.mk_int lbound) lus_var)
        (E.mk_lte lus_var (E.mk_int ubound)))
    )
  in

  let create_subrange_contract_constraint typ (ctx, acc, cpt) svar =
    let range_expr = create_range_expr svar in
    let pos =
      match C.position_of_state_variable ctx svar with
      | Some pos -> pos
      | None -> assert false
    in
    let (loc_svar, _), ctx =
      C.mk_local_for_expr ~reuse:false ~is_ghost:true pos ctx range_expr
    in
    let oname = Some (create_constraint_name svar) in
    let contract_svar = Contract.mk_svar pos cpt oname loc_svar [] in
    N.add_state_var_def loc_svar (N.ContractItem (pos, contract_svar, typ)) ;
    ctx, contract_svar :: acc, cpt + 1
  in

  let create_subrange_constraints ctx =
    (* Property constraints *)
    let ctx =
      List.fold_left
        (fun ctx svar ->
          let range_expr = create_range_expr svar in
          let source =
            let pos =
              match C.position_of_state_variable ctx svar with
              | Some pos -> pos
              | None -> assert false
            in
            let src = Property.Generated (Some pos, [svar]) in
            match C.original_int_type ctx svar with
            | Some _ -> Property.Candidate (Some src)
            | None -> src
          in
          C.add_node_property
            ctx
            source
            (create_constraint_name svar)
            range_expr
        )
        ctx
        prop_svars
    in
    let cpt_a, cpt_g =
      match C.get_node ctx with
      | None -> assert false
      | Some { N.contract } -> (
        match contract with
        | None -> 1, 1
        | Some { Contract.assumes ; Contract.guarantees } ->
          1 + List.length assumes, 1 + List.length guarantees
      )
    in
    (* Assume constraints *)
    let ctx =
      if assume_svars = [] then ctx
      else (
        let ctx, assumes, _ =
          List.fold_left
            (create_subrange_contract_constraint N.Assumption)
            (ctx, [], cpt_a)
            assume_svars
        in
        C.add_node_ass ctx assumes
      )
    in
    (* Guarantee constraints *)
    if guarantee_svars = [] then ctx
    else (
      let ctx, guarantees, _ =
      List.fold_left
        (create_subrange_contract_constraint N.Guarantee)
        (ctx, [], cpt_g)
        guarantee_svars
      in
      List.map (fun g -> g, false) guarantees
      |> C.add_node_gua ctx
    )
  in

  let ctx = create_subrange_constraints ctx in

  let ctx = C.add_node_sofar_assumption ctx in

  (* Create node from current context and return *)
  ctx


(* ********************************************************************** *)
(* Parse declarations                                                     *)
(* ********************************************************************** *)

(** Handle declaration and return context. *)
and declaration_to_context ctx = function
(* Declaration of a type as alias or free *)
| A.TypeDecl ({A.start_pos = pos}, type_rhs) ->

  let (i, type_expr) = match type_rhs with
    (* Replace type aliases with their right-hand-side *)
    | A.AliasType (_, i, type_expr) -> (i, type_expr)
    (* Replace free types with an abstract type with no user-accessible
     * representation. *)
    | A.FreeType (_, i) -> (i, A.AbstractType (pos, i))
  in

  (* Identifier of AST identifier *)
  let ident = I.mk_string_ident (HString.string_of_hstring i) in

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
  {A.start_pos = pos}, (i, ext, [], inputs, outputs, locals, items, contracts)
) -> (

  (* Identifier of AST identifier *)
  let ident = I.mk_string_ident (HString.string_of_hstring i) in

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
  {A.start_pos = pos}, (i, ext, [], inputs, outputs, locals, items, contracts)
) -> (

  (* Identifier of AST identifier *)
  let ident = I.mk_string_ident (HString.string_of_hstring i) in

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
| A.ContractNodeDecl ({A.start_pos = pos}, node_decl) ->

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
| A.NodeParamInst ({A.start_pos = pos}, _)
| A.NodeDecl ({A.start_pos = pos}, _) ->
  fail_at_position pos "Parametric nodes are not supported"
(* Parametric function declaration *)
| A.FuncDecl ({A.start_pos = pos}, _) ->
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
  
