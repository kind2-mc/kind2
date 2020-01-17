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


(* The main function {!declarations_to_nodes} iterates over the list
   of declarations obtained from parsing Lustre input and returns a
   list of Lustre nodes.

   All alias types are substituted with basic types, global constants
   are propagated to expressions, and nodes are rewritten into a
   normal form, see below. *)


(* Abbreviations *)
module A = LustreAst
module I = LustreIdent
module D = LustreIndex
module E = LustreExpr
module N = LustreNode
module C = LustreContext
module Contract = LustreContract

module Deps = LustreDependencies


let select_from_arrayintindex pos bound_e index expr =

  (* Remove top index from all elements in trie *)
  let vals= 
    D.fold
      (fun j v vals -> match j with 
         | D.ArrayIntIndex i :: [] ->
           (i, v) :: vals
         | _ -> assert false)
      expr []
  in

  let size = List.length vals in

  (* type check with length of arrays when statically known *)
  if bound_e <> None && E.is_numeral (get bound_e) &&
     (E.numeral_of_expr (get bound_e) |> Numeral.to_int) > size
  then
    C.fail_at_position pos
      (Format.asprintf "Size of indexes on left of equation (%a) \
                        is larger than size on the right (%d)"
         (E.pp_print_expr false) (get bound_e)
         size);

  
  let last, vals = match vals with
    | (_, x) :: r -> x, r
    | _ -> assert false
  in
  
  let v =
    List.fold_left (fun acc (i, v) ->
        E.mk_ite
          (E.mk_eq index (E.mk_int (Numeral.of_int i)))
          v
          acc
      )
      last vals
  in

  D.add
    [] (* D.ArrayVarIndex (List.length vals +1 |> Numeral.of_int |> E.mk_int_expr)] *)
    v D.empty


(* ******************************************************************** *)
(* Evaluation of expressions                                            *)
(* ******************************************************************** *)

(* Given an expression parsed into the AST, evaluate to a list of
   LustreExpr.t paired with an index, sorted by indexes. Unfold and
   abstract from the context, also return a list of created variables
   and node calls.

   The functions [mk_new_state_var] and [mk_new_oracle_var] return a
   fresh state variable and fresh input constant, respectively. A
   typing context is given to type check expressions, it is not
   modified, the created variables for abstracted expressions,
   variables capturing the output of node calls and oracle inputs are
   added to the abstraction context.

   There are several mutually recursive functions, [eval_ast_expr] is
   the main entry point.

   [eval_ast_expr] processes a list of AST expressions and produces a
   list of indexed Lustre expression reverse ordered by indexes.

   TODO: 

   - fail if tuples, record or array values are greater than the 
     defined type
   - multi-dimensional arrays
   - array slicing and concatenation, 
   - arrays and records with modification, 
   - current(e when c) expressions,
   - dynamically indexed arrays, 
   - parametric nodes
   - recursive nodes

*)
let rec eval_ast_expr bounds ctx = 

  function

    (* ****************************************************************** *)
    (* Identifier                                                         *)
    (* ****************************************************************** *)

  (* Identifier *)
  | A.Ident (pos, ident) ->
    eval_ident ctx pos ident

  (* Mode ref *)
  | A.ModeRef (pos, p4th) -> (
    let p4th =
      match p4th with
      | [] -> failwith "empty mode reference"
      | [_] -> (* Reference to own modes, append path. *)
        List.rev_append (C.contract_scope_of ctx) p4th
      | _ -> (
        match C.contract_scope_of ctx with
        | _ :: tail -> List.rev_append tail p4th
        | _ -> p4th
      )
    in
    let fail () =
      C.fail_at_position pos (
        Format.asprintf
          "reference to unknown mode \"::%a\""
          (pp_print_list Format.pp_print_string "::") p4th
      )
    in
    let rec find_mode = function
      | { Contract.path ; Contract.name ; Contract.requires } :: tail ->
        if path = p4th then
          requires
          |> List.map (fun { Contract.svar } -> E.mk_var svar)
          |> E.mk_and_n
          |> D.singleton D.empty_index
        else find_mode tail
      | [] -> fail ()
    in

    match C.current_node_modes ctx with
    | Some (Some modes) ->
      (* Format.printf
        "Modes:@.  @[<v>%a@]@.@."
        (pp_print_list
          (fun fmt { Contract.name ; Contract.path } ->
            Format.fprintf fmt
              "%a"
              (pp_print_list Format.pp_print_string "::")
              path
          )
          "@ "
        ) modes ; *)
      find_mode modes, ctx
    | _ -> fail ()
  )

  (* ****************************************************************** *)
  (* Nullary operators                                                  *)
  (* ****************************************************************** *)

  (* Boolean constant true [true] *)
  | A.Const (pos, A.True) -> eval_nullary_expr ctx pos E.t_true

  (* Boolean constant false [false] *)
  | A.Const (pos, A.False) -> eval_nullary_expr ctx pos E.t_false

  (* Integer constant [d] *)
  | A.Const (pos, A.Num d) -> 

    eval_nullary_expr ctx pos (E.mk_int (Numeral.of_string d) )

  (* Real constant [f] *)
  | A.Const (pos, A.Dec f) -> 

    eval_nullary_expr ctx pos (E.mk_real (Decimal.of_string f))

  (* ****************************************************************** *)
  (* Unary operators                                                    *)
  (* ****************************************************************** *)

  (* Conversion to an integer number [int expr] *)
    | A.ConvOp (pos, A.ToInt, expr) -> eval_unary_ast_expr bounds ctx pos E.mk_to_int expr 

  (* Conversion to unsigned fixed-width integer numbers [uint8-uint64 expr] *)
    | A.ConvOp (pos, A.ToUInt8, expr) -> eval_unary_ast_expr bounds ctx pos E.mk_to_uint8 expr
    | A.ConvOp (pos, A.ToUInt16, expr) -> eval_unary_ast_expr bounds ctx pos E.mk_to_uint16 expr
    | A.ConvOp (pos, A.ToUInt32, expr) -> eval_unary_ast_expr bounds ctx pos E.mk_to_uint32 expr
    | A.ConvOp (pos, A.ToUInt64, expr) -> eval_unary_ast_expr bounds ctx pos E.mk_to_uint64 expr

  (* Conversion to signed fixed-width integer numbers [int8-int64 expr] *)
    | A.ConvOp (pos, A.ToInt8, expr) -> eval_unary_ast_expr bounds ctx pos E.mk_to_int8 expr
    | A.ConvOp (pos, A.ToInt16, expr) -> eval_unary_ast_expr bounds ctx pos E.mk_to_int16 expr
    | A.ConvOp (pos, A.ToInt32, expr) -> eval_unary_ast_expr bounds ctx pos E.mk_to_int32 expr
    | A.ConvOp (pos, A.ToInt64, expr) -> eval_unary_ast_expr bounds ctx pos E.mk_to_int64 expr

  (* Conversion to a real number [real expr] *)
    | A.ConvOp (pos, A.ToReal, expr) -> eval_unary_ast_expr bounds ctx pos E.mk_to_real expr

  (* Boolean negation [not expr] *)
    | A.UnaryOp (pos, A.Not, expr) -> eval_unary_ast_expr bounds ctx pos E.mk_not expr 

  (* Unary minus [- expr] *)
    | A.UnaryOp (pos, A.Uminus, expr) -> eval_unary_ast_expr bounds ctx pos E.mk_uminus expr 

  (* Bitwise negation [! expr] *)
    | A.UnaryOp (pos, A.BVNot, expr) -> eval_unary_ast_expr bounds ctx pos E.mk_bvnot expr

  (* ****************************************************************** *)
  (* Binary operators                                                   *)
  (* ****************************************************************** *)

  (* Boolean conjunction [expr1 and expr2] *)
  | A.BinaryOp (pos, A.And, expr1, expr2) ->

      eval_binary_ast_expr bounds ctx pos E.mk_and expr1 expr2

  (* Boolean disjunction [expr1 or expr2] *)
  | A.BinaryOp (pos, A.Or, expr1, expr2) -> 

      eval_binary_ast_expr bounds ctx pos E.mk_or expr1 expr2 

  (* Boolean exclusive disjunction [expr1 xor expr2] *)
  | A.BinaryOp (pos, A.Xor, expr1, expr2) -> 

      eval_binary_ast_expr bounds ctx pos E.mk_xor expr1 expr2 

  (* Boolean implication [expr1 => expr2] *)
  | A.BinaryOp (pos, A.Impl, expr1, expr2) -> 

      eval_binary_ast_expr bounds ctx pos E.mk_impl expr1 expr2 

  (* Universal quantification *)
  | A.Quantifier (pos, A.Forall, avars, expr) ->

    let ctx, vars = vars_of_quant ctx avars in
    let bounds = bounds @
      List.map (fun v -> E.Unbound (E.unsafe_expr_of_term (Term.mk_var v)))
        vars in
    eval_unary_ast_expr bounds ctx pos (E.mk_forall vars) expr
      
  (* Existential quantification *)
  | A.Quantifier (pos, A.Exists, avars, expr) ->

    let ctx, vars = vars_of_quant ctx avars in
    let bounds = bounds @
      List.map (fun v -> E.Unbound (E.unsafe_expr_of_term (Term.mk_var v)))
        vars in
    eval_unary_ast_expr bounds ctx pos (E.mk_exists vars) expr

  (* Integer modulus [expr1 mod expr2] *)
  | A.BinaryOp (pos, A.Mod, expr1, expr2) -> 

      eval_binary_ast_expr bounds ctx pos E.mk_mod expr1 expr2 

  (* Subtraction [expr1 - expr2] *)
  | A.BinaryOp (pos, A.Minus, expr1, expr2) -> 

      eval_binary_ast_expr bounds ctx pos E.mk_minus expr1 expr2

  (* Addition [expr1 + expr2] *)
  | A.BinaryOp (pos, A.Plus, expr1, expr2) -> 

      eval_binary_ast_expr bounds ctx pos E.mk_plus expr1 expr2

  (* Real division [expr1 / expr2] *)
  | A.BinaryOp (pos, A.Div, expr1, expr2) -> 

      eval_binary_ast_expr bounds ctx pos E.mk_div expr1 expr2 

  (* Multiplication [expr1 * expr2] ]*)
  | A.BinaryOp (pos, A.Times, expr1, expr2) -> 

      eval_binary_ast_expr bounds ctx pos E.mk_times expr1 expr2 

  (* Integer division [expr1 div expr2] *)
  | A.BinaryOp (pos, A.IntDiv, expr1, expr2) -> 

      eval_binary_ast_expr bounds ctx pos E.mk_intdiv expr1 expr2 

  (* Bitwise conjunction [expr1 & expr2] *)
  | A.BinaryOp (pos, A.BVAnd, expr1, expr2) -> 

      eval_binary_ast_expr bounds ctx pos E.mk_bvand expr1 expr2

  (* Bitwise disjunction [expr1 | expr2] *)
  | A.BinaryOp (pos, A.BVOr, expr1, expr2) -> 

      eval_binary_ast_expr bounds ctx pos E.mk_bvor expr1 expr2

  (* Bitwise logical left shift *)
  | A.BinaryOp (pos, A.BVShiftL, expr1, expr2) ->
    
      eval_binary_ast_expr bounds ctx pos E.mk_bvshl expr1 expr2

  (* Bitwise logical right shift *)
  | A.BinaryOp (pos, A.BVShiftR, expr1, expr2) ->
    
      eval_binary_ast_expr bounds ctx pos E.mk_bvshr expr1 expr2

  (* Less than or equal [expr1 <= expr2] *)
  | A.CompOp (pos, A.Lte, expr1, expr2) -> 

      eval_binary_ast_expr bounds ctx pos E.mk_lte expr1 expr2 

  (* Less than [expr1 < expr2] *)
  | A.CompOp (pos, A.Lt, expr1, expr2) -> 

      eval_binary_ast_expr bounds ctx pos E.mk_lt expr1 expr2 

  (* Greater than or equal [expr1 >= expr2] *)
  | A.CompOp (pos, A.Gte, expr1, expr2) -> 

      eval_binary_ast_expr bounds ctx pos E.mk_gte expr1 expr2 

  (* Greater than [expr1 > expr2] *)
  | A.CompOp (pos, A.Gt, expr1, expr2) -> 

      eval_binary_ast_expr bounds ctx pos E.mk_gt expr1 expr2 

  (* Arrow temporal operator [expr1 -> expr2] *)
  | A.Arrow (pos, expr1, expr2) -> 

      eval_binary_ast_expr bounds ctx pos E.mk_arrow expr1 expr2 

  (* ****************************************************************** *)
  (* Other operators                                                    *)
  (* ****************************************************************** *)

  (* Equality [expr1 = expr2] *)
  | A.CompOp (pos, A.Eq, expr1, expr2) -> 

    (* Apply equality pointwise *)
    let expr, ctx = 
        eval_binary_ast_expr bounds ctx pos E.mk_eq expr1 expr2 
    in

    (* We don't want to do extensional array equality, because that
       would need quantifiers already at this level *)
    D.iter
      (fun i _ -> 
         if 
           List.exists 
             (function D.ArrayVarIndex _ -> true | _ -> false)
             i
         then 

           (* Expression has array bounds *)
           C.fail_at_position
             pos
             "Extensional array equality not supported")
      expr;

    (* Conjunction of equations *)
    let res = 
      D.singleton D.empty_index (List.fold_left E.mk_and E.t_true (D.values expr))
    in

    (* Return conjunction of equations without indexes and array bounds *)
    (res, ctx)


  (* Disequality [expr1 <> expr2] *)
  | A.CompOp (pos, A.Neq, expr1, expr2) -> 

    (* Translate to negated equation *)
    eval_ast_expr
      bounds
      ctx
      (A.UnaryOp (Lib.dummy_pos, A.Not, A.CompOp (pos, A.Eq, expr1, expr2)))

  (* If-then-else [if expr1 then expr2 else expr3 ]*)
  | A.TernaryOp (pos, A.Ite, expr1, expr2, expr3) -> 

    (* Evaluate expression for condition *)
    let expr1', ctx = 
        eval_bool_ast_expr bounds ctx pos expr1 
    in

      eval_binary_ast_expr bounds ctx pos (E.mk_ite expr1') expr2 expr3

  (* Temporal operator last *)
  | A.Last (pos, i)  -> 
    (* Translate to pre *)
    (if not (C.in_automaton ctx) then
      C.warn_at_position pos "Not in a state, last was replaced by pre"
    else ());
    eval_ast_expr bounds ctx (A.Pre (pos, A.Ident (pos, i)))

  (* Temporal operator pre [pre expr] *)
  | A.Pre (pos, expr) as original ->
    (* Evaluate expression *)
      let expr', ctx = eval_ast_expr bounds ctx expr in

    (* Apply pre operator to expression, may change context with new
       variable *)
    let res, ctx = 

      D.fold

        (fun index expr (accum, ctx) -> 

             let mk_lhs_term (sv, bounds) =
               List.fold_left (fun (i, t) -> function
                   | E.Bound b ->
                     succ i,
                     Term.mk_select t
                       (Term.mk_var @@ E.var_of_expr @@ E.mk_index_var i)
                   | E.Unbound v ->
                     i, Term.mk_select t (E.unsafe_term_of_expr v)
                   | _ -> assert false)
                 (0, Var.mk_state_var_instance sv E.pre_offset |> Term.mk_var)
                 bounds
             |> snd
             in
             
           let expr', ctx =
             E.mk_pre
              (C.mk_local_for_expr ~original ~bounds pos)
              mk_lhs_term
              ctx
              (C.guard_flag ctx)
              expr
           in
           
           (D.add index expr' accum, ctx))

        expr'
        (D.empty, ctx)

    in

    (res, ctx)

  (* Merge of complementary flows 

     [merge(h, e1, e2)] where [e1] is either 

     [(expr when h)] or
     [(activate N every h)(args)]

     and [e2] is either 

     [(expr when not h)] or
     [(activate N every not h)(args)]

  *)
  | A.Merge
      (pos, clock_ident, merge_cases) ->

    (* Evaluate expression for clock identifier *)
    let clock_expr, ctx = eval_clock_ident ctx pos clock_ident in 
    let clock_type = E.type_of_lustre_expr clock_expr in

    let cases_to_have =
      if Type.is_bool clock_type then ["true"; "false"]
      else Type.constructors_of_enum clock_type
    in
    let cases = List.map fst merge_cases in
    if List.sort String.compare cases <> List.sort String.compare cases_to_have
    then C.fail_at_position pos "Cases of merge must be exhaustive and unique";
    

    let cond_of_clock_value clock_value = match clock_value with
      | "true" -> A.Ident (pos, clock_ident)
      | "false" -> A.UnaryOp (pos, A.Not, A.Ident (pos, clock_ident))
      | _ ->
        A.CompOp (pos, A.Eq, A.Ident (pos, clock_ident), A.Ident (pos, clock_value))
    in

    let cond_expr_clock_value clock_value = match clock_value with
      | "true" -> clock_expr
      | "false" -> E.mk_not clock_expr
      | _ -> E.mk_eq clock_expr (E.mk_constr clock_value clock_type)
    in
    
    let eval_merge_case ctx = function

      (* An expression under a [when] *)
      | clock_value, A.When (pos, expr, case_clock) -> 

        (match case_clock with
          | A.ClockPos c when clock_value = "true" && c = clock_ident -> ()
          | A.ClockNeg c when clock_value = "false" && c = clock_ident -> ()
          | A.ClockConstr (cs, c) when clock_value = cs && c = clock_ident -> ()
          (* Clocks must be identical identifiers *)
          | _ -> C.fail_at_position pos "Clock mismatch for argument of merge");

        (* Evaluate expression under [when] *)
          eval_ast_expr bounds ctx expr

      (* A node call with activation condition and no defaults *)
      | clock_value, A.Activate (pos, ident, case_clock, restart_clock, args) ->

        (match case_clock with

          (* Compare high clock with merge clock by name *)
          | A.Ident (_, c) when clock_value = "true" && c = clock_ident -> ()

          (* Compare low clock with merge clock by name *)
          | A.UnaryOp (_, A.Not, A.Ident (_, c))
            when clock_value = "false" && c = clock_ident -> ()
             
          | A.CompOp (_, A.Eq, A.Ident (_, c), A.Ident (_, cv))
            when clock_value = cv && c = clock_ident -> ()
             
          (* Clocks must be identical identifiers *)
          | _ -> C.fail_at_position pos "Clock mismatch for argument of merge");
        
        (* Evaluate node call without defaults *)
        try_eval_node_call
          bounds
          ctx
          pos
          (I.mk_string_ident ident)
          case_clock
          restart_clock
          args
          None

      (* A node call, we implicitly clock it *)
      | clock_value, A.Call (pos, ident, args) -> 

        (* Evaluate node call without defaults *)
        try_eval_node_call
          bounds
          ctx
          pos
          (I.mk_string_ident ident)
          (cond_of_clock_value clock_value)
          (A.Const (pos, A.False))
          args
          None

      (* An expression not under a [when], we implicitly clock it *)
      | _, expr -> 

        (* Evaluate expression under [when] *)
          eval_ast_expr bounds ctx expr

    in

    (* Evaluate merge cases expressions *)
    let merge_cases_r, ctx =
      List.fold_left (fun (acc, ctx) ((case_value, _) as case) ->
          let e, ctx = eval_merge_case ctx case in
          (cond_expr_clock_value case_value, e) :: acc, ctx
        ) ([], ctx) merge_cases
    in

    (* isolate last case, drop condition *)
    let default_case, other_cases_r = match merge_cases_r with
      | (_, d) :: l -> d, l
      | _ -> assert false
    in
    
    (* let merge_cases' = List.rev merge_cases_r in  *)

    (* Apply merge pointwise to expressions *)
    let res = 

      try 

        List.fold_left (fun acc_else (cond, e) ->

            (* Fold simultanously over indexes in expressions

               If tries contain the same indexes, the association list
               returned by bindings contain the same keys in the same
               order. *)
            D.map2 (fun _ -> E.mk_ite cond) e acc_else
              
          ) default_case other_cases_r
          
      with 

        | Invalid_argument _ ->

          C.fail_at_position
            pos
            "Index mismatch for expressions in merge" 

        | E.Type_mismatch ->

          C.fail_at_position
            pos
            "Type mismatch for expressions in merge" 

    in
    
    (res, ctx)


  (* ****************************************************************** *)
  (* Tuple and record operators                                         *)
  (* ****************************************************************** *)

  (* Projection to a record field [expr.field] *)
  | A.RecordProject (pos, expr, field) -> 

    eval_ast_projection 
      bounds
      ctx
      pos
      expr
      (D.RecordIndex field)

  (* Projection to a tuple or array field [expr.%field_expr] *)
  | A.TupleProject (pos, expr, field_expr) -> 

    (* Evaluate expression to an integer constant *)
    let field = const_int_of_ast_expr ctx pos field_expr in

    eval_ast_projection 
      bounds
      ctx
      pos
      expr
      (D.TupleIndex (Numeral.to_int field))

  (* An expression list, flatten nested lists and add an index to
     each elements [(expr1, expr2)] *)
  | A.GroupExpr (pos, A.ExprList, expr_list) -> 

    (* Flatten nested lists *)
    let rec flatten_expr_list accum = function 

      | [] -> List.rev accum

      | A.GroupExpr (pos, A.ExprList, expr_list) :: tl -> 
        flatten_expr_list accum (expr_list @ tl)

      | expr :: tl -> flatten_expr_list (expr :: accum) tl

    in

    (* Turn ((a,b),c) into (a,b,c) *)
    let expr_list' = flatten_expr_list [] expr_list in

    let _, res, ctx = 

      (* Iterate over list of expressions *)
      List.fold_left

        (fun (i, accum, ctx) expr -> 

           (* Evaluate expression *)
             let expr', ctx = eval_ast_expr bounds ctx expr in

           (* Increment counter *)
           (succ i,

            (* Push current index to indexes in expression and add
               to accumulator trie *)
            D.fold
              (fun j e a -> 
                 D.add (D.ListIndex i :: j) e a)
              expr'
              accum,

            (* Continue with added definitions *)
            ctx))

        (* Start counting index at zero, with given abstractions and
           add to the empty trie *)
        (0, D.empty, ctx)

        expr_list'

    in

    (res, ctx)

  (* Tuple constructor [{expr1, expr2, ...}] *)
  | A.GroupExpr (pos, A.TupleExpr, expr_list) -> 

    let _, res, ctx = 

      (* Iterate over list of expressions *)
      List.fold_left

        (fun (i, accum, ctx) expr -> 

           (* Evaluate expression *)
             let expr', ctx = eval_ast_expr bounds ctx expr in

           (* Increment counter *)
           (succ i,

            (* Push current index to indexes in expression and add
               to accumulator trie *)
            D.fold
              (fun j e a -> 
                 D.add (D.TupleIndex i :: j) e a)
              expr'
              accum,

            (* Continue with added definitions *)
            ctx))

        (* Start counting index at zero, with given abstractions and
           add to the empty trie *)
        (0, D.empty, ctx)

        expr_list

    in

    (res, ctx)

  (* Record constructor [record_type {field1 = expr1; field2 = expr2; ...}] *)
  | A.RecordExpr (pos, record_type, expr_list) -> 

    let record_ident = I.mk_string_ident record_type in

    (* Extract list of fields of record *)
    let record_indexes = 

      try 

        (* Look up types of record fields by type of record *)
        C.type_of_ident ctx record_ident

      with Not_found ->
        (* Type might be forward referenced. *)
        Deps.Unknown_decl (Deps.Type, record_ident, pos) |> raise

    in

    (* Get indexed expressions in record definition *)
    let res, ctx =

      List.fold_left 
        (fun (accum, ctx) (i, expr) -> 

           (* Evaluate expression *)
             let expr', ctx = eval_ast_expr bounds ctx expr in

           (* Push field index to indexes in expression and add to
               accumulator trie *)
           (D.fold
              (fun j e t -> 
                 D.add (D.RecordIndex i :: j) e t)
              expr'
              accum), 
           ctx)

        (D.empty, ctx)

        expr_list

    in

    (* Keys in type and keys in expression must be identical *)
    if List.for_all2 D.equal_index (D.keys record_indexes) (D.keys res) then

      (res, ctx)

    else

      C.fail_at_position
        pos
        "Type mismatch in record"

  (* Update of a record, tuple or array at one index *)
  | A.StructUpdate (pos, expr1, index, expr2) -> 

    (* Evaluate expressions *)
    let expr1', ctx = eval_ast_expr bounds ctx expr1 in
    let expr2', ctx = eval_ast_expr bounds ctx expr2 in

    (* Convert an ast index to an index *)
    let rec aux accum = function 

      (* All indexes consumed return in original order *)
      | [] -> List.rev accum

      (* First index is a record field label *)
      | A.Label (pos, index) :: tl -> 

        (* Add to accumulator *)
        let accum' = D.RecordIndex index :: accum in

        (* Does expression to update have the index? *)
        if D.mem_prefix (List.rev accum') expr1' then 

          (* Continue with remaining indexes *)
          aux accum' tl

        else

          C.fail_at_position
            pos
            (Format.asprintf "Invalid index %s for expression" index)

      (* First index is an integer index *)
      | A.Index (pos, index_expr) :: tl -> 

        begin
          (* Evaluate index expression to a static integer *)
          let index_expr' = static_int_of_ast_expr ctx pos index_expr in 

          (* Expression to update with indexes already seen
             removed *)
          let expr1'_sub = 
            (* Get subtrie with index from accumulator *)
            try D.find_prefix accum expr1' with 

              (* We have checked before that the index in the
                 accumulator is a prefix of the expression to
                 update *)
              | Not_found -> assert false
          in

          (* All indexes are of the same type *)
          (match D.choose expr1'_sub with

            (* Expression is indexed with a variable *)
            | D.ArrayVarIndex _ :: _, _ -> 

              (* Abuse bound for array variable to store index to
                 update and continue *)

               (* Cast Lustre expression to a term *)
               let index_term = (index_expr' : E.expr :> Term.t) in

               let i =
                 if Term.is_numeral index_term then 
                   D.ArrayIntIndex
                     (Term.numeral_of_term index_term |> Numeral.to_int)
                 else
                   D.ArrayVarIndex index_expr'
               in

               aux (i :: accum) tl

            (* Expression is an array indexed with integers *)
            | D.ArrayIntIndex _ :: _, _ -> 

              (* Cast Lustre expression to a term *)
              let index_term = (index_expr' : E.expr :> Term.t) in

              (* Term must be a numeral *)
              if Term.is_numeral index_term then 

                (* Add array index of integer of numeral to
                   accumulator and continue *)
                aux
                  (D.ArrayIntIndex
                     (Term.numeral_of_term index_term 
                      |> Numeral.to_int) :: accum)
                  tl

              else

                C.fail_at_position
                  pos
                  "Invalid index for expression"

            (* Expression is tuple indexed with integers *)
            | D.TupleIndex _ :: _, _ -> 

              (* Cast Lustre expression to a term *)
              let index_term = (index_expr' : E.expr :> Term.t) in

              (* Term must be a numeral *)
              if Term.is_numeral index_term then 

                (* Add array index of integer of numeral to
                   accumulator and continue *)
                aux
                  (D.TupleIndex
                     (Term.numeral_of_term index_term 
                      |> Numeral.to_int) :: accum)
                  tl

              else

                C.fail_at_position
                  pos
                  "Invalid index for expression"

            (* Cannot be record, list, abstract type or empty index *)
            | D.RecordIndex _ :: _, _
            | D.ListIndex _ :: _, _
            | D.AbstractTypeIndex _ :: _, _
            | [], _ ->

              C.fail_at_position
                pos
                "Invalid index for expression")
          end

    in

    (* Get the index prefix *)
    let index' = aux D.empty_index index in

    (* Add index prefix to the indexes of the update expression *)
    let expr2'' =
      D.fold
        (fun i v a -> D.add (index' @ i) v a)
        expr2'
        D.empty
    in

      (* When the index is a variable we will need to update the structure
         conditionnaly *)
    let rec mk_cond_indexes (acc, cpt) li ri =
        match li, ri with
        | D.ArrayVarIndex v :: li', D.ArrayIntIndex vi :: ri' ->
          let acc =
            E.mk_eq (E.mk_index_var cpt) (E.mk_int (Numeral.of_int vi)) :: acc
          in
          mk_cond_indexes (acc, cpt+1) li' ri'
        | D.ArrayVarIndex v :: li', D.ArrayVarIndex vi :: ri' ->
          let acc =
            E.mk_eq (E.mk_index_var cpt) (E.mk_of_expr vi) :: acc in
          mk_cond_indexes (acc, cpt+1) li' ri'
        | _ :: li', _ :: ri' -> mk_cond_indexes (acc, cpt) li' ri'
        | [], _ | _, [] ->
          if acc = [] then raise Not_found;
          List.rev acc |> E.mk_and_n
      in

      (* how to build recursive (functional) stores in arrays *)
      let rec mk_store acc a ri x = match ri with
        | D.ArrayIntIndex vi :: ri' ->
          let i = E.mk_int (Numeral.of_int vi) in
          let a' = List.fold_left E.mk_select a acc in
          let x = mk_store [i] a' ri' x in
          E.mk_store a i x
        | D.ArrayVarIndex vi :: ri' ->
          let i = E.mk_of_expr vi in
          let a' = List.fold_left E.mk_select a acc in
          let x = mk_store [i] a' ri' x in
          E.mk_store a i x
        | _ :: ri' -> mk_store acc a ri' x
        | [] -> x
      in
      
    (* Replace indexes in updated expression *)
    let expr1'' = 
      D.fold
        (fun i v a -> 
           try 
             let v' = D.find i expr2'' in
             D.add i v' a
           with Not_found ->
           try

             begin match i with
               | D.ArrayIntIndex _ :: _ | D.ArrayVarIndex _ :: _ -> ()
               | _ -> raise Not_found
             end;

             (* The index is not in expr2'' which means we're updating an
                array that has varialbe indexes. In this case we remove
                the index and create the index variables to be able to
                mention the values of the array. *)
             (* the value if the index condition is false *)
             let old_v = List.fold_left (fun (acc, cpt) _ ->
                 E.mk_select acc (E.mk_index_var cpt), cpt + 1
               ) (v, 0) i |> fst in
             (* the new value if the condition matches *)
             let new_v = D.find index' expr2'' in
             (* the conditional value *)

             if Flags.Arrays.smt () then
               (* Build a store expression if we allow the theory of
                  arrays *)
               let v' = mk_store [] v index' new_v in
               D.add [] v' a

             else
               let v' =
                 E.mk_ite (mk_cond_indexes ([], 0) i index') new_v old_v in

               (* We've added the index variables so we can forget this
                  one *)
               D.add [] v' a
           with Not_found ->
             D.add i v a)
        expr1'
        D.empty
    in

    expr1'', ctx


  (* ****************************************************************** *)
  (* Node calls                                                         *)
  (* ****************************************************************** *)

  (* Condact, a node with an activation condition 

     [condact(cond, N(args, arg2, ...), def1, def2, ...)] *)
  | A.Condact (pos, cond, restart, ident, args, defaults) ->  

    try_eval_node_call
      bounds
      ctx
      pos
      (I.mk_string_ident ident)
      cond
      restart
      args
      (Some defaults)

  (* Node call without activation condition *)
  | A.Call (pos, ident, args)
  | A.RestartEvery (pos, ident, args, A.Const (_, A.False)) ->
    try_eval_node_call
      bounds
      ctx
      pos
      (I.mk_string_ident ident)
      (A.Const (dummy_pos, A.True))
      (A.Const (dummy_pos, A.False))
      args
      None

  (* Node call with reset/restart *)
  | A.RestartEvery (pos, ident, args, cond) ->

    try_eval_node_call
      bounds
      ctx
      pos
      (I.mk_string_ident ident)
      (A.Const (dummy_pos, A.True))
      cond
      args
      None
    
  (* ****************************************************************** *)
  (* Array operators                                                    *)
  (* ****************************************************************** *)

  (* Array constructor [[expr1, expr2]] *)
  | A.GroupExpr (pos, A.ArrayExpr, expr_list) -> 

    let _, res, ctx = 

      (* Iterate over list of expressions *)
      List.fold_left

        (fun (i, accum, ctx) expr -> 

           (* Evaluate expression *)
           let expr', ctx = eval_ast_expr bounds ctx expr in

           (* Increment counter *)
           (succ i,

            (* Push current index to indexes in expression and add
               to accumulator trie *)
            D.fold
              (fun j e a -> 
                 D.add (j @[D.ArrayIntIndex i]) e a)
              expr'
              accum,

            (* Continue with added definitions *)
            ctx))

        (* Start counting index at zero, with given abstractions and
           add to the empty trie *)
        (0, D.empty, ctx)

        expr_list

    in

    (res, ctx)

  (* Array constructor [expr^size_expr] *)
  | A.ArrayConstr (pos, expr, size_expr) -> 

    (* Evaluate expression to an integer constant *)
    let array_size = static_int_of_ast_expr ctx pos size_expr in

    (* Evaluate expression for array elements *)
      let expr', ctx = eval_ast_expr bounds ctx expr in 

      
      if not (C.are_definitions_allowed ctx) &&
         Term.is_numeral (E.unsafe_term_of_expr array_size) then
        let l_expr =
          array_size
          |> E.unsafe_term_of_expr
          |> Term.numeral_of_term
          |> Numeral.to_int
          |> Lib.list_init (fun _ -> expr) in
        
        eval_ast_expr bounds ctx (A.GroupExpr (pos, A.ArrayExpr, l_expr))
      else

        let bound =
          if Term.is_numeral (E.unsafe_term_of_expr array_size) then
            E.Fixed array_size
          else E.Bound array_size in

    (* Push array index to indexes in expression and add to
       accumulator trie *)
    let res, ctx = 
      D.fold
            (fun j e (a, ctx) ->
               (* abstract with array state variable *)
               let (state_var, _) , ctx = 
                 C.mk_local_for_expr ~bounds:[bound] pos ctx e in
               let e' = E.mk_var state_var in
               D.add (D.ArrayVarIndex array_size :: j) e' a, ctx)
        expr'
            (D.empty, ctx)
    in

    (res, ctx)

  (* Array slice [A[i..j] with i=j is just A[i] *)
  | A.ArraySlice (pos, expr, (i, j)) when i = j -> 

    (* Evaluate expression to an integer constant *)
    let index_e = static_int_of_ast_expr ctx pos i in
    let index = E.mk_of_expr index_e in
      
      let bound_e, bounds =
        try
          let index_nb = E.int_of_index_var index in
          let b, bounds = Lib.list_extract_nth bounds index_nb in
          match b with
          | E.Fixed e | E.Bound e -> Some e, bounds
          | E.Unbound _ -> None, bounds
        with Invalid_argument _ | Failure _ -> None, bounds
      in
      
      let expr', ctx = eval_ast_expr bounds ctx expr in 

      let rec push expr' =
      
    (* Every index starts with ArrayVarIndex or none does *)
      match D.choose expr' with 

      (* Projection from an array indexed by variable *)
      | D.ArrayVarIndex s :: tl, v -> 

        (* type check with length of arrays when statically known *)
        (* Disabled because not precise enough *)
        (* if bound_e <> None && E.is_numeral (get bound_e) && E.is_numeral s && *)
        (*    Numeral.geq (E.numeral_of_expr (get bound_e)) (E.numeral_of_expr s) *)
        (* then *)
        (*   C.fail_at_position pos *)
        (*     (Format.asprintf "Size of indexes on left of equation (%a) \ *)
        (*                       is larger than size on the right (%a)" *)
        (*     (E.pp_print_expr false) (get bound_e) *)
        (*     (E.pp_print_expr false) s); *)
        

        (* Remove top index from all elements in trie *)
        let expr' = 
          D.fold
            (function 
              | D.ArrayVarIndex _ :: tl -> D.add tl
              | _ -> assert false)
            expr'
            D.empty
        in

        if E.type_of_lustre_expr v |> Type.is_array then
          (* Select from array in all elements *)
          D.map (fun e -> E.mk_select e index) expr'
        else
          (* otherwise returned the indexed value *)
          expr'


      (* Projection from an array indexed by integers *)
      | D.ArrayIntIndex _ :: tl, _ -> 

        select_from_arrayintindex pos bound_e index expr'

        (*   C.fail_at_position  *)
        (*     pos *)
        (*     "Cannot use a constant array in a recursive definition" *)

      (* Projection from a tuple expression *)
        | D.TupleIndex _ :: _, _
        | D.RecordIndex _ :: _, _ 
        | D.ListIndex _ :: _, _
        | D.AbstractTypeIndex _ :: _, _ ->


          (* Try again underneath *)
          let expr' = 
            D.fold
              (fun indexes v acc -> match indexes with
                | top :: tl ->
                  let r = D.add tl v D.empty in
                  let e = push r in
                  D.fold (fun j -> D.add (top :: j)) e acc
                | _ -> assert false)
              expr'
              D.empty
          in
          expr'

      (* Other or no index *)
        | [], _ -> C.fail_at_position pos "Selection not from an array"
      in

      push expr', ctx


  (* Array slice [A[i..j,k..l]] *)
  | A.ArraySlice (pos, _, _) -> 

    C.fail_at_position pos "Array slices not implemented"

  (* ****************************************************************** *)
  (* Not implemented                                                    *)
  (* ****************************************************************** *)

  (* TODO below, roughly in order of importance and difficulty *)

  (* Concatenation of arrays [A|B] *)
  | A.ArrayConcat (pos, _, _) -> 

    C.fail_at_position pos "Array concatenation not implemented"

  (* Interpolation to base clock *)
  | A.Current (pos, A.When (_, _, _)) -> 

    C.fail_at_position pos "Current expression not supported"

  (* Boolean at-most-one constaint *)
  | A.NArityOp (pos, A.OneHot, _) -> 

    C.fail_at_position pos "One-hot expression not supported"

  (* Followed by operator *)
  | A.Fby (pos, _, _, _) -> 

    C.fail_at_position pos "Fby operator not implemented" 

  (* Projection on clock *)
  | A.When (pos, _, _) -> 

    C.fail_at_position 
      pos
      "When expression must be the argument of a current operator"

  (* Interpolation to base clock *)
  | A.Current (pos, _) -> 

    C.fail_at_position 
      pos
      "Current operator must have a when expression as argument"

  | A.Activate (pos, _, _, _, _) -> 

    C.fail_at_position 
      pos
      "Activate operator only supported in merge"

  (* With operator for recursive node calls *)
  | A.TernaryOp (pos, A.With, _, _, _) -> 

    C.fail_at_position pos "Recursive nodes not supported"

  (* Node call to a parametric node *)
  | A.CallParam (pos, _, _, _) -> 

    C.fail_at_position pos "Parametric nodes not supported" 



(* ******************************************************************** *)
(* Helper functions                                                     *)
(* ******************************************************************** *)


and var_of_quant (ctx, vars) (pos, v, ast_type) =
  (* Evaluate type expression *)
  let index_types = eval_ast_type ctx ast_type in

  (* Add state variables for all indexes of input *)
  let vars, d  =
    D.fold
      (fun index index_type (vars, d) ->
         let name = Format.sprintf "%s%s" v (D.string_of_index true index) in
         let var = Var.mk_free_var (HString.mk_hstring name) index_type in
         let ev = E.mk_free_var var in
         var :: vars, D.add index ev d)
      index_types
      (vars, D.empty)
  in

  (* Bind identifier to the index variable, shadow previous
     bindings *)
  let ctx = 
    C.add_expr_for_ident
      ~shadow:true
      ctx
      (I.mk_string_ident v)
      d
  in

  ctx, vars
  

and vars_of_quant ctx l =
  let ctx, vars = List.fold_left var_of_quant (ctx, []) l in
  ctx, List.rev vars  

(* Evaluate expression to an integer constant, return as a numeral *)
and const_int_of_ast_expr ctx pos expr =

  match

    (* Evaluate expression *)
    let expr', _ = 
      eval_ast_expr
        []
        (C.fail_on_new_definition
           ctx
           pos
           "Expression must be constant")
        expr
    in

    (* Check static and array indexes *)
    D.bindings expr'

  with

    (* Expression must evaluate to a singleton list of an integer
       expression without index and without new definitions *)
    | [ index, ({ E.expr_init = ei; E.expr_step = es }) ]
      when 
        index = D.empty_index && 
        let ei' = (ei :> Term.t) in let es' = (es :> Term.t) in 
        Term.equal ei' es' -> 

      (* Get term for initial value of expression, is equal to step *)
      let ti = E.base_term_of_expr E.base_offset ei in

      (if Term.is_numeral ti then

         Term.numeral_of_term ti

       else

         C.fail_at_position pos "Expression must be an integer")

    (* Expression is not a constant integer *)
    | _ ->       

      C.fail_at_position pos "Expression must be constant"


(* Evaluate expression to an Boolean *)
and eval_bool_ast_expr bounds ctx pos expr = 

  (* Evaluate expression to trie *)
  let expr', ctx = eval_ast_expr bounds ctx expr in

  (* Check if evaluated expression is Boolean *)
  (match D.bindings expr' with 

    (* Boolean expression without indexes *)
    | [ index, 
        ({ E.expr_type = t } as expr) ] when 
        index = D.empty_index && Type.equal_types t Type.t_bool -> 

      expr, ctx

    (* Expression is not Boolean or is indexed *)
    | _ -> 

      C.fail_at_position pos "Expression is not of Boolean type")


and eval_clock_ident ctx pos ident =

  (* Evaluate identifier to trie *)
  let expr, ctx = eval_ident ctx pos ident in

  (* Check if evaluated expression is Boolean or enumerated datatype *)
  (match D.bindings expr with 

    (* Boolean expression without indexes *)
    | [ index, 
        ({ E.expr_type = t } as expr) ] when 
        index = D.empty_index && (Type.is_bool t || Type.is_enum t) -> 

      expr, ctx

    (* Expression is not Boolean or is indexed *)
    | _ -> 

      C.fail_at_position pos "Clock identifier is not Boolean or of \
                              an enumerated datatype")


  
(* Evaluate expression to an integer expression, which is not
   necessarily an integer literal. *)
and static_int_of_ast_expr ctx pos expr =

  match

    (* Evaluate expression *)
    let expr', _ =
      eval_ast_expr
        []
        (C.fail_on_new_definition
           ctx
           pos
           "Expression must be constant")
        expr
    in

    (* Check static and array indexes *)
    D.bindings expr'

  with

    (* Expression must evaluate to a singleton list of an integer
       expression without index and without new definitions *)
    | [ index, { E.expr_init = ei; E.expr_step = es } ]
      when 
        index = D.empty_index && 
        let ei' = (ei :> Term.t) in let es' = (es :> Term.t) in 
        Term.equal ei' es' -> 

      (* Return *)
      ei

    (* Expression is not a constant integer *)
    | _ ->       

      C.fail_at_position pos "Expression must be constant"


(* Return the trie for the identifier *)
and eval_ident ctx pos i =

  let ident = I.mk_string_ident i in

  try 

    (* Get expression and bounds for identifier *)
    let res = C.expr_of_ident ctx ident in

    (* Return expresssion with its bounds and unchanged context *)
    (res, ctx)

  with Not_found ->
  try
    (* Might be a constructor *)
    let ty = Type.enum_of_constr i in
    D.singleton D.empty_index (E.mk_constr i ty), ctx
  with Not_found ->
  try
    (* Might be a free constant *)
    C.free_constant_expr_of_ident ctx ident, ctx
  with Not_found ->
    (* Might be a forward referenced constant. *)
    Deps.Unknown_decl (Deps.Const, ident, pos) |> raise

(* Return the constant inserted into an empty trie *)
and eval_nullary_expr ctx pos expr =

  (* Add expression to trie with empty index *)
  let res = D.singleton D.empty_index expr in

  (* Return expression with empty bounds and unchanged context *)
  (res, ctx)


(* Evaluate the argument of a unary expression and construct a unary
   expression of the result with the given constructor *)
and eval_unary_ast_expr bounds ctx pos mk expr = 

  try 
    (* Evaluate expression argument *)
    let expr', ctx = eval_ast_expr bounds ctx expr in

    (* Apply given constructor to each expression, return with same
       bounds for each expression and changed context *)
    (D.map mk expr', ctx)

  with 

    | E.Type_mismatch ->

      C.fail_at_position
        pos
        "Type mismatch for expression"


(* Evaluate the argument of a binary expression and construct a binary
   expression of the result with the given constructor *)
and eval_binary_ast_expr bounds ctx pos mk expr1 expr2 = 

  (* Evaluate first expression *)
  let expr1', ctx = eval_ast_expr bounds ctx expr1 in

  (* Evaluate second expression, in possibly changed context *)
  let expr2', ctx = eval_ast_expr bounds ctx expr2 in

    (* Format.eprintf *)
    (*   "E1 ==== @[<hv>%a@]@." *)
    (*   pp_print_trie_expr expr1'; *)


    (* Format.eprintf *)
    (*   "E2 ==== @[<hv>%a@]@." *)
    (*   pp_print_trie_expr expr2'; *)
    
  
  (* Apply operator pointwise to expressions *)
  let res = 

    try 

      (* Fold simultanously over indexes in expressions

         If tries contain the same indexes, the association list
         returned by bindings contain the same keys in the same
         order. *)
      D.map2

        (* Construct expressions independent of index *)
        (fun _ -> mk) 

        expr1' 
        expr2'

    with 

      | Invalid_argument s ->

        C.fail_at_position
          pos
          (Format.asprintf
             "Index mismatch for expressions %a and %a" 
             A.pp_print_expr expr1
             A.pp_print_expr expr2)

      | E.Type_mismatch ->

        C.fail_at_position
          pos
          (Format.asprintf
             "Type mismatch for expressions %a and %a" 
             A.pp_print_expr expr1
             A.pp_print_expr expr2)

      | E.NonConstantShiftOperand ->

        C.fail_at_position
          pos
          (Format.asprintf
             "Second argument %a to shift operation 
              must be constant"
              A.pp_print_expr expr2)

  in

  (res, ctx)


(* Return the trie starting at the given index *)
and eval_ast_projection bounds ctx pos expr = function

  (* Record or tuple field *)
  | D.RecordIndex _ 
  | D.TupleIndex _ 
  | D.ArrayIntIndex _ as index ->

    (* Evaluate argument of expression *)
    let expr', ctx = eval_ast_expr bounds ctx expr in

    (try 

       (* Get value for index of projected field *)
       let res = D.find_prefix [index] expr' in

       (* Return expresssion and new abstractions *)
       (res, ctx)

     with Not_found ->

       C.fail_at_position 
         pos
         (Format.asprintf 
            "Expression %a does not have index %a" 
            A.pp_print_expr expr
            (D.pp_print_one_index false) index))

  (* Cannot project array field this way, need to use select
     operator *)
  | D.ListIndex _
  | D.ArrayVarIndex _
  | D.AbstractTypeIndex _ -> raise (Invalid_argument "eval_ast_projection")


and try_eval_node_call bounds ctx pos ident cond restart args defaults =

  match 

    try 

      (* Get called node by identifier *)
      Some (C.node_of_name ctx ident)

    (* No node of that identifier *)
    with Not_found -> None

  with

    (* Evaluate call to node *)
    | Some node -> 

      eval_node_call bounds ctx pos ident node cond restart args defaults 

    (* No node of that name *)
    | None ->
      (* Node may be forward referenced *)
      Deps.Unknown_decl (Deps.NodeOrFun, ident, pos) |> raise




(* Return a trie with the outputs of a node call *)
and eval_node_call
    bounds
    ctx
    pos
    ident
    { N.name = node_name;
      N.inputs = node_inputs; 
      N.oracles = node_oracles;
      N.outputs = node_outputs; 
      N.props = node_props } 
    cond
    restart
    args
    defaults = 

  (* Type check expressions for node inputs and abstract to fresh
     state variables *)
  let node_inputs_of_exprs bounds ctx node_inputs pos expr =
    try
      (* Evaluate input value *)
      let expr', ctx = 
        (* Evaluate inputs as list *)
        let expr', ctx = eval_ast_expr bounds ctx (A.GroupExpr (dummy_pos, A.ExprList, expr)) in
        (* Return actual parameters and changed context if actual and formal
           parameters have the same indexes otherwise remove list index when
           expression is a singleton list *)
        if 
          List.for_all2 D.compatible_indexes (D.keys expr') (D.keys node_inputs)

        then

          (* Return actual parameters and changed context *)
          expr', ctx

        else


          (* Remove list index if expression is a singleton list *)
          (D.fold
             (function 
               | D.ListIndex 0 :: tl -> D.add tl
               | _ -> raise E.Type_mismatch) 
             expr'
             D.empty,
           ctx)
      in
      (* Check types and index *)
      D.fold2
        (fun i state_var ({ E.expr_type } as expr) (accum, ctx) ->
          if E.has_indexes expr
          then C.fail_at_position pos "Call with implicitely quantified index";
          (* Expression must be of a subtype of input type *)
          if Type.check_type expr_type (StateVar.type_of_state_var state_var)
             &&
             (* Expression must be constant if input is *)
             (not (StateVar.is_const state_var) || E.is_const expr)
          then (
            let bounds_state_var =
              try StateVar.StateVarHashtbl.find (C.get_state_var_bounds ctx)
                    state_var
              with Not_found -> [] in 
            (* New variable for abstraction, is constant if input is *)
            let (state_var', _) , ctx = 
              C.mk_local_for_expr
                ~is_const:(StateVar.is_const state_var)
                ~bounds:bounds_state_var
                pos
                ctx
                expr
            in
            N.set_state_var_instance state_var' pos ident state_var;
            let ctx =
              C.current_node_map ctx (
                fun node ->
                  N.set_state_var_source_if_undef node state_var' N.KLocal
              )
            in
            (* Add expression as input *)
            (D.add i state_var' accum, ctx)
          ) else
            (* Type check failed, catch exception below *)
            raise E.Type_mismatch)
        node_inputs
        expr'
        (D.empty, ctx)

    (* Type checking error or one expression has more indexes *)
    with
    | Invalid_argument _ -> 
      C.fail_at_position pos "Index mismatch for input parameters"
    | E.Type_mismatch -> 
      C.fail_at_position pos "Type mismatch for input parameters"
  in

  (* Type check defaults against outputs, return state variable for
     activation condition *)
  let node_act_cond_of_expr ctx node_outputs pos cond defaults =
    (* Evaluate activation condition *)
    let cond', ctx = eval_bool_ast_expr bounds ctx pos cond in
    (* Node call has an activation condition? *)
    if E.equal cond' E.t_true then
      (* No state variable for activation, no defaults and context is
         unchanged *)
      None, None, ctx
    else
      (* New variable for activation condition *)       
      let (state_var, _) , ctx = C.mk_local_for_expr pos ctx cond' in
      (* Evaluate default value *)
      let defaults', ctx = match defaults with
        (* Single default, do not wrap in list *)
        | Some [d] -> 
          let d', ctx = eval_ast_expr bounds ctx d in 
          Some d', ctx
        (* Not a single default, wrap in list *)
        | Some d ->
          let d', ctx = eval_ast_expr bounds ctx (A.GroupExpr (dummy_pos, A.ExprList, d)) in 
          Some d', ctx
        (* No defaults, skip *)
        | None -> None, ctx
      in

      match defaults' with 
      (* No defaults, just return state variable for activation condition *)
      | None -> Some state_var, None, ctx
      | Some defaults' -> 
        (try 
           (* Iterate over state variables in outputs and expressions for their
              defaults *)
           D.iter2 (fun i sv { E.expr_type = t } -> 
               (* Type of default must match type of respective output *)
               if not (Type.check_type t (StateVar.type_of_state_var sv)) then
                 C.fail_at_position pos
                   "Type mismatch between default arguments and outputs")
             node_outputs
             defaults'
         with Invalid_argument _ -> 
           C.fail_at_position pos
             "Number of default arguments must match number of outputs");
        (* Return state variable and changed context *)
        Some state_var, Some defaults', ctx
  in

  let restart_cond_of_expr bounds ctx pos restart =
    (* Evaluate restart condition *)
    let restart', ctx = eval_bool_ast_expr bounds ctx pos restart in
    if E.equal restart' E.t_false then None, ctx (* No restart *)
    else
      (* New variable for restart condition *)
      let (state_var, _), ctx = C.mk_local_for_expr pos ctx restart' in
      Some state_var, ctx
  in
  
  
  (* Type check and abstract inputs to state variables *)
  let input_state_vars, ctx = node_inputs_of_exprs bounds ctx node_inputs pos args in
  (* Type check and simplify defaults, abstract activation condition to state
     variable *)
  let act_state_var, defaults, ctx =
    node_act_cond_of_expr ctx node_outputs pos cond defaults in
  (* Type check restart condition *)
  let restart_state_var, ctx = restart_cond_of_expr bounds ctx pos restart in

  (* cannot have both activation condition and restart condition *)
  let cond_state_var = match act_state_var, restart_state_var with
    | None, None -> []
    | Some c, None -> [N.CActivate c]
    | None, Some r -> [N.CRestart r]
    | Some c, Some r -> [N.CActivate c; N.CRestart r]
  in
  
  match
    (* Do not reuse node call outputs if there are some oracles *)
    if node_oracles <> [] then None
    else
      (* Find a previously created node call with the same paramters *)
      C.call_outputs_of_node_call
        ctx
        ident
        cond_state_var
        input_state_vars
        defaults
  with 
    (* Re-use variables from previously created node call *)
    | Some call_outputs -> 
      (* Return tuple of state variables capturing outputs *)
      let res = D.map E.mk_var call_outputs in
      (* Return previously created state variables *)
      (res, ctx)

    (* Create a new node call, cannot re-use an already created one *)
    | None  ->
      (* Fresh state variables for oracle inputs of called node *)
      let ctx, oracle_state_vars =
        node_oracles
        |> List.rev (* Preserve order of oracles. *)
        |> List.fold_left (
          fun (ctx, accum) sv ->
             let bounds =
               try StateVar.StateVarHashtbl.find (C.get_state_var_bounds ctx) sv
               with Not_found -> [] in
            let sv', ctx = 
              C.mk_fresh_oracle
                ~is_input:true
                ~is_const:(StateVar.is_const sv)
                ~bounds
                ctx (StateVar.type_of_state_var sv) in
            N.set_state_var_instance sv' pos ident sv;
            (ctx, sv' :: accum)
        ) (ctx, [])
      in
      (* Create fresh state variable for each output *)
      let output_state_vars, ctx = 
        D.fold (
          fun i sv (accum, ctx) -> 
            let bounds =
              try StateVar.StateVarHashtbl.find (C.get_state_var_bounds ctx) sv
              with Not_found -> [] in
            let sv', ctx = 
              C.mk_fresh_local ~bounds ctx (StateVar.type_of_state_var sv)
            in
            N.set_state_var_instance sv' pos ident sv ;
            let ctx =
              C.current_node_map ctx (
                fun node -> N.set_state_var_node_call node sv'
              )
            in
            (D.add i sv' accum, ctx)
        ) node_outputs (D.empty, ctx)
      in
      (* Return tuple of state variables capturing outputs *)
      let res = D.map E.mk_var output_state_vars in
      (* Create node call *)
      let node_call = 
        { N.call_pos = pos;
          N.call_node_name = ident;
          N.call_cond = cond_state_var;
          N.call_inputs = input_state_vars;
          N.call_oracles = oracle_state_vars;
          N.call_outputs = output_state_vars;
          N.call_defaults = defaults } 
      in
      (* Add node call to context *)
      let ctx = C.add_node_call ctx pos node_call in
(*       C.current_node_map ctx (
        fun node ->
          node.LustreNode.state_var_source_map
          |> StateVar.StateVarMap.bindings
          |> Format.printf "node's svars: @[<v>%a@]@.@."
            (pp_print_list
              (fun fmt (svar, source) ->
                Format.fprintf fmt "%a -> %a"
                  StateVar.pp_print_state_var svar
                  LustreNode.pp_print_state_var_source source ;
                if source = LustreNode.Call then
                  LustreNode.get_state_var_instances svar
                  |> Format.fprintf fmt "@     -> @[<v>%a@]"
                    (pp_print_list
                      (fun fmt (_,_,sv) -> StateVar.pp_print_state_var fmt sv)
                      "@ "
                    )
              ) "@ "
            ) ;
          node.LustreNode.equations
          |> Format.printf "node's equations: @[<v>%a@]@.@."
            (pp_print_list
              (fun fmt eq ->
                Format.fprintf fmt "%a"
                  (LustreNode.pp_print_node_equation false) eq
              ) "@ "
            ) ;
          node
      ) ; *)
      (* Return expression and changed context *)
      (res, ctx)



(* ******************************************************************** *)
(* Arrays helpers                                                       *)
(* ******************************************************************** *)

(*

(* Return a list of index variables for any list *)
let index_vars_of_list l = 

  let rec index_vars' accum = function 
    | [] -> List.rev accum
    | h :: tl -> 
      index_vars' 
        ((E.mk_state_var_of_ident
            ~is_const:true
            I.empty_index
            (I.push_int_index
               (Numeral.of_int (List.length accum))
               I.index_ident)
            Type.t_int) :: accum)
        tl
  in

  index_vars' [] l



(* Take a tuple expression [a, b, c] and convert it to 
   if v=0 then a else if v=1 then b else c *)
let array_of_tuple pos index_vars expr =  

  (* Create map of conditions to expresssions per remaining index *)
  let expr' = 
    IdxTrie.fold
      (fun index expr accum -> 

         let rec aux a vl il = match vl, il with

           (* Condition for all index variables created *)
           | [], _ -> 

             (* Lookup previous expressions for remaining index *)
             let m = 
               try
                 IdxTrie.find (I.index_of_one_index_list il) accum
               with Not_found -> [] 
             in

             (* Add condition and value *)
             IdxTrie.add
               (I.index_of_one_index_list il)
               ((List.fold_left E.mk_and E.t_true a, expr) :: m)
               accum

           (* First index variable and first index of expression *)
           | index_var :: vtl, I.IntIndex i :: itl -> 

             (* Add equality between variable and index to condition *)
             aux
               ((E.mk_eq 
                   (E.mk_var index_var E.base_clock) 
                   (E.mk_int Numeral.(of_int i)))
                :: a)
               vtl 
               itl

           | _ -> 

             fail_at_position 
               pos
               (Format.asprintf 
                  "Invalid expression for array")

         in

         (* Associate condition on indexes with value *)
         aux [] index_vars (I.split_index index))

      expr
      IdxTrie.empty
  in

  (* Convert maps of conditions to expression to if-then-else
     expression *)
  IdxTrie.map
    (fun t -> 
       let rec aux = function
         | [] -> assert false

         (* Last or only condition *)
         | (c, e) :: [] -> e

         (* If condition, then expression, recurse for else *)
         | (c, e) :: tl -> E.mk_ite c e (aux tl)
       in
       aux t)
    expr'

*)


(* ******************************************************************** *)
(* Type declarations                                                    *)
(* ******************************************************************** *)
    
(* Evalute a parsed type expression to a trie of types of indexes *)
and eval_ast_type ctx = function

  (* Basic type bool, add to empty trie with empty index *)
  | A.Bool pos -> D.singleton D.empty_index Type.t_bool


  (* Basic type integer, add to empty trie with empty index *)
  | A.Int pos -> D.singleton D.empty_index Type.t_int

  | A.UInt8 pos -> D.singleton D.empty_index (Type.t_ubv 8)

  | A.UInt16 pos -> D.singleton D.empty_index (Type.t_ubv 16)

  | A.UInt32 pos -> D.singleton D.empty_index (Type.t_ubv 32)

  | A.UInt64 pos -> D.singleton D.empty_index (Type.t_ubv 64)

  | A.Int8 pos -> D.singleton D.empty_index (Type.t_bv 8)

  | A.Int16 pos -> D.singleton D.empty_index (Type.t_bv 16)

  | A.Int32 pos -> D.singleton D.empty_index (Type.t_bv 32)

  | A.Int64 pos -> D.singleton D.empty_index (Type.t_bv 64)

  (* Basic type real, add to empty trie with empty index *)
  | A.Real pos -> D.singleton D.empty_index Type.t_real


  (* Integer range type, constructed from evaluated expressions for
     bounds, and add to empty trie with empty index needs

     TODO: should allow constant node arguments as bounds, but then
     we'd have to check if in each node call the lower bound is less
     than or equal to the upper bound. *)
  | A.IntRange (pos, lbound, ubound) as t -> 

    (* Evaluate expressions for bounds to constants *)
    let const_lbound, const_ubound = 
      (const_int_of_ast_expr ctx pos lbound, 
       const_int_of_ast_expr ctx  pos ubound) 
    in

    if Numeral.lt const_ubound const_lbound then
      C.fail_at_position pos
        (Format.asprintf "Invalid range %a" A.pp_print_lustre_type t);
    
    (* Add to empty trie with empty index *)
    D.singleton D.empty_index (Type.mk_int_range const_lbound const_ubound)


  (* Enum type needs to be constructed *)
  | A.EnumType (pos, enum_name, enum_elements) -> 

    let ty = Type.mk_enum enum_name enum_elements in
      
    (* let ctx = List.fold_left (fun ctx c -> *)
    (*     C.add_expr_for_ident *)
    (*       ctx (I.mk_string_ident c)  *)
    (*       (D.singleton D.empty_index (E.mk_constr c ty)) *)
    (*   ) ctx enum_elements *)
    (* in *)
    
    (* Add to empty trie with empty index *)
    D.singleton D.empty_index ty


  (* User-defined type, look up type in defined types, return subtrie
     of starting with possibly indexed identifier *)
  | A.UserType (pos, ident) -> (
    let ident = I.mk_string_ident ident in
    try
      (* Find subtrie of types starting with identifier *)
      C.type_of_ident ctx ident
    with Not_found ->
      (* Type might be forward referenced. *)
      Deps.Unknown_decl (Deps.Type, ident, pos) |> raise
  )

  (* User-defined abstract types are represented as an integer reference
   * to an object. This reference is wrapped inside an index for that type
   * so it cannot be used as a raw integer.
   * There are abstract types in Type, but using an integer reference is able
   * to give better counterexamples. *)
  | A.AbstractType (pos, ident) ->
      D.singleton [D.AbstractTypeIndex ident] Type.t_int

  (* Record type, return trie of indexes in record *)
  | A.RecordType (pos, record_fields) -> 

    (* Take all record fields *)
    List.fold_left

      (* Each index has a separate type *)
      (fun a (_, i, t) ->
         
         (* Evaluate type expression for field to a trie *)
         let expr = eval_ast_type ctx t in

         (* Take all indexes and their defined types and add index of record
            field to index of type and add to trie *)
         D.fold (fun j t a -> 
             D.add (D.RecordIndex i :: j) t a
           ) expr a
      )

      (* Start with empty trie *)
      D.empty

      record_fields

  (* Tuple type, return trie of indexes in tuple fields *)
  | A.TupleType (pos, tuple_fields) -> 

    (* Take all tuple fields in order *)
    List.fold_left

      (* Count up index of field, each field has a separate type *)
      (fun (i, a) t -> 

         (* Evaluate type expression for field to a trie *)
         let expr = eval_ast_type ctx t in

         (* Take all indexes and their defined types and add index of tuple
            field to index of type and add to trie *)
         let d = D.fold (fun j t a ->
             D.add (D.TupleIndex i :: j) t a
           ) expr a in

         (* Increment counter for field index *)
         succ i, d
      )

      (* Start with field index zero and empty trie *)
      (0, D.empty)

      tuple_fields
      
    |> snd


  (* Array type, return trie of indexes in tuple fields *)
  | A.ArrayType (pos, (type_expr, size_expr)) -> 

    (* Evaluate size of array *)
    let array_size = static_int_of_ast_expr ctx pos size_expr in

    if not (Flags.Arrays.var_size () || E.is_const_expr array_size) then
      C.fail_at_position pos
      (Format.asprintf "Size of array (%a) has to be constant."
         (E.pp_print_expr false) array_size);
    
    (* Evaluate type expression for elements *)
    let element_type = eval_ast_type ctx type_expr in

    (* Add array bounds to type *)
    D.fold
      (fun j t a -> 
         D.add (j @ [D.ArrayVarIndex array_size])
           (Type.mk_array t
              (if E.is_numeral array_size then
                 Type.mk_int_range Numeral.zero (E.numeral_of_expr array_size)
               else Type.t_int))
           a)
      element_type
      D.empty

(*

(* Standalone Lustre simplifier for testing *)
let main () = 

  Debug.initialize ();
  Debug.enable "lustreSimplify" Format.std_formatter;

  (* Create lexing buffer *)
  let lexbuf = Lexing.from_function LustreLexer.read_from_lexbuf_stack in

  (* Read from file or standard input *)
  let in_ch, curdir = 
    if Array.length Sys.argv > 1 then 
      (let fname = Sys.argv.(1) in 

       let zero_pos = 
         { Lexing.pos_fname = fname;
           Lexing.pos_lnum = 1;
           Lexing.pos_bol = 0;
           Lexing.pos_cnum = 0 } 
       in
       lexbuf.Lexing.lex_curr_p <- zero_pos; 

       let curdir = 
         Filename.dirname fname
       in

       open_in fname, curdir) 
    else
      (stdin, Sys.getcwd ())
  in

  (* Initialize lexing buffer with channel *)
  LustreLexer.lexbuf_init in_ch curdir;

  (* Lustre file is a list of declarations *)
  let declarations = 

    try 

      (* Parse file to list of declarations *)
      LustreParser.main LustreLexer.token lexbuf 

    with 
      | LustreParser.Error ->

        let 
          { Lexing.pos_fname; 
            Lexing.pos_lnum; 
            Lexing.pos_bol; 
            Lexing.pos_cnum } = 
          Lexing.lexeme_start_p lexbuf 
        in

        Format.printf 
          "Syntax error in line %d at column %d in %s: %s@." 
          pos_lnum
          (pos_cnum - pos_bol)
          pos_fname
          (Lexing.lexeme lexbuf);

        exit 1

  in

  (* Simplify declarations to a list of nodes *)
  let nodes = declarations_to_nodes declarations in

  Format.printf 
    "@[<v>Before slicing@,%a@]@."
    (pp_print_list (LustreNode.pp_print_node false) "@,") 
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
  
