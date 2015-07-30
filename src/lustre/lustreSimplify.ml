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
module F = LustreFunction
module C = LustreContext

(* FIXME: Remove unless debugging *)
module Event = struct let log _ = Format.printf end


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
let rec eval_ast_expr ctx = 

  function

    (* ****************************************************************** *)
    (* Identifier                                                         *)
    (* ****************************************************************** *)

    (* Identifier *)
    | A.Ident (pos, ident) -> eval_ident ctx pos ident

    (* ****************************************************************** *)
    (* Nullary operators                                                  *)
    (* ****************************************************************** *)

    (* Boolean constant true [true] *)
    | A.True pos -> eval_nullary_expr ctx pos E.t_true

    (* Boolean constant false [false] *)
    | A.False pos -> eval_nullary_expr ctx pos E.t_false

    (* Integer constant [d] *)
    | A.Num (pos, d) -> 

      eval_nullary_expr ctx pos (E.mk_int (Numeral.of_string d) )

    (* Real constant [f] *)
    | A.Dec (pos, f) -> 

      eval_nullary_expr ctx pos (E.mk_real (Decimal.of_string f))

    (* ****************************************************************** *)
    (* Unary operators                                                    *)
    (* ****************************************************************** *)

    (* Conversion to an integer number [int expr] *)
    | A.ToInt (pos, expr) -> eval_unary_ast_expr ctx pos E.mk_to_int expr 

    (* Conversion to a real number [real expr] *)
    | A.ToReal (pos, expr) -> eval_unary_ast_expr ctx pos E.mk_to_real expr

    (* Boolean negation [not expr] *)
    | A.Not (pos, expr) -> eval_unary_ast_expr ctx pos E.mk_not expr 

    (* Unary minus [- expr] *)
    | A.Uminus (pos, expr) -> eval_unary_ast_expr ctx pos E.mk_uminus expr 

    (* ****************************************************************** *)
    (* Binary operators                                                   *)
    (* ****************************************************************** *)

    (* Boolean conjunction [expr1 and expr2] *)
    | A.And (pos, expr1, expr2) ->

      eval_binary_ast_expr ctx pos E.mk_and expr1 expr2

    (* Boolean disjunction [expr1 or expr2] *)
    | A.Or (pos, expr1, expr2) -> 

      eval_binary_ast_expr ctx pos E.mk_or expr1 expr2 

    (* Boolean exclusive disjunction [expr1 xor expr2] *)
    | A.Xor (pos, expr1, expr2) -> 

      eval_binary_ast_expr ctx pos E.mk_xor expr1 expr2 

    (* Boolean implication [expr1 => expr2] *)
    | A.Impl (pos, expr1, expr2) -> 

      eval_binary_ast_expr ctx pos E.mk_impl expr1 expr2 

    (* Integer modulus [expr1 mod expr2] *)
    | A.Mod (pos, expr1, expr2) -> 

      eval_binary_ast_expr ctx pos E.mk_mod expr1 expr2 

    (* Subtraction [expr1 - expr2] *)
    | A.Minus (pos, expr1, expr2) -> 

      eval_binary_ast_expr ctx pos E.mk_minus expr1 expr2

    (* Addition [expr1 + expr2] *)
    | A.Plus (pos, expr1, expr2) -> 

      eval_binary_ast_expr ctx pos E.mk_plus expr1 expr2

    (* Real division [expr1 / expr2] *)
    | A.Div (pos, expr1, expr2) -> 

      eval_binary_ast_expr ctx pos E.mk_div expr1 expr2 

    (* Multiplication [expr1 * expr2] ]*)
    | A.Times (pos, expr1, expr2) -> 

      eval_binary_ast_expr ctx pos E.mk_times expr1 expr2 

    (* Integer division [expr1 div expr2] *)
    | A.IntDiv (pos, expr1, expr2) -> 

      eval_binary_ast_expr ctx pos E.mk_intdiv expr1 expr2 

    (* Less than or equal [expr1 <= expr2] *)
    | A.Lte (pos, expr1, expr2) -> 

      eval_binary_ast_expr ctx pos E.mk_lte expr1 expr2 

    (* Less than [expr1 < expr2] *)
    | A.Lt (pos, expr1, expr2) -> 

      eval_binary_ast_expr ctx pos E.mk_lt expr1 expr2 

    (* Greater than or equal [expr1 >= expr2] *)
    | A.Gte (pos, expr1, expr2) -> 

      eval_binary_ast_expr ctx pos E.mk_gte expr1 expr2 

    (* Greater than [expr1 > expr2] *)
    | A.Gt (pos, expr1, expr2) -> 

      eval_binary_ast_expr ctx pos E.mk_gt expr1 expr2 

    (* Arrow temporal operator [expr1 -> expr2] *)
    | A.Arrow (pos, expr1, expr2) -> 

      eval_binary_ast_expr ctx pos E.mk_arrow expr1 expr2 

    (* ****************************************************************** *)
    (* Other operators                                                    *)
    (* ****************************************************************** *)

    (* Equality [expr1 = expr2] *)
    | A.Eq (pos, expr1, expr2) -> 

      (* Apply equality pointwise *)
      let expr, ctx = 
        eval_binary_ast_expr ctx pos E.mk_eq expr1 expr2 
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
    | A.Neq (pos, expr1, expr2) -> 

      (* Translate to negated equation *)
      eval_ast_expr
        ctx
        (A.Not (Lib.dummy_pos, A.Eq (pos, expr1, expr2)))

    (* If-then-else [if expr1 then expr2 else expr3 ]*)
    | A.Ite (pos, expr1, expr2, expr3) -> 

      (* Evaluate expression for condition *)
      let expr1', ctx = 
        eval_bool_ast_expr ctx pos expr1 
      in

      eval_binary_ast_expr ctx pos (E.mk_ite expr1') expr2 expr3

    (* Temporal operator pre [pre expr] *)
    | A.Pre (pos, expr) -> 

      (* Evaluate expression *)
      let expr', ctx = eval_ast_expr ctx expr in

      (* Apply pre operator to expression, may change context with new
         variable *)
      let res, ctx = 

        D.fold

          (fun index expr (accum, ctx) -> 

             (* Apply pre operator to expression, abstract
                  non-variable term and re-use previous variables *)
             let expr', ctx = 
               E.mk_pre
                 (C.mk_local_for_expr pos)
                 ctx
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
        (pos,
         (A.Ident (clock_pos, clock_ident) as clock_expr),
         [expr_high; expr_low]) ->

      (* Evaluate expression for clock *)
      let clock_expr', ctx = 
        eval_bool_ast_expr ctx clock_pos clock_expr 
      in

      let eval_merge_case clock_sign ctx = function

        (* An expression under a [when] *)
        | A.When (pos, expr, case_clock) -> 

          (match case_clock with

            (* Compare high clock with merge clock by name *)
            | A.Ident (_, high_clock)
                when clock_sign && high_clock = clock_ident -> ()
              
            (* Compare low clock with merge clock by name *)
            | A.Not (_, A.Ident (_, low_clock))
                when not clock_sign && low_clock = clock_ident -> ()
              
            (* Clocks must be identical identifiers *)
            | _ ->
              
              C.fail_at_position 
                pos
                "Clock mismatch for argument of merge");

          (* Evaluate expression under [when] *)
          eval_ast_expr ctx expr

        (* A node call with activation condition and no defaults *)
        | A.Activate (pos, ident, case_clock, args) -> 

          (match case_clock with

            (* Compare high clock with merge clock by name *)
            | A.Ident (_, high_clock)
                when clock_sign && high_clock = clock_ident -> ()

            (* Compare low clock with merge clock by name *)
            | A.Not (_, A.Ident (_, low_clock))
                when not clock_sign && low_clock = clock_ident -> ()
              
            (* Clocks must be identical identifiers *)
            | _ -> 

              C.fail_at_position 
                pos
                "Clock mismatch for argument of merge");
          
          (* Evaluate node call without defaults *)
          eval_node_or_function_call
            ctx
            pos
            (I.mk_string_ident ident)
            case_clock
            args
            None

        (* A node call, we implicitly clock it *)
        | A.Call (pos, ident, args) -> 
          
          (* Evaluate node call without defaults *)
          eval_node_or_function_call
            ctx
            pos
            (I.mk_string_ident ident)
            (if clock_sign then clock_expr else A.Not (dummy_pos, clock_expr))
            args
            None

        (* An expression not under a [when], we implicitly clock it *)
        | expr -> 

          (* Evaluate expression under [when] *)
          eval_ast_expr ctx expr

      in
      
      
      (* Evaluate expression for high clock *)
      let expr_high', ctx = eval_merge_case true ctx expr_high in

      let expr_low', ctx = eval_merge_case false ctx expr_low in
(*
      (* Evaluate expression for low clock *)
      let expr_low', ctx = match expr_low with

        (* An expression under a [when] *)
        | A.When (pos, expr, A.Not (_, (A.Ident (_, low_clock)))) -> 

          (* Compare clocks by name *)
          if clock_ident = low_clock then 

            (* Evaluate expression under [when] *)
            eval_ast_expr ctx expr

          else

            (* Clocks must be identical identifiers *)
            C.fail_at_position 
              pos
              "Clock mismatch for argument of merge"

        (* A node call with activation condition and no defaults *)
        | A.Activate
            (pos, 
             ident,
             (A.Not (_, (A.Ident (_, low_clock_ident))) as low_clock), 
             args) -> 

          (* Compare clocks by name *)
          if clock_ident = low_clock_ident then 

            (* Evaluate node call without defaults *)
            eval_node_or_function_call
              ctx
              pos
              (I.mk_string_ident ident)
              low_clock
              args
              None

          else

            (* Clocks must be identical identifiers *)
            C.fail_at_position 
              pos
              "Clock mismatch for argument of merge"

        (* Nothing else is supported *)
        | _ ->

          C.fail_at_position 
            pos
            "Unsupported argument of merge operator"

      in
*)

      (* Apply merge pointwise to expressions *)
      let res = 

        try 

          (* Fold simultanously over indexes in expressions

             If tries contain the same indexes, the association list
             returned by bindings contain the same keys in the same
             order. *)
          D.map2

            (* Construct expressions independent of index *)
            (fun _ -> E.mk_ite clock_expr') 

            expr_high' 
            expr_low'

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
        ctx
        pos
        expr
        (D.RecordIndex field)

    (* Projection to a tuple or array field [expr.%field_expr] *)
    | A.TupleProject (pos, expr, field_expr) -> 

      (* Evaluate expression to an integer constant *)
      let field = const_int_of_ast_expr ctx pos field_expr in

      eval_ast_projection 
        ctx
        pos
        expr
        (D.TupleIndex (Numeral.to_int field))

    (* An expression list, flatten nested lists and add an index to
       each elements [(expr1, expr2)] *)
    | A.ExprList (pos, expr_list) -> 

      (* Flatten nested lists *)
      let rec flatten_expr_list accum = function 

        | [] -> List.rev accum

        | A.ExprList (pos, expr_list) :: tl -> 
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
             let expr', ctx = eval_ast_expr ctx expr in

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
    | A.TupleExpr (pos, expr_list) -> 

      let _, res, ctx = 

        (* Iterate over list of expressions *)
        List.fold_left

          (fun (i, accum, ctx) expr -> 

             (* Evaluate expression *)
             let expr', ctx = eval_ast_expr ctx expr in

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

      (* Extract list of fields of record *)
      let record_indexes = 

        try 

          (* Look up types of record fields by type of record *)
          C.type_of_ident ctx (I.mk_string_ident record_type)

        with Not_found -> 

          C.fail_at_position
            pos
            (Format.asprintf 
               "Record type %a not defined" 
               A.pp_print_ident record_type)

      in

      (* Get indexed expressions in record definition *)
      let res, ctx =

        List.fold_left 
          (fun (accum, ctx) (i, expr) -> 

             (* Evaluate expression *)
             let expr', ctx = eval_ast_expr ctx expr in

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
      let expr1', ctx = eval_ast_expr ctx expr1 in
      let expr2', ctx = eval_ast_expr ctx expr2 in

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

          (

            (* Evaluate index expression to a static integer *)
            let index_expr' = 
              static_int_of_ast_expr ctx pos index_expr 
            in 

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
                aux 
                  (D.ArrayVarIndex index_expr' :: accum)
                  tl

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

              (* Cannot be record, list or empty index *)
              | D.RecordIndex _ :: _, _
              | D.ListIndex _ :: _, _
              | [], _ ->

                C.fail_at_position
                  pos
                  "Invalid index for expression")

          )

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

      (* Replace indexes in updated expression *)
      let expr1'' = 
        D.fold
          (fun i v a -> 
             try 
               let v' = D.find i expr2'' in
               D.add i v' a
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
    | A.Condact (pos, cond, ident, args, defaults) ->  

      eval_node_or_function_call
        ctx
        pos
        (I.mk_string_ident ident)
        cond
        args
        (Some defaults)

    (* Node call without activation condition *)
    | A.Call (pos, ident, args) -> 

      eval_node_or_function_call 
        ctx
        pos
        (I.mk_string_ident ident)
        (A.True dummy_pos)
        args
        None

    (* ****************************************************************** *)
    (* Array operators                                                    *)
    (* ****************************************************************** *)

    (* Array constructor [[expr1, expr2]] *)
    | A.ArrayExpr (pos, expr_list) -> 

      let _, res, ctx = 

        (* Iterate over list of expressions *)
        List.fold_left

          (fun (i, accum, ctx) expr -> 

             (* Evaluate expression *)
             let expr', ctx = eval_ast_expr ctx expr in

             (* Increment counter *)
             (succ i,

              (* Push current index to indexes in expression and add
                 to accumulator trie *)
              D.fold
                (fun j e a -> 
                   D.add (D.ArrayIntIndex i :: j) e a)
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
      let expr', ctx = eval_ast_expr ctx expr in 

      (* Push array index to indexes in expression and add to
         accumulator trie *)
      let res = 
        D.fold
          (fun j e a -> 
             D.add (D.ArrayVarIndex array_size :: j) e a)
          expr'
          D.empty
      in

      (res, ctx)

    (* Array slice [A[i..j] with i=j is just A[k] *)
    | A.ArraySlice (pos, expr, (i, j)) when i = j -> 

      (* Evaluate expression to an integer constant *)
      let index = static_int_of_ast_expr ctx pos i |> E.mk_of_expr in

      let expr', ctx = eval_ast_expr ctx expr in 

      (* Every index starts with ArrayVarIndex or none does *)
      (match D.choose expr' with 

        (* Projection from an array indexed by variable *)
        | D.ArrayVarIndex _ :: _, _ ->

          (* Remove top index from all elements in trie *)
          let expr' = 
            D.fold
              (function 
                | D.ArrayVarIndex _ :: tl -> D.add tl
                | _ -> assert false)
              expr'
              D.empty
          in

          (* Select from array in all elements *)
          (D.map (fun e -> E.mk_select e index) expr', ctx)

        (* Projection from an array indexed by integers *)
        | D.ArrayIntIndex _ :: tl, _ -> 

          C.fail_at_position 
            pos
            "Cannot use a constant array in a recursive definition"

        (* Projection from a tuple expression *)
        | D.TupleIndex _ :: tl, _ ->

          (* Try again with the correct expression *)
          eval_ast_expr ctx (A.TupleProject (pos, expr, i))

        (* Other or no index *)
        | D.RecordIndex _ :: _, _ 
        | D.ListIndex _ :: _, _ 
        | [], _ -> C.fail_at_position pos "Selection not from an array")

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
    | A.OneHot (pos, _) -> 

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

    | A.Merge (pos, _, _) ->

      C.fail_at_position 
        pos
        "Merge operator only supported for Boolean clocks"

    | A.Activate (pos, _, _, _) -> 

      C.fail_at_position 
        pos
        "Activate operator only supported in merge"


    (* With operator for recursive node calls *)
    | A.With (pos, _, _, _) -> 

      C.fail_at_position pos "Recursive nodes not supported"

    (* Node call to a parametric node *)
    | A.CallParam (pos, _, _, _) -> 

      C.fail_at_position pos "Parametric nodes not supported" 


(* ******************************************************************** *)
(* Helper functions                                                     *)
(* ******************************************************************** *)

(* Evaluate expression to an integer constant, return as a numeral *)
and const_int_of_ast_expr ctx pos expr = 

  match

    (* Evaluate expression *)
    let expr', _ = 
      eval_ast_expr 
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
and eval_bool_ast_expr ctx pos expr = 

  (* Evaluate expression to trie *)
  let expr', ctx = eval_ast_expr ctx expr in

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


(* Evaluate expression to an integer expression, which is not
   necessarily an integer literal. *)
and static_int_of_ast_expr ctx pos expr = 

  match

    (* Evaluate expression *)
    let expr', _ = 
      eval_ast_expr 
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
and eval_ident ctx pos ident = 

  try 

    (* Get expression and bounds for identifier *)
    let res = C.expr_of_ident ctx (I.mk_string_ident ident) in

    (* Return expresssion with its bounds and unchanged context *)
    (res, ctx)

  with Not_found -> 

    C.fail_at_position
      pos
      (Format.asprintf 
         "Undeclared identifier %a"
         A.pp_print_ident ident)

(* Return the constant inserted into an empty trie *)
and eval_nullary_expr ctx pos expr = 

  (* Add expression to trie with empty index *)
  let res = D.singleton D.empty_index expr in

  (* Return expression with empty bounds and unchanged context *)
  (res, ctx)


(* Evaluate the argument of a unary expression and construct a unary
   expression of the result with the given constructor *)
and eval_unary_ast_expr ctx pos mk expr = 

  try 

    (* Evaluate expression argument *)
    let expr', ctx = eval_ast_expr ctx expr in

    (* Apply given constructor to each expression, return with same
       bounds for each expression and changed context *)
    (D.map mk expr', ctx)

  with 

    | E.Type_mismatch ->

      C.fail_at_position
        pos
        "Type mismatch for expression"


(* Evaluate the argument of a unary expression and construct a unary
   expression of the result with the given constructor *)
and eval_binary_ast_expr ctx pos mk expr1 expr2 = 

  (* Evaluate first expression *)
  let expr1', ctx = eval_ast_expr ctx expr1 in

  (* Evaluate second expression, in possibly changed context *)
  let expr2', ctx = eval_ast_expr ctx expr2 in

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

      | Invalid_argument _ ->

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

  in

  (res, ctx)


(* Return the trie starting at the given index *)
and eval_ast_projection ctx pos expr = function

  (* Record or tuple field *)
  | D.RecordIndex _ 
  | D.TupleIndex _ 
  | D.ArrayIntIndex _ as index ->

    (* Evaluate argument of expression *)
    let expr', ctx = eval_ast_expr ctx expr in

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
  | D.ArrayVarIndex _ -> raise (Invalid_argument "eval_ast_projection")


and eval_node_or_function_call ctx pos ident cond args defaults = 

  match 

    try 

      (* Get called node by identifier *)
      Some (C.node_of_name ctx ident)

    (* No node of that identifier *)
    with Not_found -> None

  with

    (* Evaluate call to node *)
    | Some node -> 

      eval_node_call ctx pos ident node cond args defaults 

    (* Check if we have a function *)
    | None ->

      match 

        try 

          (* Get called function by identifier *)
          Some (C.function_of_name ctx ident)

        (* No function of that identifier *)
        with Not_found -> None

      with 

        (* Evaluate call to function *)
        | Some func -> 

          (match cond with 

            (* Can only call functions without activation condition *)
            | A.True _ -> 

              eval_function_call ctx pos ident func args 

            (* Fail if this is a condact call *)
            | _ -> 

              C.fail_at_position
                pos
                "Invalid function call")

        (* Neither node nor function of that name *)
        | None -> 

          (* Node or function may be forward referenced *)
          raise (C.Node_or_function_not_found (ident, pos))




(* Return a trie with the outputs of a node call *)
and eval_node_call
    ctx
    pos
    ident
    { N.name = node_name;
      N.inputs = node_inputs; 
      N.oracles = node_oracles;
      N.outputs = node_outputs; 
      N.props = node_props } 
    cond
    args
    defaults = 

  (* Type check expressions for node inputs and abstract to fresh
     state variables *)
  let node_inputs_of_exprs ctx node_inputs pos expr =

    try

      (* Evaluate input value *)
      let expr', ctx = 

        (* Evaluate inputs as list *)
        let expr', ctx = 
          eval_ast_expr ctx (A.ExprList (dummy_pos, expr)) 
        in

        if 

          (* Do actual and formal parameters have the same indexes? *)
          D.keys expr' = D.keys node_inputs 

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
        (fun 
          i
          state_var
          ({ E.expr_type } as expr)
          (accum, ctx) ->

          if 

            (* Expression must be of a subtype of input type *)
            Type.check_type 
              expr_type
              (StateVar.type_of_state_var state_var) &&

            (* Expression must be constant if input is *)
            (not (StateVar.is_const state_var) || 
             E.is_const expr)

          then 

            (* New variable for abstraction, is constant if input is *)
            let state_var', ctx = 
              C.mk_local_for_expr
                ~is_const:(StateVar.is_const state_var) 
                pos
                ctx
                expr
            in

            (* Add expression as input *)
            (D.add i state_var' accum, ctx)

          else

            (* Type check failed, catch exception below *)
            raise E.Type_mismatch)

        node_inputs
        expr'
        (D.empty, ctx)

    (* Type checking error or one expression has more indexes *)
    with Invalid_argument _ | E.Type_mismatch -> 

      C.fail_at_position pos "Type mismatch for input parameters"

  in

  (* Type check defaults against outputs, return state variable for
     activation condition *)
  let node_act_cond_of_expr ctx node_outputs pos cond defaults =

    (* Evaluate activation condition *)
    let cond', ctx = eval_bool_ast_expr ctx pos cond in

    if 

      (* Node call has an activation condition? *)
      E.equal cond' E.t_true

    then

      (* No state variable for activation, no defaults and context is
         unchanged *)
      None, None, ctx

    else

      (

        (* New variable for activation condition *)
        let state_var, ctx = C.mk_local_for_expr pos ctx cond' in

        (* Evaluate default value *)
        let defaults', ctx = 
          match defaults with

            (* Single default, do not wrap in list *)
            | Some [d] -> 

              let d', ctx = eval_ast_expr ctx d in 
              Some d', ctx

            (* Not a single default, wrap in list *)
            | Some d ->

              let d', ctx = 
                eval_ast_expr ctx (A.ExprList (dummy_pos, d)) 
              in 
              Some d', ctx

            (* No defaults, skip *)
            | None -> None, ctx

        in

        match defaults' with 

          (* No defaults, just return state variable for activation
             condition *)
          | None -> Some state_var, None, ctx

          | Some defaults' -> 

            (try 

               (* Iterate over state variables in outputs and expressions
                  for their defaults *)
               D.iter2 
                 (fun i sv { E.expr_type = t } -> 

                    if 

                      (* Type of default must match type of respective
                         output *)
                      not (Type.check_type t (StateVar.type_of_state_var sv)) 

                    then

                      C.fail_at_position 
                        pos
                        "Type mismatch between default arguments and outputs")

                 node_outputs
                 defaults'

             with Invalid_argument _ -> 

               C.fail_at_position 
                 pos
                 "Number of default arguments must match number of outputs");

            (* Return state variable and changed context *)
            Some state_var, Some defaults', ctx

      )

  in

  (* Type check and abstract inputs to state variables *)
  let input_state_vars, ctx =
    node_inputs_of_exprs ctx node_inputs pos args
  in

  (* Type check and simplify defaults, abstract activation condition
     to state variable *)
  let cond_state_var, defaults, ctx = 
    node_act_cond_of_expr ctx node_outputs pos cond defaults
  in

  match 

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
      let res = 
        D.map E.mk_var call_outputs
      in

      (* Return previously created state variables *)
      (res, ctx)

    (* Create a new node call, cannot re-use an already created one *)
    | None  -> 

      (* Fresh state variables for oracle inputs of called node *)
      let ctx, oracle_state_vars = 
        List.fold_left
          (fun (ctx, accum) sv ->
             let sv', ctx = 
               C.mk_fresh_oracle 
                 ~is_input:true
                 ~is_const:(StateVar.is_const sv)
                 ctx
                 (StateVar.type_of_state_var sv) 
             in
             (* N.set_state_var_instance ctx sv' pos ident sv; *)
             (ctx, sv' :: accum))
          (ctx, [])
          node_oracles 
      in

      (* Create fresh state variable for each output *)
      let output_state_vars, ctx = 
        D.fold
          (fun i sv (accum, ctx) -> 
             let sv', ctx = 
               C.mk_fresh_local
                 ctx
                 (StateVar.type_of_state_var sv)
             in
             (D.add i sv' accum, ctx))
          node_outputs
          (D.empty, ctx)
      in

      (* Return tuple of state variables capturing outputs *)
      let res = 
        D.map
          E.mk_var
          output_state_vars
      in

      (* Create node call *)
      let node_call = 
        { N.call_pos = pos;
          N.call_node_name = ident;
          N.call_clock = cond_state_var;
          N.call_inputs = input_state_vars;
          N.call_oracles = oracle_state_vars;
          N.call_outputs = output_state_vars;
          N.call_defaults = defaults } 
      in

      (* Add node call to context *)
      let ctx = C.add_node_call ctx pos node_call in

      (* Return expression and changed context *)
      (res, ctx)


and eval_function_call 
    ctx
    pos
    ident
    { F.name; 
      F.inputs; 
      F.outputs; 
      F.output_ufs; 
      F.global_contracts; 
      F.mode_contracts } 
    args = 

  (* Evaluate inputs *)
  let args', ctx = 

    try 

      (* Evaluate inputs as list *)
      let expr', ctx = 
        eval_ast_expr ctx (A.ExprList (dummy_pos, args)) 
      in

      (* Remove list index if singleton *)
      let expr', ctx = 

      if 

        (* Do actual and formal parameters have the same indexes? *)
        D.keys expr' = D.keys inputs 

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

      (* Type check actual inputs against formal inputs *)
      D.iter2
        (fun _ { E.expr_type } state_var -> 
           
           if 
             
             (* Expression must be of a subtype of input type *)
             not
               (Type.check_type 
                  expr_type
                  (StateVar.type_of_state_var state_var))

           then 
             
             (* Type check failed, catch exception below *)
             raise E.Type_mismatch)
        expr'
        inputs;

      (* Continue with inputs and context *)
      expr', ctx

    (* Type checking error or one expression has more indexes *)
    with Invalid_argument _ | E.Type_mismatch -> 

      C.fail_at_position pos "Type mismatch for input parameters"

  in

  match 
    
    (* Find a previously created node call with the same paramters *)
    C.call_outputs_of_function_call ctx ident args'
      
  with 

    (* Re-use variables from previously created node call *)
    | Some call_outputs -> 

      (* Return tuple of state variables capturing outputs *)
      let res = 
        D.map E.mk_var call_outputs
      in
      
      (* Return previously created state variables *)
      (res, ctx)

    | None -> 

      (* Create fresh state variable for each output *)
      let output_state_vars, ctx = 
        D.fold
          (fun i sv (accum, ctx) -> 
             let sv', ctx = 
               C.mk_fresh_local
                 ctx
                 (StateVar.type_of_state_var sv)
             in
             (D.add i sv' accum, ctx))
          outputs
          (D.empty, ctx)
      in

      (* Return tuple of state variables capturing outputs *)
      let res = D.map E.mk_var output_state_vars in

      (* Create function call *)
      let function_call = 
        { N.call_pos = pos;
          N.call_function_name = ident;
          N.call_inputs = args';
          N.call_outputs = output_state_vars } 
      in

      (* Add node call to context *)
      let ctx = C.add_function_call ctx pos function_call in

      (* Return expression and changed context *)
      (res, ctx)
      
    | exception Invalid_argument _ -> 
      
      C.raise_no_new_definition_exc ctx



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
let rec eval_ast_type ctx = function

  (* Basic type bool, add to empty trie with empty index *)
  | A.Bool pos -> D.singleton D.empty_index Type.t_bool


  (* Basic type integer, add to empty trie with empty index *)
  | A.Int pos -> D.singleton D.empty_index Type.t_int


  (* Basic type real, add to empty trie with empty index *)
  | A.Real pos -> D.singleton D.empty_index Type.t_real


  (* Integer range type, constructed from evaluated expressions for
     bounds, and add to empty trie with empty index needs

     TODO: should allow constant node arguments as bounds, but then
     we'd have to check if in each node call the lower bound is less
     than or equal to the upper bound. *)
  | A.IntRange (pos, lbound, ubound) -> 

    (* Evaluate expressions for bounds to constants *)
    let const_lbound, const_ubound = 
      (const_int_of_ast_expr ctx pos lbound, 
       const_int_of_ast_expr ctx  pos ubound) 
    in

    (* Add to empty trie with empty index *)
    D.singleton D.empty_index (Type.mk_int_range const_lbound const_ubound)


  (* Enum type needs to be constructed *)
  | A.EnumType (pos, enum_elements) -> 

    C.fail_at_position pos "Enum types not supported" 


  (* User-defined type, look up type in defined types, return subtrie
     of starting with possibly indexed identifier *)
  | A.UserType (pos, ident) -> 

    (try 

       (* Find subtrie of types starting with identifier *)
       C.type_of_ident ctx (I.mk_string_ident ident)

     with Not_found -> 

       C.fail_at_position 
         pos
         (Format.asprintf 
            "Type %a is not declared" 
            A.pp_print_ident ident))


  (* Record type, return trie of indexes in record *)
  | A.RecordType (pos, record_fields) -> 

    (* Take all record fields *)
    List.fold_left

      (* Each index has a separate type *)
      (fun a (_, i, t) -> 

         (* Take all indexes and their defined types *)
         D.fold
           
           (* Add index of record field to index of type and add to
              trie *)
           (fun j t a -> 
              D.add (D.RecordIndex i :: j) t a)
           
           (* Evaluate type expression for field to a trie *)
           (eval_ast_type ctx t)

           (* Add to trie in accumulator *)
           a)

      (* Start with empty trie *)
      D.empty

      record_fields

  (* Tuple type, return trie of indexes in tuple fields *)
  | A.TupleType (pos, tuple_fields) -> 

    snd

      (* Take all tuple fields in order *)
      (List.fold_left

         (* Count up index of field, each field has a separate type *)
         (fun (i, a) t -> 

            (* Increment counter for field index *)
            (succ i,

             (* Take all indexes and their defined types *)
             D.fold 

               (* Add index of tuple field to index of type and add to
                  trie *)
               (fun j t a ->
                  D.add (D.TupleIndex i :: j) t a)

               (* Evaluate type expression for field to a map of index
                  to type *)
               (eval_ast_type ctx t)

               (* Add to trie in accumulator *)
               a))

         (* Start with field index zero and empty trie *)
         (0, D.empty)

         tuple_fields)


  (* Array type, return trie of indexes in tuple fields *)
  | A.ArrayType (pos, (type_expr, size_expr)) -> 

    (* Evaluate size of array *)
    let array_size = static_int_of_ast_expr ctx pos size_expr in

    (* Evaluate type expression for elements *)
    let element_type = eval_ast_type ctx type_expr in

    (* Add array bounds to type *)
    D.fold
      (fun j t a -> 
         D.add (j @ [D.ArrayVarIndex array_size]) (Type.mk_array t Type.t_int) a)
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
  
