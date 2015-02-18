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


(* The main function {!declarations_to_nodes} iterates over the list
   of declarations obtained from parsing Lustre input and returns a
   list of Lustre nodes.

   All alias types are substituted with basic types, global constants
   are propagated to expressions, and nodes are rewritten into a
   normal form, see below.

   {!declarations_to_nodes'} adds to and returns a {!lustre_context}
   that is a record of 

   - [basic_types]: an association list of indexed identifiers to basic
     types of {!Type.t},

   - [indexed_types]: an association list of indexed identifiers to an
     association list of indexes to basic types. The latter maps each
     suffix of a type identifier to a basic type,

   - [free_types]: currently unused, intended to hold a list of types
     that are considered uninterpreted,

   - [type_ctx]: an association list of identifiers to basic types,

   - [index_ctx]: an association list of indexed identifiers to their
     suffixes, implemented as an association list of indexes to units
     for uniformity with [indexed_types],

   - [consts]: an association list of constant identifiers to expressions, and 

   - [nodes]: the list of parsed nodes. 


*)



(* Abbreviations *)
module A = LustreAst
module I = LustreIdent
module E = LustreExpr
module N = LustreNode

module ISet = I.LustreIdentSet

(* Node not found, possible forward reference 

   This is just failing at the moment, we'd need some dependency
   analysis to recognize cycles to fully support forward
   referencing. *)
exception Node_not_found of I.t * position


(* Sort a list of indexed expressions *)
let sort_indexed_pairs list =
  List.sort (fun (i1, _) (i2, _) -> I.compare_index i1 i2) list

(* Raise parsing exception *)
let fail_at_position pos msg = 

  Event.log
    L_warn
    "Parser error in %a: %s"
    pp_print_position pos
    msg;

  raise A.Parser_error
  

(* Raise parsing exception *)
let warn_at_position pos msg = 

  Event.log
    L_warn
    "Parser warning in %a: %s"
    pp_print_position pos
    msg


(* ******************************************************************** *)
(* Data structures                                                      *)
(* ******************************************************************** *)

(* Context for typing, flattening of indexed types and constant
   propagation *)
type lustre_context = 

  { 

    (* Type identifiers and their types *)
    basic_types : (LustreIdent.t * Type.t) list; 

    (* Map of prefix of a type identifiers to its suffixes and their
       types. Indexes must be sorted. *)
    indexed_types : 
      (LustreIdent.t * 
       (LustreIdent.index * Type.t) list) list; 

    (* Type identifiers for free types *)
    free_types : LustreIdent.t list; 

    (* Types of identifiers *)
    type_ctx : (LustreIdent.t * Type.t) list; 

    (* Map of prefix of an identifier to its suffixes

       Pair the suffix with a unit value to reuse function for
       [indexed_types]. *)
    index_ctx : 
      (LustreIdent.t * 
       (LustreIdent.index * unit) list) list; 
    
    (* Values of constants *)
    consts : (LustreIdent.t * LustreExpr.t) list; 
    
    (* Nodes *)
    nodes : LustreNode.t list;
    
  }
  

(* Initial, empty context *)
let init_lustre_context = 
  { basic_types = [];
    indexed_types = [];
    free_types = [];
    type_ctx = [];
    index_ctx = [];
    consts = [];
    nodes = [] }


(* Pretty-print a type identifier *)
let pp_print_basic_type safe ppf (i, t) = 
  Format.fprintf ppf 
    "%a: %a" 
    (I.pp_print_ident safe) i 
    Type.pp_print_type t


(* Pretty-print an identifier suffix and its type *)
let pp_print_index_type safe ppf (i, t) = 
  Format.fprintf ppf 
    "%a: %a" 
    (I.pp_print_index safe) i 
    Type.pp_print_type t


(* Pretty-print a prefix and its suffixes with their types *)
let pp_print_indexed_type safe ppf (i, t) = 

  Format.fprintf ppf 
    "%a: @[<hv 1>[%a]@]" 
    (I.pp_print_ident safe) i 
    (pp_print_list (pp_print_index_type safe) ";@ ") t


(* Pretty-print types of identifiers *)
let pp_print_type_ctx safe ppf (i, t) = 
  Format.fprintf ppf "%a: %a" 
    (I.pp_print_ident safe) i 
    Type.pp_print_type t


(* Pretty-print suffixes of identifiers *)
let pp_print_index_ctx safe ppf (i, j) = 

  Format.fprintf ppf 
    "%a: @[<hv 1>[%a]@]" 
    (I.pp_print_ident safe) i 
    (pp_print_list 
       (fun ppf (i, _) -> I.pp_print_index safe ppf i)
       ";@ ") 
    j


(* Pretty-print values of constants *)
let pp_print_consts safe ppf (i, e) = 
  Format.fprintf ppf 
    "%a: %a" 
    (I.pp_print_ident safe) i 
    (E.pp_print_lustre_expr safe) e

  

(* Pretty-print a context for type checking *)
let pp_print_lustre_context 
    safe
    ppf 
    { basic_types;
      indexed_types; 
      free_types; 
      type_ctx; 
      index_ctx; 
      consts } =
  
  Format.fprintf ppf
    "@[<v>@[<v>*** basic_types:@,%a@]@,\
          @[<v>*** indexed_types:@,%a@]@,\
          @[<v>*** free_types:@,@[<hv>%a@]@,@]\
          @[<v>*** type_ctx:@,%a@]@,\
          @[<v>*** index_ctx:@,%a@]@,\
          @[<v>*** consts:@,%a@]@,\
     @]" 
    (pp_print_list (pp_print_basic_type safe) "@,") basic_types
    (pp_print_list (pp_print_indexed_type safe) "@,") indexed_types
    (pp_print_list (I.pp_print_ident safe) ",@ ") free_types
    (pp_print_list (pp_print_type_ctx safe) "@,") type_ctx
    (pp_print_list (pp_print_index_ctx safe) "@,") index_ctx
    (pp_print_list (pp_print_consts safe) "@,") consts


(* Environment when simplifying an expression *)
type abstraction_context = 

  { 

    (* Scope for new identifiers *)
    scope : I.index;

    (* Create a new identifier for a variable *)
    mk_new_state_var : bool -> Type.t -> StateVar.t;

    (* Define an expression with a state variable or re-use previous
       definition *)
    mk_state_var_for_expr : bool -> (StateVar.t * E.t) list -> E.t -> StateVar.t * (StateVar.t * E.t) list;

    (* Create a new oracle input to guard pre operation on state
       variable *)
    mk_new_oracle_for_state_var : StateVar.t -> StateVar.t;

    (* Create a new oracle input *)
    mk_new_oracle : Type.t -> StateVar.t;

    (* Create a new identifier for an observer output *)
    mk_new_observer_state_var : Type.t -> StateVar.t;

    (* Definitions of new variables to add *)
    new_vars : (StateVar.t * E.t) list;

    (* Definitions of node calls to add *)
    new_calls : N.node_call list;

    (* Oracle inputs to add to the inputs of the node *)
    new_oracles : StateVar.t list;

    (* Observer oututs to add to the ouptuts of the node *)
    new_observers : StateVar.t list;

  }


(* Environment without abstrations allowed *)
let void_abstraction_context pos = 
  
  let msg = "Expression must be constant" in

  { scope = I.empty_index;
    mk_new_state_var = (fun _ -> fail_at_position pos msg); 
    mk_state_var_for_expr = (fun _ -> fail_at_position pos msg); 
    mk_new_oracle_for_state_var = (fun _ -> fail_at_position pos msg);
    mk_new_oracle = (fun _ -> fail_at_position pos msg);
    mk_new_observer_state_var = (fun _ -> fail_at_position pos msg);
    new_vars = []; 
    new_calls = [];
    new_oracles = [];
    new_observers = [] } 


(* Pretty-print an environment *)
let pp_print_abstraction_context 
    ppf
    { scope; new_vars; new_calls; new_oracles; new_observers } =

  Format.fprintf 
    ppf 
    "@[<v>Abstraction context for scope %a@,@[<hv>new_vars:@ @[<hv>%a@]@]@,@[<hv>new_calls:@ @[<hv>%a@]@]@,@[<hv>new_oracles:@ @[<hv>%a@]@]@,@[<hv>new_observers:@ @[<hv>%a@]@]@]"
    (I.pp_print_index false) scope
    (pp_print_list
       (fun ppf (sv, def) -> 
          Format.fprintf ppf "@[<hv>%a =@ %a@]"
            StateVar.pp_print_state_var sv
            (E.pp_print_lustre_expr false) def)
       ",@,")
    new_vars
    (pp_print_list
       (fun ppf -> function 
          | { N.call_returns = ret;
              N.call_observers = obs;
              N.call_clock = None;
              N.call_node_name = node;
              N.call_inputs = inp;
              N.call_defaults = init } -> 
            Format.fprintf ppf "@[<hv>%a =@ %a(%a)@]"
              (pp_print_list StateVar.pp_print_state_var ",@,") (ret @ obs)
              (I.pp_print_ident false) node
              (pp_print_list (E.pp_print_lustre_var false) ",@,") inp
          | { N.call_returns = ret;
              N.call_observers = obs;
              N.call_clock = Some clk;
              N.call_node_name = node;
              N.call_inputs = inp;
              N.call_defaults = init } -> 
            Format.fprintf ppf "@[<hv>%a =@ condact(%a,%a(%a),%a)@]"
              (pp_print_list StateVar.pp_print_state_var ",@,") (ret @ obs)
              (E.pp_print_lustre_var false) clk
              (I.pp_print_ident false) node
              (pp_print_list (E.pp_print_lustre_var false) ",@,") inp
              (pp_print_list (E.pp_print_lustre_expr false) ",@,") 
              (init @ (List.map (fun _ -> E.t_true) obs)))
       ",@,")
    new_calls
    (pp_print_list StateVar.pp_print_state_var ",@,") 
    new_oracles
    (pp_print_list StateVar.pp_print_state_var ",@,") 
    new_observers
    
    



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

   [eval_ast_expr'] processes a list of AST expressions and produces a
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
let rec eval_ast_expr'     
    ({ basic_types; 
       indexed_types; 
       free_types; 
       type_ctx; 
       index_ctx; 
       consts;
       nodes } as context)
    ({ scope;
       mk_new_state_var; 
       mk_state_var_for_expr; 
       mk_new_oracle_for_state_var; 
       mk_new_oracle; 
       mk_new_observer_state_var; 
       new_vars;
       new_calls;
       new_oracles;
       new_observers } as abstractions)
    result = 


  (* Evaluate the argument of a unary expression and construct a unary
     expression of the result with the given constructor *)
  let eval_unary_ast_expr mk expr pos tl = 

    let expr', abstractions' = 
      unary_apply_to 
        context 
        abstractions
        mk
        expr 
        pos
        result 
    in  

    eval_ast_expr' 
      context 
      abstractions'
      expr'
      tl

  in


  (* Evaluate the arguments of a binary expression and construct a
     binary expression of the result with the given constructor *)
  let eval_binary_ast_expr mk expr1 expr2 pos tl = 

    let expr', abstractions' = 
      binary_apply_to 
        context 
        abstractions
        mk
        expr1 
        expr2 
        pos
        result 
    in  

    eval_ast_expr' 
      context 
      abstractions'
      expr'
      tl

  in

  (* Evaluate an identifier to an expression *)
  let eval_ident pos ident = 

    (* Return value of constant *)
    try List.assoc ident consts with 

      (* Identifier is not constant *)
      | Not_found -> 

        try 

          (* Get state variable of identifier *)
          let state_var = E.state_var_of_ident scope ident in

          (* Return variable on the base clock *)
          E.mk_var state_var E.base_clock

        with Not_found -> 

          fail_at_position
            pos
            (Format.asprintf 
               "Undeclared identifier %a"
               (I.pp_print_ident false) ident)

  in    

  function

    (* All expressions evaluated, return result *)
    | [] -> (result, abstractions)


    (* An identifier without suffixes: a constant or a variable *)
    | A.Ident (pos, ident) :: tl when 
        List.mem_assoc ident type_ctx -> 

      (* Construct expression *)
      let expr = eval_ident pos ident in

      (* Add expression to result *)
      eval_ast_expr' 
        context 
        abstractions
        (* Identifier does not have an index 
           ((snd (ident :> string * I.index), expr) :: result)  *)
        ((I.empty_index, expr) :: result) 
        tl


    (* A nested identifier with suffixes *)
    | A.Ident (pos, ident) :: tl when 
        List.mem_assoc ident index_ctx -> 

      (* Expand indexed identifier *)
      let result' = 
        List.fold_left 
          (fun a (j, _) -> (j, eval_ident pos (I.push_back_index j ident)) :: a)
          result
          (List.assoc ident index_ctx)
      in

      (* Continue with unfolded indexes *)
      eval_ast_expr' 
        context 
        abstractions
        result' 
        tl


    (* Identifier must have a type or indexes *)
    | A.Ident (pos, ident) :: _ -> 

      fail_at_position 
        pos
        (Format.asprintf 
           "Undeclared identifier %a" 
           (I.pp_print_ident false) ident)


    (* Projection to a record field *)
    | A.RecordProject (pos, ident, field) :: tl -> 

      (* Append index to identifier *)
      let ident' = I.push_index field ident in

      (* Check if identifier has index *)
      if List.mem_assoc ident' index_ctx || List.mem_assoc ident' type_ctx then

        let expr' = A.Ident (pos, ident') in

        (* Continue with record field *)
        eval_ast_expr' 
          context 
          abstractions
          result 
          (expr' :: tl)

      else

        fail_at_position 
          pos
          (Format.asprintf 
             "Identifier %a does not have field %a" 
             (I.pp_print_ident false) ident
             (I.pp_print_index false) field)


    (* Projection to a tuple or array field *)
    | A.TupleProject (pos, ident, field_expr) :: tl -> 

      (* Evaluate expression to an integer constant *)
      let field = 
        I.mk_int_index (int_const_of_ast_expr context pos field_expr) 
      in

      (* Append index to identifier *)
      let ident' = I.push_index field ident in

      (* Check if identifier has index *)
      if List.mem_assoc ident' index_ctx || List.mem_assoc ident' type_ctx then

        let expr' = A.Ident (pos, ident') in

        (* Continue with record field *)
        eval_ast_expr' 
          context 
          abstractions
          result 
          (expr' :: tl)

      else

        fail_at_position 
          pos
          (Format.asprintf 
             "Identifier %a does not have field %a" 
             (I.pp_print_ident false) ident
             (I.pp_print_index false) field)


    (* Boolean constant true *)
    | A.True pos :: tl -> 

      (* Add expression to result *)
      eval_ast_expr' 
        context 
        abstractions
        ((I.empty_index, E.t_true) :: result) 
        tl


    (* Boolean constant false *)
    | A.False pos :: tl -> 

      (* Add expression to result *)
      eval_ast_expr'
        context
        abstractions 
        ((I.empty_index, E.t_false) :: result) 
        tl


    (* Integer constant *)
    | A.Num (pos, d) :: tl -> 

      (* Add expression to result *)
      eval_ast_expr' 
        context 
        abstractions
        ((I.empty_index, E.mk_int (Numeral.of_string d)) :: result) 
        tl


    (* Real constant *)
    | A.Dec (pos, f) :: tl -> 

      (* Add expression to result *)
      eval_ast_expr' 
        context 
        abstractions
        ((I.empty_index, E.mk_real (Decimal.of_string f)) :: result) 
        tl


    (* Conversion to an integer number *)
    | A.ToInt (pos, expr) :: tl -> 

      eval_unary_ast_expr E.mk_to_int expr pos tl


    (* Conversion to a real number *)
    | A.ToReal (pos, expr) :: tl -> 

      eval_unary_ast_expr E.mk_to_real expr pos tl


    (* An expression list, flatten nested lists and add an index to
       each elements *)
    | A.ExprList (pos, expr_list) :: tl -> 

      (* Flatten nested lists *)
      let rec flatten_expr_list accum = function 

        | [] -> List.rev accum

        | A.ExprList (pos, expr_list) :: tl -> 
          flatten_expr_list accum (expr_list @ tl)

        | expr :: tl -> flatten_expr_list (expr :: accum) tl

      in

      (* Turn ((a,b),c) into (a,b,c) *)
      let expr_list' = flatten_expr_list [] expr_list in

      (* Treat as tuple *)
      eval_ast_expr' 
        context 
        abstractions
        result
        (A.TupleExpr (pos, expr_list') :: tl)


    (* Tuple constructor *)
    | A.TupleExpr (pos, expr_list) :: tl -> 

      let _, abstractions', result' = 

        (* Iterate over list of expressions *)
        List.fold_left
          (fun (i, abstractions, accum) expr -> 

             (* Evaluate one expression *)
             let expr', abstractions' = 
               eval_ast_expr 
                 context 
                 abstractions
                 expr
             in

             (* Increment counter *)
             (Numeral.(succ i),

              (* Continue with added definitions *)
              abstractions',

              (* Append current index to each index of evaluated
                 expression *)
              List.fold_left 
                (fun a (j, e) -> (I.push_int_index_to_index i j, e) :: a)
                accum
                expr'))

          (Numeral.zero, abstractions, result)
          expr_list
      in

      (* TODO: Fail if more elements than defined in the tuple type *)

      (* Continue with result added *)
      eval_ast_expr' 
        context 
        abstractions'
        result' 
        tl


    (* Array constructor *)
    | A.ArrayConstr (pos, expr, size_expr) :: tl -> 

      (* Evaluate expression to an integer constant *)
      let array_size = int_const_of_ast_expr context pos size_expr in

      (* Size of array must be non-zero and positive *)
      if Numeral.(array_size <= zero) then 

        fail_at_position 
          pos
          (Format.asprintf 
             "Expression %a cannot be used as the size of an array" 
             A.pp_print_expr size_expr);

      (* Evaluate expression for array elements *)
      let expr_val, abstractions' = 
        eval_ast_expr 
          context 
          abstractions
          expr 
      in 

      (* Add expression paired with each index to the result *)
      let result' = 

        let rec aux accum = function 

          (* All elements of array enuerated

             Started with size of array, lowest index is zero *)
          | i when Numeral.(i >= array_size) -> accum

          (* Array element *)
          | i -> 


            (* Append current index to each index of evaluated
               expression and recurse to next lower array element *)
            aux 
              (List.fold_left
                 (fun a (j, e) -> 
                    (I.push_int_index_to_index i j, e) :: a)
                 accum
                 expr_val)
              Numeral.(succ i)

        in

        (* Add all array elements *)
        aux result Numeral.zero

      in

      (* TODO: Fail if more elements than defined in the array type *)

      (* Continue with result added *)
      eval_ast_expr' 
        context
        abstractions' 
        result' 
        tl

    (* Array slice *)
    | A.ArraySlice (pos, _, _) :: tl -> 

      fail_at_position
        pos
        "Array slices not implemented"


    (*
      | (index, A.ArraySlice (p, ident, slices)) :: tl ->  

    (* Maintain a list of pairs of indexes: an index in the array
      that is sliced and the corresponding index in the new array.

      [aux m a l u i] appends to each index pair in [m] all
      integers from [i] to [u] to the first index, the difference
      between [i] and [l] to the second index in the pair and add
      the resulting pair to [a] *)
      let rec aux indexes lbound ubound accum = 

      function 

    (* Reached maximum, return result *)
      | i when i > ubound -> accum

    (* Need to add integer i as index *)
      | i -> 

    (* Add to all elements in accum and recurse for next *)
      aux 
      indexes
      lbound 
      ubound
      (List.fold_left
      (fun a (j, j') -> 

      (I.add_int_to_index j i, 
      I.add_int_to_index j' (i - lbound)) :: a)
      accum
      indexes)
      (succ i)

      in

    (* Indexes to slice from array *)
      let index_map = 

      List.fold_left
      (fun a (el, eu) -> 

    (* Evaluate expression for lower bound to an integer *)
      let il = int_const_of_ast_expr context el in

      if il < 0 then 

    (* Fail *)
      raise 
      (Failure 
      (Format.asprintf 
      "Expression %a in %a cannot be used as \
      the lower bound of an array slice" 
      A.pp_print_expr el
      A.pp_print_position p));

    (* Evaluate expression for lower bound to an integer *)
      let iu = int_const_of_ast_expr context eu in

      if iu < il then

    (* Fail *)
      raise 
      (Failure 
      (Format.asprintf 
      "Expression %a in %a cannot be used as \
      the upper bound of an array slice" 
      A.pp_print_expr eu
      A.pp_print_position p));

    (* Append all indexes between il und iu to indexes in
      accumulator *)
      aux a il iu [] il)
      [([],[])]
      l

      in

      IndexedExpr 
      (List.fold_left 
      (fun a (i, i') -> 

      (match expr_find_index i [] expr_list with 

    (* Index not found *)
      | [] -> 

    (* Fail *)
      raise 
      (Failure 
      (Format.asprintf 
      "Array %a in %a does not have index %a" 
      I.pp_print_ident id
      A.pp_print_position p
      I.pp_print_index i))

      | l -> 

      List.fold_left
      (fun a (j, e) -> (i' @ j, e) :: a)
      a
      l))

      []
      index_map)

    *)


    (* Concatenation of arrays *)
    | A.ArrayConcat (pos, _, _) :: tl -> 

      fail_at_position pos "Array concatenation not implemented"


    (* Record constructor *)
    | A.RecordConstruct (pos, record_type, expr_list) :: tl -> 

      (* Get fields of record and their types *)
      let indexes = 

        try 

          List.map 
            (function (index, _) -> 
              (index, 

               (* Add field name to identifier and get type *)
               List.assoc (I.push_index index record_type) basic_types))

            (* Indexes of record type *)
            (List.assoc record_type indexed_types)

        with Not_found -> 

          fail_at_position
            pos
            (Format.asprintf 
               "Record type %a not defined" 
               (I.pp_print_ident false) record_type)

      in
(*
      Format.printf
        "RecordConstruct indexes: %a@."
        (pp_print_list 
           (fun ppf (i, e) -> 
              Format.fprintf 
                ppf 
                "%a: %a"
                (I.pp_print_index false) i 
                Type.pp_print_type e)
           ", ")
        indexes;
*)
      (* Convert identifiers to indexes for expressions in constructor *)
      let expr_list', abstractions' = 
        List.fold_left 
          (fun (accum, abstractions) (ident, ast_expr) -> 

             (* Evaluate one expression *)
             let expr', abstractions' = 
               eval_ast_expr 
                 context 
                 abstractions
                 ast_expr
             in

             (List.fold_left 
                (fun accum (index', expr') ->
                   (I.push_ident_index_to_index 
                      ident 
                      index', 
                    expr') :: accum)
                accum
                (List.rev expr'),
              abstractions')) 
          ([], abstractions)
          (List.sort (fun (i, _) (j, _) -> I.compare j i) expr_list)
      in
(*
      Format.printf
        "RecordConstruct expr_list': %a@."
        (pp_print_list 
           (fun ppf (i, e) -> 
              Format.fprintf 
                ppf 
                "%a: %a"
                (I.pp_print_index false) i 
                (E.pp_print_lustre_expr false) e)
           ", ")
        expr_list';
*)
      (* Add indexed expressions and new definitions to result *)
      let result' = 

        try 

          List.fold_left2 
            (fun 
              accum
              (record_index, record_type) 
              (expr_index, ({ E.expr_type } as expr)) -> 

              if 

                (* Indexes must match *)
                record_index = expr_index &&

                (* Element type must be a subtype of field type *)
                Type.check_type expr_type record_type 

              then


                (* Continue with added definitions *)
                ((expr_index, expr) :: accum)

              else 

                (debug lustreSimplify
                    "@[<hv>Type mismatch in record constructor:@ \
                     @[<hv>record_index: %a,@ \
                     record_type: %a,@ \
                     expr_index: %a,@ \
                     expr: %a@]@]"
                    (I.pp_print_index false) record_index
                    Type.pp_print_type record_type
                    (I.pp_print_index false) expr_index
                    (E.pp_print_lustre_expr false) expr
                 in
                 raise E.Type_mismatch))
            result
            indexes
            expr_list'


        (* Type checking error or one expression has more indexes *)
        with Invalid_argument "List.fold_left2" | E.Type_mismatch -> 

          fail_at_position
            pos
            (Format.asprintf 
               "Type mismatch in record of type %a" 
               (I.pp_print_ident false) record_type)

      in

      (* Continue with result added *)
      eval_ast_expr' 
        context
        abstractions' 
        result' 
        tl


    (* Boolean negation *)
    | A.Not (pos, expr) :: tl ->

      eval_unary_ast_expr E.mk_not expr pos tl


    (* Boolean conjunction *)
    | A.And (pos, expr1, expr2) :: tl -> 

      eval_binary_ast_expr E.mk_and expr1 expr2 pos tl


    (* Boolean disjunction *)
    | A.Or (pos, expr1, expr2) :: tl -> 

      eval_binary_ast_expr E.mk_or expr1 expr2 pos tl


    (* Boolean exclusive disjunction *)
    | A.Xor (pos, expr1, expr2) :: tl -> 

      eval_binary_ast_expr E.mk_xor expr1 expr2 pos tl


    (* Boolean implication *)
    | A.Impl (pos, expr1, expr2) :: tl -> 

      eval_binary_ast_expr E.mk_impl expr1 expr2 pos tl


    (* Boolean at-most-one constaint  *)
    | A.OneHot (pos, _) :: tl -> 

      fail_at_position pos "One-hot expression not supported"


    (* Unary minus *)
    | A.Uminus (pos, expr) :: tl -> 

      eval_unary_ast_expr E.mk_uminus expr pos tl


    (* Integer modulus *)
    | A.Mod (pos, expr1, expr2) :: tl -> 

      eval_binary_ast_expr E.mk_mod expr1 expr2 pos tl


    (* Subtraction *)
    | A.Minus (pos, expr1, expr2) :: tl -> 

      eval_binary_ast_expr E.mk_minus expr1 expr2 pos tl


    (* Addition *)
    | A.Plus (pos, expr1, expr2) :: tl -> 

      eval_binary_ast_expr E.mk_plus expr1 expr2 pos tl


    (* Real division *)
    | A.Div (pos, expr1, expr2) :: tl -> 

      eval_binary_ast_expr E.mk_div expr1 expr2 pos tl


    (* Multiplication *)
    | A.Times (pos, expr1, expr2) :: tl -> 

      eval_binary_ast_expr E.mk_times expr1 expr2 pos tl


    (* Integer division *)
    | A.IntDiv (pos, expr1, expr2) :: tl -> 

      eval_binary_ast_expr E.mk_intdiv expr1 expr2 pos tl


    (* If-then-else *)
    | A.Ite (pos, expr1, expr2, expr3) :: tl -> 

      let expr1', abstractions' = 
        eval_ast_expr 
          context
          abstractions
          expr1 
      in

      (* Check evaluated expression *)
      (match expr1' with 

        (* Boolean expression without indexes *)
        | [ index, ({ E.expr_type = t } as expr1) ] when 
            index = I.empty_index && Type.equal_types t Type.t_bool -> 

          let expr', abstractions' = 
            binary_apply_to 
              context 
              abstractions' 
              (E.mk_ite expr1) 
              expr2 
              expr3 
              pos
              result
          in

          (* Add expression to result *)
          eval_ast_expr' 
            context 
            abstractions' 
            expr'
            tl


        (* Expression is not Boolean or is indexed *)
        | _ -> 

          fail_at_position pos "Condition is not of Boolean type")


    (* With operator for recursive node calls *)
    | A.With (pos, _, _, _) :: tl -> 

      fail_at_position pos "Recursive nodes not supported"


    (* Equality *)
    | A.Eq (pos, expr1, expr2) :: tl -> 

      (* Evaluate left-hand side expression *)
      let expr1', abstractions' =
        eval_ast_expr 
          context
          abstractions
          expr1 
      in

      (* Evaluate right-hand side expression *)
      let expr2', abstractions'' =
        eval_ast_expr 
          context
          abstractions'
          expr2
      in

      (* Combine expressions with the same index *)
      let expr_eqs =

        try

          (List.fold_left2 
             (fun accum (i1, e1) (i2, e2) -> 

                (* Check for matching indexes, type checking is done
                   in the mk_eq constructor *)
                if i1 = i2 then E.mk_eq e1 e2 :: accum else

                  (* Fail if indexes are different *)
                  raise E.Type_mismatch)

             []
             expr1'
             expr2')

        (* Type checking error or one expression has more indexes *)
        with Invalid_argument "List.fold_left2" | E.Type_mismatch -> 

          fail_at_position
            pos
            (Format.asprintf
               "Type mismatch for expressions %a and %a" 
               A.pp_print_expr expr1
               A.pp_print_expr expr2)

      in

      (* Conjunction of equations *)
      let expr' = match expr_eqs with 
        | [] -> E.t_true
        | [e] -> e
        | h :: tl -> List.fold_left (fun a e -> E.mk_and e a) h tl
      in

      (* Return expression *)
      eval_ast_expr'
        context
        abstractions''
        ((I.empty_index, expr') :: result)
        tl


    (* Disequality *)
    | A.Neq (pos, expr1, expr2) :: tl -> 

      (* Return expression *)
      eval_ast_expr'
        context
        abstractions
        result
        (A.Not (dummy_pos, A.Eq (pos, expr1, expr2)) :: tl)


    (* Less than or equal *)
    | A.Lte (pos, expr1, expr2) :: tl -> 

      eval_binary_ast_expr E.mk_lte expr1 expr2 pos tl


    (* Less than *)
    | A.Lt (pos, expr1, expr2) :: tl -> 

      eval_binary_ast_expr E.mk_lt expr1 expr2 pos tl


    (* Greater than or equal *)
    | A.Gte (pos, expr1, expr2) :: tl -> 

      eval_binary_ast_expr E.mk_gte expr1 expr2 pos tl


    (* Greater than *)
    | A.Gt (pos, expr1, expr2) :: tl -> 

      eval_binary_ast_expr E.mk_gt expr1 expr2 pos tl


    (* Interpolation to base clock *)
    | A.Current (pos, A.When (_, _, _)) :: tl -> 

      fail_at_position pos "Current expression not supported"


    (* Projection on clock *)
    | A.When (pos, _, _) :: tl -> 

      fail_at_position 
        pos
        "When expression must be the argument of a current operator"


    (* Interpolation to base clock *)
    | A.Current (pos, _) :: tl -> 

      fail_at_position 
        pos
        "Current operator must have a when expression as argument"


    (* Condact, a node with an activation condition *)
    | A.Condact (pos, cond, ident, args, defaults) :: tl -> 

      (* Evaluate initial values as list of expressions *)
      let defaults', abstractions' = 
        eval_ast_expr
          context 
          abstractions
          (A.ExprList (pos, defaults))
      in

      (* Evaluate activation condition *)
      let cond', abstractions' = 

        bool_expr_of_ast_expr
          context 
          abstractions' 
          pos
          cond

      in

      let cond'', abstractions'' = 

        if 

          (* Input must not contain variable at previous state *)
          E.has_pre_var E.base_offset cond'

        then

          (* New variable for abstraction, not a constant *)
          let state_var, new_vars' = 
            mk_state_var_for_expr
              false 
              abstractions'.new_vars
              cond'
          in

          E.set_state_var_source state_var E.Abstract;

          (* Add definition of variable *)
          let abstractions'' =
            { abstractions' with new_vars = new_vars' }
          in

          (* Use abstracted variable as input parameter *)
          (E.mk_var state_var E.base_clock, 
           abstractions'')

        else

          (* Add expression as input *)
          (cond', abstractions')

      in

      eval_node_call 
        context 
        abstractions''
        pos
        cond''
        ident
        args
        defaults'
        result
        tl

(*

      (* Inputs, outputs and oracles of called node *)
      let { N.inputs = node_inputs; 
            N.outputs = node_outputs; 
            N.oracles = node_oracles } = 

        try 

          (* Get node context by identifier *)
          List.find
            (function { N.name = node_ident } -> node_ident = ident)
            nodes

        with Not_found -> 

          (* Node may be forward referenced *)
          raise (Node_not_found (ident, pos))

      in

      (* Evaluate inputs as list of expressions *)
      let args', abstractions' = 
        eval_ast_expr
          context 
          abstractions
          (A.ExprList (pos, args))
      in

      (* Evaluate initial values as list of expressions *)
      let init', abstractions' = 
        eval_ast_expr
          context 
          abstractions' 
          (A.ExprList (pos, init))
      in

      (* Evaluate initial values as list of expressions *)
      let cond', abstractions' = 

        bool_expr_of_ast_expr
          context 
          abstractions' 
          pos
          cond

      in

      (* Fresh state variables for oracle inputs of called node *)
      let oracle_state_vars = 
        List.map 
          (fun sv -> 
             mk_new_oracle_state_var (StateVar.type_of_state_var sv)) 
          node_oracles 
      in

      (* Expressions from state variables for oracle inputs *)
      let oracle_exprs = 
        List.map
          (fun sv -> E.mk_var sv E.base_clock) 
          oracle_state_vars 
      in

      (* Type check and flatten indexed expressions for input into
         list without indexes *)
      let node_input_exprs, abstractions' =
        node_inputs_of_exprs node_inputs abstractions' pos args'
      in

      (* Type check and flatten indexed expressions for input into
         list without indexes *)
      let node_init_exprs =
        node_init_of_exprs node_outputs pos init'
      in

(*
      (* Flatten indexed types of node outputs to a list of
         identifiers and their types *)
      let node_output_idents = 
        output_idents_of_node scope ident pos call_ident node_outputs
      in

      (* Node call evaluates to variables capturing the output of the
         node with indexes by their position *)
      let result' = 
        add_node_output_to_result index result node_output_idents
      in
*)

      let output_vars = 
        output_vars_of_node_output mk_new_state_var node_outputs 
      in

      let result' = 
        (List.map 
           (fun sv -> (I.empty_index, E.mk_var sv E.base_clock)) 
           output_vars) 
        @ result
      in

      (* Add expression to result *)
      eval_ast_expr' 
        context 
        { abstractions' 
          with new_calls =
                 { N.call_returns = output_vars;
                   N.call_clock = cond';
                   N.call_node_name = ident;
                   N.call_pos = pos;
                   N.call_inputs = node_input_exprs @ oracle_exprs; 
                   N.call_defaults = node_init_exprs } :: abstractions'.new_calls;
               new_oracles = abstractions'.new_oracles @ oracle_state_vars }
        result' 
        tl

*)

(*


      (try 

         let { node_inputs; node_outputs } = List.assoc ident nodes in

         let cond', new_defs' = 
           eval_ast_expr
             scope
             mk_new_state_var 
             mk_new_oracle_ident 
             mk_new_call_ident 
             context 
             new_defs 
             cond
         in

         let args', new_defs'' = 
           eval_ast_expr_list
             scope
             mk_new_state_var 
             mk_new_oracle_ident 
             mk_new_call_ident 
             context 
             new_defs' 
             args
         in

         let init', (vars', calls') =
           eval_ast_expr_list
             scope
             mk_new_state_var 
             mk_new_oracle_ident 
             mk_new_call_ident 
             context 
             new_defs'' 
             init
         in

         let call_ident = mk_new_call_ident ident in

         let node_input_exprs =
           node_inputs_of_exprs node_inputs args'
         in

         let node_output_idents = 
           output_idents_of_node ident pos call_ident node_outputs
         in

         (* TODO: fold_right2 on node_outputs and init', sort both by
            index, type check and add to a list *)




         let result' = 
           add_node_output_to_result index result node_output_idents
         in

         (* Add expression to result *)
         eval_ast_expr' 
           scope
           mk_new_state_var 
           mk_new_oracle_ident 
           mk_new_call_ident 
           context 
           result' 
           (vars', 
            (node_output_idents, 
             E.t_true, 
             ident, 
             node_input_exprs, 
             init_exprs) :: calls') 
           tl

       with Not_found -> 

         (* Fail *)
         raise 
           (Failure 
              (Format.asprintf 
                 "Node %a not defined or forward-referenced in %a" 
                 (I.pp_print_ident false) ident
                 A.pp_print_position dummy_pos)))

*)

    (* Temporal operator pre *)
    | A.Pre (pos, expr) :: tl -> 

      (try 

         (* Evaluate expression *)
         let expr', abstractions' = 
           eval_ast_expr 
             context 
             abstractions
             expr 
         in

         (* Abstract expression under pre to a fresh variable *)
         let expr'', abstractions'' = 

           List.fold_left
             (fun 
               (accum, ({ mk_state_var_for_expr; new_vars } as abstractions)) 
               (index, expr) -> 
               let expr', new_vars' = 
                 E.mk_pre (mk_state_var_for_expr false) new_vars expr 
               in
               (((index, expr') :: accum), 
                { abstractions with new_vars = new_vars' }))
             (result, abstractions')
             expr'

         in

         (* Add expression to result *)
         eval_ast_expr' 
           context 
           abstractions''
           expr'' 
           tl

       with E.Type_mismatch ->

         fail_at_position pos "Type mismatch for expressions")


    (* Followed by operator *)
    | A.Fby (pos, _, _, _) :: tl -> 

      fail_at_position pos "Fby operator not implemented" 


    (* Arrow temporal operator *)
    | A.Arrow (pos, expr1, expr2) :: tl -> 

      eval_binary_ast_expr E.mk_arrow expr1 expr2 pos tl


    (* Node call *)
    | A.Call (pos, ident, args) :: tl -> 

      eval_node_call 
        context 
        abstractions
        pos
        E.t_true
        ident
        args
        []
        result
        tl

    (* Node call to a parametric node *)
    | A.CallParam (pos, _, _, _) :: tl -> 

      fail_at_position pos "Parametric nodes not supported" 



(* Apply operation to expression component-wise *)
and unary_apply_to 
    context 
    abstractions
    mk 
    expr 
    pos
    accum = 

  try 

    (* Evaluate expression *)
    let expr', abstractions' = 
      eval_ast_expr 
        context 
        abstractions
        expr 
    in

    (* Expression evaluates to indexed expression (is sorted by
       indexes), add in reverse order to the stack *)
    (List.fold_left
       (fun a (j, e) -> (j, mk e) :: a)
       accum
       expr',
     abstractions')

  with E.Type_mismatch ->

    fail_at_position pos "Type mismatch for expressions"


(* Apply operation to expressions component-wise *)
and binary_apply_to 
    context 
    abstractions
    mk 
    expr1 
    expr2 
    pos
    accum = 

  (* Evaluate first expression *)
  let expr1', abstractions' = 
    eval_ast_expr 
      context 
      abstractions
      expr1 
  in

  (* Evaluate second expression *)
  let expr2', abstractions' = 
    eval_ast_expr 
      context 
      abstractions'
      expr2 
  in

  try 

    (* Check type of corresponding expressions 

       Expressions evaluate to indexed expressions (sorted by
       indexes), add in reverse order to the stack *)
    (List.fold_left2
       (fun accum (index1, expr1) (index2, expr2) -> 
          (index1, mk expr1 expr2) :: accum)
       accum
       expr1'
       expr2',
     abstractions')

  (* Type checking error or one expression has more indexes *)
  with Invalid_argument "List.fold_left2" | E.Type_mismatch -> 

    fail_at_position
      pos
      (Format.asprintf
         "Type mismatch for expressions %a and %a" 
         A.pp_print_expr expr1
         A.pp_print_expr expr2)


(* Evaluate expression *)
and eval_ast_expr 
    context 
    abstractions
    ast_expr = 

  let expr', abstractions' = 
    eval_ast_expr' 
      context
      abstractions
      [] 
      [ast_expr]
  in
(*
  Format.printf 
    "@[<hv>%a@ %a@]@."
    A.pp_print_expr ast_expr
    (pp_print_list 
       (fun ppf (i, e) ->
          Format.fprintf
            ppf
            "@[<hv>%a: %a@]"
            (I.pp_print_index false) i
            (E.pp_print_lustre_expr false) e)
       ",@ ")
    (List.rev expr');
*)
  (* Assertion to ensure list is sorted by indexes *)
  (match List.rev expr' with 
    | (h, _) :: tl -> 
      ignore 
        (List.fold_left 
           (fun a (i, _) -> assert ((I.compare_index i a) > 0); i)
           h
           tl)
    | _ -> ());

  (* Expression must be sorted by their indexes *)
  (List.rev expr', abstractions')


and eval_node_call
    ({ nodes } as context)
    ({ mk_new_state_var; 
       mk_state_var_for_expr; 
       mk_new_oracle; 
       mk_new_observer_state_var } as abstractions)
    pos
    cond
    ident
    args
    defaults
    result
    tl = 

  (* Type check expressions for node inputs and return sorted list of
     expressions for node inputs *)
  let node_inputs_of_exprs node_inputs abstractions pos expr_list =

    try

      (* Check types and index, keep lists sorted *)
      List.fold_right2
        (fun 
          (in_var, index)
          (_, ({ E.expr_type } as expr)) 
          (accum, ({ new_vars; mk_state_var_for_expr } as abstractions)) ->

          if

            (* Expression must be of a subtype of input type *)
            Type.check_type 
              expr_type
              (StateVar.type_of_state_var in_var) 

          then 

            (* New variable for abstraction, is constant if input is *)
            let state_var, new_vars' = 
              mk_state_var_for_expr
                (StateVar.is_const in_var)
                abstractions.new_vars
                expr 
            in

            E.set_state_var_instance state_var pos ident in_var ;

            E.set_state_var_source state_var E.Abstract ;

            (* Add definition of variable *)
            let abstractions' =
              { abstractions with new_vars = new_vars' }
            in

            (* Add expression as input *)
            (state_var :: accum, abstractions')

          else
            raise E.Type_mismatch)
        node_inputs
        expr_list
        ([], abstractions)

    (* Type checking error or one expression has more indexes *)
    with Invalid_argument "List.fold_right2" | E.Type_mismatch -> 

      fail_at_position pos "Type mismatch for expressions"

  in

  let

    { N.inputs = node_inputs; 
      N.oracles = node_oracles;
      N.outputs = node_outputs; 
      N.observers = node_observers;
      N.props = node_props } = 

    try 

      (* Get node context by identifier *)
      List.find
        (function { N.name = node_ident } -> node_ident = ident)
        nodes

    with Not_found -> 

      (* Node may be forward referenced *)
      raise (Node_not_found (ident, pos))

  in

  debug lustreSimplify
      "@[<hv>Node call at %a:@ properties @[<hv>%a@]@ observers @[<hv>%a@]@]"
      pp_print_position pos
      (pp_print_list StateVar.pp_print_state_var ",@ ")
      (List.map fst node_props)
      (pp_print_list StateVar.pp_print_state_var ",@ ")
      node_observers
  in


  if

    (* Node call has activation condition  *)
    not (E.equal_expr cond E.t_true)

  then 

    (

      (* Number of defaults must match number of outputs *)
      if (List.length node_outputs <> List.length defaults) then 

        fail_at_position 
          pos
          "Number of default arguments does not match number of outputs"

      else

        List.iter2 
          (fun (sv, i) (j, { E.expr_type = t }) -> 

             if 

               (* Types must match *)
               not (Type.check_type t (StateVar.type_of_state_var sv)) 

             then

               fail_at_position 
                 pos
                 "Type mismatch in default arguments with outputs")

          node_outputs
          defaults

    );

  (* Evaluate inputs as list of expressions *)
  let expr_list', abstractions' = 
    eval_ast_expr
      context 
      abstractions
      (A.ExprList (pos, args))
  in

  (* Type check and flatten indexed expressions for input into list
         without indexes *)
  let node_input_state_vars, abstractions' =
    node_inputs_of_exprs node_inputs abstractions' pos expr_list'
  in

  (* State variable for activation condition *)
  let cond_state_var, abstractions' = 

    if 
    
      (* Node call has activation condition  *)
      E.equal_expr cond E.t_true
        
    then
      
      (* No state variable and context is unchanged *)
      None, abstractions'

    else

      (* New variable for activation condition *)
      let state_var, new_vars' = 
        mk_state_var_for_expr
          false
          abstractions'.new_vars
          cond
      in

      E.set_state_var_source state_var E.Abstract ;
      
      (* Add definition of variable *)
      let abstractions' =
        { abstractions' with new_vars = new_vars' }
      in

      (* Return state variable and changed context *)
      Some state_var, abstractions'

  in

  try 

    (* Find a call to the same node on the same clock with the same
       inputs in this node *)
    let node_call = 
      List.find
        (fun { N.call_clock = cond';
               N.call_defaults = defaults';
               N.call_node_name = ident';
               N.call_inputs = inputs';
               N.call_returns = node_outputs } -> 

          (* Call to the same node *)
          (I.equal ident ident') &&

          (match cond_state_var, cond' with 

            | Some v, Some v' -> 

              (* Same activation condition *)
              StateVar.equal_state_vars v v' &&

              (* Same defaults *)
              (List.for_all2
                 (fun (_, sv1) sv2 -> E.equal_expr sv1 sv2)
                 defaults 
                 defaults')

            (* No activation condtion *)
            | None, None -> true

            | _ -> false) &&

          (* Inputs are the same up to oracles *)
          (let rec aux = 
            function 
              | [] -> (function _ -> true)
              | h :: tl -> 
                (function
                  | [] -> false
                  | h' :: tl' -> 
                    if StateVar.equal_state_vars h h' then 
                      aux tl tl'
                    else
                      false)
           in
           aux node_input_state_vars inputs'))
        abstractions'.new_calls
    in

    let result' = 
      List.fold_left2
        (fun result sv (_, index) -> 
           (index, E.mk_var sv E.base_clock) :: result)
        result
        node_call.N.call_returns
        node_outputs
    in

    (* Add expression to result *)
    eval_ast_expr' 
      context 
      abstractions' 
      result' 
      tl

  with Not_found -> 

    (* Fresh state variables for oracle inputs of called node *)
    let oracle_state_vars = 
      List.map 
        (fun node_sv ->
           let sv = mk_new_oracle (StateVar.type_of_state_var node_sv) in
           E.set_state_var_instance sv pos ident node_sv;
           sv)
        node_oracles 
    in

    (* Fresh state variables for observer outputs of called node *)
    let observer_state_vars = 
      List.map 
        (fun node_sv -> 
           let sv = 
             mk_new_observer_state_var (StateVar.type_of_state_var node_sv) 
           in
           E.set_state_var_instance sv pos ident node_sv;
           sv)
        node_observers
    in


    let result', output_vars = 
      List.fold_left
        (fun (result, output_vars) (node_sv, index) -> 

           let sv = 
             mk_new_state_var false (StateVar.type_of_state_var node_sv)
           in

           E.set_state_var_instance sv pos ident node_sv;
           (index, E.mk_var sv E.base_clock) :: result, 
           sv :: output_vars)

        (result, [])
        node_outputs
    in

    (* Add expression to result *)
    eval_ast_expr' 
      context 
      { abstractions' 
        with new_calls = { N.call_returns = (List.rev output_vars);
                           N.call_observers = observer_state_vars;
                           N.call_clock = cond_state_var;
                           N.call_node_name = ident;
                           N.call_pos = pos;
                           N.call_inputs = 
                             node_input_state_vars @ oracle_state_vars;
                           N.call_defaults = List.map snd defaults } 
                         :: abstractions'.new_calls;
             new_oracles = abstractions'.new_oracles @ oracle_state_vars;
             new_observers = abstractions'.new_observers @ observer_state_vars }
      result' 
      tl


(* Evaluate expression to an integer constant *)
and int_const_of_ast_expr context pos expr = 

  match 

    (* Evaluate expression *)
    eval_ast_expr 
      context
      (void_abstraction_context pos)
      expr 

  with

    (* Expression must evaluate to a singleton list of an integer
       expression without index and without new definitions *)
    | ([ index, { E.expr_init = ei; 
                  E.expr_step = es } ],
       { new_vars = []; 
         new_calls = []; 
         new_oracles = []; 
         new_observers = [] }) when 
        index = I.empty_index && 
        let ei' = (ei :> Term.t) in let es' = (es :> Term.t) in 
        Term.equal ei' es' -> 

      (* Get term for initial value of expression, is equal to step *)
      let ti = E.base_term_of_expr E.base_offset ei in

      (if Term.is_numeral ti then

         Term.numeral_of_term ti

       else

         fail_at_position pos "Expression must be an integer")

    (* Expression is not a constant integer *)
    | _ ->       

      fail_at_position pos "Expression must be constant"


(* Evaluate expression to an integer constant *)
and bool_expr_of_ast_expr
    context 
    abstractions
    pos
    ast_expr = 

  (* Evaluate expression *)
  let expr', abstractions' = 
    eval_ast_expr 
      context 
      abstractions
      ast_expr 
  in

  (* Check evaluated expression *)
  (match expr' with 

    (* Boolean expression without indexes *)
    | [ index, 
        ({ E.expr_init; 
           E.expr_step; 
           E.expr_type = t } as expr) ] when 
        index = I.empty_index && Type.equal_types t Type.t_bool -> 

      expr, abstractions'

    (* Expression is not Boolean or is indexed *)
    | _ -> 

      fail_at_position pos "Expression is not of Boolean type") 
  

(* Return true if expression is Boolean without indexes *)
let is_bool_expr = function

  | [ index, 
      ({ E.expr_type = t }) ] when 
      index = I.empty_index && Type.equal_types t Type.t_bool -> true

  | _ -> false
    


(* Replace unguarded pres in expression with oracle constants and
   return extened abstraction *)
let close_ast_expr pos (expr, abstractions) = 
  
  (* Replace unguarded pres in expression with oracle constants *)
  let expr', oracles' =
    E.oracles_for_unguarded_pres
      pos
      abstractions.mk_new_oracle_for_state_var
      warn_at_position
      abstractions.new_oracles
      expr
  in
  
  (* Add oracle constants to abstraction *)
  let abstractions' = 
    { abstractions with new_oracles = oracles' } 
  in
  
  (* Return expression and modified abstraction *)
  (expr', abstractions') 
   

let close_indexed_ast_expr pos (expr, abstractions) = 
      
  (* Replace unguarded pres with oracle constants *)
  let expr', abstractions' = 
    List.fold_right 

      (fun (index, expr) (accum, abstractions) -> 

         let expr', abstractions' = 
           close_ast_expr pos (expr, abstractions) 
         in

         (* Return expression and modified abstraction *)
         ((index, expr') :: accum, abstractions'))

      expr
      ([], abstractions)
  in

  (expr', abstractions')



(* ******************************************************************** *)
(* Type declarations                                                    *)
(* ******************************************************************** *)


(* Return true if type [t] has been declared in the context *)
let type_in_context { basic_types; indexed_types; free_types } t = 

  (* Check if [t] is a basic types *)
  (List.mem_assoc t basic_types) ||

  (* Check is [t] is an indexed type *)
  (List.mem_assoc t indexed_types) || 

  (* Check if [t] is a free type *)
  (List.mem t free_types) 


(* Return true if identifier [i] has been declared, raise an
   exception if the identifier is reserved. *)
let ident_in_context { type_ctx; index_ctx } i = 

  if 

    (* Identifier must not be reserved *)
    I.ident_is_reserved i

  then
    
    raise 
      (Invalid_argument 
         (Format.asprintf 
            "Identifier %a is reserved internal use" 
            (I.pp_print_ident false) i))

  else

    (* In type context or a nested identifier *)
    (List.mem_assoc i type_ctx) || (List.mem_assoc i index_ctx)



(* Add enum constants to context if type is an enumeration *)
let add_enum_to_context type_ctx pos = function

  (* Type is an enumeration *)
  | t as basic_type when Type.is_scalar t -> 

    List.fold_left
      (fun type_ctx scalar_element -> 

         let enum_element = I.mk_string_ident scalar_element in

         try 

           (* Get type of constant *)
           let enum_element_type = List.assoc enum_element type_ctx in 

           (* Skip if constant declared with the same (enum) type *)
           if basic_type = enum_element_type then type_ctx else

             fail_at_position 
               pos 
               (Format.asprintf 
                  "Enum constant %a declared with different type" 
                  (I.pp_print_ident false) enum_element);

           (* Constant not declared *)
         with Not_found -> 
           
           (* Push constant to typing context *)
           (enum_element, basic_type) :: type_ctx)
      type_ctx
      (Type.elements_of_scalar t)

  (* Other basic types do not change typing context *)
  | _ -> type_ctx



(* For an identifier t = t.i1...in associate each proper prefix with
   suffix and the given value v: add (t, (i1...in, v)), ...,
   (t.i1..in-1, (in, v)) to the map. Do not add the empty suffix, that
   is, (t.i1..in-1, ([], v)).

*)
let add_to_prefix_map map ident value =

  let rec aux prefix map = function 

    (* Do not add full index to list *)
    | [] -> map

    (* [index] is second to last or earlier *)
    | index :: tl as suffix -> 

      (* Add association of suffix and type to prefix *)
      let rec aux2 accum = function

        (* Prefix of identifier not found *)
        | [] -> 

          (* Add association of prefix with suffix and value *)
          (prefix, [(I.index_of_one_index_list suffix, value)]) :: accum

        (* Prefix of identifier found *)
        | (p, l) :: tl when p = prefix -> 

          (* Add association of prefix with suffix and type, and
             finish *)
          List.rev_append
            ((p, 
              sort_indexed_pairs
                ((I.index_of_one_index_list suffix, value) :: l)) 
             :: tl) 
            accum

        (* Recurse to keep searching for prefix of identifier *)
        | h :: tl -> aux2 (h :: accum) tl

      in

      (* Add index to prefix *)
      let prefix' = I.push_one_index index prefix in

      (* Recurse for remaining suffix *)
      aux prefix' (aux2 [] map) tl

  in

  (* Get indexes of identifier of type *)
  let (ident_base, suffix) = I.split_ident ident in

  (* Add types of all suffixes *)
  aux ident_base map suffix



(* Add type declaration for an alias type to a context

   Associate possibly indexed identifier with its Lustre type;
   associate all prefixes of an indexed identifier with its suffixes
   and their basic types; and for enum type associate the enum type to
   each constant.
*)
let add_alias_type_decl 
    ident
    pos
    ({ basic_types; indexed_types; type_ctx } as context) 
    index 
    basic_type =
(*
  Format.printf 
    "add_alias_type_decl %a %a %a@." 
    (I.pp_print_ident false) ident
    (I.pp_print_index false) index
    (T.pp_print_lustre_type false) basic_type;
*)
  (* Add index to identifier *)
  let indexed_ident = I.push_index index ident in

  (* Add alias for basic type *)
  let basic_types' = (indexed_ident, basic_type) :: basic_types in

  (* Add types of all suffixes *)
  let indexed_types' = 
    add_to_prefix_map indexed_types indexed_ident basic_type
  in

  (* Add enum constants to type context if type is an enumeration *)
  let type_ctx' = add_enum_to_context type_ctx pos basic_type in

  (* Changes to context *)
  { context with 
      basic_types = basic_types'; 
      indexed_types = indexed_types';
      type_ctx = type_ctx' }
  


(* Expand a possibly nested type expression to indexed basic types and
   apply [f] to each

   The context of the unfolding cannot be modified by f, this is a
   good thing and disallows defining types recursively. Indexes are
   presented to f in ascending order. *)
let rec fold_ast_type' 
    fold_left
    ({ basic_types; 
       indexed_types; 
       free_types; 
       type_ctx; 
       index_ctx; 
       consts } as context)
    f 
    accum = function 

  (* All types seen *)
  | [] -> accum 

  (* Basic type Boolean *)
  | (index, A.Bool pos) :: tl -> 

    fold_ast_type' fold_left context f (f accum index Type.t_bool) tl

  (* Basic type i *)
  | (index, A.Int pos) :: tl -> 

    fold_ast_type' fold_left context f (f accum index Type.t_int) tl

  (* Basic type real *)
  | (index, A.Real pos) :: tl -> 

    fold_ast_type' fold_left context f (f accum index Type.t_real) tl

  (* Integer range type needs to be constructed from evaluated
     expressions for bounds *)
  | (index, A.IntRange (pos, lbound, ubound)) :: tl -> 

    (* Evaluate expressions for bounds to constants *)
    let const_lbound, const_ubound = 
      (int_const_of_ast_expr context pos lbound, 
       int_const_of_ast_expr context pos ubound) 
    in

    (* Construct an integer range type *)
    fold_ast_type' 
      fold_left 
      context 
      f 
      (f accum index (Type.mk_int_range const_lbound const_ubound)) 
      tl

  (* Enum type needs to be constructed *)
  | (index, A.EnumType (pos, enum_elements)) :: tl -> 

    fail_at_position pos "Enum types not supported" 

(* TODO: support enum types

    (* Construct an enum type *)
    fold_ast_type' 
      fold_left 
      context 
      f
      (f 
         accum
         index
         (Type.mk_scalar 
            "TODO" 
            (List.map (I.string_of_ident false) enum_elements))) 
      tl
*)

  (* User type that is an alias *)
  | (index, A.UserType (pos, ident)) :: tl when 
      List.mem_assoc ident basic_types -> 

    (* Substitute basic type *)
    fold_ast_type' 
      fold_left 
      context 
      f 
      (f accum index (List.assoc ident basic_types)) 
      tl


  (* User type that is an alias for an indexed type *)
  | (index, A.UserType (pos, ident)) :: tl when 
      List.mem_assoc ident indexed_types -> 

    (* Apply f to basic types with index *)
    let accum' = 
      if fold_left then
        List.fold_left
          (fun a (j, s) -> f a (I.push_index_to_index index j) s)
          accum
          (List.assoc ident indexed_types)
      else
        List.fold_right
          (fun (j, s) a -> f a (I.push_index_to_index index j) s)
          (List.assoc ident indexed_types)
          accum
    in

    (* Recurse for tail of list *)
    fold_ast_type' fold_left context f accum' tl

(*
  (* User type that is a free type *)
  | (index, A.UserType ident) :: tl when 
      List.mem ident free_types -> 

    (* Substitute free type *)
    fold_ast_type' 
      fold_left 
      context 
      f 
      (f accum index (T.mk_free_type ident)) 
      tl
*)

  (* User type that is neither an alias nor free *)
  | (index, A.UserType (pos, ident)) :: _ -> 

    fail_at_position 
      pos
      (Format.asprintf 
         "Type %a is not declared" 
         (I.pp_print_ident false) ident)


  (* Record type *)
  | (index, A.RecordType (pos, record_fields)) :: tl -> 

    (* Substitute with indexed types of fields *)
    fold_ast_type' 
      fold_left 
      context 
      f 
      accum 
      (List.fold_left
         (fun a (j, s) -> 
            (I.push_index_to_index index (I.index_of_ident j), s) :: a)
         tl
         (if fold_left then
            List.sort (fun (i, _) (j, _) -> I.compare j i) record_fields
          else
            List.sort (fun (i, _) (j, _) -> I.compare i j) record_fields))


  (* Tuple type *)
  | (index, A.TupleType (pos, tuple_fields)) :: tl -> 

    (* Substitute with indexed types of elements *)
    fold_ast_type' 
      fold_left 
      context 
      f 
      accum 
      (fst
         (if fold_left then
            List.fold_right
              (fun s (a, j) -> 
                 (I.push_index_to_index index (I.mk_int_index j), s) :: a, 
                 Numeral.(pred j))
              tuple_fields
              (tl, Numeral.((of_int (List.length tuple_fields) - one)))
          else
            List.fold_left
              (fun (a, j) s -> 
                 (I.push_index_to_index index (I.mk_int_index j), s) :: a, 
                 Numeral.(succ j))
              (tl, Numeral.zero)
              tuple_fields))


  (* Array type *)
  | (index, A.ArrayType (pos, (type_expr, size_expr))) :: tl -> 

    (* Evaluate size of array to a constant integer *)
    let array_size = int_const_of_ast_expr context pos size_expr in

    (* Array size must must be at least one *)
    if Numeral.(array_size <= zero) then 

      fail_at_position 
        pos
        (Format.asprintf 
           "Expression %a must be positive as array size" 
           A.pp_print_expr size_expr);

    (* Append indexed types *)
    let rec aux_left accum = function
      | j when Numeral.(j < zero) -> accum
      | j -> 

        aux_left 
          ((I.push_index_to_index index (I.mk_int_index j), 
            type_expr) :: 
             accum)
          Numeral.(pred j)

    in

    (* Append indexed types *)
    let rec aux_right accum array_size = function
      | j when Numeral.(j >= array_size) -> accum
      | j -> 

        aux_right 
          ((I.push_index_to_index index (I.mk_int_index j), 
            type_expr) :: 
             accum)
          array_size
          Numeral.(succ j)

    in

    (* Substitute with indexed types of elements *)
    fold_ast_type' 
      fold_left
      context 
      f 
      accum 
      (if fold_left then 
         aux_left tl (Numeral.pred array_size)
       else
         aux_right tl array_size Numeral.zero)


(* Wrapper for folding function over type expression  *)
let fold_left_ast_type context f accum t = 
  fold_ast_type' true context f accum [(I.empty_index, t)] 

let fold_right_ast_type context f accum t = 
  fold_ast_type' false context f accum [(I.empty_index, t)] 


(* ******************************************************************** *)
(* Constant declarations                                                *)
(* ******************************************************************** *)


(* Add a typed or untyped constant declaration to the context *)
let add_typed_decl
    ident 
    ({ basic_types; 
       indexed_types; 
       free_types; 
       type_ctx; 
       index_ctx; 
       consts } as context) 
    pos
    expr 
    type_expr =

  try 

    (* Evaluate expression, must not generate new abstractions from
       node calls *)
    let expr_val, abstractions = 
      eval_ast_expr 
        context 
        (void_abstraction_context pos)
        expr 
    in

    (match type_expr with 

      (* No type given *)
      | None -> ()

      (* Check if type of expression matches given type *)
      | Some t -> 

        fold_left_ast_type 
          context
          (fun () type_index def_type ->
             let { E.expr_type } = 
               try 
                 List.assoc type_index expr_val 
               with Not_found -> 
                 raise E.Type_mismatch 
             in
             if 
               Type.check_type expr_type def_type
             then
               () 
             else 
               raise E.Type_mismatch)
          ()
          t

    );

    (* Add association of identifiers to values *)
    let consts' = 
      List.fold_left
        (fun a (j, e) -> (I.push_index j ident, e) :: a)
        consts
        expr_val
    in

    (* Add association of identifiers to types *)
    let type_ctx' = 
      List.fold_left
        (fun a (j, { E.expr_type = t }) ->
           (I.push_index j ident, t) :: a)
        type_ctx
        expr_val
    in

    (* Add associations of identifiers to indexes *)
    let index_ctx' = 
      List.fold_left
        (fun a (j, _) -> 
           add_to_prefix_map a (I.push_index j ident) ())
        index_ctx
        expr_val
    in

    { context with 
        consts = consts';
        type_ctx = type_ctx';
        index_ctx = index_ctx' }

  with E.Type_mismatch -> 

    fail_at_position pos "Type mismatch for expressions"


(* Add declaration of constant to context *)
let add_const_decl context = function 

  (* Free constant *)
  | A.FreeConst (pos, ident, _) -> 

    fail_at_position pos "Free constants not supported"


  (* Constant without type *)
  | A.UntypedConst (pos, ident, expr) -> 
    add_typed_decl ident context pos expr None

  (* Constant with given type *)
  | A.TypedConst (pos, ident, expr, type_expr) -> 
    add_typed_decl ident context pos expr (Some type_expr)
  

(* ******************************************************************** *)
(* Node declarations                                                    *)
(* ******************************************************************** *)


(* Add declaration of a node input to contexts *)
let add_node_input_decl
    ident
    pos
    is_const
    (({ type_ctx; index_ctx } as context), 
     ({ N.inputs = node_inputs; N.name = node_ident } as node))
    index 
    basic_type =

(*
  Format.printf "add_node_input_decl: %a %a %a@."
    (I.pp_print_ident false) ident
    (I.pp_print_index false) index
    Type.pp_print_type basic_type;
*)

  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Add index to identifier *)
  let ident' = I.push_index index ident in

  (* Add to typing context *)
  let type_ctx' = 
    (ident', basic_type) :: 
      (add_enum_to_context type_ctx pos basic_type) 
  in

  (* Add indexed identifier to context *)
  let index_ctx' = add_to_prefix_map index_ctx ident' () in

  (* Create state variable as input and contant *)
  let state_var = 
    E.mk_state_var_of_ident
      ~is_input:true
      ~is_const:is_const
      scope
      (I.push_back_index index ident) 
      basic_type
  in

  (* State variable is an input *)
  E.set_state_var_source state_var E.Input;

  (* Add state variable to inputs *)
  let node_inputs' = (state_var, index) :: node_inputs in
  
  ({ context with type_ctx = type_ctx'; index_ctx = index_ctx' }, 
   { node with N.inputs = node_inputs' })


(* Add declaration of a node output to contexts *)
let add_node_output_decl
    ident
    param_index
    pos
    (({ type_ctx; index_ctx } as context), 
     ({ N.outputs = node_outputs; N.name = node_ident } as node))
    index 
    basic_type =
(*
  Format.printf "add_node_output_decl: %a %a %a %a@."
    (I.pp_print_ident false) ident
    (function ppf -> function 
       | None -> Format.fprintf ppf "[]"
       | Some i -> Format.fprintf ppf "%a" Numeral.pp_print_numeral i)
    param_index
    (I.pp_print_index false) index
    Type.pp_print_type basic_type;
*)
  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Add index to identifier *)
  let index' = 
    match param_index with 
      | None -> index
      | Some i -> I.push_int_index_to_index i index
  in

  let ident' = I.push_index index ident in

  (* Add to typing context *)
  let type_ctx' = 
    (ident', basic_type) :: 
      (add_enum_to_context type_ctx pos basic_type) 
  in
  
  (* Add indexed identifier to context *)
  let index_ctx' = add_to_prefix_map index_ctx ident' () in

  (* Create state variable as neither constant nor input *)
  let state_var = 
    E.mk_state_var_of_ident
      ~is_input:false
      ~is_const:false
      scope
      (I.push_back_index index ident)
      basic_type
  in

  (* State variable is an output *)
  E.set_state_var_source state_var E.Output;

  (* Add state variable to outputs *)
  let node_outputs' = (state_var, index') :: node_outputs in

  ({ context with type_ctx = type_ctx'; index_ctx = index_ctx' }, 
   { node with N.outputs = node_outputs' })


(* Add declaration of a node local variable or constant to contexts *)
let add_node_var_decl
    ident
    pos
    (({ type_ctx; index_ctx } as context), 
     ({ N.name = node_ident} as node))
    index 
    basic_type =
(*
  Format.printf "add_node_var_decl: %a %a %a@."
    (I.pp_print_ident false) ident
    (I.pp_print_index false) index
    (E.pp_print_lustre_type false) basic_type;
*)

  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Add index to identifier *)
  let ident' = I.push_index index ident in

  (* Add to typing context *)
  let type_ctx' = 
    (ident', basic_type) :: 
      (add_enum_to_context type_ctx pos basic_type) 
  in

  (* Add indexed identifier to context *)
  let index_ctx' = add_to_prefix_map index_ctx ident' () in

  (* Create state variable as neither constant nor input *)
  let state_var = 
    E.mk_state_var_of_ident
      ~is_input:false
      ~is_const:false
      scope
      (I.push_back_index index ident) 
      basic_type
  in

  (* State variable is locally defined or abstract variable *)
  E.set_state_var_source 
    state_var 
    (if is_dummy_pos pos then E.Abstract else E.Local);

  (* Add state variable to local variables *)
  let node_locals' = (state_var, index) :: node.N.locals in

  (* Must return node in accumulator *)
  ({ context with type_ctx = type_ctx'; index_ctx = index_ctx' }, 
   { node with N.locals = node_locals'})


(* Add declaration of an oracle input to contexts *)
let add_node_oracle_decl
    ident
    (({ type_ctx; index_ctx } as context), 
     ({ N.oracles = node_oracles; N.name = node_ident } as node))
    index 
    state_var =

  (* Oracles are re-used, check if declaration already added *)
  if List.exists (StateVar.equal_state_vars state_var) node_oracles then

    (* Return context and node unchanged *)
    (context, node)

  else 

    (* Node name is scope for naming of variables *)
    let scope = I.index_of_ident node_ident in 

    (* Add index to identifier *)
    let ident' = I.push_index index ident in

    (* Type of state variable *)
    let basic_type = StateVar.type_of_state_var state_var in

    (* Add to typing context *)
    let type_ctx' = 
      (ident', basic_type) :: 
      (add_enum_to_context type_ctx dummy_pos basic_type) 
    in

    (* Add indexed identifier to context *)
    let index_ctx' = add_to_prefix_map index_ctx ident' () in

    (* Create state variable as constant and input *)
    let state_var =
      E.mk_state_var_of_ident
        ~is_input:true
        ~is_const:true
        scope
        (I.push_back_index index ident)
        basic_type
    in

    (* State variable is an oracle input variable *)
    E.set_state_var_source state_var E.Oracle;

    (* Add state variable to oracles *)
    let node_oracles' = state_var :: node_oracles in

    ({ context with type_ctx = type_ctx'; index_ctx = index_ctx' }, 
     { node with N.oracles = node_oracles' })


(* Add declaration of an oracle output to contexts *)
let add_node_observer_decl
    ident
    (({ type_ctx; index_ctx } as context), 
     ({ N.props = node_props;
        N.observers = node_observers; 
        N.name = node_ident } as node))
    index 
    state_var =

  debug lustreSimplify
    "Adding declaration of observer %a to %a"
    StateVar.pp_print_state_var state_var
    (I.pp_print_ident false) node_ident
  in

  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Add index to identifier *)
  let ident' = I.push_index index ident in

  let basic_type = StateVar.type_of_state_var state_var in

  (* Add to typing context *)
  let type_ctx' = 
    (ident', basic_type) :: 
      (add_enum_to_context type_ctx dummy_pos basic_type) 
  in

  (* Add indexed identifier to context *)
  let index_ctx' = add_to_prefix_map index_ctx ident' () in

  (* Create state variable as constant and input *)
  let state_var =
    E.mk_state_var_of_ident
      ~is_input:false
      ~is_const:false
      scope
      (I.push_back_index index ident)
      basic_type
  in
  
  (* State variable is an oracle input variable *)
  E.set_state_var_source state_var E.Observer;

  (* Add state variable to observers *)
  let node_observers' = state_var :: node_observers in

  ({ context with type_ctx = type_ctx'; index_ctx = index_ctx' }, 
   { node with N.observers = node_observers' })


(* Add all node inputs to contexts *)
let rec parse_node_inputs context node = function

  (* All inputs parsed, return in original order *)
  | [] -> (context, { node with N.inputs = List.rev node.N.inputs })


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
  | (pos, ident, var_type, A.ClockTrue, is_const) :: tl -> 

    (* Add declaration of possibly indexed type to contexts *)
    let context', node' = 
      fold_left_ast_type 
        context
        (add_node_input_decl ident pos is_const)
        (context, node)
        var_type
    in

    (* Continue with following inputs *)
    parse_node_inputs context' node' tl

  | (pos, _, _, _, _) :: _ -> 

    fail_at_position pos "Clocked node inputs not supported"


(* Add all node outputs to contexts *)
let rec parse_node_outputs context node index = function

  (* All outputs parsed, return in original order *)
  | [] -> (context, { node with N.outputs = List.rev node.N.outputs })


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
  | (pos, ident, var_type, A.ClockTrue) :: tl -> 

    (* Add declaration of possibly indexed type to contexts *)
    let context', node' = 
      fold_left_ast_type 
        context
        (add_node_output_decl ident index pos)
        (context, node)
        var_type
    in

    (* Increment counter of parameter position *)
    let index' = 
      match index with
        | None -> None 
        | Some i -> Some (Numeral.succ i)
    in

    (* Continue with following outputs *)
    parse_node_outputs context' node' index' tl

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

    (* Add declaration of possibly indexed type to contexts *)
    let context', node' = 
      fold_right_ast_type 
        context
        (add_node_var_decl ident pos)
        (context, node)
        var_type
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
    context
    node
    ({ mk_state_var_for_expr; new_vars } as abstractions)
    pos
    source
    expr =

  (* State variable for property and changed environment *)
  let state_var, context', node', abstractions' =

    if 

      (* Property is a state variable at current offset? *)
      E.is_var expr

    then 

      (* State variable of expression *)
      let state_var = E.state_var_of_expr expr in

      (* No abstraction necessary *)
      (state_var, context, node, abstractions)

    else

      (* State variable of abstraction variable *)
      let state_var, new_vars' = 
        mk_state_var_for_expr 
          false
          new_vars
          expr 
      in

      (* State variable is a locally abstracted variable *)
      E.set_state_var_source state_var E.Abstract;

      (* Add definition of abstraction variable to node *)
      let context', node', abstractions' = 
        equation_to_node
          context
          node
          abstractions
          dummy_pos  
          (state_var, expr)
      in

      (* Property is new state variable *)
      (state_var, 
       context', 
       node', 
       { abstractions' with new_vars = new_vars' })

  in

  if 

    (* Skip if property already in node *)
    List.exists
      (fun (sv, _) -> StateVar.equal_state_vars state_var sv)
      node.N.props 

  then

    (* Add property to node *)
    (context, node, abstractions)

  else

    (* Add declaration of variable to observers if not already an
       output *)
    let node_observers' = 
      node'.N.observers @
      (if 
        List.exists
          (fun (sv, _) -> StateVar.equal_state_vars sv state_var)
          node'.N.outputs
       then
         []
       else
         [state_var])
    in

    (* Remove declaration of variable from locals *)
    let node_locals' = 
      List.filter
        (fun (sv, _) -> not (StateVar.equal_state_vars sv state_var))
        node'.N.locals
    in

    (* Add property to node *)
    (context', 
     { node' with 
         N.props = (state_var, source) :: node'.N.props; 
         N.observers = node_observers';
         N.locals = node_locals' },
     abstractions')


(* Add an expression as an assertion *)
and assertion_to_node context node abstractions pos expr = 

  let node' = { node with N.asserts = expr :: node.N.asserts } in

  (context, node', abstractions)


(* Add an expression as a contact clause *)
and requires_to_node context node abstractions pos expr =

  let node' = { node with N.requires = expr :: node.N.requires } in

  (context, node', abstractions)


(* Add an expression as a contact clause *)
and ensures_to_node context node abstractions pos expr =

  let node' = { node with N.ensures = expr :: node.N.ensures } in

  (context, node', abstractions)


(* Add equational definition of a variable *)
and equation_to_node 
    context 
    node 
    abstractions
    pos
    (state_var, ({ E.expr_type } as expr)) = 

  (* Replace unguarded pre with oracle constants *)
  let expr', oracles' = 
    E.oracles_for_unguarded_pres
      pos
      abstractions.mk_new_oracle_for_state_var
      warn_at_position
      abstractions.new_oracles
      expr
  in

  (* Type of state variable defined by expression *)
  let state_var_type = StateVar.type_of_state_var state_var in 

  (* Node with property added if subtyping cannot be inferred *)
  let context', node', abstractions' =

    if 

      (* Type must be a subtype of declared type *)
      Type.check_type expr_type state_var_type 

    then

      (* Nothing to add *)
      context, node, abstractions

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
            context 
            node
            abstractions 
            dummy_pos 
            (TermLib.Generated [state_var])
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
  (context',
   { node' with N.equations = (state_var, expr') :: node'.N.equations }, 
   abstractions')


(* Add abstracted variables and node calls to context *)
let abstractions_to_context_and_node 
    context 
    node
    ({ new_vars } as abstractions)
    pos =

  (* Add declaration of variables to context

     Must add variables first, this may generate new abstractions from
     unguarded pres. *)
  let context', node', ({ new_oracles } as abstractions') = 

    List.fold_left 
      (fun (context, node, abstractions) (state_var, expr) -> 

         (* Split scope from name of variable *)
         let (base_ident, index) = 
           I.split_ident (fst (E.ident_of_state_var state_var))
         in

         (* Add variable declaration to context *)
         let context', node' = 
           add_node_var_decl 
             base_ident
             dummy_pos
             (context, node)
             (I.index_of_one_index_list index)
             (StateVar.type_of_state_var state_var)
         in

         (* Add equation to node *)
         let context', node', abstractions' = 
           equation_to_node context' node' abstractions pos (state_var, expr) 
         in

         (context', node', abstractions'))

      (context, node, abstractions)
      new_vars

  in

  (* Add declaration of oracle inputs to context *)
  let context', node', ({ new_calls } as abstractions') = 

    List.fold_left 
      (fun (context, node, abstractions) (state_var) -> 

         (* Split scope from name of variable *)
         let (base_ident, index) = 
           I.split_ident (fst (E.ident_of_state_var state_var))
         in

         (* Add variable declaration to context and oracle input to node *)
         let context', node' = 
           add_node_oracle_decl 
             base_ident
             (context, node)
             (I.index_of_one_index_list index)
             state_var
         in

         (context', node', abstractions))

      (context', node', abstractions')
      new_oracles

  in

  (* Add declaration of return variables of calls to context

     No need to iterate over observers, they will become observers of
     the calling node *)
  let context', node', ({ new_observers } as abstractions') = 

    List.fold_left
      (fun 
        accum
        ({ N.call_returns = outputs;
           N.call_observers = observers;
           N.call_node_name = node_call_ident } as call) ->

         let context', node', abstractions' = 
           List.fold_left 
             (fun (context, node, abstractions) state_var -> 
                
                (* Split scope from name of variable *)
                let (base_ident, index) = 
                  I.split_ident (fst (E.ident_of_state_var state_var))
                in
                
                (* Add variable declaration to context *)
                let context', node' = 

                  if 

                    (* Variable is already declared as output or
                       local? *)
                    (List.exists 
                       (fun (sv, _) -> 
                          StateVar.equal_state_vars sv state_var)
                       node.N.outputs)

                    || (List.exists 
                          (fun (sv, _) -> 
                             StateVar.equal_state_vars sv state_var)
                          node.N.locals)

                  then

                    (* Return context and node unchanged *)
                    (context, node)

                  else

                    (* Add new local variable to node *)
                    add_node_var_decl 
                      base_ident
                      dummy_pos
                      (context, node)
                      (I.index_of_one_index_list index)
                      (StateVar.type_of_state_var state_var)

                in

                context', node', abstractions)
             accum
             outputs
         in 
 
         (context', 
          { node' with N.calls = call :: node'.N.calls }, 
          abstractions'))

      (context', node', abstractions')
      new_calls

  in

  (* Add declaration of observer outputs to context *)
  let context', node', abstractions' = 

    List.fold_left 
      (fun (context, node, abstractions) (state_var) -> 

         (* Split scope from name of variable *)
         let (base_ident, index) = 
           I.split_ident (fst (E.ident_of_state_var state_var))
         in

         (* Add variable declaration to context and oracle input to node *)
         let context', node' = 
           add_node_observer_decl 
             base_ident
             (context, node)
             (I.index_of_one_index_list index)
             state_var
         in

         (context', node', abstractions))

      (context', node', abstractions')
      new_observers

  in

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
let rec parse_node_contract 
    context 
    empty_abstractions
    ({ N.name = node_ident } as node) = 

  function

    (* No more contract clauses *)
    | [] -> node 


    (* Assumption *)
    | A.Requires (pos, expr) :: tl -> 

      (* Evaluate Boolean expression and guard all pre operators *)
      let expr', abstractions = 
        close_ast_expr
          pos
          (bool_expr_of_ast_expr 
             context 
             empty_abstractions
             pos
             expr)
      in

      (* Add assertion to node *)
      let context', node', abstractions' = 
        requires_to_node context node abstractions pos expr'
      in
      
      (* Add new definitions to context *)
      let context', node', abstractions' = 
        abstractions_to_context_and_node context' node' abstractions' pos
      in

      (* Continue with next contract clauses *)
      parse_node_contract 
        context' 
        empty_abstractions
        node'
        tl


    (* Guarantee *)
    | A.Ensures (pos, expr) :: tl -> 

      (* Evaluate Boolean expression and guard all pre operators *)
      let expr', abstractions = 
        close_ast_expr
          pos
          (bool_expr_of_ast_expr 
             context 
             empty_abstractions
             pos
             expr)
      in

      (* Add assertion to node *)
      let context', node', abstractions' = 
        ensures_to_node context node abstractions pos expr'
      in
      
      (* Add new definitions to context *)
      let context', node', abstractions' = 
        abstractions_to_context_and_node context' node' abstractions' pos
      in

      (* Continue with next contract clauses *)
      parse_node_contract 
        context' 
        empty_abstractions
        node'
        tl


(* Return a LustreNode.t from a node LustreAst.node_decl *)
let parse_node  
    node_ident
    global_context
    inputs 
    outputs 
    locals 
    equations 
    contract =

  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Empty node *)
  let node = N.empty_node node_ident in

  (* Create a new state variable for abstractions *)
  let mk_new_state_var is_const state_var_type = 
    E.mk_fresh_state_var
      ~is_input:false
      ~is_const:is_const
      scope
      I.abs_ident
      state_var_type
      node.N.fresh_state_var_index
  in

  (* Create a new state variable for abstractions *)
  let mk_state_var_for_expr is_const new_vars ({ E.expr_type } as expr) =

    try

      (* Find previous definition of expression *)
      let state_var =
        E.ExprHashtbl.find
          node.N.expr_state_var_map
          expr
      in

      (* Return state variable and no new defintiion *)
      (state_var, new_vars)

    with Not_found ->

      (* Create a fresh state variable for definition *)
      let state_var =
        E.mk_fresh_state_var
          ~is_input:false
          ~is_const:is_const
          scope
          I.abs_ident
          expr_type
          node.N.fresh_state_var_index
      in

      (* Record definition of expression by state variable *)
      E.ExprHashtbl.add
        node.N.expr_state_var_map
        expr
        state_var;

      (* Return variable and add definition *)
      (state_var, ((state_var, expr) :: new_vars))

  in

  (* Create a new constant to guard pre operator on state variable *)
  let mk_new_oracle_for_state_var state_var = 

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
  let mk_new_observer_state_var = 
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
      mk_new_state_var = mk_new_state_var;
      mk_state_var_for_expr = mk_state_var_for_expr;
      mk_new_oracle_for_state_var = mk_new_oracle_for_state_var;
      mk_new_oracle = mk_new_oracle;
      mk_new_observer_state_var = mk_new_observer_state_var;
      new_vars = [];
      new_calls = [];
      new_oracles = [];
      new_observers = [] }
  in

  (* Parse inputs, add to global context and node context *)
  let local_context, node = 
    parse_node_inputs global_context node inputs
  in

  (* Parse outputs, add to local context and node context *)
  let local_context, node = 
    parse_node_outputs
      local_context 
      node 
      (match outputs with | [] | [_] -> None | _ -> Some Numeral.zero)
      outputs
  in

  (* Parse contract

     Must check before adding local variable to context, may not use
     local variables *)
  let node = 
    parse_node_contract 
      local_context 
      empty_abstractions
      node 
      contract
  in

  (* Parse local declarations, add to local context and node context *)
  let local_context, node = 
    parse_node_locals local_context node locals
  in

  (* Parse equations and assertions, add to node context, local
     context is not modified *)
  let abstractions', context', node = 
    parse_node_equations 
      local_context 
      empty_abstractions
      node 
      equations
  in

  (* Add new definitions to context *)
  let _, node', _ = 
    abstractions_to_context_and_node context' node abstractions' dummy_pos
  in

  (* Simplify by substituting variables that are aliases *)
  (* N.solve_eqs_node_calls node' *)
  node'


(* ******************************************************************** *)
(* Main                                                                 *)
(* ******************************************************************** *)

(* Iterate over a list of declarations and return a context *)
let rec declarations_to_nodes'
    ({ basic_types; 
       indexed_types; 
       free_types; 
       type_ctx; 
       index_ctx; 
       consts; 
       nodes } as global_context) = 

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
            fold_left_ast_type 
              global_context
              (add_alias_type_decl ident pos) 
              global_context 
              type_expr
          in

          (* Return changed context and unchanged declarations *)
          global_context'

        (* Identifier is a free type *)
        | A.FreeType (_, ident) -> 

          (* Add type identifier to free types *)
          let free_types' = ident :: free_types in

          (* Changes to global context *)
          { global_context with free_types = free_types' }

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
           equations, 
           contract))) :: decls ->

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
            contract
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
              | A.NodeDecl (_, (i, _, _, _, _, _, _)) when i = ident -> true 
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


(* Iterate over the declarations and return the nodes *)
let declarations_to_nodes decls = 

  (* Extract nodes from produced global context *)
  let { nodes } as global_context = 
    declarations_to_nodes' init_lustre_context decls 
  in

  (* Return nodes *)
  nodes


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
