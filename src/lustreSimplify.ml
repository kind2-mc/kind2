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

(* Abbreviations *)
module A = LustreAst
module I = LustreIdent
module E = LustreExpr
module N = LustreNode

module ISet = I.LustreIdentSet

(* Call to a node that is only defined later

   This is just failing at the moment, we'd need some dependency
   analysis to recognize cycles to fully support forward
   referencing. *)
exception Forward_reference of I.t * A.position


(* Identifier for new variables from abstrations *)
let new_var_ident = I.mk_string_ident "__abs" 

(* Identifier for new oracle input *)
let new_oracle_ident = I.mk_string_ident "__nondet" 

(* Identifier for new variables from node calls *)
let new_call_ident = I.mk_string_ident "__returns" 


(* Sort a list of indexed expressions *)
let sort_indexed_pairs list =
  List.sort (fun (i1, _) (i2, _) -> I.compare_index i1 i2) list


(* Raise exception *)
let fail_at_position pos msg = 

  raise 
    (Failure 
       (Format.asprintf 
          "Parsing error in %a: %s" 
          A.pp_print_position pos 
          msg))
  

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
  

(* Initial context *)
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


type abstraction_context = 

  { 

    (* Scope for new identifiers *)
    scope : I.index;

    (* Create a new identifier for a variable *)
    mk_new_var_ident : unit -> LustreIdent.index * LustreIdent.t;

    (* Create a new identifier for a node call *)
    mk_new_call_ident : LustreIdent.t -> LustreIdent.t;

    (* Create a new identifier for an oracle input *)
    mk_new_oracle_ident : unit -> LustreIdent.index * LustreIdent.t;

    (* Added definitions of variables *)
    new_vars : (StateVar.t * E.t) list;

    (* Added definitions of node calls *)
    new_calls : (StateVar.t list * E.t * ISet.elt * E.t list * E.t list) list;

    (* Added oracle inputs *)
    new_oracles : StateVar.t list;

  }


let void_abstraction_context pos = 
  
  let msg = "Expression must be a constant integer" in

  { scope = I.empty_index;
    mk_new_var_ident = (fun _ -> fail_at_position pos msg); 
    mk_new_call_ident = (fun _ -> fail_at_position pos msg);
    mk_new_oracle_ident = (fun _ -> fail_at_position pos msg);
    new_vars = []; 
    new_calls = [];
    new_oracles = [] } 


let pp_print_abstraction_context 
    ppf
    { scope; new_vars; new_calls; new_oracles} =

  Format.fprintf 
    ppf 
    "@[<v>Abstraction context for scope %a@,@[<hv>new_vars:@ @[<hv>%a@]@]@,@[<hv>new_calls:@ @[<hv>%a@]@]@,@[<hv>new_oracles:@ @[<hv>%a@]@]@]"
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
          | (ret, clk, node, inp, init) when E.equal_expr clk E.t_true -> 
            Format.fprintf ppf "@[<hv>%a =@ %a(%a)@]"
              (pp_print_list StateVar.pp_print_state_var ",@,") ret
              (I.pp_print_ident false) node
              (pp_print_list (E.pp_print_lustre_expr false) ",@,") inp
          | (ret, clk, node, inp, init) -> 
            Format.fprintf ppf "@[<hv>%a =@ condact(%a,%a(%a),%a)@]"
              (pp_print_list StateVar.pp_print_state_var ",@,") ret
              (E.pp_print_lustre_expr false) clk
              (I.pp_print_ident false) node
              (pp_print_list (E.pp_print_lustre_expr false) ",@,") inp
              (pp_print_list (E.pp_print_lustre_expr false) ",@,") init)
       ",@,")
    new_calls
    (pp_print_list StateVar.pp_print_state_var ",@,") 
    new_oracles
    
    



(* ******************************************************************** *)
(* Evaluation of expressions                                            *)
(* ******************************************************************** *)

(* Given an expression parsed into the AST, evaluate to a list of
   LustreExpr.t paired with an index, sorted by indexes. Unfold and
   abstract from the context, also return a list of created variables
   and node calls.

   The functions [mk_new_var_ident] and [mk_new_call_ident] return a
   fresh identifier for a variable and for a variable capturing the
   output of a node call, respectively. The former is called with a
   unit argument and returns an identifier __abs[n], the latter is is
   given the name of the node as an argument and returns an identifier
   __returns.X[n] where X is the node name.

   A typing context is given to type check expressions, it is not
   modified.

   There are several mutually recursive functions, [eval_ast_expr] is
   the main entry point.

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
       mk_new_var_ident; 
       mk_new_oracle_ident; 
       mk_new_call_ident;
       new_vars;
       new_calls;
       new_oracles } as abstractions)
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

  function

    (* All expressions evaluated, return result *)
    | [] -> (result, abstractions)


    (* An identifier without suffixes: a constant or a variable *)
    | (index, A.Ident (_, ident)) :: tl when 
        List.mem_assoc (I.push_index index ident) type_ctx -> 

      (* Add index to identifier *)
      let ident' = I.push_index index ident in

      (* Construct expression *)
      let expr = 

        (* Return value of constant *)
        try List.assoc ident' consts with 

          (* Identifier is not constant *)
          | Not_found -> 

            (* Return variable on the base clock *)
            E.mk_var 
              scope
              ident' 
              (List.assoc ident' type_ctx) 
              E.base_clock

      in

      (* Add expression to result *)
      eval_ast_expr' 
        context 
        abstractions
        ((index, expr) :: result) 
        tl


    (* A nested identifier with suffixes *)
    | (index, (A.Ident (_, ident) as e)) :: tl when 
        List.mem_assoc ident index_ctx -> 

      (* Expand indexed identifier *)
      let tl' = 
        List.fold_left 
          (fun a (j, _) -> (I.push_index_to_index j index, e) :: a)
          tl
          (List.rev (List.assoc ident index_ctx))
      in

      (* Continue with unfolded indexes *)
      eval_ast_expr' 
        context 
        abstractions
        result 
        tl'


    (* Identifier must have a type or indexes *)
    | (_, A.Ident (pos, ident)) :: _ -> 

      fail_at_position 
        pos
        (Format.asprintf 
           "Identifier %a not declared" 
           (I.pp_print_ident false) ident)
        

    (* Projection to a record field *)
    | (index, A.RecordProject (pos, ident, field)) :: tl -> 

      (try

         (* Check if identifier has index *)
         if List.mem_assoc field (List.assoc ident index_ctx) then

           (* Append index to identifier *)
           let expr' = 
             A.Ident (pos, I.push_index field ident) 
           in

           (* Continue with record field *)
           eval_ast_expr' 
             context 
             abstractions
             result 
             ((index, expr') :: tl)

         else

           raise Not_found

       with Not_found ->

         fail_at_position 
           pos
           (Format.asprintf 
              "Identifier %a does not have field %a" 
              (I.pp_print_ident false) ident
              (I.pp_print_index false) field))


    (* Projection to a tuple or array field *)
    | (index, A.TupleProject (pos, ident, field_expr)) :: tl -> 

      (try

         (* Evaluate expression to an integer constant *)
         let field_index = 
           I.mk_int_index (int_const_of_ast_expr context pos field_expr) 
         in

         (* Check if identifier has index *)
         if List.mem_assoc field_index (List.assoc ident index_ctx) then

           (* Append index to identifier *)
           let expr' = 
             A.Ident (pos, I.push_index field_index ident) 
           in

           (* Continue with array or tuple field *)
           eval_ast_expr' 
             context 
             abstractions
             result 
             ((index, expr') :: tl)

         else

           raise Not_found 

       with Not_found -> 

         fail_at_position 
           pos
           (Format.asprintf 
              "Identifier %a does not have field %a" 
              (I.pp_print_ident false) ident
              A.pp_print_expr field_expr))


    (* Boolean constant true *)
    | (index, A.True pos) :: tl -> 

      (* Add expression to result *)
      eval_ast_expr' 
        context 
        abstractions
        ((index, E.t_true) :: result) 
        tl


    (* Boolean constant false *)
    | (index, A.False pos) :: tl -> 

      (* Add expression to result *)
      eval_ast_expr'
        context
        abstractions 
        ((index, E.t_false) :: result) 
        tl


    (* Integer constant *)
    | (index, A.Num (pos, d)) :: tl -> 

      (* Add expression to result *)
      eval_ast_expr' 
        context 
        abstractions
        ((index, E.mk_int (Numeral.of_string d)) :: result) 
        tl


    (* Real constant *)
    | (index, A.Dec (pos, f)) :: tl -> 

      (* Add expression to result *)
      eval_ast_expr' 
        context 
        abstractions
        ((index, E.mk_real (Decimal.of_string f)) :: result) 
        tl


    (* Conversion to an integer number *)
    | (index, A.ToInt (pos, expr)) :: tl -> 

      eval_unary_ast_expr E.mk_to_int expr pos tl


    (* Conversion to a real number *)
    | (index, A.ToReal (pos, expr)) :: tl -> 

      eval_unary_ast_expr E.mk_to_real expr pos tl


    (* An expression list, flatten nested lists and add an index to
       each elements *)
    | (index, A.ExprList (pos, expr_list)) :: tl -> 

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
        ((index, A.TupleExpr (pos, expr_list')) :: tl)


    (* Tuple constructor *)
    | (index, A.TupleExpr (pos, expr_list)) :: tl -> 

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

      (* Continue with result added *)
      eval_ast_expr' 
        context 
        abstractions'
        result' 
        tl


    (* Array constructor *)
    | (index, A.ArrayConstr (pos, expr, size_expr)) :: tl -> 

      (* Evaluate expression to an integer constant *)
      let array_size = int_const_of_ast_expr context pos size_expr in

      (* Size of array must be non-zero and positive *)
      if Numeral.(array_size <= zero) then 

      fail_at_position 
        pos
        (Format.asprintf 
           "Expression %a cannot be used to \
            construct an array" 
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

      (* Continue with result added *)
      eval_ast_expr' 
        context
        abstractions' 
        result' 
        tl

    (* Array slice *)
    | (index, A.ArraySlice (pos, _, _)) :: tl -> 

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
    | (index, A.ArrayConcat (pos, _, _)) :: tl -> 

      fail_at_position pos "Array concatenation not implemented"


    (* Record constructor *)
    | (index, A.RecordConstruct (pos, record_type, expr_list)) :: tl -> 

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
                (T.pp_print_lustre_type false) e)
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

                raise E.Type_mismatch)
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
    | (index, A.Not (pos, expr)) :: tl ->

      eval_unary_ast_expr E.mk_not expr pos tl


    (* Boolean conjunction *)
    | (index, A.And (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_and expr1 expr2 pos tl


    (* Boolean disjunction *)
    | (index, A.Or (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_or expr1 expr2 pos tl


    (* Boolean exclusive disjunction *)
    | (index, A.Xor (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_xor expr1 expr2 pos tl


    (* Boolean implication *)
    | (index, A.Impl (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_impl expr1 expr2 pos tl


    (* Boolean at-most-one constaint  *)
    | (index, A.OneHot (pos, _)) :: tl -> 

      fail_at_position pos "One-hot expression not supported"


    (* Unary minus *)
    | (index, A.Uminus (pos, expr)) :: tl -> 

      eval_unary_ast_expr E.mk_uminus expr pos tl


    (* Integer modulus *)
    | (index, A.Mod (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_mod expr1 expr2 pos tl


    (* Subtraction *)
    | (index, A.Minus (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_minus expr1 expr2 pos tl


    (* Addition *)
    | (index, A.Plus (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_plus expr1 expr2 pos tl


    (* Real division *)
    | (index, A.Div (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_div expr1 expr2 pos tl


    (* Multiplication *)
    | (index, A.Times (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_times expr1 expr2 pos tl


    (* Integer division *)
    | (index, A.IntDiv (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_intdiv expr1 expr2 pos tl


    (* If-then-else *)
    | (index, A.Ite (pos, expr1, expr2, expr3)) :: tl -> 

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
            index = I.empty_index && t == Type.t_bool -> 

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
    | (index, A.With (pos, _, _, _)) :: tl -> 

      fail_at_position pos "Recursive nodes not supported in"


    (* Equality *)
    | (index, A.Eq (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_eq expr1 expr2 pos tl


    (* Disequality *)
    | (index, A.Neq (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_neq expr1 expr2 pos tl


    (* Less than or equal *)
    | (index, A.Lte (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_lte expr1 expr2 pos tl


    (* Less than *)
    | (index, A.Lt (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_lt expr1 expr2 pos tl


    (* Greater than or equal *)
    | (index, A.Gte (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_gte expr1 expr2 pos tl


    (* Greater than *)
    | (index, A.Gt (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_gt expr1 expr2 pos tl


    (* Projection on clock *)
    | (index, A.When (pos, _, _)) :: tl -> 

      fail_at_position pos "When expression not supported"


    (* Interpolation to base clock *)
    | (index, A.Current (pos, _)) :: tl -> 

      fail_at_position pos "Current expression not supported"


    (* Condact, a node with an activation condition *)
    | (index, A.Condact (pos, cond, ident, args, init)) :: tl -> 

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

          (* Forward referenced node *)
          raise (Forward_reference (ident, pos))

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

      (* Fresh identifier for node call *)
      let call_ident = mk_new_call_ident ident in

      (* Fresh state variables for oracle inputs of called node *)
      let oracle_state_vars = 
        List.map 
          (fun sv -> 
            let scope, oracle_ident = mk_new_oracle_ident () in
            E.state_var_of_ident 
              scope
              oracle_ident
              (StateVar.type_of_state_var sv))
          node_oracles 
      in

      (* Expressions from state variables for oracle inputs *)
      let oracle_exprs = 
        List.map
          (fun sv -> E.mk_var_of_state_var sv E.base_clock) 
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

      (* Add expression to result *)
      eval_ast_expr' 
        context 
        { abstractions' 
          with new_calls =
                 (node_output_idents, 
                  cond', 
                  ident, 
                  node_input_exprs @ oracle_exprs, 
                  node_init_exprs) :: abstractions'.new_calls;
               new_oracles = abstractions'.new_oracles @ oracle_state_vars }
        result' 
        tl



(*


      (try 

         let { node_inputs; node_outputs } = List.assoc ident nodes in

         let cond', new_defs' = 
           eval_ast_expr
             scope
             mk_new_var_ident 
             mk_new_oracle_ident 
             mk_new_call_ident 
             context 
             new_defs 
             cond
         in

         let args', new_defs'' = 
           eval_ast_expr_list
             scope
             mk_new_var_ident 
             mk_new_oracle_ident 
             mk_new_call_ident 
             context 
             new_defs' 
             args
         in

         let init', (vars', calls') =
           eval_ast_expr_list
             scope
             mk_new_var_ident 
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
           mk_new_var_ident 
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
                 A.pp_print_position A.dummy_pos)))

*)

    (* Temporal operator pre *)
    | (index, A.Pre (pos, expr)) :: tl -> 

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
               (accum, ({ mk_new_var_ident; new_vars } as abstractions)) 
               (index, expr) -> 
                let expr', new_vars' = 
                  E.mk_pre mk_new_var_ident new_vars expr 
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
    | (index, A.Fby (pos, _, _, _)) :: tl -> 

      fail_at_position pos "Fby operator not implemented" 


    (* Arrow temporal operator *)
    | (index, A.Arrow (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_arrow expr1 expr2 pos tl


    (* Node call *)
    | (index, A.Call (pos, ident, expr_list)) :: tl -> 

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

          (* Forward referenced node *)
          raise (Forward_reference (ident, pos))

      in

      (* Evaluate inputs as list of expressions *)
      let expr_list', abstractions' = 
        eval_ast_expr
          context 
          abstractions
          (A.ExprList (pos, expr_list))
      in

      (* Fresh identifier for node call *)
      let call_ident = mk_new_call_ident ident in

      (* Fresh state variables for oracle inputs of called node *)
      let oracle_state_vars = 
        List.map 
          (fun sv -> 
            let scope, oracle_ident = mk_new_oracle_ident () in
            E.state_var_of_ident 
              scope
              oracle_ident
              (StateVar.type_of_state_var sv))
          node_oracles 
      in

      (* Expressions from state variables for oracle inputs *)
      let oracle_exprs = 
        List.map
          (fun sv -> E.mk_var_of_state_var sv E.base_clock) 
          oracle_state_vars 
      in

      (* Type check and flatten indexed expressions for input into
         list without indexes *)
      let node_input_exprs, abstractions' =
        node_inputs_of_exprs node_inputs abstractions' pos expr_list'
      in

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

      (* Add expression to result *)
      eval_ast_expr' 
        context 
        { abstractions' 
          with new_calls = (node_output_idents, 
                            E.t_true, 
                            ident, 
                            node_input_exprs @ oracle_exprs,
                            []) :: abstractions'.new_calls;
               new_oracles = abstractions'.new_oracles @ oracle_state_vars }
        result' 
        tl


    (* Node call to a parametric node *)
    | (index, A.CallParam (pos, _, _, _)) :: tl -> 

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

          (* Indexes must match *)
          if index1 = index2 then 

            (index1, mk expr1 expr2) :: accum

          else          

            raise E.Type_mismatch)

       accum
       expr1'
       expr2',
     abstractions')

  (* Type checking error or one expression has more indexes *)
  with Invalid_argument "List.fold_left2" | E.Type_mismatch -> 

    fail_at_position pos "Type mismatch for expressions" 


(* Evaluate expression *)
and eval_ast_expr 
    context 
    abstractions
    expr = 

  let expr', abstractions' = 
    eval_ast_expr' 
      context
      abstractions
      [] 
      [(I.empty_index, expr)]
  in

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


(* Evaluate expression to an integer constant *)
and int_const_of_ast_expr context pos expr = 

  (* Evaluate expression *)
  match 

    eval_ast_expr 
      context
      (void_abstraction_context pos)
      expr 

  with

    (* Expression must evaluate to a singleton list of an integer
       expression without index and without new definitions *)
    | ([ index, { E.expr_init = ei; 
                  E.expr_step = es } ],
       { new_vars = []; new_calls = []; new_oracles = []}) when 
        index = I.empty_index && 
        ei == es -> 
      
      (match Term.destruct (E.base_term_of_expr E.base_offset ei) with 
        | Term.T.Const c when Symbol.is_numeral c ->
          Symbol.numeral_of_symbol c
            
        (* Expression is not a constant integer *)
        | _ ->       
          
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
        index = I.empty_index && t == Type.t_bool -> 
      
      expr, abstractions'

    (* Expression is not Boolean or is indexed *)
    | _ -> 
      
      fail_at_position pos "Expression is not of Boolean type") 
  


(* Type check expressions for node inputs and return sorted list of
   expressions for node inputs *)
and node_inputs_of_exprs node_inputs abstractions pos expr_list =

  try

    (* Check types and index, keep lists sorted *)
    List.fold_right2
      (fun 
        in_var
        (_, ({ E.expr_type } as expr)) 
        (accum, ({ new_vars; mk_new_var_ident } as abstractions)) ->

        if

          (* Expression must be of a subtype of input type *)
          Type.check_type 
            expr_type
            (StateVar.type_of_state_var in_var) 

        then 
    
          if 

            (* Input must not contain variable at previous state *)
            E.has_pre_var expr 

          then

            (* New variable for abstraction *)
            let scope, ident = mk_new_var_ident () in
      
            (* State variable of abstraction variable *)
            let state_var = 
              E.state_var_of_ident scope ident expr_type
            in

            (* Add definition of variable *)
            let abstractions' =
              { abstractions with
                  new_vars = (state_var, expr) :: abstractions.new_vars }
            in

            (* Use abstracted variable as input parameter *)
            (E.mk_var_of_state_var state_var E.base_clock :: accum, 
             abstractions')

          else
      
            (* Add expression as input *)
            (expr :: accum, abstractions)

        else
          raise E.Type_mismatch)
      node_inputs
      expr_list
      ([], abstractions)

  (* Type checking error or one expression has more indexes *)
  with Invalid_argument "List.fold_right2" | E.Type_mismatch -> 

    fail_at_position pos "Type mismatch for expressions"



(* Type check expressions for node inputs and return sorted list of
   expressions for node inputs *)
and node_init_of_exprs node_outputs pos expr_list =

  try

    (* Check types and index, keep lists sorted *)
    List.fold_right2
      (fun 
        out_var 
        (_, ({ E.expr_type } as expr)) 
        accum ->

        (* Expression must be of a subtype of input type *)
        if 
          Type.check_type 
            expr_type
            (StateVar.type_of_state_var out_var)
        then 
            expr :: accum
          else
            raise E.Type_mismatch) 
      node_outputs
      expr_list
      []

  (* Type checking error or one expression has more indexes *)
  with Invalid_argument "List.fold_right2" | E.Type_mismatch -> 

    fail_at_position pos "Type mismatch for expressions"



(* Return list of identifier and types to capture node outputs *)
and output_idents_of_node scope ident pos call_ident = function 

  (* Node must have outputs *)
  | [] ->  

    fail_at_position 
      pos
      (Format.asprintf 
         "Node %a cannot be called, it does not have outputs" 
         (I.pp_print_ident false) ident)

  | node_outputs -> 

    List.map
      (fun out_var -> 
         E.state_var_of_ident 
           scope
           (I.push_back_ident_index 
              (E.ident_of_state_var out_var)
              call_ident)
           (StateVar.type_of_state_var out_var))
      node_outputs

(* Add list of variables capturing the output with indexes to the result *)
and add_node_output_to_result index result = function

  (* Node must have outputs, this has been checked before *)
  | [] -> assert false

  (* Don't add index if node has a single output *)
  | [state_var] -> 

    (index, E.mk_var_of_state_var state_var E.base_clock) :: result

  (* Add indexes to be able to sort if node has more than one output *)
  | node_output_idents -> 

    snd
      (* Add indexes to variables capturing node outputs

         Must add indexes in order *)
      (List.fold_left
         (fun (i, accum) state_var -> 
            (Numeral.(succ i),
             (I.push_int_index_to_index i index, 
              E.mk_var_of_state_var state_var E.base_clock) :: accum))
         (Numeral.zero, result)
         node_output_idents)
      
      

(* Return true if expression is Boolean without indexes *)
let is_bool_expr = function

  | [ index, 
      ({ E.expr_type = t } as expr) ] when 
      index = I.empty_index && t == Type.t_bool -> true

  | _ -> false
    


let close_ast_expr (expr, abstractions) = 
  
  (* Replace unguarded pres in expression with oracle constants *)
  let expr', oracles' =
    E.oracles_for_unguarded_pres
      abstractions.mk_new_oracle_ident
      abstractions.new_oracles
      expr
  in
  
  (* Add oracle constants to abstraction *)
  let abstractions' = 
    { abstractions with new_oracles = oracles' } 
  in
  
  (* Return expression and modified abstraction *)
  (expr', abstractions') 
   

let close_indexed_ast_expr (expr, abstractions) = 
      
  (* Replace unguarded pres with oracle constants *)
  let expr', abstractions' = 
    List.fold_right 

      (fun (index, expr) (accum, abstractions) -> 

         let expr', abstractions' = close_ast_expr (expr, abstractions) in

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
   exceptions if the identifier is reserved. *)
let ident_in_context { type_ctx; index_ctx } i = 

  if 

    (* Identifier must not be reserved *)
    i = new_var_ident || i = new_call_ident 

  then
    
    raise 
      (Invalid_argument 
         (Format.asprintf 
            "Identifier %a is reserved internal use" 
            (I.pp_print_ident false) new_var_ident))

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

    (* Evaluate expression *)
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

  let node_inputs' = 
    E.state_var_of_ident scope (I.push_back_index index ident) basic_type :: 
    node_inputs
  in

  ({ context with type_ctx = type_ctx'; index_ctx = index_ctx' }, 
   { node with N.inputs = node_inputs' })


(* Add declaration of a node output to contexts *)
let add_node_output_decl
    ident
    pos
    (({ type_ctx; index_ctx } as context), 
     ({ N.outputs = node_outputs; N.name = node_ident } as node))
    index 
    basic_type =

(*  
  Format.printf "add_node_output_decl: %a %a %a@."
    (I.pp_print_ident false) ident
    (I.pp_print_index false) index
    (T.pp_print_lustre_type false) basic_type;
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

  let node_outputs' = 
    E.state_var_of_ident scope (I.push_back_index index ident) basic_type ::
    node_outputs 
  in

  ({ context with type_ctx = type_ctx'; index_ctx = index_ctx' }, 
   { node with N.outputs = node_outputs' })


(* Add declaration of a node local variable or constant to contexts *)
let add_node_var_decl
    ident
    pos
    (({ type_ctx; index_ctx } as context), 
     ({ N.name = node_ident} as node), 
      node_locals)
    index 
    basic_type =

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

  let node_locals' = 
    E.state_var_of_ident scope (I.push_back_index index ident) basic_type :: 
    node_locals
  in

  (* Must return node in accumulator *)
  ({ context with type_ctx = type_ctx'; index_ctx = index_ctx' }, 
   { node with N.locals = node.N.locals @ (List.rev node_locals') },
   node_locals')


(* Add declaration of a node input to contexts *)
let add_node_oracle_decl
    ident
    (({ type_ctx; index_ctx } as context), 
     ({ N.oracles = node_oracles; N.name = node_ident } as node))
    index 
    state_var =

  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Add index to identifier *)
  let ident' = I.push_index index ident in

  let basic_type = StateVar.type_of_state_var state_var in

  (* Add to typing context *)
  let type_ctx' = 
    (ident', basic_type) :: 
      (add_enum_to_context type_ctx A.dummy_pos basic_type) 
  in

  (* Add indexed identifier to context *)
  let index_ctx' = add_to_prefix_map index_ctx ident' () in

  let node_oracles' = 
    E.state_var_of_ident scope (I.push_back_index index ident) basic_type :: 
    node_oracles
  in

  ({ context with type_ctx = type_ctx'; index_ctx = index_ctx' }, 
   { node with N.oracles = node_oracles' })



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
let rec parse_node_outputs context node = function

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
        (add_node_output_decl ident pos)
        (context, node)
        var_type
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

    (* Add declaration of possibly indexed type to contexts *)
    let context', node', node_locals' = 
      fold_left_ast_type 
        context
        (add_node_var_decl ident pos)
        (context, node, [])
        var_type
    in
    
    (* Continue with following outputs *)
    parse_node_locals 
      context'
      node'
      tl

  |  A.NodeVarDecl (pos, (_, ident, _, _)) :: _ -> 

    fail_at_position 
      pos 
      (Format.asprintf 
         "Clocked node local variables not supported for %a" 
         (I.pp_print_ident false) ident)


  (* Local constant *)
  | A.NodeConstDecl (pos, const_decl) :: tl -> 

    let context' = add_const_decl context const_decl in

    (* Continue with following outputs *)
    parse_node_locals context' node tl


(* Add an expression as a property *)
let rec property_to_node 
    context
    node
    ({ mk_new_var_ident } as abstractions)
    pos
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

      (* New variable for abstraction *)
      let scope, ident = mk_new_var_ident () in
      
      (* State variable of abstraction variable *)
      let state_var = 
        E.state_var_of_ident scope ident Type.t_bool 
      in
      
      (* Add definition of abstraction variable to node *)
      let context', node', abstractions' = 
        equation_to_node
          context
          node
          abstractions
          A.dummy_pos  
          (state_var, expr)
      in

      (state_var, context', node', abstractions')

  in

  (* Add property to node *)
  (context', 
   { node' with N.props = (state_var :: node.N.props) },
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
      abstractions.mk_new_oracle_ident
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
        | t, s when Type.is_int_range t && Type.is_int s -> 

          let (lbound, ubound) = Type.bounds_of_int_range t in

          (* Value of expression is in range of declared type: 
             lbound <= expr and expr <= ubound *)
          let range_expr = 
            (E.mk_and 
               (E.mk_lte (E.mk_int lbound) expr) 
               (E.mk_lte expr (E.mk_int ubound)))
          in

          (* Add property to node *)
          property_to_node 
            context 
            node
            abstractions 
            A.dummy_pos 
            range_expr

        | _ -> 

          fail_at_position pos "Type mismatch for expressions")

  in

  (* Add oracle constants to abstraction *)
  let abstractions' = 
    { abstractions with new_oracles = oracles' } 
  in

  (* Add equation and abstractions *)
  (context,
   { node with N.equations = (state_var, expr') :: node.N.equations;
               N.locals = 
                 if List.mem state_var node.N.locals then 
                   node.N.locals 
                 else 
                   state_var :: node.N.locals }, 
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
           I.split_ident (E.ident_of_state_var state_var) 
         in

         (* Add variable declaration to context *)
         let context', node', node_locals' = 
           add_node_var_decl 
             base_ident
             A.dummy_pos
             (context, node, [])
             (I.index_of_one_index_list index)
             (StateVar.type_of_state_var state_var)
         in

         (* Add equation to node *)
         let context', node', abstractions' = 
           equation_to_node context node abstractions pos (state_var, expr) 
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
           I.split_ident (E.ident_of_state_var state_var) 
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

  (* Add declaration of return variables of calls to context *)
  let context', node', abstractions' = 

    List.fold_left
      (fun accum ((outputs, _, node_call_ident, _, _) as call) ->

         let context', node', abstractions' = 
           List.fold_left 
             (fun (context, node, abstractions) state_var -> 
                
                (* Split scope from name of variable *)
                let (base_ident, index) = 
                  I.split_ident (E.ident_of_state_var state_var) 
                in
                
                (* Add variable declaration to context *)
                let context', node', node_locals' = 
                  add_node_var_decl 
                    base_ident
                    A.dummy_pos
                    (context, node, [])
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

  context', node', abstractions' 


(* Parse a statement (equation, assert or annotation) in a node *)
let rec parse_node_equations 
    context 
    empty_abstractions 
    ({ N.name = node_ident } as node ) = 
  
  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 
  
  function

    | [] -> node 

    (* Assertion *)
    | A.Assert (pos, ast_expr) :: tl -> 

      (* Evaluate expression *)
      let expr', abstractions = 
        close_ast_expr
          (bool_expr_of_ast_expr 
             context 
             empty_abstractions
             pos
             ast_expr)
      in
      
      (* Add assertion to node *)
      let context', node', abstractions' = 
        assertion_to_node context node abstractions pos expr'
      in
      
      (* Add new definitions to context *)
      let context', node', abstractions' = 
        abstractions_to_context_and_node context' node' abstractions' pos
      in

      (* Continue with next node statements *)
      parse_node_equations 
        context'
        empty_abstractions
        node' 
        tl

    (* Property annotation *)
    | A.AnnotProperty (pos, ast_expr) :: tl -> 

      (* Evaluate expression *)
      let expr', abstractions = 
        close_ast_expr
          (bool_expr_of_ast_expr 
             context 
             empty_abstractions
             pos
             ast_expr)
      in
      
      (* Add assertion to node *)
      let context', node', abstractions' = 
        property_to_node context node abstractions pos expr'
      in
      
      (* Add new definitions to context *)
      let context', node', abstractions' = 
        abstractions_to_context_and_node context' node' abstractions' pos
      in

      (* Continue with next node statements *)
      parse_node_equations 
        context'
        empty_abstractions
        node' 
        tl


    (* Equations with possibly more than one variable on the left-hand side

       The expression is without node calls, those have been
       abstracted *)
    | A.Equation (pos, struct_items, ast_expr) :: tl -> 

      (* Evaluate expression *)
      let expr', abstractions = 
        close_indexed_ast_expr
          (eval_ast_expr 
             context 
             empty_abstractions

             (* Wrap right-hand side in a singleton list, nested lists
                are flattened, s.t. ((a,b)) become (a,b) *)
             (A.ExprList (pos, [ast_expr])))
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
                      (fun a v -> 
                         try 
                           (ignore 
                              (I.get_suffix ident (E.ident_of_state_var v)); 
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
                        (fun a v -> 
                           try 
                             (ignore 
                                (I.get_suffix ident (E.ident_of_state_var v));
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
      in

      (* Add abstractions to context and node *)
      let context', node', abstractions' =
        abstractions_to_context_and_node 
          context' 
          node' 
          abstractions' 
          pos
      in

      (* Continue *)
      parse_node_equations 
        context'
        empty_abstractions
        node'
        tl


    (* Annotation for main node *)
    | A.AnnotMain :: tl -> 

      parse_node_equations 
        context 
        empty_abstractions
        { node with N.is_main = true }
        tl


(* Parse a contract annotation of a node *)
let rec parse_node_contract 
    context 
    empty_abstractions
    ({ N.name = node_ident } as node) = 

  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  function

    | [] -> node 

    (* Assumption *)
    | A.Requires (pos, expr) :: tl -> 

      (* Evaluate expression *)
      let expr', abstractions = 
        close_ast_expr
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

      parse_node_contract 
        context' 
        empty_abstractions
        node'
        tl


    (* Guarantee *)
    | A.Ensures (pos, expr) :: tl -> 

      (* Evaluate expression *)
      let expr', abstractions = 
        close_ast_expr
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

      parse_node_contract 
        context' 
        empty_abstractions
        node'
        tl


let parse_node_signature  
    node_ident
    global_context
    inputs 
    outputs 
    locals 
    equations 
    contract =

  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  let mk_new_var_ident = 
    let r = ref Numeral.(- one) in
    fun () -> Numeral.incr r; (scope, I.push_int_index !r new_var_ident)
  in

  let rec mk_new_call_ident =
    let l = ref [] in
    fun ident -> 
      try 
        let r = List.assoc ident !l in
        Numeral.(incr r);
        I.push_back_int_index 
          !r 
          (I.push_back_ident_index ident new_call_ident) 
      with Not_found -> 
        l := (ident, ref Numeral.(- one)) :: !l;
        mk_new_call_ident ident
  in

  let mk_new_oracle_ident = 
    let r = ref Numeral.(- one) in
    fun () -> Numeral.incr r; (scope, I.push_int_index !r new_oracle_ident)
  in

  let empty_abstractions = 
    { scope;
      mk_new_var_ident = mk_new_var_ident;
      mk_new_oracle_ident = mk_new_oracle_ident;
      mk_new_call_ident = mk_new_call_ident;
      new_vars = [];
      new_calls = [];
      new_oracles = [] }
  in

  (* Parse inputs, add to global context and node context *)
  let local_context_inputs, node_context_inputs = 
    parse_node_inputs global_context (N.empty_node node_ident) inputs
  in

  (* Parse outputs, add to local context and node context *)
  let local_context_outputs, node_context_outputs = 
    parse_node_outputs local_context_inputs node_context_inputs outputs
  in

  (* Parse contract

     Must check here, may not use local variables *)
  let node_context_contract = 
    parse_node_contract 
      local_context_outputs 
      empty_abstractions
      node_context_outputs 
      contract
  in

  (* Parse local declarations, add to local context and node context *)
  let local_context_locals, node_context_locals = 
    parse_node_locals local_context_outputs node_context_contract locals
  in

  (* Parse equations and assertions, add to node context, local
     context is not modified *)
  let node_context_equations = 
    parse_node_equations 
      local_context_locals 
      empty_abstractions
      node_context_locals 
      equations
  in

  let node_context_equations = N.solve_eqs_node_calls node_context_equations in

  let var_dep = 
    N.node_var_dependencies 
      false 
      global_context.nodes
      node_context_equations
      []
      ((List.map (fun (v, _) -> (v, [])) node_context_equations.N.equations) @
       (List.map (fun v -> (v, [])) node_context_equations.N.outputs))
  in
(*
  Format.printf "@[<v>%a@]@."
    (pp_print_list 
      (fun ppf (v, d) ->
        Format.fprintf ppf 
          "@[<h>%a:@ %a@]"
          (I.pp_print_ident false) v 
          (pp_print_list 
             (I.pp_print_ident false)
             " ")
          (ISet.elements d))
      "@,")
    var_dep;
*)
  let node_context_deps = 
    { node_context_equations with 
        N.output_input_dep = 
          N.output_input_dep_of_var_dep 
            node_context_equations 
            var_dep } 
  in

  let equations_sorted =
    List.sort
      (fun (v1, _) (v2, _) -> 
         if StateVar.StateVarSet.mem v1 (List.assoc v2 var_dep) then (- 1) 
         else if StateVar.StateVarSet.mem v2 (List.assoc v1 var_dep) then 1 
         else StateVar.compare_state_vars v1 v2)
      node_context_deps.N.equations
  in

  let node_context_dep_order =
    { node_context_deps with N.equations = equations_sorted }
  in

  node_context_dep_order

(* ******************************************************************** *)
(* Main                                                                 *)
(* ******************************************************************** *)

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

         with Invalid_argument e -> 

           fail_at_position pos e)

      then

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

        (* Add declarations to global context *)
        let node_context = 
          parse_node_signature
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

       (* Forward reference in node *)
       with Forward_reference (ident, pos) -> 

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


let declarations_to_nodes decls = 

  let { nodes } = declarations_to_nodes' init_lustre_context decls in

  nodes


(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
