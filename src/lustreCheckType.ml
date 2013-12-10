(* This file is part of the Kind verifier

 * Copyright (c) 2007-2009 by the Board of Trustees of the University of Iowa, 
 * here after designated as the Copyright Holder.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the University of Iowa, nor the
 *       names of its contributors may be used to endorse or promote products
 *       derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *)

open Lib

(* Abbreviations *)
module A = LustreAst
module I = LustreIdent
module T = LustreType
module E = LustreExpr
module ISet = I.LustreIdentSet



type const_val =
  | ConstInt of int
  | ConstFloat of float
  | ConstBool of bool
  | ConstEnum of I.t

type expr_val = 
  | Const of const_val
  | Expr of E.t
  | IndexedExpr of (I.t * expr_val) list


type expr_type = 
  | Type of T.t 
  | IndexedType of  (I.index list * T.t) list


(* Return an integer of a value *)
let int_of_expr_val = function
  | Const (ConstInt n) -> n
  | _ -> raise (Invalid_argument "int_of_expr_val")



(* Convert a built-in type to a parsed type *)
let ast_type_of_lustre_type = function 

  | T.Bool -> A.Bool

  | T.Int -> A.Int

  | T.Real -> A.Real

  | T.IntRange (i, j) -> 

    A.IntRange 
      (A.Num (A.dummy_pos, string_of_int i), 
       A.Num (A.dummy_pos, string_of_int j))

  | T.Enum l -> A.EnumType l

  | T.FreeType t -> A.UserType t



type node_context = 

  { 

    (* Constant inputs of node *)
    node_input_consts : (LustreIdent.t  * LustreType.t) list;

    (* Input variables of node *)
    node_inputs : (LustreIdent.t * LustreType.t) list;

    (* Output variables of node *)
    node_outputs : (LustreIdent.t * LustreType.t) list;
    
    (* Local variables of node *)
    node_vars : (LustreIdent.t * LustreType.t) list;

    (* Equations for local and output variables *)
    node_eqs : (LustreIdent.t * LustreExpr.t) list;

    (* Assertions of node *)
    node_asserts : LustreExpr.t list;

    (* Proof obligations for node *)
    node_prop : LustreExpr.t list;

    (* Contract for node, assumptions *)
    node_requires : LustreExpr.t list;

    (* Contract for node, guarantees *)
    node_ensures : LustreExpr.t list }


let init_node_context = 
  { node_input_consts = [];
    node_inputs = [];
    node_outputs = [];
    node_vars = [];
    node_eqs = [];
    node_asserts = [];
    node_prop = [];
    node_requires = [];
    node_ensures = [] }


(* A context of the type checker and preprocessor *)
type lustre_context = 

    { 

      (* Type identifiers and their types *)
      basic_types : (LustreIdent.t * LustreType.t) list; 

      (* Prefixes of indexed type identifiers, their suffixes and types *)
      indexed_types : 
        (LustreIdent.t * 
           (LustreIdent.index * LustreType.t) list) list; 

      (* Type identifiers for free types *)
      free_types : LustreIdent.t list; 

      (* Types of constants and variables *)
      type_ctx : (LustreIdent.t * LustreType.t) list; 

      (* Indexes of constants and variables *)
      index_ctx : 
        (LustreIdent.t * 
           (LustreIdent.index * unit) list) list; 

      (* Values of constants *)
      consts : (LustreIdent.t * LustreExpr.t) list; 

      (* Defined nodes *)
      nodes : (LustreIdent.t * node_context) list;

      (* Preprocessed and checked Lustre program *)
      result : unit 

    }

(* Initial context *)
let init_lustre_context = 
  { basic_types = [];
    indexed_types = [];
    free_types = [];
    type_ctx = [];
    index_ctx = [];
    consts = [];
    nodes = [];
    result = () }



let pp_print_basic_type ppf (i, t) = 
  Format.fprintf ppf "%a: %a" I.pp_print_ident i T.pp_print_lustre_type t

let pp_print_index_type ppf (i, t) = 
  Format.fprintf ppf "%a: %a" I.pp_print_index i T.pp_print_lustre_type t

let pp_print_indexed_type ppf (i, t) = 

  Format.fprintf ppf 
    "%a: @[<hv 1>[%a]@]" 
    I.pp_print_ident i 
    (pp_print_list pp_print_index_type ";@ ") t

let pp_print_type_ctx ppf (i, t) = 
  Format.fprintf ppf "%a: %a" I.pp_print_ident i T.pp_print_lustre_type t

let pp_print_index_ctx ppf (i, j) = 

  Format.fprintf ppf 
    "%a: @[<hv 1>[%a]@]" 
    I.pp_print_ident i 
    (pp_print_list 
       (fun ppf (i, _) -> I.pp_print_index ppf i)
       ";@ ") 
    j

let pp_print_consts ppf (i, e) = 
  Format.fprintf ppf "%a: %a" I.pp_print_ident i E.pp_print_lustre_expr e

  


let pp_print_lustre_context 
    ppf 
    { basic_types;
      indexed_types; 
      free_types; 
      type_ctx; 
      index_ctx; 
      consts; 
      result } =
  
  Format.fprintf ppf
    "@[<v>@[<v>*** basic_types:@,%a@]@,\
          @[<v>*** indexed_types:@,%a@]@,\
          @[<v>*** free_types:@,@[<hv>%a@]@,@]\
          @[<v>*** type_ctx:@,%a@]@,\
          @[<v>*** index_ctx:@,%a@]@,\
          @[<v>*** consts:@,%a@]@,\
     @]" 
    (pp_print_list pp_print_basic_type "@,") basic_types
    (pp_print_list pp_print_indexed_type "@,") indexed_types
    (pp_print_list I.pp_print_ident ",@ ") free_types
    (pp_print_list pp_print_type_ctx "@,") type_ctx
    (pp_print_list pp_print_index_ctx "@,") index_ctx
    (pp_print_list pp_print_consts "@,") consts


(* An well-typed and well-clocked expression with its type and clock *)
type typed_clocked_expr = 
    { 
      
      (* Simplified expression *)
      expr_sim : LustreExpr.t;

      (* Type of expression *)
      expr_type : LustreType.t;

      (* Clock of expression  *)
      expr_clock : LustreExpr.t 

    }


(* A well-typed and well-clocked expression or a set of indexed
   well-typed and well-typed expressions *)
type expr = 

  (* An expression *)
  | Expr of typed_clocked_expr

  (* A set of indexed expressions *)
  | IndexedExpr of (LustreIdent.index * typed_clocked_expr) list



(* For an identifier t = t.i1...in associate each prefix with suffix
   and type t'': add (t, (i1...in, t'')), ..., (t.i1..in-1, (in, t''))
   to indexed_types *)
let add_to_prefix_map map ident (value : 'a) =

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
          (prefix, [(suffix, value)]) :: accum

        (* Prefix of identifier found *)
        | (p, l) :: tl when p = prefix -> 

          (* Add association of prefix with suffix and type, and
             finish *)
          List.rev_append ((p, (suffix, value) :: l) :: tl) accum

        (* Recurse to keep searching for prefix of identifier *)
        | h :: tl -> aux2 (h :: accum) tl

      in

      (* Add index to prefix *)
      let prefix' = I.add_index prefix [index] in

      (* Recurse for remaining suffix *)
      aux prefix' (aux2 [] map) tl

  in

  (* Get indexes of identifier of type *)
  let (ident_base, suffix) = ident in

  (* Add types of all suffixes *)
  aux (ident_base, []) map suffix 




(* Add type declaration for an alias type to a context

   Associate possibly indexed identifier with its Lustre type;
   associate all prefixes of an indexed identifier with its suffixes
   and their basic types; and for enum type associate the enum type to
   each constant.
*)
let add_alias_type_decl 
    ident
    ({ basic_types; indexed_types; type_ctx } as context) 
    index 
    basic_type =

  (* Add index to identifier *)
  let indexed_ident = I.add_index ident index in

  (* Output type declaration *)
  Format.printf 
    "-- type %a = %a;@." 
    I.pp_print_ident indexed_ident
    T.pp_print_lustre_type basic_type;

  (* Add alias for basic type *)
  let basic_types' = (indexed_ident, basic_type) :: basic_types in

  (* Add types of all suffixes *)
  let indexed_types' = 
    add_to_prefix_map indexed_types indexed_ident basic_type
  in

  (* Add enum constants to typing context *)
  let type_ctx' = match basic_type with 

    (* Type is an enumeration *)
    | T.Enum l -> 

      List.fold_left
        (fun type_ctx enum_element -> 
           
           try 

             (* Get type of constant *)
             let enum_element_type = List.assoc enum_element type_ctx in 

             (* Skip if constant declared with the same (enum) type *)
             if basic_type = enum_element_type then type_ctx else

               (* Fail *)
               raise 
                 (Failure 
                    (Format.asprintf 
                       "Enum constant %a declared with \
                        different type in %a" 
                       I.pp_print_ident enum_element
                       A.pp_print_position A.dummy_pos));
             
           (* Constant not declared *)
           with Not_found -> 

             (* Push constant to typing context *)
             (enum_element, basic_type) :: type_ctx)
        type_ctx
        l

    (* Other basic types do not change typing context *)
    | _ -> type_ctx

  in

  (* Changes to context *)
  { context with 
      basic_types = basic_types'; 
      indexed_types = indexed_types';
      type_ctx = type_ctx' }
  


(* ******************************************************************** *)
(* Evaluation of expressions                                            *)
(* ******************************************************************** *)

let rec eval_ast_expr'     
    ({ basic_types; 
       indexed_types; 
       free_types; 
       type_ctx; 
       index_ctx; 
       consts } as context)
    result = function

  (* All expressions evaluated, return result *)
  | [] -> result


  (* An identifier without indexes *)
  | (index, A.Ident (_, ident)) :: tl when 
      List.mem_assoc (I.add_index ident index) type_ctx -> 

    (* Construct expression *)
    let expr = 

      (* Return value of constant *)
      try List.assoc ident consts with 

        (* Identifier is not constant *)
        | Not_found -> 

          (* Return variable of defined type on the base clock *)
          E.mk_var ident (List.assoc ident type_ctx) E.base_clock

    in

    (* Add expression to result *)
    eval_ast_expr' context ((index, expr) :: result) tl


  (* A nested identifier with indexes *)
  | (index, (A.Ident (_, ident) as e)) :: tl when 
      List.mem_assoc ident index_ctx -> 

    (* Expand indexed identifier *)
    let tl' = 
      List.fold_left 
        (fun a (j, _) -> (index @ j, e) :: a)
        tl
        (List.assoc ident index_ctx)
    in

    (* Continue with unfolded indexes *)
    eval_ast_expr' context result tl'


  (* Identifier must have a type or indexes *)
  | (_, A.Ident (pos, ident)) :: _ -> 

    (* Fail *)
    raise 
      (Failure 
         (Format.asprintf 
            "Identifier %a not declared in %a" 
            I.pp_print_ident ident
            A.pp_print_position pos))


  (* Projection to a record field *)
  | (index, A.RecordProject (pos, ident, field)) :: tl -> 

    (try

       (* Check if identifier has index *)
       if List.mem_assoc field (List.assoc ident index_ctx) then

         (* Append index to identifier *)
         let expr' = 
           A.Ident (pos, I.add_index ident field) 
         in

         (* Continue with record field *)
         eval_ast_expr' context result ((index, expr') :: tl)

       else

         raise Not_found

     with Not_found ->

       (* Fail *)
       raise 
         (Failure 
            (Format.asprintf 
               "Identifier %a does not have field %a in %a" 
               I.pp_print_ident ident
               A.pp_print_position pos
               I.pp_print_index field)))


  (* Projection to a tuple or array field *)
  | (index, A.TupleProject (pos, ident, field_expr)) :: tl -> 

    (try

       (* Evaluate expression to an integer constant *)
       let field_index = 
         I.index_of_int (int_const_of_ast_expr context field_expr) 
       in

       (* Check if identifier has index *)
       if List.mem_assoc field_index (List.assoc ident index_ctx) then

         (* Append index to identifier *)
         let expr' = 
           A.Ident (pos, I.add_index ident field_index) 
         in

         (* Continue with array or tuple field *)
         eval_ast_expr' context result ((index, expr') :: tl)

       else

         raise Not_found 

     with Not_found -> 

       (* Fail *)
       raise 
         (Failure 
            (Format.asprintf 
               "Identifier %a does not have field %a in %a" 
               I.pp_print_ident ident
               A.pp_print_expr field_expr
               A.pp_print_position pos)))


  (* Boolean constant true *)
  | (index, A.True pos) :: tl -> 

    (* Add expression to result *)
    eval_ast_expr' context ((index, E.t_true) :: result) tl


  (* Boolean constant true *)
  | (index, A.False pos) :: tl -> 

    (* Add expression to result *)
    eval_ast_expr' context ((index, E.t_false) :: result) tl


  (* Integer constant *)
  | (index, A.Num (pos, d)) :: tl -> 

    (* Add expression to result *)
    eval_ast_expr' 
      context 
      ((index, E.mk_int (int_of_string d)) :: result) 
      tl


  (* Real constant *)
  | (index, A.Dec (pos, f)) :: tl -> 

    (* Add expression to result *)
    eval_ast_expr' 
      context 
      ((index, E.mk_real (float_of_string f)) :: result) 
      tl


  (* Conversion to an integer  *)
  | (index, A.ToInt (pos, expr)) :: tl -> 

    (* Add expression to result *)
    eval_ast_expr' 
      context 
      (unary_apply_to context E.mk_to_int expr result)  
      tl


  (* Conversion to an integer  *)
  | (index, A.ToReal (pos, expr)) :: tl -> 

    (* Add expression to result *)
    eval_ast_expr' 
      context 
      (unary_apply_to context E.mk_to_real expr result) 
      tl


  (* Tuple constructor *)
  | (index, A.TupleExpr (pos, expr_list)) :: tl -> 

    let _, result' = 

      (* Iterate over list of expressions *)
      List.fold_left
        (fun (i, a) e -> 

           (* Evaluate one expression *)
           let expr_val = eval_ast_expr context e in

           (* Index of counter *)
           let index = I.index_of_int i in

           (* Increment counter *)
           (succ i,

            (* Append current index to each index of evaluated
               expression *)
            List.fold_left 
              (fun a (j, e) -> (index @ j, e) :: a)
              a
              expr_val))

        (0, result)
        expr_list
    in

    (* Continue with result added *)
    eval_ast_expr' context result' tl


  (* Array constructor *)
  | (index, A.ArrayConstr (pos, expr, size_expr)) :: tl -> 

    (* Evaluate expression to an integer constant *)
    let array_size = int_const_of_ast_expr context size_expr in

    (* Size of array must be non-zero and positive *)
    if array_size <= 0 then 

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Expression %a cannot be used to \
               construct an array in %a " 
              A.pp_print_expr size_expr
              A.pp_print_position pos));

    (* Evaluate expression for array elements *)
    let expr_val = eval_ast_expr context expr in 

    let result' = 

      let rec aux accum = function 

        (* All elements of array enuerated

           Started with size of array, lowest index is zero  *)
        | 0 -> accum

        (* Array element *)
        | i -> 


          (* Append current index to each index of evaluated
               expression and recurse to next lower array element *)
          aux 
            (List.fold_left
               (fun a (j, e) -> (I.add_int_to_index j (pred i), e) :: a)
               accum
               expr_val)
            (pred i)

      in

      (* Add all array elements *)
      aux result array_size

    in

    (* Continue with result added *)
    eval_ast_expr' context result' tl

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

  | (index, A.Not (pos, expr)) :: tl -> 

    (* Add expression to result *)
    eval_ast_expr' 
      context 
      (unary_apply_to context E.mk_not expr result)  
      tl

and unary_apply_to context mk expr accum = 

  let expr' = eval_ast_expr context expr in

  List.fold_right
    (fun (j, e) a -> (j, mk e) :: a)
    expr'
    accum

and binary_apply_to context mk expr1 expr2 accum = 

  (* Sort a list indexed expressions *)
  let sort_indexed_expr = 
    List.sort (fun (i1, _) (i2, _) -> I.compare_index i1 i2) 
  in
  
  (* Evaluate and sort first expression by indexes *)
  let expr1' = sort_indexed_expr (eval_ast_expr context expr1) in

  (* Evaluate and sort second expression by indexes *)
  let expr2' = sort_indexed_expr (eval_ast_expr context expr2) in

  List.fold_right2
    (fun (j1, e1) (j2, e2) a -> 

       if j1 = j2 then (j1, mk e1 e2) else          

         (* Fail *)
         raise 
           (Failure 
              (Format.asprintf 
                 "Type mismatch for expressions at %a" 
                 A.pp_print_position A.dummy_pos)))
    expr1'
    expr2'
    accum
  
  


and eval_ast_expr context expr = eval_ast_expr' context [] [([], expr)]

and int_const_of_ast_expr context expr = 

  (* Evaluate expression *)
  match eval_ast_expr context expr with

    (* Expression must evaluate to a singleton list of an integer
       expression without index *)
    | [ [], { E.expr_pre_vars; 
              E.expr_init = E.Int di; 
              E.expr_step = E.Int ds } ] 
      when ISet.is_empty expr_pre_vars && di = ds -> di

    (* Expression is not a constant integer *)
    | _ ->       

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Expression %a in %a must be a constant integer" 
              A.pp_print_expr expr
              A.pp_print_position A.dummy_pos))



(* Expand a possibly nested type expression to indexed basic types and
   apply [f] to each

   The context of the unfolding cannot be modified by f, this is a
   good thing and disallows defining types recursively. *)
let rec fold_ast_type' 
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

  (* Basic Lustre types *)
  | (index, A.Bool) :: tl -> 

    fold_ast_type' context f (f accum index T.t_bool) tl

  | (index, A.Int) :: tl -> 

    fold_ast_type' context f (f accum index T.t_int) tl

  | (index, A.Real) :: tl -> 

    fold_ast_type' context f (f accum index T.t_real) tl

  (* Integer range type needs to be constructed from evaluated
     expressions for bounds *)
  | (index, A.IntRange (lbound, ubound)) :: tl -> 

    (* Evaluate expressions for bounds to constants *)
    let const_lbound, const_ubound = 
      (int_const_of_ast_expr context lbound, 
       int_const_of_ast_expr context ubound) 
    in

    (* Construct an integer range type *)
    fold_ast_type' 
      context 
      f 
      (f accum index (T.mk_int_range const_lbound const_ubound)) 
      tl

  (* Enum type needs to be constructed *)
  | (index, A.EnumType enum_elements) :: tl -> 

    (* Construct an enum type *)
    fold_ast_type' context f (f accum index (T.mk_enum enum_elements)) tl


  (* User type that is an alias *)
  | (index, A.UserType ident) :: tl when 
      List.mem_assoc ident basic_types -> 

    (* Substitute basic type *)
    fold_ast_type' 
      context 
      f 
      (f accum index (List.assoc ident basic_types)) 
      tl

  (* User type that is an alias for an indexed type *)
  | (index, A.UserType ident) :: tl when 
      List.mem_assoc ident indexed_types -> 

    (* Apply f to basic types with index *)
    let accum' = 
      List.fold_left
        (fun a (j, s) -> f a (index @ j) s)
        accum
        (List.assoc ident indexed_types)
    in

    (* Recurse for tail of list *)
    fold_ast_type' context f accum' tl

  (* User type that is a free type *)
  | (index, A.UserType ident) :: tl when 
      List.mem ident free_types -> 

    (* Substitute free type *)
    fold_ast_type' 
      context 
      f 
      (f accum index (T.mk_free_type ident)) 
      tl

  (* User type that is neither an alias nor free *)
  | (index, A.UserType ident) :: _ -> 

    (* Fail *)
    raise 
      (Failure 
         (Format.asprintf 
            "Type %a in %a is not declared" 
            I.pp_print_ident ident
            A.pp_print_position A.dummy_pos))

  (* Record type *)
  | (index, A.RecordType record_fields) :: tl -> 

    (* Substitute with indexed types of fields *)
    fold_ast_type' 
      context 
      f 
      accum 
      (List.fold_left
         (fun a (j, s) -> (index @ (I.index_of_ident j), s) :: a)
         tl
         record_fields)

  (* Tuple type *)
  | (index, A.TupleType tuple_fields) :: tl -> 

    (* Substitute with indexed types of elements *)
    fold_ast_type' 
      context 
      f 
      accum 
      (fst
         (List.fold_left
            (fun (a, j) s -> (index @ (I.index_of_int j), s) :: a, succ j)
            (tl, 0)
            tuple_fields))

  (* Array type *)
  | (index, A.ArrayType (type_expr, size_expr)) :: tl -> 

    (* Evaluate size of array to a constant integer *)
    let array_size = int_const_of_ast_expr context size_expr in

    (* Array size must must be at least one *)
    if array_size <= 0 then 

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Expression %a must be positive as array size in %a" 
              A.pp_print_expr size_expr
              A.pp_print_position A.dummy_pos));

    (* Append indexed types *)
    let rec aux accum = function
      | 0 -> accum
      | j -> 

        aux 
          ((index @ (I.index_of_int (pred j)), type_expr) :: accum)
          (pred j)

    in

    (* Substitute with indexed types of elements *)
    fold_ast_type' 
      context 
      f 
      accum 
      (aux tl array_size)


(* Wrapper for folding function over type expression  *)
let fold_ast_type context f accum t = 
  fold_ast_type' context f accum [([], t)] 



(* TODO: preserve order of positional parameters or add indexes *)

let add_const_node_input_decl
    ident
    (({ type_ctx; index_ctx } as context), 
     ({ node_input_consts } as node))
    index 
    basic_type =
  
  (* Add index to identifier *)
  let ident' = I.add_index ident index in

  (* Add to typing context *)
  let type_ctx' = (ident', basic_type) :: type_ctx in

  (* Add to constant node inputs *)
  let node_input_consts' = (ident', basic_type) :: node_input_consts in

  ({ context with type_ctx = type_ctx' }, 
   { node with node_input_consts = node_input_consts' })



let rec parse_node_input_signature context node = function

  | [] -> (context, node)

  (* A constant input *)
  | (ident, var_type, A.ClockTrue, true) :: tl -> 

    let context', node' = 
      fold_ast_type 
        context
        (add_const_node_input_decl ident)
        (context, node)
        var_type
    in

    parse_node_input_signature context' node' tl

  (* A variable input *)
  | (ident, var_type, A.ClockTrue, false) :: tl -> 

    let context', node' = context, node in

    parse_node_input_signature context' node' tl
    
  | _ -> 

    (* Fail *)
    raise 
      (Failure 
         (Format.asprintf 
            "Clocked node inputs not supported in %a" 
            A.pp_print_position A.dummy_pos))








(*

   type_aliases is an association list from type names to basic types,
   free_types is a list of types 
   indexed_types is an association list of type names to their indexes 

   A type occurs at most in one of type_aliases, free_types and indexed_types

*)
let rec check_declarations
    ({ basic_types; 
       indexed_types; 
       free_types; 
       type_ctx; 
       index_ctx; 
       consts; 
       result } as global_context) = 



(*


  (* Apply function pointwise *)
  let unary_apply_to f = function 
    | Expr e -> Expr (f e)
    | IndexedExpr l -> IndexedExpr (List.map (function (i, e) -> (i, f e)) l)
  in


  (* Apply function pointwise *)
  let binary_apply_to pos f = function 

    | Expr e1, Expr e2 -> Expr (f (e1, e2))

    | IndexedExpr l1, IndexedExpr l2 -> 

      (

        (* Sort a list indexed expressions *)
        let sort_indexed_expr = 
          List.sort (fun (i1, _) (i2, _) -> I.compare_index i1 i2) 
        in

        (* Sort indexed expression lists *)
        let l1', l2' = sort_indexed_expr l1, sort_indexed_expr l2 in

        try 

          IndexedExpr 
            (List.map2 
               (fun (i1, e1) (i2, e2) -> 

                  (* Indexes must match *)
                  if i1 = i2 then 

                    (* Clocks must match *)
                    if check_clocks e1.expr_clock e2.expr_clock then 

                      (* Apply function to expressions *)
                      (i1, f (e1, e2))

                    else

                      (* Fail *)
                      raise 
                        (Failure 
                           (Format.asprintf 
                              "Clock mismatch for expressions at %a" 
                              A.pp_print_position pos))

                  else

                    (* Fail *)
                    raise 
                      (Failure 
                         (Format.asprintf 
                            "Type mismatch for expressions at %a" 
                            A.pp_print_position pos)))
               l1'
               l2')

        with Invalid_argument _ -> 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Type mismatch for expressions at %a" 
                  A.pp_print_position pos))

      )

    | _ -> 

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Type mismatch for expressions at %a" 
              A.pp_print_position pos))

  in

  (* Filter the indexed expression for the given indexes, flatten if
     necessary *)
  let rec expr_find_index index accum = function 

    (* End of list, return found indexes *)
    | [] -> accum

    (* Expression at index *)
    | (i, e) :: tl -> 

      (try 

         (* Get suffix if index is a prefix *)
         let i' = I.get_index_suffix index i in 

         (* Add expression and suffix to accumulator *)
         expr_find_index index ((i', e) :: accum) tl

       (* Index is no prefix *)
       with Invalid_argument "get_index_suffix" -> 

         expr_find_index index accum tl)

  in

  (* Return type of expression *)
  let rec check_expr = function

    (* An identifier without indexes *)
    | A.Ident (p, id) when List.mem_assoc id type_ctx -> 

      (* Simplify expression by susbtituting value of constant if
         possible *)
      let expr_sim = 

        (* Return value of constant *)
        try List.assoc id consts with 

          (* Otherwise return variable *)
          | Not_found -> E.mk_var id 

      in

      (* Type of expression is type of identifier *)
      let expr_type = List.assoc id type_ctx in 

      (* Clock of expression is base clock *)
      let expr_clock = E.t_true in

      (* Return simplified expression, type and clock *)
      Expr 
        { expr_sim = expr_sim; 
          expr_type = expr_type; 
          expr_clock = expr_clock }


    (* A nested identifier with indexes *)
    | A.Ident (p, id) when List.mem_assoc id index_ctx -> 

      (* Simlifiy each index *)
      let res = 
        List.fold_left 
          (fun a idx -> 
             match check_expr (A.Ident (p, I.add_index id idx)) with 

               (* Expresssion is simple *)
               | Expr e -> (idx, e) :: a 

               (* Expression is nested *)
               | IndexedExpr l -> 

                 (* Flatten *)
                 List.fold_left 
                   (fun a (i, e) -> (idx @ i, e) :: a)
                   a
                   l)
          []
          (List.assoc id index_ctx)
      in

      (* Return list of indexed simplified expresssions *)
      IndexedExpr res


    (* Identifier must have a type or indexes *)
    | A.Ident (p, id) -> 

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Identifier %a in %a is not declared" 
              I.pp_print_ident id
              A.pp_print_position p))


    (* Projection to a record field *)
    | A.RecordProject (p, id, idx) -> 

      (* Evaluate identifier *)
      (match check_expr (A.Ident (p, id)) with 

        (* Must be an indexed expression *)
        | IndexedExpr l -> 

          (* Find all expression with index as prefix of their
             index *)
          (match expr_find_index idx [] l with 

            (* Index not found *)
            | [] -> 

              (* Fail *)
              raise 
                (Failure 
                   (Format.asprintf 
                      "Identifier %a in %a does not have field %a" 
                      I.pp_print_ident id
                      A.pp_print_position p
                      I.pp_print_index idx))

            (* Reduced to a single expression with empty index  *)
            | [([], e)] -> Expr e

            (* Reduced to a nested expression *)
            | l' -> IndexedExpr l'

          )

        (* Identifier is no record *)
        | Expr _ -> 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Identifier %a in %a does not have fields" 
                  I.pp_print_ident id
                  A.pp_print_position p))

      )

    (* Projection of a tuple or array *)
    | A.TupleProject (p, id, e) -> 

      (match check_expr (A.Ident (p, id)) with 

        | IndexedExpr l -> 

          (* Turn expresssion into index *)
          let idx = 

            match check_expr e with 

              (* Expresssion must be simplified to zero or a
                 positive integer *)
              | Expr { expr_sim = E.Int i } when i >= 0 -> 

                I.index_of_int i 

              (* Expression cannot be nested or negative *)
              | Expr _
              | IndexedExpr _ -> 

                (* Fail *)
                raise 
                  (Failure 
                     (Format.asprintf 
                        "Expression %a in %a cannot be used as index" 
                        A.pp_print_expr e
                        A.pp_print_position p))

          in

          (* Evaluate as projection of record *)
          check_expr (A.RecordProject (p, id, idx))

        (* Identifier is no record *)
        | Expr _ -> 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Identifier %a in %a does not have fields" 
                  I.pp_print_ident id
                  A.pp_print_position p))

      )

    | A.True p -> 

      Expr 
        { expr_sim = E.t_true; 
          expr_type = T.t_bool; 
          expr_clock = E.t_true } 

    | A.False p -> 

      Expr 
        { expr_sim = E.t_false; 
          expr_type = T.t_bool; 
          expr_clock = E.t_true } 

    | A.Num (p, d) -> 

      Expr 
        { expr_sim = E.mk_int (int_of_string d); 
          expr_type = T.t_int; 
          expr_clock = E.t_true } 

    | A.Dec (p, f) -> 

      Expr 
        { expr_sim = E.mk_real (float_of_string f); 
          expr_type = T.t_real; 
          expr_clock = E.t_true } 


    | A.ToInt (p, e) -> 

      let eval = function 

        | { expr_sim = E.Real f; expr_type = T.Real } as expr -> 

          { expr with 
              expr_sim = E.mk_int (int_of_float f); 
              expr_type = T.t_int }

        | { expr_sim = e; expr_type = T.Real } as expr -> 

          { expr with 
              expr_sim = E.mk_to_int e; 
              expr_type = T.t_int }

        | _ ->

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a must have type real" 
                  A.pp_print_expr e
                  A.pp_print_position p))

      in

      unary_apply_to 
        eval
        (check_expr e)

    | A.ToReal (p, e) -> 

      let eval = function 

        | { expr_sim = E.Int d; expr_type = T.Int } as expr -> 

          { expr with 
              expr_sim = E.mk_real (float_of_int d); 
              expr_type = T.t_real }

        | { expr_sim = e; expr_type = T.Int } as expr -> 

          { expr with 
              expr_sim = E.mk_to_real e; 
              expr_type = T.t_real }

        | _ ->

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a must have type int" 
                  A.pp_print_expr e
                  A.pp_print_position p))

      in

      unary_apply_to 
        eval
        (check_expr e)

    (* TODO *)
    | A.ExprList _ -> assert false 

    | A.TupleExpr (p, l) -> 

      IndexedExpr 
        (snd
           (List.fold_left
              (fun (i, a) e -> 
                 match check_expr e with 
                   | Expr e -> (succ i, (I.index_of_int i, e) :: a)
                   | IndexedExpr l -> 
                     (succ i, 
                      List.fold_left
                        (fun a (j, e) -> (I.IntIndex i :: j, e) :: a)
                        a
                        l))
              (0, [])
              l))


    | A.ArrayConstr (p, e1, e2) -> 

      let n = 

        match check_expr e2 with 

          (* Expresssion must be simplified to a non-zero positive
             integer *)
          | Expr { expr_sim = E.Int i } when i >= 1 -> i 

          (* Expression cannot be nested *)
          | Expr _
          | IndexedExpr _ -> 

            (* Fail *)
            raise 
              (Failure 
                 (Format.asprintf 
                    "Expression %a in %a cannot be used to \
                     construct an array" 
                    A.pp_print_expr e2
                    A.pp_print_position p))

      in

      let e = check_expr e1 in

      IndexedExpr 
        (let rec aux accum = function
           | 0 -> accum
           | i -> 
             match e with 
               | Expr e -> 
                 aux ((I.index_of_int (pred i), e) :: accum) (pred i)

               | IndexedExpr l -> 

                 aux 
                   (List.fold_left
                      (fun a (j, e) -> 
                         (I.add_int_to_index j i, e) :: a)
                      accum
                      l)
                   (pred i)
         in
         aux [] n)

    | A.ArraySlice (p, id, l) ->  

      let expr_list = match check_expr (A.Ident (p, id)) with 
        | IndexedExpr l -> l 
        | Expr _ -> 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Identifier %a in %a does not have fields" 
                  I.pp_print_ident id
                  A.pp_print_position p))

      in

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
             let il = 

               match check_expr el with 

                 (* Expresssion must be simplified to zero or a positive
                    integer *)
                 | Expr { expr_sim = E.Int i } when i >= 0 -> i 

                 (* Expression cannot be nested *)
                 | Expr _
                 | IndexedExpr _ -> 

                   (* Fail *)
                   raise 
                     (Failure 
                        (Format.asprintf 
                           "Expression %a in %a cannot be used as \
                            the lower bound of an array" 
                           A.pp_print_expr el
                           A.pp_print_position p))

             in

             (* Evaluate expression for lower bound to an integer *)
             let iu = 

               match check_expr eu with 

                 (* Expresssion must be simplified to a non-zero
                    positive integer *)
                 | Expr { expr_sim = E.Int i } when i >= il -> i 

                 (* Expression cannot be nested *)
                 | Expr _
                 | IndexedExpr _ -> 

                   (* Fail *)
                   raise 
                     (Failure 
                        (Format.asprintf 
                           "Expression %a in %a cannot be used as \
                            the upper bound of an array slice" 
                           A.pp_print_expr eu
                           A.pp_print_position p))

             in

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


    | A.ArrayConcat (p, e1, e2) -> 

      IndexedExpr
        (match check_expr e1, check_expr e2 with 

          | IndexedExpr l1, IndexedExpr l2 -> 

            (let n = List.length l1 in 

             List.fold_left
               (fun a (i, e) -> 
                  (match i with 

                    | I.IntIndex i :: tl -> 
                      (I.IntIndex (i + n) :: tl, e) :: a

                    | _ -> 

                      (* Fail *)
                      raise 
                        (Failure 
                           (Format.asprintf 
                              "Expression %a in %a is not an array" 
                              A.pp_print_expr e2
                              A.pp_print_position p))))
               l1
               l2)

          | Expr _, _ -> 

            (* Fail *)
            raise 
              (Failure 
                 (Format.asprintf 
                    "Expression %a in %a is not an array" 
                    A.pp_print_expr e1
                    A.pp_print_position p))

          | _, Expr _ -> 

            (* Fail *)
            raise 
              (Failure 
                 (Format.asprintf 
                    "Expression %a in %a is not an array" 
                    A.pp_print_expr e2
                    A.pp_print_position p)))

    | A.RecordConstruct (p, t, l) -> 

      (

        let indexes = 

          try 

            List.map 
              (function (i, _) -> 

                (i, List.assoc (I.add_index t i) basic_types))
              (List.assoc t indexed_types)

          with Not_found -> 

            (* Fail *)
            raise 
              (Failure 
                 (Format.asprintf 
                    "Record type %a in %a is not defined" 
                    I.pp_print_ident t
                    A.pp_print_position p))

        in

        let l' = 
          List.fold_left
            (fun a (i, e) -> 

               if List.mem_assoc (I.index_of_ident i) a then 

                 (* Fail *)
                 raise 
                   (Failure 
                      (Format.asprintf 
                         "Record field %a assigned twice in %a" 
                         I.pp_print_ident i
                         A.pp_print_position p));


               match check_expr e with 

                 | Expr ({ expr_type = t' } as e) -> 

                   let t = 

                     try 

                       List.assoc (I.index_of_ident i) indexes 

                     with Not_found ->  

                       (* Fail *)
                       raise 
                         (Failure 
                            (Format.asprintf 
                               "Record type %a in %a does not have a field %a" 
                               I.pp_print_ident t
                               A.pp_print_position p
                               I.pp_print_ident i))

                   in

                   if check_type t' t then

                     (I.index_of_ident i, e) :: a

                   else

                     (* Fail *)
                     raise 
                       (Failure 
                          (Format.asprintf 
                             "Type mismatch at record field %a in %a" 
                             I.pp_print_ident i
                             A.pp_print_position p))


                 | IndexedExpr l -> 

                   List.fold_left 
                     (fun a (j, ({ expr_type = t' } as e)) ->

                        let i' = I.index_of_ident i @ j in

                        let t = 

                          try 

                            List.assoc i' indexes 

                          with Not_found ->  

                            (* Fail *)
                            raise 
                              (Failure 
                                 (Format.asprintf 
                                    "Record type %a in %a does not have a field %a" 
                                    I.pp_print_ident t
                                    A.pp_print_position p
                                    I.pp_print_index i'))

                        in

                        if check_type t' t then 

                          (i', e) :: a

                        else

                          (* Fail *)
                          raise 
                            (Failure 
                               (Format.asprintf 
                                  "Type mismatch at record field %a in %a" 
                                  I.pp_print_ident i
                                  A.pp_print_position p)))
                     a
                     l)
            []
            l
        in

        if 

          List.for_all 
            (fun (i, _) -> List.mem_assoc i l')
            indexes 

        then 

          IndexedExpr l'

        else 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Not all fields of record type %a assigned in %a" 
                  I.pp_print_ident t
                  A.pp_print_position p)))

    | A.Not (p, e) -> 

      let eval = function 

        | { expr_sim = E.True } as expr -> 

          { expr with expr_sim = E.t_false }

        | { expr_sim = E.False } as expr -> 

          { expr with expr_sim = E.t_true }

        | { expr_sim = e; expr_type = T.Bool } as expr -> 

          { expr with expr_sim = E.mk_not e }

        | _ ->

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a must have type bool" 
                  A.pp_print_expr e
                  A.pp_print_position p))

      in

      unary_apply_to 
        eval
        (check_expr e)

    | A.And (p, e1, e2) -> 

      let eval = function 

        | { expr_sim = E.True }, 
          ({ expr_sim = e; expr_type = T.Bool } as expr2) -> 

          expr2

        | ({ expr_sim = e; expr_type = T.Bool } as expr1),
          { expr_sim = E.True } ->

          expr1

        | ({ expr_sim = E.False } as expr1), 
          { expr_sim = e; expr_type = T.Bool } -> 

          expr1

        | { expr_sim = e; expr_type = T.Bool },
          ({ expr_sim = E.False } as expr2) ->

          expr2

        | { expr_sim = e1; expr_type = T.Bool; expr_clock = c },
          { expr_sim = e2; expr_type = T.Bool } -> 

          { expr_sim = E.mk_and e1 e2; 
            expr_type = T.t_bool; 
            expr_clock = c }

        | { expr_type = T.Bool },  _ ->

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a must have type bool" 
                  A.pp_print_expr e2
                  A.pp_print_position p))

        | _ ->

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a must have type bool" 
                  A.pp_print_expr e2
                  A.pp_print_position p))

      in

      binary_apply_to 
        p
        eval
        (check_expr e1, check_expr e2)

    | A.Or (p, e1, e2) -> 

      let eval = function 

        | { expr_sim = E.False }, 
          ({ expr_sim = e; expr_type = T.Bool } as expr2) -> 

          expr2

        | ({ expr_sim = e; expr_type = T.Bool } as expr1),
          { expr_sim = E.False } ->

          expr1

        | ({ expr_sim = E.True } as expr1), 
          { expr_sim = e; expr_type = T.Bool } -> 

          expr1

        | { expr_sim = e; expr_type = T.Bool },
          ({ expr_sim = E.True } as expr2) ->

          expr2

        | { expr_sim = e1; expr_type = T.Bool; expr_clock = c },
          { expr_sim = e2; expr_type = T.Bool } -> 

          { expr_sim = E.mk_or e1 e2; 
            expr_type = T.t_bool; 
            expr_clock = c }

        | { expr_type = T.Bool },  _ ->

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a must have type bool" 
                  A.pp_print_expr e2
                  A.pp_print_position p))

        | _ ->

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a must have type bool" 
                  A.pp_print_expr e2
                  A.pp_print_position p))

      in

      binary_apply_to 
        p
        eval
        (check_expr e1, check_expr e2)

    | A.Xor (p, e1, e2) -> 

      let eval = function 

        | ({ expr_sim = E.False }, 
           ({ expr_type = T.Bool } as expr2)) -> 

          expr2

        | (({ expr_type = T.Bool } as expr1),
           { expr_sim = E.False }) ->

          expr1

        | ({ expr_sim = E.True } as expr1, 
                                    { expr_sim = E.True }) -> 

          { expr1 with expr_sim = E.t_false }

        | ({ expr_sim = E.True }, 
           ({ expr_sim = e; expr_type = T.Bool } as expr2)) -> 

          { expr2 with expr_sim = E.mk_not e }

        | ({ expr_sim = e; expr_type = T.Bool } as expr1,
                                                   { expr_sim = E.True }) -> 

          { expr1 with expr_sim = E.mk_not e }

        | { expr_sim = e1; expr_type = T.Bool; expr_clock = c },
          { expr_sim = e2; expr_type = T.Bool } -> 

          { expr_sim = E.mk_xor e1 e2; 
            expr_type = T.t_bool; 
            expr_clock = c }

        | { expr_type = T.Bool },  _ ->

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a must have type bool" 
                  A.pp_print_expr e2
                  A.pp_print_position p))

        | _ ->

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a must have type bool" 
                  A.pp_print_expr e2
                  A.pp_print_position p))

      in

      binary_apply_to 
        p
        eval
        (check_expr e1, check_expr e2)

    | A.Impl (p, e1, e2) -> 

      let eval = function 

        | (({ expr_sim = E.False } as expr1), 
           { expr_sim = e; expr_type = T.Bool }) -> 

          { expr1 with expr_sim = E.t_true }

        | ({ expr_sim = E.True }, 
           ({ expr_sim = e; expr_type = T.Bool } as expr2)) -> 

          expr2

        | ({ expr_sim = e; expr_type = T.Bool } as expr1,
                                                   { expr_sim = E.False }) ->

          { expr1 with expr_sim = E.mk_not e }

        | ({ expr_type = T.Bool },
           ({ expr_sim = E.True } as expr2)) ->

          expr2

        | { expr_sim = e1; expr_type = T.Bool; expr_clock = c },
          { expr_sim = e2; expr_type = T.Bool } -> 

          { expr_sim = E.mk_impl e1 e2; 
            expr_type = T.t_bool; 
            expr_clock = c }

        | { expr_type = T.Bool },  _ ->

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a must have type bool" 
                  A.pp_print_expr e2
                  A.pp_print_position p))

        | _ ->

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a must have type bool" 
                  A.pp_print_expr e2
                  A.pp_print_position p))

      in

      binary_apply_to 
        p
        eval
        (check_expr e1, check_expr e2)

    (* TODO *)
    | A.OneHot _ -> assert false 

    | A.Uminus (p, e) -> 

      let eval = function 

        | { expr_sim = E.Int d } as expr -> 

          { expr with expr_sim = E.mk_int (- d) }

        | { expr_sim = E.Real f } as expr -> 

          { expr with expr_sim = E.mk_real (-. f) }

        | { expr_sim = e; expr_type = T.Int } as expr -> 

          { expr with expr_sim = E.mk_uminus e }

        | { expr_sim = e; expr_type = T.Real } as expr -> 

          { expr with expr_sim = E.mk_uminus e }

        | { expr_sim = e; expr_type = T.IntRange (l, u) } as expr -> 

          { expr with expr_sim = E.mk_uminus e; expr_type = T.mk_int_range (- u) (- l)  }

        | _ ->

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a must have type int or real" 
                  A.pp_print_expr e
                  A.pp_print_position p))

      in

      unary_apply_to 
        eval
        (check_expr e)

    | A.Mod (p, e1, e2) -> 

      let eval = function 

        | (({ expr_sim = E.Int d1 } as expr1),
           { expr_sim = E.Int d2 }) -> 

          { expr1 with expr_sim = E.mk_int (d1 mod d2) }

        | ({ expr_sim = e1; expr_type = T.Int } as expr1,
                                                   { expr_sim = e2; expr_type = T.Int }) ->

          { expr1 with expr_sim = E.mk_mod e1 e2 }

        | _ ->

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a must have type int" 
                  A.pp_print_expr e2
                  A.pp_print_position p))

      in

      binary_apply_to 
        p
        eval
        (check_expr e1, check_expr e2)

    | A.Times (p, e1, e2) -> 

      let eval = function 

        | (({ expr_sim = E.Int d1 } as expr1),
           { expr_sim = E.Int d2 }) -> 

          { expr1 with expr_sim = E.mk_int (d1 * d2) }

        | (({ expr_sim = E.Real d1 } as expr1),
           { expr_sim = E.Real d2 }) -> 

          { expr1 with expr_sim = E.mk_real (d1 *. d2) }

        | ({ expr_sim = e1; expr_type = T.Int } as expr1,
                                                   { expr_sim = e2; expr_type = T.Int }) ->

          { expr1 with expr_sim = E.mk_times e1 e2 }

        | ({ expr_sim = e1; expr_type = T.Real } as expr1,
                                                    { expr_sim = e2; expr_type = T.Real }) ->

          { expr1 with expr_sim = E.mk_times e1 e2 }

        | _ ->

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a must have type int" 
                  A.pp_print_expr e2
                  A.pp_print_position p))

      in

      binary_apply_to 
        p
        eval
        (check_expr e1, check_expr e2)

    | A.Plus (p, e1, e2) -> 

      (* TODO: adjust integer ranges *)
      let eval = function 

        | (({ expr_sim = E.Int d1 } as expr1),
           { expr_sim = E.Int d2 }) -> 

          { expr1 with expr_sim = E.mk_int (d1 + d2) }

        | (({ expr_sim = E.Real d1 } as expr1),
           { expr_sim = E.Real d2 }) -> 

          { expr1 with expr_sim = E.mk_real (d1 +. d2) }

        | ({ expr_sim = e1; expr_type = T.Int } as expr1,
                                                   { expr_sim = e2; expr_type = T.Int }) ->

          { expr1 with expr_sim = E.mk_plus e1 e2 }

        | ({ expr_sim = e1; expr_type = T.Real } as expr1,
                                                    { expr_sim = e2; expr_type = T.Real }) ->

          { expr1 with expr_sim = E.mk_plus e1 e2 }

        | _ ->

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a must have type int" 
                  A.pp_print_expr e2
                  A.pp_print_position p))

      in

      binary_apply_to 
        p
        eval
        (check_expr e1, check_expr e2)


  in


  let int_const_of_expr e = match check_expr e with
    | Expr { expr_sim = E.Int d } -> d
    | _ -> 

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Expression %a in %a must be a constant integer" 
              A.pp_print_expr e
              A.pp_print_position A.dummy_pos))

  in
*)

  (* Return true if type [t] was already declared *)
  let type_is_declared t = 

    (* Check if [t] is a basic types *)
    (List.mem_assoc t basic_types) ||

    (* Check is [t] is an indexed type *)
    (List.mem_assoc t indexed_types) || 

    (* Check if [t] is a free type *)
    (List.mem t free_types) 

  in

(*
  (* Convert a parsed type to a built-in type *)
  let lustre_type_of_ast_type = function

    | A.Bool -> T.t_bool

    | A.Int -> T.t_int

    | A.Real -> T.t_real

    | A.IntRange (i, j) -> 

      (* Evaluate expression for lower bound to a constant *)
      let ci = int_const_of_expr i in

      (* Evaluate expression for upper bound to a constant *)
      let cj = int_const_of_expr j in

      (* Construct an integer range type *)
      T.mk_int_range ci cj

    | A.EnumType l -> T.mk_enum l

    | A.UserType t when List.mem_assoc t basic_types -> 

      List.assoc t basic_types

    | A.UserType t -> T.mk_free_type t

    (* All other types are nested and must be flattended to indexed types *)
    | _ -> raise (Invalid_argument "lustre_type_of_ast_type")

  in
*)

  (* ******************************************************************** *)
  (* Alias type declarations                                              *)
  (* ******************************************************************** *)





  (* ******************************************************************** *)
  (* Helper functions for type expressions                                *)
  (* ******************************************************************** *)





(*
  let check_alias_type_decl t t' decls = 

    if       

      (* Type t must not be declared *)
      type_is_declared t

    then

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Type %a defined in %a is redeclared in %a" 
              I.pp_print_ident t
              A.pp_print_position A.dummy_pos
              A.pp_print_position A.dummy_pos));


    (* Change state or add new declarations *)
    (match t' with 

      (* ********************************************************** *)

      (* type t = struct { i1: t1; ...; in: tn };

         Expand to declarations

         type t.i1 = t1;
         ...
         type t.in = tn;

      *)
      | A.RecordType l -> 

        (* Push declarations for indexed identifiers *)
        let decls' = 

          List.fold_left

            (fun a (j, s) -> 

               (* Construct an index of an identifier *)
               let idx = I.index_of_ident j in

               (* Fail if type of field is the type defined

                  Need this check because record definitions are
                  unfolded; no other check is needed, since nesting of
                  records can only happen through an alias type that
                  must have been defined before. *)
               if s = A.UserType t then 

                 (* Fail *)
                 raise 
                   (Failure 
                      (Format.asprintf 
                         "Type %a is defined recursively in %a" 
                         I.pp_print_ident t
                         A.pp_print_position A.dummy_pos));

               (* Expand to declaration [type t.j = s] *)
               ((A.TypeDecl 
                   (A.AliasType (I.add_index t idx, s))) :: a))

            decls
            l

        in

        (* State unchanged, new declarations pushed *)
        (state, decls')


      (* ********************************************************** *)

      (* type t = [ t1, ..., tn ];

         Expand to declarations

         type t[0] = t1;
         ...
         type t[n-1] = tn;

      *)
      | A.TupleType l -> 

        (* Push declarations for indexed identifiers *)
        let decls', _ = 

          List.fold_left

            (fun (a, j) s -> 

               (* Construct an index of an identifier *)
               let idx = I.index_of_int j in

               (* Fail if type of field is the type defined

                  Need this check because record definitions are
                  unfolded; no other check is needed, since nesting of
                  records can only happen through an alias type that
                  must have been defined before. *)
               if s = A.UserType t then 

                 (* Fail *)
                 raise 
                   (Failure 
                      (Format.asprintf 
                         "Type %a is defined recursively in %a" 
                         I.pp_print_ident t
                         A.pp_print_position A.dummy_pos));

               (* Expand to declaration to [type t[j] = s] *)
               ((A.TypeDecl 
                   (A.AliasType (I.add_index t idx, s))) :: a, 
                succ j))

            (decls, 0)
            l
        in

        (* State unchanged, new declarations pushed *)
        (state, decls')


      (* ********************************************************** *)

      (* type t = s^e;

         Expand to declarations

         type t[0] = s;
         ...
         type t[e-1] = s;

      *)
      | A.ArrayType (s, e) -> 

        (* Evaluate size of array to a constant integer *)
        let n = int_const_of_ast_expr context e in

        (* Array size must must be at least one *)
        if n <= 0 then 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a must be positive as array size in %a" 
                  A.pp_print_expr e
                  A.pp_print_position A.dummy_pos));

        (* Append type declarations for indexed identifiers *)
        let rec aux accum = function

          (* All array fields consumed *)
          | 0 -> accum

          (* An array field *)
          | i -> 

            (* Construct an index of an integer *)
            let idx = I.index_of_int (pred i) in

            (* Expand to declaration to [type t[j] = s] *)
            aux 
              (A.TypeDecl 
                 (A.AliasType (I.add_index t idx, s)) :: accum)
              (pred i)

        in

        (* Push declarations for indexed identifiers *)
        let decls' = aux decls n in

        (* State unchanged, new declarations pushed *)
        (state, decls')


      (* ********************************************************** *)

      (* type t = t';

         If t' was defined as 

         type t' = t'';

         expand to

         type t = t'';

      *)
      | A.UserType t' when List.mem_assoc t' basic_types -> 

        (* Replace declaration with alias replaced by actual type *)
        let decls' = 
          A.TypeDecl 
            (A.AliasType 
               (t, 
                ast_type_of_lustre_type (List.assoc t' basic_types))) :: 
            decls
        in

        (* State unchanged, new declarations pushed *)
        (state, decls')


      (* type t = t';

         If there were definitions

         type t'.i1 = t1;
         ...
         type t'.in = tn;

         expand to 

         type t.i1 = t1;
         ...
         type t.in = tn;

      *)
      | A.UserType t' when List.mem_assoc t' indexed_types -> assert false

(*
        (* Push declarations for indexed identifiers *)
        let decls' = 
          List.fold_left 
            (fun a (j, s) -> 
               (A.TypeDecl 
                  (A.AliasType (I.add_index t j, s))) :: a)
            decls
            (List.assoc t' indexed_types) 
        in 

        (* State unchanged, new declarations pushed *)
        (state, decls')
*)

      (* type t = t';

         If t' was defined as

         type t';

         expand to

         type t = t'';

      *)
      | A.UserType t' when List.mem t' free_types ->  assert false

(*
        (* Add association of type to free type *)
        let basic_types' = 
          (t, T.mk_free_type t') :: basic_types 
        in

        (* Add types of all suffixes *)
        let indexed_types' = add_to_indexed_types t (A.UserType t') in

        (* Changed aliases of basic types *)
        ({ state with 
             basic_types = basic_types'; 
             indexed_types = indexed_types' }, 
         decls)
*)

      (* type t = t';

         if t' is not in basic_types, indexed_types or free_types 

      *)
      | A.UserType t' ->  

        (* Fail *)
        raise 
          (Failure 
             (Format.asprintf 
                "Type %a in %a is not declared" 
                I.pp_print_ident t'
                A.pp_print_position A.dummy_pos))


      (* ********************************************************** *)

      (* type t = t'; 

         where t' is a basic type. *)
      | A.Bool 
      | A.Int 
      | A.Real 
      | A.IntRange _ 
      | A.EnumType _ as t' -> assert false 

(*
        (* Basic type of type in AST *)
        let t'' = lustre_type_of_ast_type t' in

        (* Add alias for basic type *)
        let basic_types' = (t, t'') :: basic_types in

        (* Add types of all suffixes *)
        let indexed_types' = add_to_indexed_types t t' in

        (* Add enum constants to typing context *)
        let type_ctx' = match t' with 

          (* Type is an enumeration *)
          | A.EnumType l -> 

            List.fold_left
              (fun a e -> 

                 try 

                   (* Get type of constant *)
                   let s = List.assoc e a in 

                   (* Skip if constant declared with the same (enum) type *)
                   if t'' = s then a else

                     (* Fail *)
                     raise 
                       (Failure 
                          (Format.asprintf 
                             "Enum constant %a declared with\
                              different type in %a" 
                             I.pp_print_ident e
                             A.pp_print_position A.dummy_pos));

                   (* Constant not declared *)
                 with Not_found -> 

                   (* Push constant to typing context *)
                   (e, t'') :: a)
              type_ctx
              l

          (* Other basic types do not change typing context *)
          | _ -> type_ctx

        in

        (* Changes to state *)
        ({ state 
           with 
               basic_types = basic_types'; 
               indexed_types = indexed_types';
               type_ctx = type_ctx' }, 
         decls)
*)

    )

  in

  (* ******************************************************************** *)
  (* Free type declarations                                               *)
  (* ******************************************************************** *)

  (* type t; 

     t is a free type *)
  let check_free_type_decl t decls = 

    if

      (* Type t must not be declared *)
      type_is_declared t

    then

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Type %a defined in %a is redeclared in %a" 
              I.pp_print_ident t
              A.pp_print_position A.dummy_pos
              A.pp_print_position A.dummy_pos));

    (* Add type identifier to free types *)
    let free_types' = t :: free_types in

    (* Changes to state *)
    ({ state with free_types = free_types' }, decls)

  in

*)

  (* ******************************************************************** *)
  (* Free constant declarations                                           *)
  (* ******************************************************************** *)
(*
  (* const c : t; 

     Free constant of basic type *)
  let check_free_const_decl c t decls = 

    (* FIXME: Need to add to index_ctx if type t is indexed *)

    if

      (* Identifier must not be declared *)
      List.mem_assoc c type_ctx 

    then

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Identifier %a is redeclared as free constant in %a" 
              I.pp_print_ident c
              A.pp_print_position A.dummy_pos));


    match t with 

      (* const c : t'; 

         where t' is a basic type. *)
      | A.Bool 
      | A.Int 
      | A.Real 
      | A.IntRange _ 
      | A.EnumType _ as t' -> 

        (* Add to typing context *)
        let type_ctx' = (c, lustre_type_of_ast_type t') :: type_ctx in

        (* State modified *)
        ({ global_context with type_ctx = type_ctx' }, decls)


      (* const c : t'; 

         where t' is a basic type *)
      | A.UserType t' when List.mem_assoc t' basic_types -> 

        (* Add to typing context *)
        let type_ctx' = (c, List.assoc t' basic_types) :: type_ctx in

        (* State modified *)
        ({ global_context with type_ctx = type_ctx' }, decls)


      (* const c : t'; 

         where t' is an indexed type *)
      | A.UserType t' when List.mem_assoc t' indexed_types -> assert false

(*
        (* Push declarations for indexed identifiers *)
        let decls' = 
          List.fold_left 
            (fun a (j, s) -> 

               (* Expand to declaration [const c.j] *)
               (A.ConstDecl 
                  (A.FreeConst (I.add_index c j, s))) :: a)

            decls 
            (List.assoc t' indexed_types) 
        in 

        (* State unchanged, new declarations pushed *)
        (state, decls')
*)

      (* const c : t'; 

         where t' is a free type. 

      *)
      | A.UserType t' when List.mem t' free_types -> 


        (* Add to typing context *)
        let type_ctx' = (c, T.mk_free_type t') :: type_ctx in

        (* State modified *)
        ({ global_context with type_ctx = type_ctx' }, decls)


      (* const c : t';

         where t' is not in basic_types, indexed_types or free_types 

      *)
      | A.UserType t' ->  

        (* Fail *)
        raise 
          (Failure 
             (Format.asprintf 
                "Type %a in %a is not declared" 
                I.pp_print_ident t'
                A.pp_print_position A.dummy_pos))


      (* const c : t';

         where t' is a record type

      *)
      | A.RecordType l -> 

        (* Push declarations for indexed identifiers *)
        let decls' = 

          List.fold_left

            (fun a (j, s) -> 

               (* Construct an index of an identifier *)
               let idx = I.index_of_ident j in

               (* Expand to declaration [const t.j] *)
               ((A.ConstDecl 
                   (A.FreeConst (I.add_index c idx, s))) :: a))

            decls
            l

        in

        (* State unchanged, new declarations pushed *)
        (global_context, decls')


      (* const c : t';

         where t' is an array type

      *)
      | A.ArrayType (s, e) ->

        (* Evaluate size of array to a constant integer *)
        let n = int_const_of_ast_expr context e in

        (* Array size must must be at least one *)
        if n <= 0 then 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a must be positive as array size in %a" 
                  A.pp_print_expr e
                  A.pp_print_position A.dummy_pos));

        (* Append type declarations for indexed identifiers *)
        let rec aux accum = function

          (* All array fields consumed *)
          | 0 -> accum

          (* An array field *)
          | i -> 

            (* Construct an index of an integer *)
            let idx = I.index_of_int (pred i) in

            (* Expand to declaration to [const c[j]] *)
            aux 
              (A.ConstDecl 
                 (A.FreeConst (I.add_index c idx, s)) :: accum)
              (pred i)

        in

        (* Push declarations for indexed identifiers *)
        let decls' = aux decls n in

        (* State unchanged, new declarations pushed *)
        (global_context, decls')


      (* const c : t';

         where t' is a tuple type

      *)
      | A.TupleType l -> 

        (* Push declarations for indexed identifiers *)
        let decls', _ = 

          List.fold_left

            (fun (a, j) s -> 

               (* Construct an index of an identifier *)
               let idx = I.index_of_int j in

               (* Expand to declaration to [const c[j]] *)
               ((A.ConstDecl 
                   (A.FreeConst (I.add_index c idx, s))) :: a, 
                succ j))

            (decls, 0)
            l
        in

        (* State unchanged, new declarations pushed *)
        (global_context, decls')


  in

  (* ******************************************************************** *)
  (* Untyped constant declarations                                        *)
  (* ******************************************************************** *)

  (* const c [ : t ]  = e; *)
  let check_const_decl c t e decls = 

    try

      (match check_expr e with 

        (* Integer constant *)
        | Expr { expr_sim = (E.Int d as e); expr_type = t' }
          when 
            match t with 
              | None -> true 
              | Some t -> check_type t' (lustre_type_of_ast_type t) -> 

          ({ global_context with 
               consts = (c, e) :: consts; 
               type_ctx = (c, T.mk_int_range d d) :: type_ctx },
           decls)

        (* Real constant *)
        | Expr { expr_sim = (E.Real f as e); expr_type = t'  }
          when 
            match t with 
              | None -> true 
              | Some t -> check_type t' (lustre_type_of_ast_type t) -> 

          ({ global_context with 
               consts = (c, e) :: consts; 
               type_ctx = (c, T.t_real) :: type_ctx },
           decls)

        (* Boolean constant *)
        | Expr { expr_sim = (E.True as e); expr_type = t' }
        | Expr { expr_sim = (E.False as e); expr_type = t' } 
          when 
            match t with 
              | None -> true 
              | Some t -> check_type t' (lustre_type_of_ast_type t) -> 

          ({ global_context with 
               consts = (c, e) :: consts; 
               type_ctx = (c, T.t_bool) :: type_ctx },
           decls)

        (* Enum constant *)
        | Expr { expr_sim = e; expr_type = (T.Enum _ as t') } 
          when 
            match t with 
              | None -> true 
              | Some t -> check_type t' (lustre_type_of_ast_type t) -> 

          ({ global_context with 
               consts = (c, e) :: consts; 
               type_ctx = (c, t') :: type_ctx },
           decls)

        (* Constant of free type *)
        | Expr { expr_sim = e; expr_type = (T.FreeType _ as t') } 
          when 
            match t with 
              | None -> true 
              | Some t -> check_type t' (lustre_type_of_ast_type t) -> 

          ({ global_context with 
               consts = (c, e) :: consts; 
               type_ctx = (c, t') :: type_ctx },
           decls)

        (* Constants with failed type check *)
        | Expr { expr_sim = E.Int _ } 
        | Expr { expr_sim = E.Real _ }
        | Expr { expr_sim = E.True }
        | Expr { expr_sim = E.False } 
        | Expr { expr_type = T.Enum _ } 
        | Expr { expr_type = T.FreeType _ } -> 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Type mismatch at constant declaration of %a in %a" 
                  I.pp_print_ident c
                  A.pp_print_position A.dummy_pos))


        (* No other expression can be constant *)
        | Expr _ -> 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a is not constant" 
                  A.pp_print_expr e
                  A.pp_print_position A.dummy_pos))

        (* List of indexed values *)
        | IndexedExpr l -> 

          (* Associate index with identifier of constant in index_ctx *)
          let rec aux i accum = function 

            (* Identifier of constant not found: create new entry *)
            | [] -> (c, [i]) :: accum

            (* Found some indexes for constant identifier: add index *)
            | (d, l) :: tl when d = c -> 

              List.rev_append tl ((c, i :: l) :: accum)

            (* Not matching indentifier *)
            | h :: tl -> 

              aux i (h :: accum) tl

          in


          (* Push declarations for indexed identifiers *)
          let (type_ctx', index_ctx', consts') = 
            List.fold_left 
              (fun 
                (type_ctx, index_ctx, consts) 
                (j, { expr_sim; expr_type }) -> 

                (

                  (* Add indexed identifier to type context *)
                  (I.add_index c j, expr_type) :: type_ctx,

                  (* Append index to index context *)
                  aux j [] index_ctx,

                  (* Expand to declaration [const c.j] *)
                  (I.add_index c j, expr_sim) :: consts

                ))

              (type_ctx, index_ctx, consts)
              l
          in 

          (* State with extended index map *)
          ({ global_context with 
               type_ctx = type_ctx'; 
               index_ctx = index_ctx'; 
               consts = consts' }, 
           decls)

      )

    with Invalid_argument "lustre_type_of_ast_type" -> 

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Type mismatch at constant declaration of %a in %a" 
              I.pp_print_ident c
              A.pp_print_position A.dummy_pos))

  in
*)
  function

    (* All declarations processed, return result *)
    | [] -> global_context

    (* Declaration of a type as alias or free *)
    | (A.TypeDecl (A.AliasType (ident, _) as type_decl) as decl) :: decls
    | (A.TypeDecl (A.FreeType ident as type_decl) as decl) :: decls -> 

      (* Output type declaration *)
      Format.printf "-- %a@." A.pp_print_declaration decl;

      if       

        (* Type t must not be declared *)
        type_is_declared ident

      then

        (* Fail *)
        raise 
          (Failure 
             (Format.asprintf 
                "Type %a is redeclared in %a" 
                I.pp_print_ident ident
                A.pp_print_position A.dummy_pos));

      (* Change context with alias type declaration *)
      let global_context' = match type_decl with 

        (* Identifier is an alias for a type *)
        | A.AliasType (ident, type_expr) -> 

          (* Add alias type declarations for the possibly indexed
             type expression *)
          let global_context' = 
            fold_ast_type 
              global_context
              (add_alias_type_decl ident) 
              global_context 
              type_expr
          in

          (* Return changed context and unchanged declarations *)
          global_context'

        (* Identifier is a free type *)
        | A.FreeType ident -> 

          (* Add type identifier to free types *)
          let free_types' = ident :: free_types in

          (* Changes to global context *)
          { global_context with free_types = free_types' }

      in

      (* Recurse for next declarations *)
      check_declarations global_context' decls

    (* Declaration of a typed, untyped or free constant *)
    | (A.ConstDecl (A.FreeConst (ident, _) as const_decl) as decl) :: decls 
    | (A.ConstDecl (A.UntypedConst (ident, _) as const_decl) as decl) :: decls 
    | (A.ConstDecl (A.TypedConst (ident, _, _) as const_decl) as decl) :: decls ->

      (* Output constant declaration *)
      Format.printf "-- %a@." A.pp_print_declaration decl;

      if

        (* Identifier must not be declared *)
        List.mem_assoc ident type_ctx 

      then

        (* Fail *)
        raise 
          (Failure 
             (Format.asprintf 
                "Identifier %a is redeclared as constant in %a" 
                I.pp_print_ident ident
                A.pp_print_position A.dummy_pos));

      (* Change context with constant declaration *)
      let global_context' = match const_decl with 

        (* Identifier is a free constant with given type *)
        | A.FreeConst (ident, type_expr) -> 

          let global_context' = global_context 
          (*            fold_ast_type 
                        (add_const_decl ident)
                        global_context 
                        type_expr *)
          in


          global_context'

        (* Identifier is a constant without given type *)
        | A.UntypedConst (ident, expr) -> 

          let expr_val = eval_ast_expr global_context expr in

          let consts' = 
            List.fold_left
              (fun a (j, e) -> (I.add_index ident j, e) :: a)
              consts
              expr_val
          in

          let type_ctx' = 
            List.fold_left
              (fun a (j, { E.expr_type = t }) -> 
                 (I.add_index ident j, t) :: a)
              type_ctx
              expr_val
          in

          let index_ctx' = 
            List.fold_left
              (fun a (j, _) -> 
                 add_to_prefix_map a (I.add_index ident j) ())
              index_ctx
              expr_val
          in

          { global_context with 
              consts = consts';
              type_ctx = type_ctx';
              index_ctx = index_ctx' }


        (* Identifier is a constant with given type *)
        | A.TypedConst (ident, expr, type_expr) -> 

          let global_context' = global_context 
          (*            fold_ast_type 
                        (add_const_decl ident)
                        global_context 
                        type_expr *)
          in

          let global_context'' = global_context 
          (*            fold_ast_expr 
                        (add_const_val ident)
                        global_context
                        expr *)
          in

          global_context''

      in

      (* Recurse for next declarations *)
      check_declarations global_context' decls


    | (A.NodeDecl 
         (node_ident, 
          [], 
          inputs, 
          outputs, 
          vars, 
          equations, 
          contract)) as decl :: decls ->

      (* Output node declaration *)
      Format.printf "-- %a@." A.pp_print_declaration decl;
      
      (* Add declarations to global context *)
      let local_context, node_context = global_context, init_node_context
(*        parse_node_signature
          inputs 
          outputs
          vars
          global_context *)
      in

      (* Recurse for next declarations *)
      check_declarations global_context decls


    | d :: decls ->

      (* Output const declaration *)
      Format.printf "-- skipped: %a@." A.pp_print_declaration d;

      (* Recurse for next declarations *)
      check_declarations global_context decls


let check_program p = 
  let global_context = check_declarations init_lustre_context p in

  Format.printf "%a@." pp_print_lustre_context global_context


(* 
   Local Variables:
   compile-command: "make -C .. lustre-checker"
   indent-tabs-mode: nil
   End: 
*)
  
