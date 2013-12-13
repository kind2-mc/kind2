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


(* Identifier for new variables from abstrations *)
let new_var_ident = I.mk_string_id "__abs" 

(* Identifier for new variables from node calls *)
let new_call_ident = I.mk_string_id "__call" 


(* Sort a list indexed expressions *)
let sort_indexed_pairs (list : (I.index * 'a) list) : (I.index * 'a) list = 
  List.sort (fun (i1, _) (i2, _) -> I.compare_index i1 i2) list



type node_context = 

  { 

    (* Input variables of node, some flagged as constant

       The order of the list is important *)
    node_inputs : 
      (LustreIdent.t * (((LustreIdent.index * LustreType.t) list) * bool)) list;

    (* Output variables of node 

       The order of the list is important *)
    node_outputs : 
      (LustreIdent.t * ((LustreIdent.index * LustreType.t) list)) list;
    
    (* Local variables of node 

       The order of the list is irrelevant. Local constants are
       propagated and do not need to be stored. *)
    node_vars :
      (LustreIdent.t * ((LustreIdent.index * LustreType.t) list)) list;

    (* Equations for local and output variables *)
    node_eqs : (LustreIdent.t * LustreExpr.t) list;

    (* Node calls: variables capturing the outputs, name of the called
       node and expressions for input parameters *)
    node_calls : 
      ((LustreIdent.t * LustreType.t) list * LustreIdent.t * LustreExpr.t list) list;

    (* Assertions of node *)
    node_asserts : LustreExpr.t list;

    (* Proof obligations for node *)
    node_props : LustreExpr.t list;

    (* Contract for node, assumptions *)
    node_requires : LustreExpr.t list;

    (* Contract for node, guarantees *)
    node_ensures : LustreExpr.t list;

    (* Node is annotated as main node *)
    node_is_main : bool }


let init_node_context = 
  { node_inputs = [];
    node_outputs = [];
    node_vars = [];
    node_eqs = [];
    node_calls = [];
    node_asserts = [];
    node_props = [];
    node_requires = [];
    node_ensures = [];
    node_is_main = false }


let pp_print_node_input ppf (ident, (index_list, is_const)) =

  Format.fprintf ppf
    "%t%a"
    (function ppf -> if is_const then Format.fprintf ppf "const ")
    (pp_print_list 
       (fun ppf (j, t) -> 
         Format.fprintf ppf 
           "%a: %a" 
           I.pp_print_ident (I.add_index ident j)
           T.pp_print_lustre_type t)
       ";@ ")
    index_list


let pp_print_node_output ppf (ident, index_list) =

  Format.fprintf ppf
    "%a"
    (pp_print_list 
       (fun ppf (j, t) -> 
         Format.fprintf ppf 
           "%a: %a" 
           I.pp_print_ident (I.add_index ident j)
           T.pp_print_lustre_type t)
       ";@ ")
    index_list

let pp_print_node_var ppf (ident, index_list) =

  Format.fprintf ppf
    "%a"
    (pp_print_list 
       (fun ppf (j, t) -> 
         Format.fprintf ppf 
           "%a: %a;" 
           I.pp_print_ident (I.add_index ident j)
           T.pp_print_lustre_type t)
       "@ ")
    index_list

let pp_print_node_assert ppf expr = 

  Format.fprintf ppf
    "@[<hv 2>assert@ %a;@]"
    E.pp_print_lustre_expr expr


let pp_print_node_eq ppf (ident, expr) = 

  Format.fprintf ppf
    "@[<hv 2>%a@ =@ %a;@]"
    I.pp_print_ident ident
    E.pp_print_lustre_expr expr


let pp_print_node_call ppf (out_vars, node, exprs) = 

  Format.fprintf ppf
    "@[<hv 2>%a@ =@ %a(%a);@]"
    (pp_print_list 
       (fun ppf (i, _) -> I.pp_print_ident ppf i)
       ",@ ") 
    out_vars
    I.pp_print_ident node
    (pp_print_list E.pp_print_lustre_expr ",@ ") exprs


let pp_print_node_prop ppf expr = 

  Format.fprintf ppf
    "@[<hv 2>--%%PROPERTY@ %a;@]"
    E.pp_print_lustre_expr expr


let pp_print_node_requires ppf expr = 

  Format.fprintf ppf
    "@[<hv 2>--@@requires@ %a;@]"
    E.pp_print_lustre_expr expr


let pp_print_node_ensures ppf expr = 

  Format.fprintf ppf
    "@[<hv 2>--@@ensures %a;@]"
    E.pp_print_lustre_expr expr


let pp_print_node_context 
    node_ident 
    ppf 
    { node_inputs; 
      node_outputs; 
      node_vars; 
      node_eqs; 
      node_calls; 
      node_asserts; 
      node_props; 
      node_requires; 
      node_ensures } = 

  Format.fprintf ppf 
    "@[<hv>@[<hv 2>node %a@ @[<hv 1>(%a)@]@;<1 -2>\
       returns@ @[<hv 1>(%a)@];@]@ \
     %t@,\
     @[<hv 2>let@ \
     %a@,\
     %a@,\
     %a@,\
     %a@,\
     %a@,\
     %a@;<1 -2>\
     tel;@]@]"  
    I.pp_print_ident node_ident
    (pp_print_list pp_print_node_input ";@ ") node_inputs
    (pp_print_list pp_print_node_output ";@ ") node_outputs
    (function ppf -> 
      if node_vars = [] then () else 
        Format.fprintf ppf 
          "@[<hv 2>var@ %a@]" 
          (pp_print_list pp_print_node_var "@ ") node_vars)
    (pp_print_list pp_print_node_requires "@ ") node_requires
    (pp_print_list pp_print_node_ensures "@ ") node_ensures
    (pp_print_list pp_print_node_prop "@ ") node_props
    (pp_print_list pp_print_node_assert "@ ") node_asserts
    (pp_print_list pp_print_node_call "@ ") node_calls
    (pp_print_list pp_print_node_eq "@ ") node_eqs
    



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



(* Return true if type [t] was already declared *)
let type_in_context { basic_types; indexed_types; free_types } t = 

  (* Check if [t] is a basic types *)
  (List.mem_assoc t basic_types) ||

  (* Check is [t] is an indexed type *)
  (List.mem_assoc t indexed_types) || 

  (* Check if [t] is a free type *)
  (List.mem t free_types) 


(* Return true if identifier [i] was already declared *)
let ident_in_context { type_ctx; index_ctx } i = 

  if 

    (* Identifier must not be reserved *)
    i = new_var_ident || i = new_call_ident 

  then

    (* Fail *)
    raise 
      (Failure 
         (Format.asprintf 
            "Identifier %a is reserved internal use in %a" 
            I.pp_print_ident new_var_ident
            A.pp_print_position A.dummy_pos))

  else

    (* In type context or a nested identifier *)
    (List.mem_assoc i type_ctx) || (List.mem_assoc i index_ctx)



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


(* Add enum constants to context if type is an enumeration *)
let add_enum_to_context type_ctx = function

  (* Type is an enumeration *)
  | T.Enum l as basic_type -> 
    
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

  (* Add enum constants to type context if type is an enumeration *)
  let type_ctx' = add_enum_to_context type_ctx basic_type in

  (* Changes to context *)
  { context with 
      basic_types = basic_types'; 
      indexed_types = indexed_types';
      type_ctx = type_ctx' }
  


(* ******************************************************************** *)
(* Evaluation of expressions                                            *)
(* ******************************************************************** *)

let rec eval_ast_expr'     
    mk_new_var_ident 
    mk_new_call_ident
    ({ basic_types; 
       indexed_types; 
       free_types; 
       type_ctx; 
       index_ctx; 
       consts;
       nodes } as context)
    result
    ((new_vars, new_calls) as new_defs) = 

  let eval_unary_ast_expr mk expr tl = 

    let expr', new_defs' = 
      unary_apply_to 
        mk_new_var_ident 
        mk_new_call_ident 
        context 
        new_defs 
        mk
        expr 
        result 
    in  

    (* Add expression to result *)
    eval_ast_expr' 
      mk_new_var_ident 
      mk_new_call_ident 
      context 
      expr'
      new_defs'
      tl

  in

  let eval_binary_ast_expr mk expr1 expr2 tl = 

    let expr', new_defs' = 
      binary_apply_to 
        mk_new_var_ident 
        mk_new_call_ident 
        context 
        new_defs 
        mk
        expr1 
        expr2 
        result 
    in  

    (* Add expression to result *)
    eval_ast_expr' 
      mk_new_var_ident 
      mk_new_call_ident 
      context 
      expr'
      new_defs'
      tl

  in

  function

    (* All expressions evaluated, return result *)
    | [] -> (result, new_defs)


    (* An identifier without indexes *)
    | (index, A.Ident (_, ident)) :: tl when 
        List.mem_assoc (I.add_index ident index) type_ctx -> 

      let ident' = I.add_index ident index in

      (* Construct expression *)
      let expr = 

        (* Return value of constant *)
        try List.assoc ident' consts with 

          (* Identifier is not constant *)
          | Not_found -> 

            (* Return variable of defined type on the base clock *)
            E.mk_var 
              ident' 
              (List.assoc ident' type_ctx) 
              E.base_clock

      in

      (* Add expression to result *)
      eval_ast_expr' 
        mk_new_var_ident 
        mk_new_call_ident 
        context 
        ((index, expr) :: result) 
        new_defs 
        tl


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
      eval_ast_expr' 
        mk_new_var_ident 
        mk_new_call_ident 
        context 
        result 
        new_defs 
        tl'


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
           eval_ast_expr' 
             mk_new_var_ident 
             mk_new_call_ident 
             context 
             result 
             new_defs 
             ((index, expr') :: tl)

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
           eval_ast_expr' 
             mk_new_var_ident 
             mk_new_call_ident 
             context 
             result 
             new_defs 
             ((index, expr') :: tl)

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
      eval_ast_expr' 
        mk_new_var_ident 
        mk_new_call_ident 
        context 
        ((index, E.t_true) :: result) 
        new_defs 
        tl


    (* Boolean constant true *)
    | (index, A.False pos) :: tl -> 

      (* Add expression to result *)
      eval_ast_expr'
        mk_new_var_ident 
        mk_new_call_ident 
        context
        ((index, E.t_false) :: result) 
        new_defs 
        tl


    (* Integer constant *)
    | (index, A.Num (pos, d)) :: tl -> 

      (* Add expression to result *)
      eval_ast_expr' 
        mk_new_var_ident 
        mk_new_call_ident 
        context 
        ((index, E.mk_int (int_of_string d)) :: result) 
        new_defs 
        tl


    (* Real constant *)
    | (index, A.Dec (pos, f)) :: tl -> 

      (* Add expression to result *)
      eval_ast_expr' 
        mk_new_var_ident 
        mk_new_call_ident 
        context 
        ((index, E.mk_real (float_of_string f)) :: result) 
        new_defs 
        tl


    (* Conversion to an integer  *)
    | (index, A.ToInt (pos, expr)) :: tl -> 

      eval_unary_ast_expr E.mk_to_int expr tl


    (* Conversion to an integer  *)
    | (index, A.ToReal (pos, expr)) :: tl -> 

      eval_unary_ast_expr E.mk_to_real expr tl


    | (index, A.ExprList (pos, expr_list)) :: tl -> 

      (* Treat as tuple *)
      eval_ast_expr' 
        mk_new_var_ident
        mk_new_call_ident 
        context 
        result
        new_defs 
        ((index, A.TupleExpr (pos, expr_list)) :: tl)


    (* Tuple constructor *)
    | (index, A.TupleExpr (pos, expr_list)) :: tl -> 

      let _, new_defs', result' = 

        (* Iterate over list of expressions *)
        List.fold_left
          (fun (i, new_defs, accum) expr -> 

             (* Evaluate one expression *)
             let expr', new_defs' = 
               eval_ast_expr 
                 mk_new_var_ident
                 mk_new_call_ident 
                 context 
                 new_defs 
                 expr
             in

             (* Index of counter *)
             let index = I.index_of_int i in

             (* Increment counter *)
             (succ i,

              (* Continue with added definitions *)
              new_defs',

              (* Append current index to each index of evaluated
                 expression *)
              List.fold_left 
                (fun a (j, e) -> (index @ j, e) :: a)
                accum
                expr'))

          (0, new_defs, result)
          expr_list
      in

      (* Continue with result added *)
      eval_ast_expr' 
        mk_new_var_ident
        mk_new_call_ident 
        context 
        result' 
        new_defs' 
        tl


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
      let expr_val, new_defs' = 
        eval_ast_expr 
          mk_new_var_ident 
          mk_new_call_ident 
          context 
          new_defs 
          expr 
      in 

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
      eval_ast_expr' 
        mk_new_var_ident
        mk_new_call_ident 
        context
        result' 
        new_defs' 
        tl


    | (index, A.ArraySlice (pos, _, _)) :: tl -> 

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Array slices not implemented in %a" 
              A.pp_print_position A.dummy_pos))


    | (index, A.ArrayConcat (pos, _, _)) :: tl -> 

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Array concatenation not implemented in %a" 
              A.pp_print_position A.dummy_pos))


    | (index, A.RecordConstruct (pos, _, _)) :: tl -> 

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Records not implemented in %a" 
              A.pp_print_position A.dummy_pos))


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

      eval_unary_ast_expr E.mk_not expr tl

    | (index, A.And (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_and expr1 expr2 tl


    | (index, A.Or (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_or expr1 expr2 tl


    | (index, A.Xor (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_xor expr1 expr2 tl


    | (index, A.Impl (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_impl expr1 expr2 tl


    | (index, A.OneHot (pos, _)) :: tl -> 

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "One-hot expression not supported in %a" 
              A.pp_print_position A.dummy_pos))


    | (index, A.Uminus (pos, expr)) :: tl -> 

      eval_unary_ast_expr E.mk_uminus expr tl


    | (index, A.Mod (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_mod expr1 expr2 tl


    | (index, A.Minus (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_minus expr1 expr2 tl


    | (index, A.Plus (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_plus expr1 expr2 tl


    | (index, A.Div (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_div expr1 expr2 tl


    | (index, A.Times (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_times expr1 expr2 tl


    | (index, A.IntDiv (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_intdiv expr1 expr2 tl


    | (index, A.Ite (pos, expr1, expr2, expr3)) :: tl -> 

      let expr1', new_defs' = 
        eval_ast_expr 
          mk_new_var_ident 
          mk_new_call_ident 
          context
          new_defs 
          expr1 
      in

      (* Check evaluated expression *)
      (match expr1' with 

        (* Boolean expression without indexes *)
        | [ [], 
            ({ E.expr_init; E.expr_step; E.expr_type = T.Bool } as expr1) ] -> 

          let expr', new_defs' = 
            binary_apply_to 
              mk_new_var_ident 
              mk_new_call_ident 
              context 
              new_defs' 
              (E.mk_ite expr1) 
              expr2 
              expr3 
              result
          in

          (* Add expression to result *)
          eval_ast_expr' 
            mk_new_var_ident 
            mk_new_call_ident 
            context 
            expr'
            new_defs' 
            tl


        (* Expression is not Boolean or is indexed *)
        | _ -> 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Condition is not of Boolean type in %a" 
                  A.pp_print_position A.dummy_pos)))


    | (index, A.With (pos, _, _, _)) :: tl -> 

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "With expression not supported in %a" 
              A.pp_print_position A.dummy_pos))


    | (index, A.Eq (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_eq expr1 expr2 tl


    | (index, A.Neq (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_neq expr1 expr2 tl


    | (index, A.Lte (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_lte expr1 expr2 tl


    | (index, A.Lt (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_lt expr1 expr2 tl


    | (index, A.Gte (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_gte expr1 expr2 tl


    | (index, A.Gt (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_gt expr1 expr2 tl


    | (index, A.When (pos, _, _)) :: tl -> 

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "When expression not supported in %a" 
              A.pp_print_position A.dummy_pos))


    | (index, A.Current (pos, _)) :: tl -> 

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Current expression not supported in %a" 
              A.pp_print_position A.dummy_pos))


    | (index, A.Condact (pos, _, _, _)) :: tl -> 

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Condact expression not implemented in %a" 
              A.pp_print_position A.dummy_pos))


    | (index, A.Pre (pos, expr)) :: tl -> 

      (try 

         (* Evaluate expression *)
         let expr', new_defs' = 
           eval_ast_expr 
             mk_new_var_ident 
             mk_new_call_ident 
             context 
             new_defs 
             expr 
         in

         let expr'', new_defs'' = 

           List.fold_right
             (fun (index, expr) (accum, new_defs) -> 
                let expr', new_defs' = 
                  E.mk_pre mk_new_var_ident new_defs expr 
                in
                (((index, expr') :: accum), new_defs'))
             expr'
             (result, new_defs')

         in

         (* Add expression to result *)
         eval_ast_expr' 
           mk_new_var_ident 
           mk_new_call_ident 
           context 
           expr'' 
           new_defs'' 
           tl

       with E.Type_mismatch ->

         (* Fail *)
         raise 
           (Failure 
              (Format.asprintf 
                 "Type mismatch for expressions at %a"
                 A.pp_print_position A.dummy_pos)))


    | (index, A.Fby (pos, _, _, _)) :: tl -> 

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Condact expression not implemented in %a" 
              A.pp_print_position A.dummy_pos))


    | (index, A.Arrow (pos, expr1, expr2)) :: tl -> 

      eval_binary_ast_expr E.mk_arrow expr1 expr2 tl


    | (index, A.Call (pos, ident, expr_list)) :: tl -> 

      (try 

         let { node_inputs; node_outputs } = List.assoc ident nodes in

         let expr_list', ((vars', calls') as new_defs') = 
           eval_ast_expr_list
             mk_new_var_ident 
             mk_new_call_ident 
             context 
             new_defs 
             expr_list
         in

         let call_ident = mk_new_call_ident ident in

         let node_input_exprs =

           try

             List.fold_right2
               (fun (_, (in_param, is_const)) in_expr accum ->

                  (* TODO: check if expression is actually constant. How
                     to optimize in that case? *)

                  List.fold_right2 
                    (fun 
                      (in_index, in_type) 
                      (index, ({ E.expr_type } as expr))
                      accum ->

                      (* Indexes must match *)
                      if in_index = index then 
                        
                        (* Expression must be of a subtype of input
                           type*)
                        if T.check_type expr_type in_type then 

                          expr :: accum

                        else

                          raise E.Type_mismatch

                      else

                        raise E.Type_mismatch)
                    (sort_indexed_pairs in_param)
                    (sort_indexed_pairs in_expr)
                    accum
               )
               node_inputs 
               expr_list'
               []

           (* Type checking error or one expression has more indexes *)
           with Invalid_argument "List.fold_right2" | E.Type_mismatch -> 

             (* Fail *)
             raise 
               (Failure 
                  (Format.asprintf 
                     "Type mismatch for expressions at %a"
                     A.pp_print_position A.dummy_pos))
         in
         
         let node_output_idents = 
           
           match node_outputs with 
             
             (* Node must have outputs *)
             | [] ->  
               
               (* Fail *)
               raise 
                 (Failure 
                    (Format.asprintf 
                       "Node %a cannot be called, it does not have \
                        outputs in %a" 
                       I.pp_print_ident ident
                       A.pp_print_position pos))
                 
             | _ -> 
               
               List.fold_left
                 (fun accum (out_ident, out_type) -> 
                 
                    let out_ident = 
                      I.add_ident_index call_ident out_ident 
                    in

                    List.fold_left 
                      (fun accum (index, out_type) ->
                         (I.add_index out_ident index, out_type) :: accum)
                      accum
                      out_type)
                 []
                 node_outputs
                 
         in

         let result' = match node_output_idents with 
           | [] -> assert false
           | [(var_ident, var_type)] -> 
             (index, E.mk_var var_ident var_type E.base_clock) :: result
           | _ -> failwith "stop"
         in

         (* Add expression to result *)
         eval_ast_expr' 
           mk_new_var_ident 
           mk_new_call_ident 
           context 
           result' 
           (vars', (node_output_idents, ident, node_input_exprs) :: calls') 
           tl

       with Not_found -> 

         (* Fail *)
         raise 
           (Failure 
              (Format.asprintf 
                 "Node %a not defined or forward-referenced in %a" 
                 I.pp_print_ident ident
                 A.pp_print_position A.dummy_pos)))


    | (index, A.CallParam (pos, _, _, _)) :: tl -> 

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Parametric nodes not supported in %a" 
              A.pp_print_position A.dummy_pos))



(* Apply operation to expression component-wise *)
and unary_apply_to 
    mk_new_var_ident
    mk_new_call_ident 
    context 
    new_defs 
    mk 
    expr 
    accum = 

  try 

    (* Evaluate expression *)
    let expr', new_defs' = 
      eval_ast_expr 
        mk_new_var_ident 
        mk_new_call_ident 
        context 
        new_defs 
        expr 
    in

    (List.fold_right
       (fun (j, e) a -> (j, mk e) :: a)
       expr'
       accum,
     new_defs')

  with E.Type_mismatch ->

    (* Fail *)
    raise 
      (Failure 
         (Format.asprintf 
            "Type mismatch for expressions at %a"
            A.pp_print_position A.dummy_pos))


(* Apply operation to expressions component-wise *)
and binary_apply_to 
    mk_new_var_ident
    mk_new_call_ident 
    context 
    new_defs 
    mk 
    expr1 
    expr2 
    accum = 

  (* Evaluate and sort first expression by indexes *)
  let expr1', new_defs' = 
    eval_ast_expr 
      mk_new_var_ident 
      mk_new_call_ident 
      context 
      new_defs 
      expr1 
  in

  (* Evaluate and sort second expression by indexes *)
  let expr2', new_defs' = 
    eval_ast_expr 
      mk_new_var_ident 
      mk_new_call_ident 
      context 
      new_defs' 
      expr2 
  in

  try 

    (List.fold_right2
       (fun (index1, expr1) (index2, expr2) accum -> 

          (* Indexes must match *)
          if index1 = index2 then 

            (index1, mk expr1 expr2) :: accum

          else          

            raise E.Type_mismatch)
       (sort_indexed_pairs expr1')
       (sort_indexed_pairs expr2')
       accum,
     new_defs')

  (* Type checking error or one expression has more indexes *)
  with Invalid_argument "List.fold_right2" | E.Type_mismatch -> 

    (* Fail *)
    raise 
      (Failure 
         (Format.asprintf 
            "Type mismatch for expressions at %a"
            A.pp_print_position A.dummy_pos))


(* Evaluate expression *)
and eval_ast_expr 
    mk_new_var_ident 
    mk_new_call_ident 
    context 
    new_defs 
    expr = 

  eval_ast_expr' 
    mk_new_var_ident
    mk_new_call_ident 
    context
    [] 
    new_defs 
    [([], expr)]


(* Evaluate list of expressions *)
and eval_ast_expr_list 
    mk_new_var_ident
    mk_new_call_ident 
    context 
    new_defs 
    expr_list =

  List.fold_right 
    (fun expr (accum, new_defs) -> 
       let expr', new_defs' = 
         eval_ast_expr 
           mk_new_var_ident 
           mk_new_call_ident 
           context 
           new_defs 
           expr
       in
       (expr' :: accum, new_defs'))
    expr_list
    ([], new_defs)


(* Evaluate expression to an integer constant *)
and int_const_of_ast_expr context expr = 

  (* Evaluate expression *)
  match 

    eval_ast_expr 

      (* Immediately fail when abstraction expressions to a
         definition *)
      (fun _ ->       
         (* Fail *)
         raise 
           (Failure 
              (Format.asprintf 
                 "Expression %a in %a must be a constant integer" 
                 A.pp_print_expr expr
                 A.pp_print_position A.dummy_pos))) 

      (* Immediately fail when abstraction expressions to a
         node call *)
      (fun _ ->       
         (* Fail *)
         raise 
           (Failure 
              (Format.asprintf 
                 "Expression %a in %a must be a constant integer" 
                 A.pp_print_expr expr
                 A.pp_print_position A.dummy_pos))) 

      context
      ([], [])
      expr 

  with

    (* Expression must evaluate to a singleton list of an integer
       expression without index and without new definitions *)
    | ([ [], { E.expr_pre_vars; 
               E.expr_init = E.Int di; 
               E.expr_step = E.Int ds } ],
       ([], []))
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


(* ******************************************************************** *)
(* Node declarations                                                    *)
(* ******************************************************************** *)


(* Add declaration of a node input to contexts *)
let add_node_input_decl
    ident
    is_const
    (({ type_ctx; index_ctx } as context), 
     ({ node_inputs } as node))
    index 
    basic_type =
  
  (* Add index to identifier *)
  let ident' = I.add_index ident index in

  (* Add to typing context *)
  let type_ctx' = 
    (ident', basic_type) :: 
      (add_enum_to_context type_ctx basic_type) 
  in

  (* Add indexed identifier to context *)
  let index_ctx' = add_to_prefix_map index_ctx ident' () in

  (* Add to constant node inputs *)
  let node_inputs' = match node_inputs with 

    | (i, (l, c)) :: tl when i = ident -> 
      
      (ident, ((index, basic_type) :: l, c)) :: tl 
        
    | _ -> (ident, ([(index, basic_type)], is_const)) :: node_inputs 

  in

  ({ context with type_ctx = type_ctx'; index_ctx = index_ctx' }, 
   { node with node_inputs = node_inputs' })


(* Add declaration of a node output to contexts *)
let add_node_output_decl
    ident
    (({ type_ctx; index_ctx } as context), 
     ({ node_outputs } as node))
    index 
    basic_type =
  
  (* Add index to identifier *)
  let ident' = I.add_index ident index in

  (* Add to typing context *)
  let type_ctx' = 
    (ident', basic_type) :: 
      (add_enum_to_context type_ctx basic_type) 
  in
  
  (* Add indexed identifier to context *)
  let index_ctx' = add_to_prefix_map index_ctx ident' () in

  (* Add to constant node inputs *)
  let node_outputs' = match node_outputs with 

    | (i, l) :: tl when i = ident -> 
      
      (ident, (index, basic_type) :: l) :: tl 
        
    | _ -> (ident, [(index, basic_type)]) :: node_outputs 

  in

  ({ context with type_ctx = type_ctx'; index_ctx = index_ctx' }, 
   { node with node_outputs = node_outputs' })


(* Add declaration of a node local variable or constant to contexts *)
let add_node_var_decl
    ident
    (({ type_ctx; index_ctx } as context), 
     ({ node_vars } as node))
    index 
    basic_type =
  
  (* Add index to identifier *)
  let ident' = I.add_index ident index in

  (* Add to typing context *)
  let type_ctx' = 
    (ident', basic_type) :: 
      (add_enum_to_context type_ctx basic_type) 
  in

  (* Add indexed identifier to context *)
  let index_ctx' = add_to_prefix_map index_ctx ident' () in

  (* Add to constant node inputs *)
  let node_vars' = match node_vars with 

    | (i, l) :: tl when i = ident -> 
      
      (ident, (index, basic_type) :: l) :: tl 
        
    | _ -> (ident, [(index, basic_type)]) :: node_vars 

  in

  ({ context with type_ctx = type_ctx'; index_ctx = index_ctx' }, 
   { node with node_vars = node_vars' })


(* Add all node inputs to contexts *)
let rec parse_node_inputs context node = function

  (* All inputs parsed, return in original order *)
  | [] -> (context, { node with node_inputs = List.rev node.node_inputs })


  (* Identifier must not be declared *)
  | (ident, _, _, _) :: _ when ident_in_context context ident -> 

    (* Fail *)
    raise 
      (Failure 
         (Format.asprintf 
            "Node input %a already declared in %a" 
            I.pp_print_ident ident
            A.pp_print_position A.dummy_pos))


  (* Input on the base clock *)
  | (ident, var_type, A.ClockTrue, is_const) :: tl -> 

    (* Add declaration of possibly indexed type to contexts *)
    let context', node' = 
      fold_ast_type 
        context
        (add_node_input_decl ident is_const)
        (context, node)
        var_type
    in

    (* Continue with following inputs *)
    parse_node_inputs context' node' tl

  | _ -> 

    (* Fail *)
    raise 
      (Failure 
         (Format.asprintf 
            "Clocked node inputs not supported in %a" 
            A.pp_print_position A.dummy_pos))


(* Add all node outputs to contexts *)
let rec parse_node_outputs context node = function

  (* All outputs parsed, return in original order *)
  | [] -> (context, { node with node_outputs = List.rev node.node_outputs })


  (* Identifier must not be declared *)
  | (ident, _, _) :: _ when ident_in_context context ident -> 

    (* Fail *)
    raise 
      (Failure 
         (Format.asprintf 
            "Node output %a already declared in %a" 
            I.pp_print_ident ident
            A.pp_print_position A.dummy_pos))


  (* Output on the base clock *)
  | (ident, var_type, A.ClockTrue) :: tl -> 

    (* Add declaration of possibly indexed type to contexts *)
    let context', node' = 
      fold_ast_type 
        context
        (add_node_output_decl ident)
        (context, node)
        var_type
    in

    (* Continue with following outputs *)
    parse_node_outputs context' node' tl

  | _ -> 

    (* Fail *)
    raise 
      (Failure 
         (Format.asprintf 
            "Clocked node outputs not supported in %a" 
            A.pp_print_position A.dummy_pos))



(* Add all node local declarations to contexts *)
let rec parse_node_locals context node = function

  (* All local declarations parsed, order does not matter *)
  | [] -> (context, node)


  (* Identifier must not be declared *)
  | A.NodeVarDecl (ident, _, _) :: _ 
  | A.NodeConstDecl (A.FreeConst (ident, _)) :: _
  | A.NodeConstDecl (A.UntypedConst (ident, _)) :: _
  | A.NodeConstDecl (A.TypedConst (ident, _, _)) :: _
    when ident_in_context context ident -> 

    (* Fail *)
    raise 
      (Failure 
         (Format.asprintf 
            "Node local variable or constant %a already declared in %a" 
            I.pp_print_ident ident
            A.pp_print_position A.dummy_pos))


  (* Output on the base clock *)
  | A.NodeVarDecl (ident, var_type, A.ClockTrue) :: tl -> 

    (* Add declaration of possibly indexed type to contexts *)
    let context', node' = 
      fold_ast_type 
        context
        (add_node_var_decl ident)
        (context, node)
        var_type
    in

    (* Continue with following outputs *)
    parse_node_locals context' node' tl

  | _ -> 

    (* Fail *)
    raise 
      (Failure 
         (Format.asprintf 
            "Clocked node local variables not supported in %a" 
            A.pp_print_position A.dummy_pos))


let new_defs_to_context context node (vars, calls) =

  let context', node' = 

    List.fold_left 
      (fun (context, node) ((ident, index), { E.expr_type }) -> 
         add_node_var_decl 
           (I.mk_string_id ident)
           (context, node)
           index 
           expr_type)
      (context, node)
      vars

  in

  List.fold_left
    (fun accum (outputs, _, _) ->
       List.fold_left 
         (fun (context, node) ((ident, index), expr_type) -> 
            add_node_var_decl 
              (I.mk_string_id ident)
              (context, node)
              index
              expr_type)
         accum
         outputs)
    (context', node')
    calls



let rec parse_node_equations 
    mk_new_var_ident
    mk_new_call_ident 
    context 
    node = 

  function

    | [] -> node 

    (* Assertion *)
    | A.Assert expr :: tl -> 

      (* Evaluate expression *)
      let expr', ((new_vars, new_calls) as new_defs) = 
        eval_ast_expr 
          mk_new_var_ident 
          mk_new_call_ident 
          context 
          ([], []) 
          expr 
      in

      (* Add new definitions to context *)
      let context', node' = new_defs_to_context context node new_defs in

      (* Check evaluated expression *)
      (match expr' with 

        (* Boolean expression without indexes *)
        | [ [], 
            ({ E.expr_init; E.expr_step; E.expr_type = T.Bool } as expr) ] -> 

          parse_node_equations 
            mk_new_var_ident 
            mk_new_call_ident 
            context'
            { node' with 
                node_asserts = (expr :: node.node_asserts); 
                node_eqs = new_vars @ node.node_eqs; 
                node_calls = new_calls @ node.node_calls }
            tl

        (* Expression is not Boolean or is indexed *)
        | _ -> 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Assertion is not of Boolean type in %a" 
                  A.pp_print_position A.dummy_pos)))


    (* Property annotation *)
    | A.AnnotProperty expr :: tl -> 

      (* Evaluate expression *)
      let expr', ((new_vars, new_calls) as new_defs) = 
        eval_ast_expr 
          mk_new_var_ident 
          mk_new_call_ident 
          context 
          ([], []) 
          expr 
      in

      (* Add new definitions to context *)
      let context', node' = new_defs_to_context context node new_defs in

      (* Check evaluated expression *)
      (match expr' with 

        (* Boolean expression without indexes *)
        | [ [], 
            ({ E.expr_init; E.expr_step; E.expr_type = T.Bool } as expr) ] -> 

          parse_node_equations 
            mk_new_var_ident 
            mk_new_call_ident 
            context' 
            { node' with 
                node_props = (expr :: node.node_props); 
                node_eqs = new_vars @ node.node_eqs; 
                node_calls = new_calls @ node.node_calls }
            tl

        (* Expression is not Boolean or is indexed *)
        | _ -> 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Property is not of Boolean type in %a" 
                  A.pp_print_position A.dummy_pos)))


    (* Equation x = f(x) *)
    | A.Equation ([A.SingleIdent ident], expr) :: tl -> 

      (* Type of equation *)
      let eq_type = 

        (* TODO: Could have an indexed identifier and assign to one field of it:
           
           x[0] = c;

           Would need to search for type instead of looking up in the
           list, but some fields could be left unassigned without
           warning. *)

        try 

          (* Return type if assigning to an output *)
          List.assoc ident node.node_outputs 

        with Not_found -> 

          (* Return type if assigning to a local variable *)
          try List.assoc ident node.node_vars 

          with Not_found -> 

            (* Fail *)
            raise 
              (Failure 
                 (Format.asprintf 
                    "Equation does not assign to output or local \
                     variable in %a" 
                    A.pp_print_position A.dummy_pos))

      in

      (* Evaluate expression *)
      let expr', ((new_vars, new_calls) as new_defs) = 
        eval_ast_expr 
          mk_new_var_ident 
          mk_new_call_ident 
          context 
          ([], []) 
          expr 
      in

      (* Add new definitions to context *)
      let context', node' = new_defs_to_context context node new_defs in

      (* Add node equations *)
      let node_eqs', node_props' = 

        List.fold_right2

          (fun 
            (def_index, def_type) 
            (expr_index, ({ E.expr_type } as expr)) 
            (node_eqs, node_props) -> 

            (* Indexes must match *)
            if def_index = expr_index then 

              (* Equation to add to node *)
              let eq = I.add_index ident def_index, expr in

              (* Type must be a subtype of declared type *)
              if T.check_type expr_type def_type then

                (* Add equation *)
                (eq :: node_eqs, node_props) 

              else

                (* Type of expression may not be subtype of declared
                   type *)
                (match def_type, expr_type with 

                  (* Declared type is integer range, expression is of
                     type integer *)
                  | T.IntRange (lbound, ubound), T.Int -> 

                    (* Value of expression is in range of declared
                       type: lbound <= expr and expr <= ubound *)
                    let range_expr = 
                      (E.mk_and 
                         (E.mk_lte (E.mk_int lbound) expr) 
                         (E.mk_lte expr (E.mk_int ubound)))
                    in

                    Format.printf 
                      "@[<v>Expression may not be in subrange of variable. \
                       Need to add property@;%a@]@."
                      E.pp_print_lustre_expr range_expr;

                    (eq :: node_eqs, range_expr :: node_props) 

                  | _ -> 

                    (* Fail *)
                    raise 
                      (Failure 
                         (Format.asprintf 
                            "Type mismatch for expressions at %a" 
                            A.pp_print_position A.dummy_pos)))
            else       

              (* Fail *)
              raise 
                (Failure 
                   (Format.asprintf 
                      "Type mismatch for expressions at %a" 
                      A.pp_print_position A.dummy_pos)))
          (sort_indexed_pairs eq_type)
          (sort_indexed_pairs expr')
          (node'.node_eqs, node'.node_props)
      in

      parse_node_equations 
        mk_new_var_ident 
        mk_new_call_ident 
        context 
        { node' with 
            node_eqs = new_vars @ node_eqs'; 
            node_props = node_props'; 
            node_calls = new_calls @ node.node_calls }
        tl

    (* TODO: catch all singleton lists here *)

    (* TODO: This would need a change for SingleIdent, see note there
    | A.Equation ([A.TupleSelection (ident, index_expr)], expr) :: tl -> 

      let index = int_const_of_ast_expr context index_expr in 

      let ident' = I.add_int_index ident index in 

      parse_node_equations 
        mk_new_var_ident 
        mk_new_call_ident 
        context 
        node
        (A.Equation ([A.SingleIdent ident'], expr) :: tl)
      
      *)      

(*
    (* Equations with more than one variable on the left-hand side *)
    | A.Equation (struct_items, expr) :: tl -> 
      
      let _, tl' = 

        List.fold_left 
          (function (i, accum) -> 

            (function 
              | A.SingleIdent ident -> 

                let eq = 
                  A.Equation 
                    ([A.SingleIdent ident], 
                     A.TupleProject (A.dummy_pos, expr, A.Num i))
                in

                (succ i, eq :: accum)))
          
          (0, tl)
          struct_items

      in

      parse_node_equations 
        mk_new_var_ident 
        mk_new_call_ident 
        context 
        node
        tl'
*)
      


    (* Annotation for main node *)
    | A.AnnotMain :: tl -> 

      parse_node_equations 
        mk_new_var_ident 
        mk_new_call_ident 
        context 
        { node with node_is_main = true }
        tl


let rec parse_node_contract 
    mk_new_var_ident 
    mk_new_call_ident
    context 
    node = 

  function

    | [] -> node 

    (* Assumption *)
    | A.Requires expr :: tl -> 

      (* Evaluate expression *)
      let expr', ((new_vars, new_calls) as new_defs) = 
        eval_ast_expr 
          mk_new_var_ident 
          mk_new_call_ident 
          context 
          ([], []) 
          expr 
      in

      (* Add new definitions to context *)
      let context', node' = new_defs_to_context context node new_defs in

      (* Check evaluated expression *)
      (match expr' with 

        (* Boolean expression without indexes *)
        | [ [], 
            ({ E.expr_init; E.expr_step; E.expr_type = T.Bool } as expr) ] -> 

          parse_node_contract 
            mk_new_var_ident 
            mk_new_call_ident 
            context' 
            { node' with 
                node_requires = (expr :: node.node_requires); 
                node_eqs = new_vars @ node.node_eqs; 
                node_calls = new_calls @ node.node_calls }
            tl

        (* Expression is not Boolean or is indexed *)
        | _ -> 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Requires clause is not of Boolean type in %a" 
                  A.pp_print_position A.dummy_pos)))

    (* Guarantee *)
    | A.Ensures expr :: tl -> 

      (* Evaluate expression *)
      let expr', ((new_vars, new_calls) as new_defs) = 
        eval_ast_expr 
          mk_new_var_ident 
          mk_new_call_ident 
          context 
          ([], []) 
          expr 
      in

      (* Add new definitions to context *)
      let context', node' = new_defs_to_context context node new_defs in

      (* Check evaluated expression *)
      (match expr' with 

        (* Boolean expression without indexes *)
        | [ [], 
            ({ E.expr_init; E.expr_step; E.expr_type = T.Bool } as expr) ] -> 

          parse_node_contract 
            mk_new_var_ident 
            mk_new_call_ident 
            context' 
            { node' with 
                node_ensures = (expr :: node.node_ensures); 
                node_eqs = new_vars @ node.node_eqs;
                node_calls = new_calls @ node.node_calls }
            tl

        (* Expression is not Boolean or is indexed *)
        | _ -> 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Ensures clause is not of Boolean type in %a" 
                  A.pp_print_position A.dummy_pos)))



let parse_node_signature  
    node_ident
    global_context
    inputs 
    outputs 
    locals 
    equations 
    contract =

  let mk_new_var_ident = 
    let r = ref (-1) in
    fun () -> incr r; I.add_int_index new_var_ident !r
  in

  let rec mk_new_call_ident =
    let l = ref [] in
    fun ident -> 
      try 
        let r = List.assoc ident !l in
        incr r;
        I.add_int_index (I.add_ident_index new_call_ident ident) !r
      with Not_found -> 
        l := (ident, ref (-1)) :: !l;
        mk_new_call_ident ident
  in
  
  (* Parse inputs, add to global context and node context *)
  let local_context_inputs, node_context_inputs = 
    parse_node_inputs global_context init_node_context inputs
  in

  (* Parse outputs, add to local context and node context *)
  let local_context_outputs, node_context_outputs = 
    parse_node_outputs local_context_inputs node_context_inputs outputs
  in

  (* Parse contract

     Must check here, may not use local variables *)
  let node_context_contract = 
    parse_node_contract 
      mk_new_var_ident 
      mk_new_call_ident 
      local_context_outputs 
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
      mk_new_var_ident 
      mk_new_call_ident 
      local_context_locals 
      node_context_locals 
      equations
  in

  Format.printf "%a@." pp_print_lustre_context local_context_locals;

  Format.printf "%a@." (pp_print_node_context node_ident) node_context_equations;

  node_context_locals



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
       nodes;
       result } as global_context) = 



(*
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
        type_in_context global_context ident

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
        ident_in_context global_context ident 

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

          let expr_val, new_defs = 
            eval_ast_expr 

              (* Immediately fail when abstraction expressions to a
                 definition *)
              (fun _ ->       
                 (* Fail *)
                 raise 
                   (Failure 
                      (Format.asprintf 
                         "Expression %a in %a must be a constant" 
                         A.pp_print_expr expr
                         A.pp_print_position A.dummy_pos))) 

              (* Immediately fail when abstraction expressions to a
                 node call *)
              (fun _ ->       
                 (* Fail *)
                 raise 
                   (Failure 
                      (Format.asprintf 
                         "Expression %a in %a must be a constant" 
                         A.pp_print_expr expr
                         A.pp_print_position A.dummy_pos))) 

              global_context 
              ([], [])
              expr 
          in

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


    (* Node declaration without parameters *)
    | (A.NodeDecl 
         (node_ident, 
          [], 
          inputs, 
          outputs, 
          locals, 
          equations, 
          contract)) as decl :: decls ->

      (* Output node declaration *)
      Format.printf "-- %a@." A.pp_print_declaration decl;
      
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
      check_declarations 
        { global_context with 
            nodes = (node_ident, node_context) :: nodes }
        decls


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
  
