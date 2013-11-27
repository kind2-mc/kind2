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

module A = LustreAst
module I = LustreIdent

module T = LustreType
module E = LustreExpr

module IdentSet = Set.Make (I)


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



(* The state of the type checker and preprocessor *)
type check_declaration_state = 

    { 

      (* Type identifiers and their types *)
      basic_types : (LustreIdent.t * LustreType.t) list; 

      (* Prefixes of indexed type identifiers, their suffixes and types *)
      indexed_types : 
        (LustreIdent.t * 
           (LustreIdent.index * LustreAst.lustre_type) list) list; 

      (* Type identifiers for free types *)
      free_types : LustreIdent.t list; 

      (* Types of constants and variables *)
      type_ctx : (LustreIdent.t * LustreType.t) list; 

      (* Indexes of constants and variables *)
      index_ctx : (LustreIdent.t * (LustreIdent.index list)) list; 

      (* Values of constants *)
      consts : (LustreIdent.t * LustreExpr.t) list; 

      (* Preprocessed and checked Lustre program *)
      result : unit 

    }

(* Initial state *)
let init_state = 
  { basic_types = [];
    indexed_types = [];
    free_types = [];
    type_ctx = [];
    index_ctx = [];
    consts = [];
    result = () }



let pp_print_basic_type ppf (i, t) = 
  Format.fprintf ppf "%a: %a" I.pp_print_ident i T.pp_print_lustre_type t

let pp_print_index_type ppf (i, t) = 
  Format.fprintf ppf "%a: %a" I.pp_print_index i A.pp_print_lustre_type t

let pp_print_indexed_type ppf (i, t) = 

  Format.fprintf ppf 
    "%a: @[<hv 1>[%a]@]" 
    I.pp_print_ident i 
    (pp_print_list pp_print_index_type ";@ ") t


let pp_print_state ppf { basic_types; indexed_types; free_types; type_ctx; consts; result } =
  
  Format.fprintf ppf
    "@[<v>@[<v>basic_types:@,%a@]@,\
          @[<v>indexed_types:@,%a@]@,\
          @[<v>free_types:@,@[<hv>%a@]@]\
     @]" 
    (pp_print_list pp_print_basic_type "@,") basic_types
    (pp_print_list pp_print_indexed_type "@,") indexed_types
    (pp_print_list I.pp_print_ident ",@ ") free_types


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
       result } as state) = 


  (* Return true if type [t] was already declared *)
  let type_is_declared t = 

    (* Check if [t] is a basic types *)
    (List.mem_assoc t basic_types) ||

    (* Check is [t] is an indexed type *)
    (List.mem_assoc t indexed_types) || 

    (* Check if [t] is a free type *)
    (List.mem t free_types) 

  in

  (* Convert a parsed type to a built-in type *)
  let lustre_type_of_ast_type = function

    | A.Bool -> T.t_bool

    | A.Int -> T.t_int

    | A.Real -> T.t_real

    | A.IntRange (i, j) -> 

      (* let ci = int_const_of_expr type_ctx const_val i in

         let cj = int_const_of_expr type_ctx const_val j in

         T.mk_int_range ci cj *)
      assert false 


    | A.EnumType l -> T.mk_enum l

    | A.UserType t -> T.mk_free_type t

    | _ -> raise (Invalid_argument "lustre_type_of_ast_type")

  in


  (* Apply function pointwise *)
  let apply_to f = function 
    | Expr e -> Expr (f e)
    | IndexedExpr l -> IndexedExpr (List.map (function (i, e) -> (i, f e)) l)
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


    (* An nested identifier with indexes *)
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

      apply_to 
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
                        (fun a (j, e) -> (I.add_int_to_index j i, e) :: a)
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

    | A.ArraySlice (p, i, l) ->  

      (* Fold l until empty, each time popping a pair (l, u) and
         filter expression for indexes between l and u. *)

      let rec aux = function

        (* Expression is not nested  *)
        | Expr _ -> 

          (function _ -> 

            (* Fail *)
            raise 
              (Failure 
                 (Format.asprintf 
                    "Identifier %a in %a does not have fields" 
                    I.pp_print_ident id
                    A.pp_print_position p)))


        | IndexedExpr l -> 

          (function 

            | [] -> IndexedExpr l 

            | (l, u) :: tl -> 

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

              let iu = 

                match check_expr e2 with 

                  (* Expresssion must be simplified to a non-zero positive
                     integer *)
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
                            A.pp_print_expr e2
                            A.pp_print_position p))

              in

              let rec aux2 = function 
                
                expr_find_index idx [] l 
                  
           
              in


              (* Must store  *)

              aux (aux2 [] ) 
              

      in

      aux (check_expr (A.Ident (p, i)) l

  in


(*
    | A.True p -> (Const (ConstBool true), Type T.bool)

    | A.False p -> (Const (ConstBool false), Type T.bool)

    | A.Num (p, n) -> 

    let v = int_of_string n in 
    let t = T.mk_int_range v v in

    (Const (ConstInt v), Type t)

  | A.Dec (p, n) -> 

    let v = float_of_string n in 
    let t = T.real in

    (Const (ConstFloat v), Type t)

  (* Identifier *)
  | A.Ident (p, i) as e -> 

    (

      let t = 

        (* Get type from context *)
        try Type (List.assoc i type_ctx) with 

          (* Identifier may be indexed *)
          | Not_found -> 

            (* Find all identifiers with this identifier as prefix *)
            let suffixes = 
              List.fold_left 
                (fun a (s, s') -> 
                   try 
                     (I.get_suffix i s, s') :: a 
                   with Invalid_argument _ -> a)
                []
                type_ctx
            in

            (* Identifier was not declared and no identifier with
               prefix declared *)
            if suffixes = [] then 

              (* Fail *)
              raise 
                (Failure 
                   (Format.asprintf 
                      "Identifier %a in %a is not declared" 
                      I.pp_print_ident i
                      A.pp_print_position p))

            else

              (* IndexedType suffixes  *)
              assert false

      in

      let v = 

        (* Substitute value if identifier is a constant *)
        try Const (List.assoc i const_val) with 

          | Not_found -> Expr (E.mk_ident i)

      in

      (* Return value and type *)
      (v, t)

    )


  (* t { a = s { x = 1; y = 2 }; b = 3 } 

     { a.x = 1; a.y = 2; b = 3 }
*)
(*
  | A.RecordConstruct (p, t, l) -> 

  | A.ArrayConstruct (p, e1, e2) -> 

  | A.TupleExpr (p, l) ->
*)


    (* [1, 2, 3] 
       [0] = 1, [1] = 2, [2] = 3 *)



    (* Point-wise operators

       [ [0] = 1, [1] = 2, [2] = 3 ] + [ [0] = 4, [1] = 5, [2] = 6]

       [ [0] = 5, [1] = 7, [2] = 9 ]

    *)


  | A.Uminus (p, e) -> 

    (match type_of_expr type_ctx const_val e with 

      | Const (ConstInt i), (Type T.Int as t) -> 

        (Const (ConstInt (- i)), t)

      | Const (ConstInt i), (Type T.IntRange (l, u) as t)
        when l <= i && i <= u -> 

        (Const (ConstInt (- i)), t) 

      | Const (ConstFloat i), (Type T.Real as t) -> 

        (Const (ConstFloat (-. i)), t)

      | Expr e, (Type T.Int as t) 
      | Expr e, (Type T.Real as t) -> 

        (Expr (E.mk_uminus  e), t)

      | Expr e, (Type (T.IntRange (l, u)) as t) ->

        (Expr (E.mk_uminus e), Type (T.mk_int_range (- u) (- l)))

    )



let int_const_of_expr type_ctx const_val c = 

  try 

    int_of_expr_val (fst (type_of_expr type_ctx const_val c))

  with Invalid_argument "int_of_expr_val" ->  

    (* Fail *)
    raise 
      (Failure 
         (Format.asprintf 
            "Expression %a must be a constant integer in %a" 
            A.pp_print_expr c
            A.pp_print_position A.dummy_pos))

*)

  (* ******************************************************************** *)
  (* Alias type declarations                                              *)
  (* ******************************************************************** *)

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

        (*

        (* Evaluate size of array to a constant integer *)
        let n = int_const_of_expr type_ctx const_val e in
        *)

        let n = 1 in

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

        (* Add association of type to basic type *)
        let basic_types' = 
          (t, List.assoc t' basic_types) :: basic_types 
        in

        (* Changed aliases of basic types *)
        ({ state with basic_types = basic_types' }, decls)


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
      | A.UserType t' when List.mem_assoc t' indexed_types -> 

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

      (* type t = t';

         If t' was defined as

         type t';

         expand to

         type t = t'';
         
      *)
      | A.UserType t' when List.mem t' free_types ->  
        
        (* Add association of type to free type *)
        let basic_types' = 
          (t, T.mk_free_type t') :: basic_types 
        in
        
        (* Changed aliases of basic types *)
        ({ state with basic_types = basic_types' }, decls)


      (* type t = t';

         if t' is not in basic_types, indexed_types or free_types 

      *)
      | A.UserType t' ->  

        
        Format.printf "%a@." pp_print_state state;

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
      | A.EnumType _ as t' -> 

        (* Basic type of type in AST *)
        let t'' = lustre_type_of_ast_type t' in

        (* Add alias for basic type *)
        let basic_types' = (t, t'') :: basic_types in

        (* For an identifier t = t.i1...in associate each prefix with suffix and type t'':
           add (t, (i1...in, t'')), ..., (t.i1..in-1, (in, t'')) to indexed_types *)
        let rec aux prefix indexed_types = function 

          (* Do not add full index to list, this is in basic_types already *)
          | [] -> indexed_types

          (* [index] is second to last or earlier *)
          | index :: tl as suffix -> 

            (* Add association of suffix and type to prefix *)
            let rec aux2 accum = function

              (* Prefix of identifier not found *)
              | [] -> 

                (* Add association of prefix with suffix and type *)
                (prefix, [(suffix, t')]) :: accum

              (* Prefix of identifier found *)
              | (p, l) :: tl when p = prefix -> 

                (* Add association of prefix with suffix and type, and
                   finish *)
                List.rev_append ((p, (suffix, t') :: l) :: tl) accum

              (* Recurse to keep searching for prefix of identifier *)
              | h :: tl -> aux2 (h :: accum) tl

            in

            (* Add index to prefix *)
            let prefix' = I.add_index prefix [index] in

            (* Recurse for remaining suffix *)
            aux prefix' (aux2 [] indexed_types) tl

        in
        
        (* Get indexes of identifier of type *)
        let (id, suffix) = t in
        
        (* Add types of all suffixes *)
        let indexed_types' = aux (id, []) indexed_types suffix in

        (* Add enum constants to typing context *)
        let type_ctx' = match t' with 
          
          (* Type is an enumeration *)
          | A.EnumType l -> 

            List.fold_left
              (fun a e -> 
                
                (* Check that constant not already defined *)
                if List.mem_assoc e a then 

                  (* Fail *)
                  raise 
                    (Failure 
                       (Format.asprintf 
                          "Enum constant %a in %a already declared" 
                          I.pp_print_ident e
                          A.pp_print_position A.dummy_pos));
                
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


  (* ******************************************************************** *)
  (* Free constant declarations                                           *)
  (* ******************************************************************** *)

    (* const c : t; 

       Free constant of basic type *)
  let check_free_const_decl c t decls = 
    
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
        ({ state with type_ctx = type_ctx' }, decls)

          
      (* const c : t'; 
         
         where t' is a basic type *)
      | A.UserType t' when List.mem_assoc t' basic_types -> 
        
        (* Add to typing context *)
        let type_ctx' = (c, List.assoc t' basic_types) :: type_ctx in

        (* State modified *)
        ({ state with type_ctx = type_ctx' }, decls)


      (* const c : t'; 
         
         where t' is an indexed type *)
      | A.UserType t' when List.mem_assoc t' indexed_types -> 
        
        (* Push declarations for indexed identifiers *)
        let decls' = 
          List.fold_left 
            (fun a (j, s) -> 

              (* Expand to declaration [const c.j;] *)
              (A.ConstDecl 
                 (A.FreeConst (I.add_index c j, s))) :: a)

            decls 
            (List.assoc t' indexed_types) 
        in 
        
        (* State unchanged, new declarations pushed *)
        (state, decls')
  

      (* const c : t'; 
         
         where t' is a free type. *)
      | A.UserType t' when List.mem t' free_types -> 

        (* Add to typing context *)
        let type_ctx' = (c, T.mk_free_type t') :: type_ctx in

        (* State modified *)
        ({ state with type_ctx = type_ctx' }, decls)

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
          

      (* TODO *)
      | A.RecordType _
      | A.ArrayType _
      | A.TupleType _ -> assert false 

        
  in
  

  function


    (* All declarations processed, return result *)
    | [] -> state


    (* Identifier [t] is an alias for type [t'] *)
    | A.TypeDecl (A.AliasType (t, t')) as d :: decls ->

      (* Output type declaration *)
      Format.printf "-- %a@." A.pp_print_declaration d;

      (* Check alias type declaration *)
      let state', decls' = check_alias_type_decl t t' decls in

      (* Recurse for next declarations *)
      check_declarations state' decls' 


    (* Identifier [t] is a free type *)
    | A.TypeDecl (A.FreeType t) as d :: decls -> 

      (* Output type declaration *)
      Format.printf "-- %a@." A.pp_print_declaration d;

      (* Check free type declaration *)
      let state', decls' = check_free_type_decl t decls in

      (* Recurse for next declarations *)
      check_declarations state' decls' 


    (* Identifier [c] of type [t] is a free constant *)
    | (A.ConstDecl (A.FreeConst (c, t)) as d) :: decls ->

      (* Output const declaration *)
      Format.printf "-- %a@." A.pp_print_declaration d;

      (* Check const declaration *)
      let state', decls' = check_free_const_decl c t decls in

      (* Recurse for next declarations *)
      check_declarations state' decls' 

    | d :: decls ->

      (* Output const declaration *)
      Format.printf "-- skipped: %a@." A.pp_print_declaration d;

      (* Recurse for next declarations *)
      check_declarations state decls
      
      
(*

  (* ************************************************************** *)
  (* Revise from here *)

  function

    (* type t = struct { i1: t1; ...; in: tn };

       Expand to declarations

       type t.i1 = t1;
       ...
       type t.in = tn;

    *)
    | A.TypeDecl (A.AliasType (t, A.RecordType l)) as d :: tl -> 

      (

        if       

          (* Type t must not be declared *)
          type_is_declared free_types type_map t

        then

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Type %a defined in %a is redeclared in %a" 
                  I.pp_print_ident t
                  A.pp_print_position A.dummy_pos
                  A.pp_print_position A.dummy_pos));

        (* Append type declarations for indexed identifiers *)
        let rec aux accum = function 

          (* All record fields consumed *)
          | [] -> accum

          (* A record field j of type s *)
          | (j, s) :: tl -> 

            (* Expand to declaration [type t.j = s] *)
            aux 
              ((A.TypeDecl (A.AliasType (I.add_ident_index t j, s))) :: accum)
              tl 
        in

        (* Push declarations for indexed identifiers *)
        let tl' = aux tl l in

        (* Output dropped type declaration *)
        Format.printf "-- %a@." A.pp_print_declaration d;

        (* Recurse with new declarations *)
        check_declaration
          (type_map, free_types, type_ctx, const_val, accum)
          tl'

      )

    (* type t = [ t1, ..., tn ];

       Expand to declarations

       type t[0] = t1;
       ...
       type t[n-1] = tn;

    *)
    | A.TypeDecl (A.AliasType (t, A.TupleType l)) as d :: tl -> 

      (

        if       

          (* Type t must not be declared *)
          type_is_declared free_types type_map t

        then

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Type %a defined in %a is redeclared in %a" 
                  I.pp_print_ident t
                  A.pp_print_position A.dummy_pos
                  A.pp_print_position A.dummy_pos));

        (* Append type declarations for indexed identifiers *)
        let rec aux (accum, j) = function 

          (* All tuple fields consumed *)
          | [] -> accum

          (* A tuple field type s *)
          | s :: tl -> 

            (* Expand to declaration to [type t.j = s] *)
            aux 
              (
                (A.TypeDecl (A.AliasType (I.add_int_index t j, s))) :: accum, 
                succ j)
              tl

        in

        (* Push declarations for indexed identifiers *)
        let tl' = aux (tl, 0) l in

        (* Output dropped type declaration *)
        Format.printf "-- %a@." A.pp_print_declaration d;

        (* Recurse with new declarations *)
        check_declaration
          (type_map, free_types, type_ctx, const_val, accum)
          tl'

      )


    (* type t = t'^e;

       Expand to declarations

       type t[0] = t';
       ...
       type t[e] = t';

    *)
    | A.TypeDecl (A.AliasType (t, A.ArrayType (t', e))) as d :: tl -> 

      (

        if       

          (* Type t must not be declared *)
          type_is_declared free_types type_map t

        then

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Type %a defined in %a is redeclared in %a" 
                  I.pp_print_ident t
                  A.pp_print_position A.dummy_pos
                  A.pp_print_position A.dummy_pos));

        (* TODO: evaluate e to a constant integer, then expand declaration *)

        let n = int_const_of_expr type_ctx const_val e in

        if n <= 0 then 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a must be positive in %a" 
                  A.pp_print_expr e
                  A.pp_print_position A.dummy_pos));


        let rec aux accum = function
          | 0 -> accum
          | i -> 

            aux 
              (A.TypeDecl (A.AliasType (I.add_int_index t (pred i), t')) :: accum)
              (pred i)

        in

        let tl' = aux tl n in

        let tl' = aux tl n in

        (* Recurse with new declarations *)
        check_declaration
          (type_map, free_types, type_ctx, const_val, accum)
          tl'

      )

    (* type t = t'; 

       If t' was defined as 

       type t' = t'';

       expand to

       type t = t'';

       Othwise, there must have been definitions

       type t'.i1 = t1;
       ...
       type t'.in = tn;

       expand to 

       type t.i1 = t1;
       ...
       type t.in = tn;

    *)
    | A.TypeDecl (A.AliasType (t, A.UserType t')) as d :: tl -> 

      (

        if       

          (* Type t must not be declared *)
          type_is_declared free_types type_map t

        then

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Type %a defined in %a is redeclared in %a" 
                  I.pp_print_ident t
                  A.pp_print_position A.dummy_pos
                  A.pp_print_position A.dummy_pos));


        if

          (* Type t' must have been declared *)
          not (type_is_declared free_types type_map t')

        then

          (

            (* Find all identifiers with this identifier as prefix *)
            let suffixes = 
              List.fold_left 
                (fun a (s, s') -> 
                   try 
                     (I.get_suffix t' s, s') :: a 
                   with Invalid_argument _ -> a)
                []
                type_map
            in

            (* Identifier was not declared and no identifier with prefix
               declared *)
            if suffixes = [] then 

              (* Fail *)
              raise 
                (Failure 
                   (Format.asprintf 
                      "Type %a in %a is not declared" 
                      I.pp_print_ident t'
                      A.pp_print_position A.dummy_pos))

            else

              (* Append declarations with all suffixes appended  *)
              let rec aux accum = function 

                (* All tuple fields consumed *)
                | [] -> accum

                (* Suffix j with type s *)
                | (j, s) :: tl -> 

                  (* Expand to declaration [type t.j = s] *)
                  aux 
                    ((A.TypeDecl (A.AliasType (I.add_index t j, ast_type_of_lustre_type s))) :: accum)
                    tl 
              in

              (* Push declarations for indexed identifiers *)
              let tl' = aux tl suffixes in

              (* Output dropped type declaration *)
              Format.printf "-- %a@." A.pp_print_declaration d;

              check_declaration
                (type_map, free_types, type_ctx, const_val, accum)
                tl'

          )

        else

          (* Reduce type t' *)
          let t'' = 

            try 

              (* All types in type_map are basic *)
              List.assoc t' type_map

            (* t' is free *)
            with Not_found -> T.mk_free_type t'

          in

          (* Output dropped normalized type declaration *)
          Format.printf 
            "-- type %a = %a@." 
            I.pp_print_ident t
            T.pp_print_lustre_type t'';

          check_declaration
            (

              (* Add alias type to map *)
              (t, t'') :: type_map, 

              (* No new free types *)
              free_types, 

              (* Typing context unchanged *)
              type_ctx, 

              (* No new constant declaration *)
              const_val,

              (* Remove alias declaration *)
              accum

            )
            tl

      )


    (* type t = t'; 

       where t' is a basic type. *)
    | A.TypeDecl (A.AliasType (t, (A.Bool as t'))) :: tl
    | A.TypeDecl (A.AliasType (t, (A.Int as t'))) :: tl
    | A.TypeDecl (A.AliasType (t, (A.Real as t'))) :: tl 
    | A.TypeDecl (A.AliasType (t, (A.IntRange _ as t'))) :: tl -> 

      (

        (* TODO: add all prefixes of the identifier to indexed_types *)

        if       

          (* Type t must not be declared *)
          type_is_declared free_types type_map t

        then

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Type %a defined in %a is redeclared in %a" 
                  I.pp_print_ident t
                  A.pp_print_position A.dummy_pos
                  A.pp_print_position A.dummy_pos));

        Format.printf 
          "-- %a@." 
          A.pp_print_declaration 
          (A.TypeDecl (A.AliasType (t, t')));

        check_declaration
          (

            (* Add alias type to map *)
            (t, lustre_type_of_ast_type type_ctx const_val t') :: type_map, 

            (* No new free types *)
            free_types, 

            (* Typing context unchanged *)
            type_ctx, 

            (* No new constant declaration *)
            const_val,

            (* Remove alias declaration *)
            accum

          )
          tl

      )


    (* type t = enum { x1, ..., xn }; 

       where t' is a basic type. *)
    | A.TypeDecl (A.AliasType (t, (A.EnumType l as t'))) as d :: tl -> 

      (

        if

          (* Type t must not be declared *)
          type_is_declared free_types type_map t

        then

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Type %a defined in %a is redeclared in %a" 
                  I.pp_print_ident t
                  A.pp_print_position A.dummy_pos
                  A.pp_print_position A.dummy_pos));

        let t'' = lustre_type_of_ast_type type_ctx const_val t' in

        (* Append enum elements to typing context *)
        let rec aux accum = function 

          | [] -> accum

          | e :: tl -> 

            try 

              (* Check if identifier declared with a different type *)
              match List.assoc e type_ctx with 

                (* Identifier is in another enum type *)
                | T.Enum _ as s -> 

                  (* Allow if enums are equal *)
                  if T.equal s t'' then raise Not_found else

                    (* Fail *)
                    raise 
                      (Failure 
                         (Format.asprintf 
                            "Enum element %a defined in %a \
                             is also in enum of type %a in %a" 
                            I.pp_print_ident e
                            A.pp_print_position A.dummy_pos
                            T.pp_print_lustre_type s
                            A.pp_print_position A.dummy_pos))

                | s ->

                  (* Fail *)
                  raise 
                    (Failure 
                       (Format.asprintf 
                          "Enum element %a defined in %a \
                           declared as of type %a in %a" 
                          I.pp_print_ident e
                          A.pp_print_position A.dummy_pos
                          T.pp_print_lustre_type s
                          A.pp_print_position A.dummy_pos))

            with Not_found -> 

              (* Append type of identifier to typing context  *)
              aux
                ((e, t'') :: accum)
                tl

        in

        (* Push types of enum constants to typing context *)
        let type_ctx' = aux type_ctx l in

        (* TODO: push enum types as constant declarations *)

        let rec aux accum = function
          | [] -> accum
          | e :: tl -> (e, ConstEnum e) :: accum 
        in

        let const_val' = aux const_val l in

        check_declaration
          (

            (* New alias type for enum *)
            (t, t'') :: type_map, 

            (* Add type to free types *)
            free_types, 

            (* Enum elements addedd to typing context *)
            type_ctx', 

            (* No new constant declaration *)
            const_val',

            (* Keep type declaration *)
            d :: accum

          )
          tl

      )

    (* type t; 

       t is a free type *)
    | A.TypeDecl (A.FreeType t) as d :: tl -> 

      (

        if

          (* Type t must not be declared *)
          type_is_declared free_types type_map t

        then

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Type %a defined in %a is redeclared in %a" 
                  I.pp_print_ident t
                  A.pp_print_position A.dummy_pos
                  A.pp_print_position A.dummy_pos));

        check_declaration
          (

            (* No new alias type *)
            type_map, 

            (* Add type to free types *)
            t :: free_types, 

            (* Typing context unchanged *)
            type_ctx, 

            (* No new constant declaration *)
            const_val,

            (* Keep type declaration *)
            d :: accum

          )
          tl

      )

    (* ******************************************************************** *)
    (* Constant declarations                                                *)
    (* ******************************************************************** *)

    (* const c : t; 

       Free constant of basic type *)
    | (A.ConstDecl (A.FreeConst (c, (A.Bool as t))) as d) :: tl 
    | (A.ConstDecl (A.FreeConst (c, (A.Int as t))) as d) :: tl 
    | (A.ConstDecl (A.FreeConst (c, (A.Real as t))) as d) :: tl 
    | (A.ConstDecl (A.FreeConst (c, (A.EnumType _ as t))) as d) :: tl 
    | (A.ConstDecl (A.FreeConst (c, (A.IntRange _ as t))) as d) :: tl -> 

      if

        (* Identifier must not be declared *)
        List.exists (function (n, _) -> n = c) type_ctx 

      then

        (* Fail *)
        raise 
          (Failure 
             (Format.asprintf 
                "Identifier %a is redeclared as constant in %a" 
                I.pp_print_ident c
                A.pp_print_position A.dummy_pos));

      (* Output dropped const declaration *)
      Format.printf "-- %a@." A.pp_print_declaration d;

      check_declaration
        (

          (* No new alias type *)
          type_map, 

          (* No new free types *)
          free_types, 

          (* Add to typing context *)
          (c, lustre_type_of_ast_type type_ctx const_val t) :: type_ctx, 

          (* No new constant declaration *)
          const_val,

          (* Drop constant declaration *)
          accum

        )
        tl

    (* const c : t; 

       Free constant of alias or free type *)
    | A.ConstDecl (A.FreeConst (c, (A.UserType t))) as d :: tl -> 

      (

        if

          (* Identifier must not be declared *)
          List.exists (function (n, _) -> n = c) type_ctx 

        then

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Identifier %a is redeclared as constant in %a" 
                  I.pp_print_ident c
                  A.pp_print_position A.dummy_pos));

        try 

          (* Resolve alias type *)
          let t' = List.assoc t type_map in 

          (* Output dropped const declaration *)
          Format.printf "-- %a@." A.pp_print_declaration d;

          check_declaration
            (type_map, free_types, (c, t') :: type_ctx, const_val, accum)
            tl

        with 

          (* Type is free or indexed *)
          | Not_found -> 

            (* Type has been declared as free? *)
            if List.mem t free_types then 

              (

                (* Output dropped const declaration *)
                Format.printf "-- %a@." A.pp_print_declaration d;

                check_declaration
                  (type_map, 
                   free_types, 
                   (c, T.mk_free_type t) :: type_ctx, 
                   const_val, 
                   accum)
                  tl

              )

            else

              (* Find all identifiers with this identifier as prefix *)
              let suffixes = 
                List.fold_left 
                  (fun a (s, s') -> 
                     try 
                       (I.get_suffix t s, s') :: a 
                     with Invalid_argument _ -> a)
                  []
                  type_map
              in

              (* Identifier was not declared and no identifier with
                 prefix declared *)
              if suffixes = [] then 

                (* Fail *)
                raise 
                  (Failure 
                     (Format.asprintf 
                        "Type %a in %a is not declared" 
                        I.pp_print_ident t
                        A.pp_print_position A.dummy_pos))

              else

                (* Append declarations with all suffixes appended  *)
                let rec aux accum = function 

                  (* All tuple fields consumed *)
                  | [] -> accum

                  (* Suffix j with type s *)
                  | (j, s) :: tl -> 

                    let d' = 
                      A.ConstDecl 
                        (A.FreeConst 
                           (I.add_index c j, ast_type_of_lustre_type s))
                    in

                    (* Expand to declaration [const c.j;] *)
                    aux 
                      (d' :: accum)
                      tl 
                in

                (* Push declarations for indexed identifiers *)
                let tl' = aux tl suffixes in

                (* Output dropped const declaration *)
                Format.printf "-- %a@." A.pp_print_declaration d;

                check_declaration
                  (type_map, free_types, type_ctx, const_val, accum)
                  tl'

      )

    (* const c = e; *)
    | A.ConstDecl (A.UntypedConst (c, e)) as d :: tl ->

      if

        (* Identifier must not be declared *)
        List.exists (function (n, _) -> n = c) type_ctx 

      then

        (* Fail *)
        raise 
          (Failure 
             (Format.asprintf 
                "Identifier %a is redeclared as constant in %a" 
                I.pp_print_ident c
                A.pp_print_position A.dummy_pos));

      (match type_of_expr type_ctx const_val e with 

        | Const v, Type t ->

          (* Output dropped const declaration *)
          Format.printf "-- %a@." A.pp_print_declaration d;

          check_declaration
            (

              (* No new alias type *)
              type_map, 

              (* No new free types *)
              free_types, 

              (* Add to typing context *)
              (c, t) :: type_ctx, 

              (* Add to constant declaration *)
              (c, v) :: const_val,

              (* Drop constant declaration *)
              accum

            )
            tl

        | Expr _, _ -> 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a in %a is not constant" 
                  A.pp_print_expr e
                  A.pp_print_position A.dummy_pos))

        | IndexedExpr lc, IndexedType lt -> assert false

      )


(*

  (* const c : t = e; *)
  | A.ConstDecl (A.TypedConst (c, e, t)) as d :: tl ->


    let (v, Type t) = type_of_expr type_ctx const_val e in

    check_declaration
      (

        (* No new alias type *)
        type_map, 

        (* No new free types *)
        free_types, 

        (* Add to typing context *)
        (c, t) :: type_ctx, 

        (* Add to constant declaration *)
        (c, v) :: const_val,

        (* Drop constant declaration *)
        accum

      )
      tl
      
*)
*)


let check_program p = 
  let state = check_declarations init_state p in

  Format.printf "%a@." pp_print_state state


(* 
   Local Variables:
   compile-command: "make -C .. lustre-checker"
   indent-tabs-mode: nil
   End: 
*)
  
