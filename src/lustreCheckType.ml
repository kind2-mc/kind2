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



(* Return type of expression *)
let rec type_of_expr type_ctx const_val = function

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
              
              IndexedType suffixes 

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





(* 
   
   type_aliases is an association list from type names to basic types,
   free_types is a list of types 
   indexed_types is an association list of type names to their indexes 

   A type occurs at most in one of type_aliases, free_types and indexed_types

*)
let rec check_declaration
    (basic_types, indexed_types, free_types, type_ctx, const_val, accum) = 


  (* Return true if type [t] was already declared *)
  let type_is_declared t = 

    (* Check for [t] in list of free types *)
    (List.exists (function s -> s = t) free_types) ||

    (* Check for [t] in type aliases *)
    (List.exists (function (s, _) -> s = t) type_aliases) || 

    (* Check if [t] is an indexed type *)
    (List.exists (function (s, _) -> s = t) indexed_types) 

  in

  (* Convert a parsed type to a built-in type *)
  let lustre_type_of_ast_type = function

    | A.Bool -> T.bool

    | A.Int -> T.int

    | A.Real -> T.real

    | A.IntRange (i, j) -> 

      let ci = int_const_of_expr type_ctx const_val i in

      let cj = int_const_of_expr type_ctx const_val j in

      T.mk_int_range ci cj

    | A.EnumType l -> T.mk_enum l

    | A.UserType t -> T.mk_free_type t

    | _ -> raise (Invalid_argument "lustre_type_of_ast_type")
  


  (* ******************************************************************** *)
  (* Alias type declarations                                              *)
  (* ******************************************************************** *)

  let check_alias_type_declaration t t' defs_stack = 

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


    (* An alias declarations may add a new alias, a new indexed type
       or push new flattened type declarations to be parsed *)
    let type_aliases', indexed_types', defs_stack' = match t' with 

      (* ********************************************************** *)

      (* type t = struct { i1: t1; ...; in: tn };

         Expand to declarations

         type t.i1 = t1;
         ...
         type t.in = tn;

      *)
      | A.RecordType l -> 

        (* Append type declarations for indexed identifiers *)
        let rec aux defs_stack = function 

          (* All record fields consumed *)
          | [] -> defs_stack

          (* A record field with identifier j of type s *)
          | (j, s) :: tl -> 

            (* Construct an index of an identifier *)
            let idx = I.index_of_ident j in

            (* Expand to declaration [type t.j = s] *)
            aux 
              ((A.TypeDecl 
                  (A.AliasType (I.add_index t idx, s))) :: defs_stack)
              tl 

        in

        (* Push declarations for indexed identifiers *)
        let defs_stack' = aux defs_stack l in

        (* Associate identifier with indexes and unfold to new indexed
           declarations *)
        (type_aliases, indexed_types, defs_stack')


      (* ********************************************************** *)

      (* type t = [ t1, ..., tn ];

         Expand to declarations

         type t[0] = t1;
         ...
         type t[n-1] = tn;

      *)
      | A.TupleType l -> 

        (* Append type declarations for indexed identifiers *)
        let rec aux (defs_stack, j) = function 

          (* All tuple fields consumed *)
          | [] -> defs_stack

          (* A tuple field type s *)
          | s :: tl -> 

            (* Construct an index of an integer *)
            let idx = I.index_of_int j in

            (* Expand to declaration to [type t[j] = s] *)
            aux 
              (((A.TypeDecl 
                   (A.AliasType (I.add_index t idx, s))) :: accum), 
               succ j)
              tl

        in

        (* Push declarations for indexed identifiers *)
        let defs_stack' = aux (defs_stack, 0) l in

        (* Associate identifier with indexes and unfold to new indexed
           declarations *)
        (type_aliases, indexed_types, defs_stack')


      (* ********************************************************** *)

      (* type t = s^e;

         Expand to declarations

         type t[0] = s;
         ...
         type t[e-1] = s;

      *)
      | A.ArrayType (s, e) -> 

        (* Evaluate size of array to a constant integer *)
        let n = int_const_of_expr type_ctx const_val e in

        (* Array size must must be at least one *)
        if n <= 0 then 

          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a must be positive in %a" 
                  A.pp_print_expr e
                  A.pp_print_position A.dummy_pos));

        (* Append type declarations for indexed identifiers *)
        let rec aux defs_stack = function

          (* All array fields consumed *)
          | 0 -> defs_stack

          (* An array field *)
          | i -> 

            (* Construct an index of an integer *)
            let idx = I.index_of_int (pred i) in

            (* Expand to declaration to [type t[j] = s] *)
            aux 
              (A.TypeDecl 
                 (A.AliasType (I.add_index t idx, s)) :: defs_stack)
              (pred i)

        in

        (* Push declarations for indexed identifiers *)
        let defs_stack' = aux defs_stack n in

        (* Associate identifier with indexes and unfold to new indexed
             declarations *)
        (type_aliases, indexed_types, defs_stack')


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

        (* Continue with next declarations *)
        (basic_types', indexed_types, defs_stack)


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

        (* Append declarations with all suffixes appended  *)
        let rec aux defs_stack = function 

          (* All indexes consumed *)
          | [] -> defs_stack

          (* Suffix j with type s *)
          | (j, s) :: tl -> 

            (* Expand to declaration [type t.j = s] *)
            aux 
              ((A.TypeDecl 
                  (A.AliasType (I.add_index t j, s))) :: defs_stack)
              tl 
        in

        (* Push declarations for indexed identifiers *)
        let defs_stack' = aux defs_stack (List.assoc t' indexed_types) in 

        (* Continue with next declarations *)
        (basic_types, indexed_types, defs_stack')

      (* type t = t';

         If t' was defined as

         type t';;

         expand to

         type t = t'';
         
      *)
      | A.UserType t' when List.mem t' free_types ->  
        
        (* Add association of type to free type *)
        let basic_types' = 
          (t, T.mk_free_type t') :: basic_types 
        in
        
        (* Continue with next declarations *)
        (basic_types', indexed_types, defs_stack)
        

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
      | A.Bool as t'
      | A.Int as t'
      | A.Real as t'
      | A.IntRange _ as t' -> 

        (* Basic type of type in AST *)
        let t'' = lustre_type_of_ast_type t' in

        (* Add alias for basic type *)
        let basic_types' = (t, t'') :: basic_types in

        (* Get indexes of identifier of type *)
        let (id, suf) = t in
        
        let aux indexed_types = function 
          | [] -> indexed_types
          | j :: tl -> 

            let rec aux2 accum = function

              (* Prefix of identifier not found *)
              | [] -> 

                (* Add association of prefix with suffix and type *)
                (t, [(j, t'')]) :: accum

              (* Prefix of identifier found *)
              | (s, l) :: tl when s = t -> 

                (* Add association of prefix with suffix and type, and
                   finish *)
                List.rev_append ((s, (j, t'') :: l) :: tl) accum

              (* Recurse to keep searching for prefix of identifier *)
              | h :: tl -> aux2 (h :: accum) tl

            in

            aux (aux2 [] indexed_types) tl

        in

        let indexed_types' = aux indexed_types suf in
        
        (* Continue with next declarations *)
        (basic_types', indexed_types', defs_stack)

    in

    (* Recurse with new declarations *)
    check_declaration
      (type_aliases', free_types, indexed_types', type_ctx, const_val, accum)
      tl'

  in

  function

    (* All declarations processed, return in original order *)
    | [] -> List.rev accum


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

let check_program p = 

  let p' =
    check_declaration
      ([], [], [], [], [])
      p
  in
  
  p'

(* 
   Local Variables:
   compile-command: "make -C .. lustre-checker"
   indent-tabs-mode: nil
   End: 
*)
  
