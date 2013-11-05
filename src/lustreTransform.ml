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
module E = LustreExpr
module I = LustreIdent
module N = LustreNode
module T = LustreType


let add_type_alias_from_decl (type_map, free_types) = 

  (* Raise exception if identifier [t] was already declared *)
  let check_redeclared t = 
    
    if

      (* Check for [t] in list of free types and map of types *)
      (List.exists (function s -> s = t) free_types) ||
      (List.exists (function (s, _) -> s = t) type_map)

    then

      (* Fail *)
      raise 
        (Failure 
           (Format.asprintf 
              "Type %a defined in %a is redeclared in %a" 
              A.pp_print_ident t
              A.pp_print_position A.dummy_pos
              A.pp_print_position A.dummy_pos))
        
  in 

  (* Rewrite each occurrence of type [t] to [t'] *)
  let rec rewrite_type t t' = function

    (* Keep basic types *)
    | A.Bool
    | A.Int
    | A.Real
    | A.IntRange _
    | A.EnumType _ as e -> e

    (* Rewrite matching user type *)
    | A.UserType s when s = t -> t'

    (* Keep unmatched user type *)
    | A.UserType _ as e -> e

    (* Rewrite each type of a tuple type *)
    | A.TupleType l -> A.TupleType (List.map (rewrite_type t t') l)

    (* Rewrite each field of a record type *)
    | A.RecordType l -> 

      A.RecordType 
        (List.map (function (n, k) -> (n, rewrite_type t t' k)) l)

    (* Rewrite type of array *)
    | A.ArrayType (l, e) -> A.ArrayType (rewrite_type t t' l, e)

  in

  function

    (* TYPE t = t'; *)
    | A.TypeDecl (A.AliasType (t, t')) -> 

      (

        (* Fail if type is redeclared *)
        check_redeclared t;

        (* Reduce type *)
        let t'' = 
          List.fold_left 
            (fun a (t, t') -> rewrite_type t t' a)
            t'
            type_map
        in

        (* Check if type is rewritten to itself *)
        (match t'' with

          | A.UserType s when t = s -> 

            (* Fail *)
            raise 
              (Failure 
                 (Format.asprintf 
                    "Cyclic type alias involving %a" 
                    A.pp_print_ident t));
            
          | _ -> ()

        );

        (* Reduce all types *)
        let type_map' = 
          List.map (function (n, e) -> (n, rewrite_type t t' e)) type_map
        in

        (* Add type to map and return *)
        ((t, t'') :: type_map', free_types)

      )


    (* TYPE t; must remain free *)
    | A.TypeDecl (A.FreeType t) -> 

      (

        (* Fail if type is redeclared *)
        check_redeclared t;

        (* Add type to free types *)
        let free_types' = t :: free_types in


        (* Add type to free types and return *)
        (type_map, free_types')

      )

    (* Not a type declaration *)
    | _ -> (type_map, free_types)



(* Collect and normalize all types 

   Return a map of types to basic types and a list of free types.  *)
let resolve_type_aliases decl = 

  (* Return true if type is basic or free *)
  let rec is_basic free_types = function 

    (* Basic types *)
    | A.Bool
    | A.Int
    | A.IntRange _
    | A.Real
    | A.EnumType _ -> true

    (* User type is basic if it is free *)
    | A.UserType t -> List.mem t free_types

    (* Tuple type is basic if each element type is basic *)
    | A.TupleType l -> List.for_all (is_basic free_types) l

    (* Record type is basic if each field type is basic *)
    | A.RecordType l -> 

      List.for_all (function (_, t) -> is_basic free_types t) l

    (* Array type is basic if element type is basic *)
    | A.ArrayType (l, _) -> is_basic free_types l

  in

  (* Collect all defined types and normalize *)
  let type_map, free_types =
    List.fold_left 
      add_type_alias_from_decl
      ([], [])
      decl
  in

  (try 
     
     (* Check if all types are basic or free *)
     let (n, t) = 
       List.find (function (_, t) -> not (is_basic free_types t)) type_map 
     in 
     
     (* Fail *)
     raise 
       (Failure 
          (Format.asprintf 
             "Type %a is not defined as free" 
             A.pp_print_lustre_type t))

   (* No type is not basic or free *)
   with Not_found -> ());

  (* Return types *)
  (type_map, free_types)


let rec substitute_type_in_lustre_type type_map = function 

  (* Basic types *)
  | A.Bool
  | A.Int
  | A.IntRange _
  | A.Real 
  | A.EnumType _ as t -> t
  
  (* Substitute for type *)
  | A.UserType t -> List.assoc t type_map  

  (* Substitute within tuple type *)
  | A.TupleType l -> 

    A.TupleType 
      (List.map 
         (substitute_type_in_lustre_type type_map) 
         l)

  (* Substitute within record type *)
  | A.RecordType l -> 
    
    A.RecordType 
      (List.map 
         (function (n, t) -> 
           (n, substitute_type_in_lustre_type type_map t)) 
         l)

  (* Substitute within array type *)
  | A.ArrayType (t, e) -> 

    A.ArrayType 
      (substitute_type_in_lustre_type type_map t, e)


let substitute_type_in_const_decl type_map = function

  | A.FreeConst (n, t) -> 
    (n, substitute_type_in_lustre_type type_map t)

  | A.UntypedConst _ as c -> c

  | A.TypedConst (n, e, t) -> 
    (n, e, substitute_type_in_lustre_type type_map t)


let substitute_type_in_var_decl type_map (n, t, c) = 
  (n, substitute_type_in_lustre_type type_map t, c)


let substitute_type_in_typed_decl type_map (n, t) =
  (n, substitute_type_in_lustre_type type_map t)


let substitute_type_in_clocked_typed_decl type_map (n, t, c, s) =
  (n, substitute_type_in_lustre_type type_map t, c)


let substitute_type_in_const_clocked_typed_decl type_map (n, t, c, s) =
  (n, substitute_type_in_lustre_type type_map t, c, s)


let substitute_type_in_node_local_decl type_map = function

  | A.NodeConstDecl c -> 

    A.NodeConstDecl (substitute_type_in_const_decl type_map c)

  | A.NodeVarDecl v -> 

    A.NodeConstDecl (substitute_type_in_var_decl type_map v)
    




let substitute_type_in_declaration type_map accum = function

  (* Keep tuple, record, array and enum type declarations *)
  | A.TypeDecl (A.AliasType (_, A.TupleType _))
  | A.TypeDecl (A.AliasType (_, A.RecordType _ ))
  | A.TypeDecl (A.AliasType (_, A.ArrayType _))
  | A.TypeDecl (A.AliasType (_, A.EnumType _)) as t -> t :: accum

  (* Remove alias type declarations *)
  | A.TypeDecl (A.AliasType (_, A.Bool))
  | A.TypeDecl (A.AliasType (_, A.Int))
  | A.TypeDecl (A.AliasType (_, A.IntRange _)) 
  | A.TypeDecl (A.AliasType (_, A.Real))
  | A.TypeDecl (A.AliasType (_, A.UserType _)) -> accum

  (* Substitute type in constant declaration *)
  | A.ConstDecl (A.FreeConst (n, t)) -> 

    (A.ConstDecl 
      (A.FreeConst (n, substitute_type_in_lustre_type type_map t))) :: accum

  (* Substitute type in a node declaration *)
  | A.NodeDecl (n, p, i, o, d, e, c) -> 

    A.NodeDecl 
      (n, 
       p, 
       List.map (substitute_type_in_const_clocked_typed_decl type_map) i,
       List.map (substitute_type_in_clocked_typed_decl type_map) o,
       List.map (substitute_type_in_node_local_decl type_map) d,
       List.map (substitute_type_in_node_equation type_map) e,
       List.map (substitute_type_in_contract type_map) c)

;;

let decl = [
  A.TypeDecl (A.FreeType "t1");
  A.TypeDecl (A.AliasType ("t2", A.UserType "t1"))
  ]

;;

resolve_type_aliases decl;;
    
(* 
   Local Variables:
   compile-command: "ocamlbuild -tag menhir lustreTransform.native"
   tuareg-interactive-program: "./lustre.top -I ./_build"
   indent-tabs-mode: nil
   End: 
*)
  
