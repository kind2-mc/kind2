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
              Ast.pp_print_ident t
              Ast.pp_print_position Ast.dummy_pos
              Ast.pp_print_position Ast.dummy_pos))
        
  in 

  (* Rewrite each occurrence of type [t] to [t'] *)
  let rec rewrite_type t t' = function

    (* Keep basic types *)
    | Ast.Bool
    | Ast.Int
    | Ast.Real
    | Ast.IntRange _
    | Ast.EnumType _ as e -> e

    (* Rewrite matching user type *)
    | Ast.UserType s when s = t -> t'

    (* Keep unmatched user type *)
    | Ast.UserType _ as e -> e

    (* Rewrite each type of a tuple type *)
    | Ast.TupleType l -> Ast.TupleType (List.map (rewrite_type t t') l)

    (* Rewrite each field of a record type *)
    | Ast.RecordType l -> 

      Ast.RecordType 
        (List.map (function (n, k) -> (n, rewrite_type t t' k)) l)

    (* Rewrite type of array *)
    | Ast.ArrayType (l, e) -> Ast.ArrayType (rewrite_type t t' l, e)

  in

  function

    (* TYPE s = t; *)
    | Ast.TypeDecl (Ast.AliasType (t, t')) -> 

      (

        (* Fail if type is redeclared *)
        check_redeclared t;

        (* Rewrite all types t to s *)
        let type_map' = 
          List.map (function (n, e) -> (n, rewrite_type t t' e)) type_map
        in

        (type_map', free_types)

      )


    (* TYPE t; must remain free *)
    | Ast.TypeDecl (Ast.FreeType t) -> 

      (

        (* Fail if type is redeclared *)
        check_redeclared t;

        (* Add type to free types *)
        let free_types' = t :: free_types in

        (type_map, t :: free_types')

      )

    (* *)
    | _ -> (type_map, free_types)




let resolve_type_aliases decl = 

  let rec is_basic free_types = function 

    (* Basic types *)
    | Ast.Bool
    | Ast.Int
    | Ast.IntRange _
    | Ast.Real
    | Ast.EnumType _ -> true

    (* User type is basic if it is free *)
    | Ast.UserType t -> List.mem t free_types

    (* Tuple type is basic if each element type is basic *)
    | Ast.TupleType l -> List.for_all (is_basic free_types) l

    (* Record type is basic if each field type is basic *)
    | Ast.RecordType l -> 

      List.for_all (function (_, t) -> is_basic free_types t) l

    (* Array type is basic if element type is basic *)
    | Ast.ArrayType (l, _) -> is_basic free_types l

  in

  (* Collect all defined types and normalize *)
  let type_map, free_types =
    List.fold_left 
      add_type_alias_from_decl
      ([], [])
      decl
  in

  (try 
     
     (* Check if all types are basic *)
     let (n, _) = 
       List.find (function (_, t) -> not (is_basic free_types t)) type_map 
     in 
     
     (* Fail *)
     raise 
       (Failure 
          (Format.asprintf 
             "Type %a is not defined as free" 
             Ast.pp_print_ident n))

   with Not_found -> ())

(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
