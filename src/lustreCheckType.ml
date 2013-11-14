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


(* Raise exception if type [t] was already declared as free or alias *)
let type_is_declared free_types type_map t = 
  
  (* Check for [t] in list of free types and map of types *)
  (List.exists (function s -> s = t) free_types) ||
    (List.exists (function (s, _) -> s = t) type_map)


(* Substitute basic type for alias type *)    
let rec substitute_type_in_lustre_type free_types type_map = function 

  (* Basic types *)
  | A.Bool
  | A.Int
  | A.IntRange _
  | A.Real 
  | A.EnumType _ as t -> t
    
  (* Substitute for type *)
  | A.UserType t as s -> 
    
    (try 

       (* Substitue basic type for alias type  *)
       List.assoc t type_map 

     (* Type may be free *)
     with Not_found -> 

       if 

         (* Free types must be declared *)
         List.mem t free_types 

       then 
         
         (* Keep free type *)
         s

       else

        (* Fail *)
        raise 
          (Failure 
             (Format.asprintf 
                "Type %a is undefined in %a" 
                I.pp_print_ident t
                A.pp_print_position A.dummy_pos))
         
    )
      
  (* Substitute within tuple type *)
  | A.TupleType l -> 

    A.TupleType 
      (List.map 
         (substitute_type_in_lustre_type free_types type_map) 
         l)

  (* Substitute within record type *)
  | A.RecordType l -> 
    
    A.RecordType 
      (List.map 
         (function (n, t) -> 
           (n, substitute_type_in_lustre_type free_types type_map t)) 
         l)

  (* Substitute within array type *)
  | A.ArrayType (t, e) -> 

    A.ArrayType 
      (substitute_type_in_lustre_type free_types type_map t, e)


let rec type_of_expr type_ctx const_val = function

  (* Identifier *)
  | A.Ident (p, i) as e -> 

    (

      let t = 

        (* Get type from context *)
        try List.assoc i type_ctx 
              
            
        with Not_found -> 
          
          (* Fail *)
          raise 
            (Failure 
               (Format.asprintf 
                  "Identifier %a in %a is not declared" 
                  I.pp_print_ident i
                  A.pp_print_position p))

      in

      let v = 
        
        (* Substitute value if identifier is a constant *)
        try List.assoc i const_val with Not_found -> e

      in

      (* Return value and type *)
      (v, t)

    )
         

(* 
   
   type_map is an association list from type names to basic types. 
*)
let check_declaration (type_map, free_types, type_ctx, const_val, accum) = function

  (* TYPE t = t'; 

     Type t' must have been defined before, type t must not. *)
  | A.TypeDecl (A.AliasType (t, t')) -> 
    
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

      (match t' with 

        (* t' is not a basic type *)
        | A.UserType s ->
          
          if
            
            (* Type t' must have been declared *)
            not (type_is_declared free_types type_map s)
              
          then
            
            (* Fail *)
            raise 
              (Failure 
                 (Format.asprintf 
                    "Type %a in %a is not declared" 
                    I.pp_print_ident t
                    A.pp_print_position A.dummy_pos))

        (* t' is a basic type *)
        | _ -> ());
      

      (* Reduce type t' *)
      let t'' = 
        
        try 
          
          (* All types in type_map are basic *)
          List.assoc t type_map
        
        (* t' is already basic *)
        with Not_found -> t'

      in
      
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
        
    )
      
      
  (* TYPE t; must remain free *)
  | A.TypeDecl (A.FreeType t) as d-> 
    
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

    )

  (* TYPE t = { i1: t1; ...; in: tn }  

     TODO: resolve each tj to a basic type, add (t.i1, t1) to type_map

     t1 may be a record type itself

  *)
  | A.TypeDecl (A.RecordType l) -> 

    (


      let type_ctx' = 

        List.fold_left
          (fun a (n, t) -> )
          type_ctx
          l
      in

    )


  (* CONST c : t; *)
  | A.ConstDecl (A.FreeConst (c, t)) as d -> 

    (

        (* No new alias type *)
        type_map, 

        (* No new free types *)
        free_types, 

        (* Add to typing context *)
        (c, t) :: type_ctx, 
        
        (* No new constant declaration *)
        const_val,

        (* Drop constant declaration *)
        accum

      )

  (* CONST c = e; *)
  | A.ConstDecl (A.UntypedConst (c, e)) as d ->

    
    let (v, t) = type_of_expr type_ctx const_val e in
    
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
      
      

let check_program p = 

  let _, _, _, _, p' =
    List.fold_left 
      check_declaration
      ([], [], [], [], [])
      p
  in
  
  ()

(* 
   Local Variables:
   compile-command: "make -C .. lustre-checker"
   indent-tabs-mode: nil
   End: 
*)
  
