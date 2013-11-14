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

module I = LustreIdent
module A = LustreAst


type value = 
  | ValBool of bool
  | ValNum of string
  | ValDec of string
  | ValEnum of ident
  | ValTuple of value list
  | ValRecord of (I.t * value) list


let rec eval ident_map = 

  let eval_int ident_map e = match eval ident_map e with

    | ValNum n -> 

      (try int_of_string n with 
        | Failure _ -> 

          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a is not a constant integer" 
                  A.pp_print_expr e)))
        
    | ValBool _
    | ValDec _ -> 
      
      raise 
        (Failure 
           (Format.asprintf 
              "Expression %a is not a constant integer" 
              A.pp_print_expr e))

  in

  let eval_int ident_map e = match eval ident_map e with

    | ValNum n -> 

      (try int_of_string n with 
        | Failure _ -> 

          raise 
            (Failure 
               (Format.asprintf 
                  "Expression %a is not a constant integer" 
                  A.pp_print_expr e)))
        
    | ValBool _
    | ValDec _ -> 
      
      raise 
        (Failure 
           (Format.asprintf 
              "Expression %a is not a constant integer" 
              A.pp_print_expr e))

  in


  let find_value ident_map i = 
    try List.assoc ident_map i with 
      | Not_found -> 
        failwith (Format.asprintf "No value for %a" I.pp_print_ident i)
  in

  function
  
    | A.Ident (p, i) -> find_value ident_map i
      
    | A.RecordProject (_, r, i) -> 
      
      (match eval r with 
        | ValRecord l -> 
          (let e = 
             try List.assoc l i with
               | Not_found ->         
                 failwith (Format.asprintf "No value for %a" I.pp_print_ident i)
           in

           eval ident_map e)
        | _ ->                  
          failwith (Format.asprintf "Not a record: %a" A.pp_print_expr e))

       
    | A.TupleProject(p, e1, e2) -> 
      
      let ident_map' = add_tuple_to_ident_map ident_map (eval ident_map e1) in
      
      find_value
        ident_map'
        (I.add_int r (eval_int ident_map e2))
        
    | A.True -> ValBool true
    | A.False -> ValBool false
    | A.Num (_, e)-> ValNum e
    | A.Dec (_, e) -> ValDec e
      
    | A.ToInt (p, e) -> 
      
      

      A.ToInt 
        (p, 
         substitute_type_in_expr type_map e)
        
    | A.ToReal (p, e) -> 
      
      A.ToReal 
        (p, 
         substitute_type_in_expr type_map e)
        
    | A.ExprList (p, l) -> 

      A.ExprList (p, List.map (substitute_type_in_expr type_map) l)

    | A.TupleExpr (p, l) -> 

      A.TupleExpr (p, List.map (substitute_type_in_expr type_map) l)

    | A.ArrayConstr (p, e1, e2) ->

      A.ArrayConstr
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)
        
    | A.ArraySlice (p, e, l) ->

      A.ArraySlice
        (p,
         substitute_type_in_expr type_map e, 
         List.map
           (function (e1, e2) -> 
             (substitute_type_in_expr type_map e1, 
              substitute_type_in_expr type_map e2))
           l)
        
    | A.ArrayConcat (p, e1, e2) ->

      A.ArrayConcat
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)
        
    | A.RecordConstruct (p, l) -> 

      A.RecordConstruct
        (p,
         List.map
           (function (n, e) -> 
             (n, substitute_type_in_expr type_map e))
           l)

    | A.Not (p, e) -> 

      A.Not
        (p, 
         substitute_type_in_expr type_map e)

    | A.And (p, e1, e2) -> 

      A.And 
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)

    | A.Or (p, e1, e2) ->

      A.Or
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)
        
    | A.Xor (p, e1, e2) ->
      
      A.Xor
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)
        
    | A.Impl (p, e1, e2) ->
      
      A.Impl
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)

    | A.OneHot (p, l) -> 

      A.OneHot
        (p,
         List.map (substitute_type_in_expr type_map) l)

    | A.Uminus (p, e) ->

      A.Uminus
        (p, 
         substitute_type_in_expr type_map e)

    | A.Mod (p, e1, e2) ->
      
      A.Mod
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)
        
    | A.Minus (p, e1, e2) ->
      
      A.Minus
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)

    | A.Plus (p, e1, e2) ->
      
      A.Plus
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)

    | A.Div (p, e1, e2) ->
      
      A.Div
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)

    | A.Times (p, e1, e2) ->
      
      A.Times
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)

    | A.Intdiv (p, e1, e2) ->
      
      A.Intdiv
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)

    | A.Ite (p, e1, e2, e3) -> 

      A.Ite 
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2,
         substitute_type_in_expr type_map e3)

    | A.With (p, e1, e2, e3) -> 

      A.With
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2,
         substitute_type_in_expr type_map e3)

    | A.Eq (p, e1, e2) ->
      
      A.Eq
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)
        
    | A.Neq (p, e1, e2) ->
      
      A.Neq
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)

    | A.Lte (p, e1, e2) ->
      
      A.Lte
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)

    | A.Lt (p, e1, e2) ->
      
      A.Lt
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)

    | A.Gte (p, e1, e2) ->
      
      A.Gte
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)

    | A.Gt (p, e1, e2) ->
      
      A.Gt
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)

    | A.When (p, e1, e2)  ->
      
      A.When
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)

    | A.Current (p, e) -> 

      A.Current
        (p, 
         substitute_type_in_expr type_map e)

    | A.Condact (p, e1, e2, l) ->

      A.Condact
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2,
         List.map (substitute_type_in_expr type_map) l)

    | A.Pre (p, e) -> 

      A.Pre
        (p, 
         substitute_type_in_expr type_map e)

    | A.Fby (p, e1, i, e2) ->

      A.Fby
        (p, 
         substitute_type_in_expr type_map e1,
         i,
         substitute_type_in_expr type_map e2)

    | A.Arrow (p, e1, e2)  ->
      
      A.Arrow
        (p, 
         substitute_type_in_expr type_map e1, 
         substitute_type_in_expr type_map e2)

    | A.Call (p, n, l) -> 

      A.Call (p, n, List.map (substitute_type_in_expr type_map) l)

    | A.CallParam (p, n, t, l) -> 

      A.CallParam 
        (p,
         n,
         List.map (substitute_type_in_lustre_type type_map) t,
         List.map (substitute_type_in_expr type_map) l)


(* 
   Local Variables:
   indent-tabs-mode: nil
   End: 
*)
  
