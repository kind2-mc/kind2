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

(* A node declaration *)
type t =

    { 
      
      (* ID of the node *)
      ident : LustreIdent.t;

      (* Input *)
      in_params : LustreIdent.t * LustreType.t list;

      (* Output *)
      out_params : LustreIdent.t * LustreType.t list;

      (* Local constants *)
      consts : (LustreIdent.t * (LustreType.t * LustreExpr.t)) list;

      (* Local variables *)
      vars : (LustreIdent.t * LustreType.t) list;

      (* Equations *)
      equations : (LustreIdent.t * LustreExpr.t) list;
  
      (* Calls to nodes *)
      node_calls : LustreIdent.t * LustreIdent.t list;

      (* Assertions *)
      asserts : LustreExpr.t list;

      (* Properties *)
      properties : LustreExpr.t list;
      
      (* Pre-conditions *)
      requires : LustreExpr.t list;
      
      (* Post-conditions *)
      ensures : LustreExpr.t list;
      
    } 

let pp_print_typed_ident ppf (i, t) =
  Format.fprintf ppf "@[<hv 2>%a:@ %a@]"
    
  
  
(*
let pp_print_node 
    ppf 
    { ident; 
      in_params; 
      out_params; 
      consts; 
      vars; 
      equations; 
      asserts; 
      properties;
      requires;
      ensures } =

    Format.fprintf ppf
      "@[<hv>@[<hv 2>node %a@ \
       @[<hv 1>(%a)@]@;<1 -2>\
       returns@ @[<hv 1>(%a)@];@]@ \
       %a\
       %a\
       @[<hv 2>let@ \
       %a@;<1 -2>\
       tel;@]@]" 
      I.pp_print_ident ident
      (pp_print_list pp_print_typed_ident ";@ ") i
      (pp_print_list pp_print_clocked_typed_ident ";@ ") o
      pp_print_contract r
      pp_print_node_local_decl lc
      (pp_print_list pp_print_node_equation "@ ") e 
*)

(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
