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


(* ********************************************************************** *)
(* Types                                                                  *)
(* ********************************************************************** *)

(* An index of an identifier *)
type index = 

  (* String as index *)
  | StringIndex of string

  (* Integer as index *)
  | IntIndex of int


(* An identifier *)
type t = string * (index list)


(* ********************************************************************** *)
(* Pretty-printers                                                        *)
(* ********************************************************************** *)


(* Pretty-print an index *)
let pp_print_index ppf = function 
  | StringIndex i -> Format.fprintf ppf ".%s" i
  | IntIndex i -> Format.fprintf ppf "[%d]" i


(* Pretty-print a list of indexes *)
let rec pp_print_index_list ppf = function 
  | [] -> ()
  | h :: tl -> pp_print_index ppf h; pp_print_index_list ppf tl


(* Pretty-print an identifier *)
let rec pp_print_ident ppf (s, i) = 

  Format.fprintf ppf "%s%a" s pp_print_index_list i

(* ********************************************************************** *)
(* Constructors                                                           *)
(* ********************************************************************** *)


(* Construct an identifier of a string *)
let mk_string_id s = (s, [])


(* Add a string as an index to an identifier *)
let add_string_index (s, i) j = (s, i @ [StringIndex j])


(* Add an integer as an index to an identifier *)
let add_int_index (s, i) j = (s, i @ [IntIndex j])


(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
