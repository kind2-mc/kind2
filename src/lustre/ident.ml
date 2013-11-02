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


(* An identifier *)
type t = 

  (* A string identifier *)
  | StringId of string 

  (* An indexed identifier  *)
  | IndexedId of string * index

(* An index of an identifier *)
and index = 

  (* Identifier as index *)
  | IdentIndex of t

  (* Integer as index *)
  | IntIndex of int


(* ********************************************************************** *)
(* Pretty-printers                                                        *)
(* ********************************************************************** *)


(* Pretty-print an identifier *)
let rec pp_print_ident ppf = function
  | StringId i -> Format.fprintf ppf "%s" i
  | IndexedId (i, j) -> Format.fprintf ppf "%s.%a" i pp_print_index j

(* Pretty-print an index *)
and pp_print_index ppf = function 
  | IdentIndex i -> Format.fprintf ppf "%a" pp_print_ident i
  | IntIndex i -> Format.fprintf ppf "%d" i


(* ********************************************************************** *)
(* Constructors                                                           *)
(* ********************************************************************** *)


(* Construct an identifier of a string *)
let mk_string_id s = StringId s

(* Construct an identifier indexed by an integer *)
let mk_indexed_id_of_int s i = IndexedId (s, IntIndex i)

(* Construct an identifier indexed by an identifier *)
let mk_indexed_id_of_ident s i = IndexedId (s, IdentIndex i)

(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
