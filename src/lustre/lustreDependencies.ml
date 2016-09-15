(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)

open Lib

module I = LustreIdent
module ISet = I.Set
module IMap = I.Hashtbl

module A = LustreAst

(** Enum over declaration types. *)
type decl =
| NodeOrFun | Type | Contract | Const

(** Reference to an unknown declaration. *)
exception Unknown_decl of decl * I.t

(** Integer representation of a declaration. *)
let int_of_decl = function
| NodeOrFun -> 0
| Type -> 1
| Contract -> 2
| Const -> 3

module Decl = struct
  type t = decl
  let equal = (=)
  let hash = int_of_decl
end

module DeclMap = Hashtbl.Make (Decl)

(** Pretty printer for declarations. *)
let pp_print_decl fmt = function
| NodeOrFun -> Format.fprintf fmt "node or function"
| Type -> Format.fprintf fmt "type"
| Contract -> Format.fprintf fmt "contract"
| Const -> Format.fprintf fmt "constant"



(** A dependency map from declarations to identifiers. *)
type dep = ISet.t DeclMap.t

(** Empty dependency map. *)
let dep_empty : dep = DeclMap.create 3

(** Adds a dependency in a dependency map. *)
let dep_add dep decl ident =
  ( try DeclMap.find dep decl
    with Not_found -> ISet.empty )
  |> ISet.add ident
  |> DeclMap.replace dep decl

(** Checks if a dependency map mentions a declaration. *)
let dep_mem dep decl ident =
  try DeclMap.find dep decl |> ISet.mem ident
  with Not_found -> false



(** A dependency context. *)
type t = (dep IMap.t) DeclMap.t

(** Empty dependency context. *)
let empty : t = DeclMap.create 3

(** Adds a dependency in a dependency context. *)
let add deps (key_type, key_ident) (val_type, val_ident) =
  let deps =
    try DeclMap.find deps key_type with Not_found -> (
      let deps' = IMap.create 3 in
      DeclMap.replace deps key_type deps' ;
      deps'
    )
  in
  let dep =
    try IMap.find deps key_ident with Not_found -> (
      let dep = DeclMap.create 3 in
      IMap.replace deps key_ident dep ;
      dep
    )
  in
  
  (* Transitivity *)
  (try DeclMap.iter
         (fun t -> ISet.iter (dep_add dep t))
         (IMap.find deps val_ident)
   with Not_found -> ());
  
  dep_add dep val_type val_ident

(** Checks if an identifier depends on a declaration. *)
let mem deps (key_type, key_ident) (val_type, val_ident) =
  try dep_mem (
    IMap.find (DeclMap.find deps key_type) key_ident
  ) val_type val_ident
  with Not_found -> false



(** Identifier corresponding to a declaration. *)
let info_of_decl = function
| A.TypeDecl (pos, A.AliasType (_, ident, _)) ->
  pos, ident |> I.mk_string_ident, Type
| A.TypeDecl (pos, A.FreeType (_, ident)) ->
  pos, ident |> I.mk_string_ident, Type

| A.ConstDecl (pos, A.FreeConst(_, ident, _)) ->
  pos, ident |> I.mk_string_ident, Const
| A.ConstDecl (pos, A.UntypedConst(_, ident, _)) ->
  pos, ident |> I.mk_string_ident, Const
| A.ConstDecl (pos, A.TypedConst(_, ident, _, _)) ->
  pos, ident |> I.mk_string_ident, Const

| A.NodeDecl (pos, (ident, _, _, _, _, _, _)) ->
  pos, ident |> I.mk_string_ident, NodeOrFun
| A.FuncDecl (pos, (ident, _, _, _)) ->
  pos, ident |> I.mk_string_ident, NodeOrFun

| A.ContractNodeDecl (pos, (ident, _, _, _, _)) ->
  pos, ident |> I.mk_string_ident, Contract

| decl ->
  Format.asprintf
    "info requested on unsupported declaration: %a"
    A.pp_print_declaration decl
  |> failwith

(** Inserts a declaration in a list of declarations, after the one with name
[f_ident]. *)
let insert_decl decl (f_type, f_ident) decls =
  let ident = I.string_of_ident false f_ident in
  let has_ident = match f_type with
    | NodeOrFun -> (
      function
      | A.NodeDecl (_, (i, _, _, _, _, _, _)) -> i = ident
      | A.FuncDecl (_, (i, _, _, _)) -> i = ident
      | _ -> false
    )
    | Type -> (
      function
      | A.TypeDecl (_, A.AliasType(_, i, _)) -> i = ident
      | A.TypeDecl (_, A.FreeType(_, i)) -> i = ident
      | _ -> false
    )
    | Contract -> (
      function
      | A.ContractNodeDecl (_, (i, _, _, _, _)) -> i = ident
      | _ -> false
    )
    | Const -> (
      function
      | A.ConstDecl (_, A.FreeConst(_, i, _)) -> i = ident
      | A.ConstDecl (_, A.UntypedConst(_, i, _)) -> i = ident
      | A.ConstDecl (_, A.TypedConst(_, i, _, _)) -> i = ident
      | _ -> false
    )
  in

  let rec loop pref = function
    | head :: tail when has_ident head ->
      head :: decl :: tail |> List.rev_append pref
    | head :: tail -> loop (head :: pref) tail
    | [] -> raise Not_found
  in

  loop [] decls





(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
