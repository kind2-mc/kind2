(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

(* The SMT sorts the fields of a recursive datatype have where the field's
   compiled Lustre type is not a single SMT sort of its own *)

module E = LustreExpr
module X = LustreIndex

(* SMT symbol of a datatype's name: angle brackets are legal in an SMT-LIB
   simple symbol, so they are kept, and any character that is not is mangled *)
let smt_name_of_adt_name name =
  String.map (function
    | ('a'..'z' | 'A'..'Z' | '0'..'9'
      | '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_' | '-' | '+' | '='
      | '<' | '>' | '.' | '?' | '/') as c -> c
    | _ -> '$') name

(* An enum is an integer everywhere else, but a datatype field of integer sort
   lets a model read a value outside the enum out of a free datatype value: a
   field is pinned by its constructor, so no range constraint can be put on one
   after the fact. An enum-typed field is given a datatype sort with one
   nullary constructor per enum value instead. *)
let enum_field_ctor_sym sort_name ctor = sort_name ^ "$" ^ ctor

let enum_field_sort ty =
  let name = "enum$" ^ smt_name_of_adt_name (Type.name_of_enum ty) in
  let ctors = Type.constructors_of_enum ty in
  let sort =
    Type.mk_enum_field_sort name
      (List.map (fun c -> (enum_field_ctor_sym name c, [])) ctors) ty
  in
  (* A model may mention any of them, so declare every one *)
  List.iter (fun c ->
    ignore (UfSymbol.mk_uf_symbol (enum_field_ctor_sym name c) [] sort)
  ) ctors;
  sort

(* The constructor of an enum field sort holding each value of the enum it
   stands for, paired with that value *)
let enum_field_values sort =
  List.combine
    (List.map fst (Type.constructors_of_datatype sort))
    (Type.constructors_of_enum (Type.enum_of_field_sort sort))

(* An if-then-else chain over the given cases; the last is the unconditional
   branch *)
let rec ite_over cond value = function
  | [] -> assert false
  | [v] -> value v
  | v :: rest -> E.mk_ite (cond v) (value v) (ite_over cond value rest)

(* The integer-encoded enum value a field of enum field sort holds *)
let decode_enum_field sort e =
  let ety = Type.enum_of_field_sort sort in
  ite_over
    (fun (sym, _) -> E.mk_is_constructor sym e)
    (fun (_, v) -> E.mk_constr v ety)
    (enum_field_values sort)

(* The value of an enum field sort an integer-encoded enum expression denotes *)
let encode_enum_field sort e =
  let ety = Type.enum_of_field_sort sort in
  ite_over
    (fun (_, v) -> E.mk_eq e (E.mk_constr v ety))
    (fun (sym, _) -> E.mk_uf (UfSymbol.uf_symbol_of_string sym) sort [])
    (enum_field_values sort)

(* The components of a compiled trie, paired with the first index of each;
   ordered as the trie is, which is the same for a type and its values *)
let components trie =
  X.keys trie
  |> List.fold_left (fun acc idx ->
    match idx with
    | i :: _ ->
      if List.exists (fun j -> X.equal_index [i] [j]) acc then acc
      else i :: acc
    | [] -> invalid_arg "LustreRecAdtFieldSort.components: leaf")
    []
  |> List.rev
  |> List.map (fun i -> (i, X.find_prefix [i] trie))

let is_leaf trie = match X.bindings trie with
  | [(idx, _)] -> X.equal_index idx X.empty_index
  | _ -> false

(* The part of a component's sort name that comes from its index *)
let label_of_index = function
  | X.RecordIndex s -> s
  | X.TupleIndex (i, None) -> string_of_int i
  | X.AdtTagIndex s -> smt_name_of_adt_name s ^ "$tag"
  | X.AdtPayloadIndex (ctor, j) ->
    smt_name_of_adt_name ctor ^ "$" ^ string_of_int j
  | X.TupleIndex (_, Some _) | X.ListIndex _ | X.ArrayIntIndex _
  | X.ArrayVarIndex _ | X.SetMapIndex _ | X.AbstractTypeIndex _ ->
    invalid_arg "LustreRecAdtFieldSort: unsupported component of a field type"

let is_tuple_index = function
  | X.TupleIndex _ -> true
  | X.RecordIndex _ | X.ListIndex _ | X.ArrayIntIndex _ | X.ArrayVarIndex _
  | X.SetMapIndex _ | X.AbstractTypeIndex _ | X.AdtTagIndex _
  | X.AdtPayloadIndex _ -> false

(* How the values of a field sort of a tuple, a record or a non-recursive
   datatype map onto the compiled trie of the field's source type *)
type shape =
  (* The first index of each argument of the sole constructor *)
  | Product of X.one_index list
  (* The index and enum type of the tag of the desugared datatype, and the
     payload indexes of each constructor, in the order of the sort's *)
  | Sum of X.one_index * Type.t * (string * X.one_index list) list

(* The shape of each field sort, by the sort's name, which is unique to the
   field *)
let shapes : (string, shape) Hashtbl.t = Hashtbl.create 7

let shape_of_sort sort =
  if Type.is_datatype sort then Hashtbl.find_opt shapes (Type.name_of_datatype sort)
  else None

(* The tag and the payloads of each constructor of the components of a
   desugared non-recursive datatype, if the components are those of one *)
let sum_components comps =
  match List.partition (fun (i, _) -> match i with
    | X.AdtTagIndex _ -> true
    | X.RecordIndex _ | X.TupleIndex _ | X.ListIndex _ | X.ArrayIntIndex _
    | X.ArrayVarIndex _ | X.SetMapIndex _ | X.AbstractTypeIndex _
    | X.AdtPayloadIndex _ -> false) comps
  with
  | [(tag_idx, tag)], payloads when is_leaf tag ->
    let tag_ty = X.find X.empty_index tag in
    if not (Type.is_enum tag_ty) then None
    else
      let ctors = Type.constructors_of_enum tag_ty in
      let payloads_of c =
        List.filter_map (fun (i, sub) -> match i with
          | X.AdtPayloadIndex (c', j) when String.equal c c' -> Some (j, (i, sub))
          | X.AdtPayloadIndex _ | X.RecordIndex _ | X.TupleIndex _ | X.ListIndex _
          | X.ArrayIntIndex _ | X.ArrayVarIndex _ | X.SetMapIndex _
          | X.AbstractTypeIndex _ | X.AdtTagIndex _ -> None) payloads
        |> List.sort (fun (j, _) (j', _) -> compare j j')
        |> List.map snd
      in
      let by_ctor = List.map (fun c -> (c, payloads_of c)) ctors in
      if List.length (List.concat_map snd by_ctor) = List.length payloads
      then Some (tag_idx, tag_ty, by_ctor)
      else None
  | _ -> None

(* The sort of a field of the given compiled type, with the given name if it is
   one of its own. A tuple or record is a datatype with one constructor, one
   argument per component; a desugared non-recursive datatype is a datatype
   with its own constructors and their payloads, without the tag *)
let rec sort_of_field_type name ty =
  if is_leaf ty then
    let t = X.find X.empty_index ty in
    if Type.is_enum t then enum_field_sort t
    else if Type.is_array t then
      invalid_arg "LustreRecAdtFieldSort: array in a field type"
    else t
  else
    let comps = components ty in
    let sort, ctors, shape =
      match sum_components comps with
      | Some (tag_idx, tag_ty, by_ctor) ->
        let ctors =
          List.map (fun (c, payloads) ->
            (name ^ "$" ^ c,
             List.map (fun (i, sub) ->
               sort_of_field_type (name ^ "$" ^ label_of_index i) sub
             ) payloads)
          ) by_ctor
        in
        let shape =
          Sum (tag_idx, tag_ty,
               List.map (fun (c, payloads) -> (c, List.map fst payloads)) by_ctor)
        in
        Type.mk_datatype name ctors, ctors, shape
      | None ->
        let args =
          List.map (fun (i, sub) ->
            sort_of_field_type (name ^ "$" ^ label_of_index i) sub
          ) comps
        in
        let kind =
          if List.for_all (fun (i, _) -> is_tuple_index i) comps then "tuple"
          else "struct"
        in
        let ctors = [(name ^ "$" ^ kind, args)] in
        Type.mk_datatype name ctors, ctors, Product (List.map fst comps)
    in
    (* A model may mention any of them, so declare every one *)
    List.iter (fun (c, args) -> ignore (UfSymbol.mk_uf_symbol c args sort)) ctors;
    Hashtbl.replace shapes name shape;
    sort

let field_sort dt_name ctor field ty =
  sort_of_field_type (dt_name ^ "$" ^ ctor ^ "$" ^ field) ty

let rec encode sort e =
  if Type.is_enum_field_sort sort then
    encode_enum_field sort (X.find X.empty_index e)
  else
    match shape_of_sort sort with
    | None -> X.find X.empty_index e
    | Some (Product idxs) ->
      let ctor, arg_sorts = List.hd (Type.constructors_of_datatype sort) in
      E.mk_uf (UfSymbol.uf_symbol_of_string ctor) sort (encode_args arg_sorts idxs e)
    | Some (Sum (tag_idx, tag_ty, by_ctor)) ->
      let tag = X.find [tag_idx] e in
      ite_over
        (fun ((c, _), _) -> E.mk_eq tag (E.mk_constr c tag_ty))
        (fun ((_, idxs), (ctor, arg_sorts)) ->
          E.mk_uf (UfSymbol.uf_symbol_of_string ctor) sort
            (encode_args arg_sorts idxs e))
        (List.combine by_ctor (Type.constructors_of_datatype sort))

and encode_args arg_sorts idxs e =
  List.map2 (fun s i -> encode s (X.find_prefix [i] e)) arg_sorts idxs

(* The default value of a type, as the canonical form of a desugared datatype
   holds in the payloads of its inactive constructors *)
let rec default_value scalar_default ty =
  if Type.is_datatype ty then
    let ctors = Type.constructors_of_datatype ty in
    let ctor, args =
      match List.find_opt (fun (_, args) -> not (List.exists Type.is_datatype_ref args)) ctors with
      | Some c -> c
      | None -> List.hd ctors
    in
    E.mk_uf (UfSymbol.uf_symbol_of_string ctor) ty
      (List.map (default_value scalar_default) args)
  else scalar_default ty

let rec decode scalar_default sort e =
  if Type.is_enum_field_sort sort then
    X.singleton X.empty_index (decode_enum_field sort e)
  else
    match shape_of_sort sort with
    | None -> X.singleton X.empty_index e
    | Some (Product idxs) ->
      let ctor, arg_sorts = List.hd (Type.constructors_of_datatype sort) in
      decode_args scalar_default ctor arg_sorts idxs e X.empty
    | Some (Sum (tag_idx, tag_ty, by_ctor)) ->
      let ctors = List.combine by_ctor (Type.constructors_of_datatype sort) in
      let tag =
        ite_over
          (fun (_, (ctor, _)) -> E.mk_is_constructor ctor e)
          (fun ((c, _), _) -> E.mk_constr c tag_ty)
          ctors
      in
      (* A payload of a constructor other than the active one holds the default
         value, so that the value is in canonical form *)
      List.fold_left (fun acc ((_, idxs), (ctor, arg_sorts)) ->
        let active = E.mk_is_constructor ctor e in
        decode_args scalar_default ctor arg_sorts idxs e X.empty
        |> X.map (fun v ->
          E.mk_ite active v (default_value scalar_default (E.type_of_lustre_expr v)))
        |> fun payloads -> X.fold X.add payloads acc
      ) (X.singleton [tag_idx] tag) ctors

and decode_args scalar_default ctor arg_sorts idxs e acc =
  List.combine arg_sorts idxs
  |> List.mapi (fun pos (arg_sort, i) ->
    let sel = E.mk_selector (ctor ^ "_" ^ string_of_int pos) arg_sort e in
    (i, decode scalar_default arg_sort sel))
  |> List.fold_left (fun acc (i, sub) ->
    X.fold (fun j v acc -> X.add (i :: j) v acc) sub acc
  ) acc

let declaration_order declared dt =
  let mem ty l = List.exists (Type.equal_types ty) l in
  (* Post-order over the field sorts reached from a sort's fields *)
  let rec visit acc ty =
    if not (Type.is_datatype ty) || mem ty declared || mem ty acc then acc
    else
      let acc =
        Type.constructors_of_datatype ty
        |> List.concat_map snd
        |> List.fold_left visit acc
      in
      acc @ [ty]
  in
  declared @ visit [] dt
