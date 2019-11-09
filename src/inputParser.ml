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

(* ====================== CSV ======================== *)

(* typing errors *)
exception Type_error of Type.t * string

let divsep = Str.regexp "/"

(* Parse one value *)
let value_of_str ty s =
  try (
    match Type.node_of_type ty with
    | Type.Bool -> (
      match s with
      | "true" -> Term.t_true
      | "false" -> Term.t_false
      | _ -> raise (Type_error (ty, s))
    )
    | Type.Int ->
      Term.mk_num (Numeral.of_string s)
    | Type.Real -> (
      match Str.split_delim divsep s with
      | [s] -> Term.mk_dec (Decimal.of_string s)
      | [s1; s2] ->
        Decimal.(div (of_string s1) (of_string s2)) |> Term.mk_dec
      | _ -> raise (Type_error (ty, s))
    )
    | Type.IntRange (l, u, Type.Range) -> (
      let n = Numeral.of_string s in
      if (Numeral.leq l n && Numeral.leq n u) then Term.mk_num n
      else raise (Type_error (ty, s))
    )
    | Type.IntRange (_, _, Type.Enum) ->
      if Type.enum_of_constr s == ty then Term.mk_constr s
      else raise (Type_error (ty, s))
    | _ -> raise (Type_error (ty, s))
  )
  with Invalid_argument _ | Not_found ->
    raise (Type_error (ty, s))


(* Parse list of values *)
let values_of_strs ty l =
  List.rev_map (value_of_str ty) l |> List.rev 


let separator = Str.regexp " *, *"

let parse_identifier scope name =
  match String.split_on_char '.' name with
  | [] -> failwith "split_on_char returned an empty list"
  | _ :: fields -> (
    let index =
      fields |> List.map (fun f -> LustreIndex.RecordIndex f)
    in
    let index_scope = LustreIndex.mk_scope_for_index index in
    StateVar.state_var_of_string (name, scope @ index_scope)
  )

(* Parse a line *)
let parse_stream scope chan =
  let line = input_line chan |> String.trim in
  let l = Str.split separator line in
  match l with
  | [] -> raise Not_found
  | name :: stream ->
    try
      let sv = parse_identifier scope name in
      if StateVar.is_input sv then 
        (* Return state variable and its input *)
        (sv, values_of_strs (StateVar.type_of_state_var sv) stream)
      else raise Not_found
    with Not_found ->
      (* Fail *)
      KEvent.log L_fatal "State variable %s is not an input state variable" name;
      raise (Parsing.Parse_error)


let rec parse =
  let line_nb = ref 0 in
  fun scope chan acc ->
    try
      incr line_nb;
      parse scope chan (parse_stream scope chan :: acc)
    with
    | Not_found -> parse scope chan acc
    | End_of_file -> close_in chan; acc
    | Type_error (ty, s) ->
      Log.log L_fatal
        "Typing error in input values file at line %d: \
         expected value of type %a, got value %s"
        !line_nb Type.pp_print_type ty s;
      raise (Parsing.Parse_error)


(* Read in a csv file *)
let read_csv_file top_scope_index filename = 
  let chan = open_in filename in
  parse top_scope_index chan []


(* ====================== JSON ======================== *)

open Yojson.Safe.Util

type assignment_lhs = StateVar.t * int list

module StringMap = Map.Make (String)
module SVMap = StateVar.StateVarMap
module LHS =
struct
  type t = assignment_lhs
  let compare (a,b) (a',b') =
    match StateVar.compare_state_vars a a' with
    | 0 -> Pervasives.compare b b'
    | i -> i
end
module LHSMap = Map.Make(LHS)

exception Missing_definition of int * assignment_lhs

(* Transforms a list of list of variable assignments
  (the outer list representing the steps and the inner the different variables)
  into a list associating to each variable the list of all its successive assignments *)
let group_by_var lst =
  let steps_passed = ref 0 in
  List.fold_right
    (fun lst acc -> 
      List.fold_left (fun acc (var, term) ->
          let old = match LHSMap.find_opt var acc with
          | None -> []
          | Some lst -> lst
          in
          let n = List.length old in
          if n < !steps_passed then raise (Missing_definition(n, var)) ;
          steps_passed := n ;
          LHSMap.add var (term::old) acc
        )
        acc lst
    ) lst LHSMap.empty
  |> LHSMap.bindings

exception Not_an_input of string
exception Type_mismatch of string

(* Convert a record of the format { "0":elt0 , "1":elt1 ... } into a tuple *)
let record_to_tuple assoc =
  try (
    assoc
    |> List.map (fun (str, elt) -> (int_of_string str, elt))
    |> List.sort (fun (i,_) (j,_) -> compare i j)
    |> List.map snd
    |> (fun x -> Some x)
  )
  with Failure _ -> None

(* Take as input a JSON element representing the value of a variable (at a given step)
   and return the associated assignments.
   It can return multiple variable assignements if the value is an array/record/tuple. *)
let rec read_val scope name indexes arr_indexes json =
  match json with
  | `Assoc lst ->
    (* Can represent a record or a tuple *)
    begin try (
      lst |>
      List.map (
        fun (str, json) ->
        read_val scope name ((LustreIndex.RecordIndex str)::indexes) arr_indexes json
      )
      |> List.flatten
    )
    with Not_an_input str -> (* If it is not a record, it must be a tuple *)
      begin match record_to_tuple lst with
      | None -> raise (Not_an_input str)
      | Some lst -> read_val scope name indexes arr_indexes (`Tuple lst)
      end
    end
  | `List lst -> lst |>
    List.mapi (
      fun i json ->
      let new_index = LustreIndex.ArrayVarIndex (LustreExpr.mk_int_expr Numeral.one) in
      read_val scope name (new_index::indexes) (i::arr_indexes) json
    )
    |> List.flatten
  | `Tuple lst -> lst |>
    List.mapi (
      fun i json ->
      read_val scope name ((LustreIndex.TupleIndex i)::indexes) arr_indexes json
    )
    |> List.flatten
  | json ->
    let indexes = List.rev indexes in
    let arr_indexes = List.rev arr_indexes in
    let full_scope = scope @ (LustreIndex.mk_scope_for_index indexes) in
    (* See LustreContext.mk_state_var for more information
       about how variable names are choosen *)
    let full_name =
      indexes
      |>
      List.filter
        (function 
          | LustreIndex.ArrayVarIndex _ 
          | LustreIndex.ArrayIntIndex _ -> false
          | LustreIndex.RecordIndex _
          | LustreIndex.TupleIndex _
          | LustreIndex.ListIndex _ -> true)
      |>
      Format.asprintf "%s%a" name (LustreIndex.pp_print_index true) 
    in

    let sv =
      try (StateVar.state_var_of_string (full_name, full_scope))
      with Not_found -> raise (Not_an_input full_name) in
    if not (StateVar.is_input sv) then raise (Not_an_input full_name) ;
    let typ = StateVar.type_of_state_var sv in
    let sv = (sv, arr_indexes) in

    (* Is a numeral in the range of a type? *)
    let is_in_range n t =
      match Type.node_of_type t with
      | Int -> true
      | IntRange (l, u, Range) ->
        Numeral.leq l n && Numeral.leq n u
      | _ -> false
    in
    (* Is an integer in the range of a type? *)
    let is_in_range_i i = is_in_range (Numeral.of_int i) in

    (* Extract the type of an element of an array (and check the ranges) *)
    let rec extract_element_type arr_indexes typ =
      match arr_indexes, Type.node_of_type typ with
      | [], _ -> typ
      | i::arr_indexes, Array (elt, t) when is_in_range_i i t  ->
        extract_element_type arr_indexes elt
      | _, _ -> raise (Type_mismatch full_name)
    in
    let typ = extract_element_type arr_indexes typ in

    try (
      let open Type in
      match Type.node_of_type typ, json with

      | Bool, `Bool b -> [sv, Term.mk_bool b]

      | IntRange (_, _, Enum), `String str when equal_types (enum_of_constr str) typ ->
        [sv, Term.mk_constr str]

      | Real, `Float f -> [sv, string_of_float f |> Decimal.of_string |> Term.mk_dec]
      | Real, `Int i -> [sv, Decimal.of_int i |> Term.mk_dec]
      | Real, `String str | Real, `Intlit str ->
        [sv, Decimal.of_string str |> Term.mk_dec]

      | _, `Int i                       when is_in_range_i i typ ->
        [sv, Term.mk_num_of_int i]
      | _, `Intlit str | _, `String str when is_in_range (Numeral.of_string str) typ ->
        [sv, Numeral.of_string str |> Term.mk_num]

      | _ -> raise (Type_mismatch full_name)
    )
    with Invalid_argument _ -> raise (Type_mismatch full_name)

(* Parse the assignments of a JSON object representing a step *)
let read_vars scope json =
  to_assoc json |> List.map (fun (name, json) -> read_val scope name [] [] json)

(* Parse a JSON input file *)
let read_json_file top_scope_index filename =
  Yojson.Safe.from_file filename |> to_list
  |> List.map (read_vars top_scope_index) |> List.flatten |> group_by_var


(* ====================== GENERAL ======================== *)

(* Parse a JSON or CSV input file. The format is determined from the extension. *)
let read_file top_scope_index filename =
  if Filename.check_suffix filename ".json"
  then
    read_json_file top_scope_index filename
  else
    read_csv_file top_scope_index filename
    |> List.map (fun (sv,vs) -> ((sv,[]),vs))

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
