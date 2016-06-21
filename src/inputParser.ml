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

(* typing errors *)
exception Type_error of Type.t * string

let divsep = Str.regexp "/"

(* Parse one value *)
let value_of_str ty = function
  | "true" when Type.(check_type ty t_bool) ->
    Term.t_true
  | "false" when Type.(check_type ty t_bool) ->
    Term.t_false
  | s ->
    try
      if Type.(check_type ty t_int) then
        Term.mk_num (Numeral.of_string s)
      else if Type.(check_type ty t_real) then
        match Str.split_delim divsep s with
        | [s] -> Term.mk_dec (Decimal.of_string s)
        | [s1; s2] ->
          Decimal.(div (of_string s1) (of_string s2)) |> Term.mk_dec
        | _ -> raise (Type_error (ty, s))
      else
        raise (Type_error (ty, s))
    with Invalid_argument _ ->
      raise (Type_error (ty, s))


(* Parse list of values *)
let values_of_strs ty l =
  List.rev_map (value_of_str ty) l |> List.rev 


let separator = Str.regexp " *, *"

(* Parse a line *)
let parse_stream scope chan =
  let line = input_line chan |> String.trim in
  let l = Str.split separator line in
  match l with
  | [] -> raise Not_found
  | name :: stream ->
    try
      let sv = StateVar.state_var_of_string (name, scope) in
      if StateVar.is_input sv then 
        (* Return state variable and its input *)
        (sv, values_of_strs (StateVar.type_of_state_var sv) stream)
      else raise Not_found
    with Not_found ->
      (* Fail *)
      Event.log L_fatal "State variable %s is not an input state variable" name;
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
      exit 2


(* Read in a csv file *)
let read_file top_scope_index filename = 
  let chan = open_in filename in
  parse top_scope_index chan []


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
