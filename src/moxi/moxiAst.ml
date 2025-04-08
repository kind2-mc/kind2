(* This file is part of the Kind 2 model checker.

   Copyright (c) 2025 by the Board of Trustees of the University of Iowa

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

type symbol_hs = HString.t

type symbol = span * symbol_hs

type numeral = span * Numeral.t

type decimal = span * Decimal.t

type bitvector = span * Bitvector.t

type index =
  | NumericIndex of numeral
  | SymbolicIndex of symbol

type identifier =
  span *
  symbol *
  index list (* Empty for non-indexed identifiers *)

type sort = {
  id: identifier ;
  parameters: sort list ; (* Empty for non-parametric sorts *)
}

type sorted_var = span * symbol * sort

type constant =
  | True | False
  | Numeral of numeral
  | Decimal of decimal
  | Bitvector of bitvector

type qual_identifier = identifier * bool * sort option

type term =
  | Constant of constant
  | QualId of qual_identifier
  | App of span * qual_identifier * term list

type formula_type =
  | Assumption
  | Reachable

type formula_attr = formula_type * (symbol * term)

type query_attr = symbol * symbol list

type check_system_attr =
  | FormulaAttr of formula_attr
  | QueryAttr of query_attr

type system_variables = (span * sorted_var list) option

type check_system_cmd =
{
  loc: span;
  system_id: symbol ;
  input: system_variables ;
  output: system_variables ;
  local: system_variables ;
  attrs: check_system_attr list ;
}

type subsystem =
{
  loc: span ;
  instance_name: symbol ;
  system_name: symbol ;
  variables: symbol list;
}

type define_system_cmd =
{
  loc: span ;
  name: symbol ;
  input: system_variables ;
  output: system_variables ;
  local: system_variables ;
  subsys: subsystem list ;
  init: term ;
  trans: term ;
  inv: term ;
}

type command =
  | CheckSystemCmd of check_system_cmd
  | DefineSystemCmd of define_system_cmd
  | SetLogicCmd of symbol

type script = command list

type t = script


let is_query_attr = function
| QueryAttr _ -> true
| _ -> false