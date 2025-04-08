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

%{

open Lib
   
module A = MoxiAst

type var_kind = Input | Output | Local

let is_input (kind, _) = kind = Input
let is_output (kind, _) = kind = Output
let is_local (kind, _) = kind = Local

let get_vars p l =
  match List.filter p l with
  | [] -> None
  | [(_, vars)] -> Some vars
  | _ -> failwith("Attribute is not repeatable")

type sys_formula = Init | Trans | Inv

let is_init (kind, _) = kind = Init
let is_trans (kind, _) = kind = Trans
let is_inv (kind, _) = kind = Inv

let get_formula p l =
  match List.filter p l with
  | [] -> A.Constant A.True
  | [(_, f)] -> f
  | _ -> failwith("Attribute is not repeatable")

let mk_pos = position_of_lexing 

let mk_span start_pos end_pos =
  mk_span (mk_pos start_pos) (mk_pos end_pos)

%}

(* Reserved words *)
%token AS

(* Command names *)
%token CHECK_SYSTEM
%token DEFINE_SYSTEM
%token SET_LOGIC

(* Keywords *)
%token INPUT_KW
%token OUTPUT_KW
%token LOCAL_KW

%token INIT_KW
%token TRANS_KW
%token INV_KW

%token SUBSYS_KW

%token ASSUMPTION_KW
%token REACHABLE_KW
%token QUERY_KW

(* Symbols *)
%token <HString.t>QUOTED_SYMBOL
%token <HString.t>SIMPLE_SYMBOL

(* Numeric literals *)
%token <Numeral.t>NUMERAL_LIT
%token <Decimal.t>DECIMAL_LIT
%token <Bitvector.t>BITVECTOR_LIT

%token TRUE
%token FALSE

%token UNDERSCORE "_"
%token LPAREN "("
%token RPAREN ")"
%token APOSTROPHE "'"

%token EOF

%start<MoxiAst.script> script

%%

script: cmds=command* EOF { cmds }

command:
  | c=check_system { c }
  | c=define_system { c }
  | c=set_logic { c }

set_logic:
  "(" SET_LOGIC logic=symbol ")"
  { 
    A.SetLogicCmd logic
  }

check_system:
  | "(" CHECK_SYSTEM system_id=symbol
    vars=system_variables*
    attrs=check_system_attribute*
    ")"
  {
    let input = get_vars is_input vars in
    let output = get_vars is_output vars in
    let local = get_vars is_local vars in
    A.CheckSystemCmd {
      loc = mk_span $startpos $endpos;
      system_id;
      input;
      output;
      local;
      attrs;
    }
  }

check_system_attribute:
  | ASSUMPTION_KW "(" s=symbol t=term ")"
  {
    A.FormulaAttr (Assumption, (s, t))
  } 
  | REACHABLE_KW "(" s=symbol t=term ")"
  {
    A.FormulaAttr (Reachable, (s, t))
  }
  | QUERY_KW "(" s=symbol "(" l=symbol+ ")" ")"
  {
    A.QueryAttr (s, l)
  }

define_system:
  "(" DEFINE_SYSTEM name=symbol 
  vars=system_variables*
  items=define_system_items
  ")"
  {
    let input = get_vars is_input vars in
    let output = get_vars is_output vars in
    let local = get_vars is_local vars in
    let subsys, formulas = items in
    let init = get_formula is_init formulas in
    let trans = get_formula is_trans formulas in
    let inv = get_formula is_inv formulas in
    A.DefineSystemCmd {
      loc = mk_span $startpos $endpos;
      name;
      input;
      output;
      local;
      subsys;
      init;
      trans;
      inv;
    }
  }

system_variables:
  | INPUT_KW "(" vars=sorted_var* ")"
  {
    (Input, (mk_span $startpos $endpos, vars))
  }
  | OUTPUT_KW "(" vars=sorted_var* ")"
  {
    (Output, (mk_span $startpos $endpos, vars))
  }
  | LOCAL_KW "(" vars=sorted_var* ")" 
  {
    (Local, (mk_span $startpos $endpos, vars))
  }

define_system_items:
  | /* Empty */
    { ([], []) }
  | items=define_system_items f=system_formula 
    {
      let subsys, formulas = items in
      (subsys, f :: formulas)
    }
  | items=define_system_items s=subsystem 
    {
      let subsys, formulas = items in
      (s :: subsys, formulas)
    }

subsystem:
  | SUBSYS_KW "(" local_name=symbol "(" sys_name=symbol vars=symbol* ")" ")"
  {
    A.{
      loc = mk_span $startpos $endpos ;
      instance_name = local_name ;
      system_name = sys_name ;
      variables = vars ; 
    }
  }

system_formula:
  | INIT_KW f=term
  {
    (Init, f)
  }
  | TRANS_KW f=term
  {
    (Trans, f)
  }
  | INV_KW f=term
  {
    (Inv, f)
  }

term:
  | c=spec_constant
  {
    A.Constant c
  }
  | qid=qual_identifier
  {
    A.QualId qid
  }
  | "(" qid=qual_identifier ts=term+ ")"
  {
    A.App (mk_span $startpos $endpos, qid, ts)
  }

spec_constant:
  | TRUE
  {
    A.True
  }
  | FALSE
  {
    A.False
  }
  | c=NUMERAL_LIT
  {
    A.Numeral (mk_span $startpos $endpos, c)
  }
  | c=DECIMAL_LIT
  {
    A.Decimal (mk_span $startpos $endpos, c)
  }
  | c=BITVECTOR_LIT
  {
    A.Bitvector (mk_span $startpos $endpos, c)
  }
  (* | STRING_LIT {} *)

qual_identifier:
  | id=identifier p=prime_modifier
  {
    (id, p, None)
  }
  | "(" AS id=identifier p=prime_modifier s=sort ")"
  {
    (id, p, Some s)
  }

prime_modifier:
  | { false }
  | APOSTROPHE { true }

sorted_var: "(" v=symbol s=sort ")"
{
  (mk_span $startpos $endpos, v, s)
}

sort:
  | id=identifier
  {
    A.{ id; parameters=[] }
  }
  | "(" id=identifier parameters=sort+ ")"
  {
    A.{ id; parameters }
  }

identifier:
  | s=symbol
  {
    (mk_span $startpos $endpos, s, [])
  }
  | "(" "_" s=symbol l=index+ ")"
  {
    (mk_span $startpos $endpos, s, l)
  }

index:
  | n=NUMERAL_LIT
  {
    A.NumericIndex (mk_span $startpos $endpos, n)
  }
  | s=symbol
  {
    A.SymbolicIndex s
  }

symbol:
  | s=SIMPLE_SYMBOL
  {
    (mk_span $startpos $endpos, s)
  }
  | s=QUOTED_SYMBOL
  {
    (mk_span $startpos $endpos, s)
  }