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

module Sys = TransSys
module Num = Numeral
module Sym = UfSymbol

let fmt_sym = Sym.pp_print_uf_symbol

let fmt_expr = GenericSMTLIBDriver.pp_print_expr

let fmt_sort = GenericSMTLIBDriver.pp_print_sort
let string_of_sort = GenericSMTLIBDriver.string_of_sort

let fmt_var ppf var =
  Format.fprintf
    ppf "(%s %a)" (Var.string_of_var var) fmt_sort (Var.type_of_var var)

let fmt_def fmt sym args def =
  Format.fprintf fmt
    "\
      (define-fun@.  \
        @[<v>%a (@   \
          @[<v>%a@]@ \
        ) %a@ \
          @[<v>%a@]\
        @]@ \
      )@.@.\
    "
    fmt_sym sym
    (pp_print_list fmt_var "@ ")
    args
    fmt_sort (Sym.res_type_of_uf_symbol sym)
    fmt_expr def

let fmt_dec fmt sym =
  Format.fprintf fmt
    "@[<hv 2>(declare-fun@ %a@ (@[<hv 2>%a@])@ %a)@]@."
    fmt_sym sym
    (pp_print_list fmt_sort "@ ") (Sym.arg_type_of_uf_symbol sym)
    fmt_sort (Sym.res_type_of_uf_symbol sym)

let trans_conj_of_bounds sys lo hi =
  assert (hi >= lo) ;
  let rec loop terms k_int =
    if k_int < lo then terms else (
      let k = Num.of_int k_int in
      let trans = Sys.trans_of_bound sys k in
      let props =
        Sys.props_list_of_bound sys k
        |> List.map snd
        |> Term.mk_and
        |> if k_int = hi then Term.mk_not else identity
      in
      k_int - 1 |> loop (trans :: props :: terms)
    )
  in
  loop [] hi

let generate target_dir (low, upp) sys =
  let target_file = "target" in
  let fmt = open_out target_file |> Format.formatter_of_out_channel in
  let low, upp = low + 1, upp + 1 in

  let fmt_def, fmt_dec = fmt_def fmt, fmt_dec fmt in

  let rec loop low = if low <= upp then (
    let l_bound = Num.of_int low in
    Sys.define_and_declare_of_bounds
      sys fmt_def fmt_dec Numeral.zero Numeral.zero ;
    (* Variables to eliminate. *)
    let qe_vars = Numeral.of_int low |> Sys.vars_of_bounds sys Numeral.one in
    (* Printing qe challenge. *)
    trans_conj_of_bounds sys 1 low
    |> fun terms ->
      let props_at_0 =
        Sys.props_list_of_bound sys Numeral.zero
        |> List.map snd
        |> Term.mk_and
      in
      props_at_0 :: terms |> Term.mk_and
    |> Format.fprintf fmt
      "@.@.\
        ;; Eliminate all variables @i for 1 <= i <= %d.@.\
        (get-qe@.  @[<v>\
          (exists@   @[<v>\
            (@   @[<v>%a@]@ )@ \
            %a\
          @]@ )\
        @]@ )@.\
      "
      low
      (pp_print_list fmt_var "@ ")
      qe_vars
      fmt_expr ;
    exit 0 ;
    low + 1 |> loop
  ) in

  loop low


