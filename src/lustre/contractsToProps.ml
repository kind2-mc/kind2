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

module Ast = LustreAst
module LE = LustreErrors
           
let blah txt pos = Format.asprintf "%s at %a" txt pp_print_position pos
let blah_opt txt name pos =
  Format.asprintf "%s%t at %a"
    txt
    (fun fmt -> match name with
      | None -> ()
      | Some name -> Format.fprintf fmt " (%s)" (HString.string_of_hstring name)
    )
    pp_print_position pos

let rec collect_contracts (equations, locals, asserts, props) = function
| head :: tail -> (
  let quad = match head with

    | Ast.AssumptionVars _ -> equations, locals, asserts, props

    | Ast.GhostConst dec ->
      let pos, (id, expr, typ) = match dec with
        | Ast.FreeConst (pos,_,_)
        | Ast.UntypedConst (pos,_,_) ->
          Format.asprintf "\
            [contracts translator] %a: untyped ghost consts are unsupported\
          " pp_print_position pos
          |> failwith
        | Ast.TypedConst (pos,id,expr,typ) -> pos, (id, expr, typ)
      in
      (blah "Contract constant definition" pos, ((Ast.GhostVarDec (pos, [(pos, id, typ)])), expr)) :: equations, 
      (blah "Contract constant declaration" pos, (id, expr, typ)) :: locals, 
      asserts, props
    
    (* Add all identifers in typed ident list to "locals", but only add the full equation
       to "equations" once *)
    | Ast.GhostVars (pos, (GhostVarDec (_, tis) as lhs), expr) ->
      (blah "Contract variable definition" pos, (lhs, expr)) :: equations, 
      List.fold_left (fun acc (_, id, typ) -> (blah "Contract variable declaration" pos, (id, expr, typ)) :: acc)
                     locals
                     tis,
      asserts, 
      props

    | Ast.Assume (pos, name, _, expr) ->
      equations, locals, 
      (blah_opt "Assumption" name pos, Ast.Assert (dummy_pos, expr)) :: asserts, 
      props

    | Ast.Guarantee (pos, name, _, expr) ->
      equations, locals, asserts, (blah_opt "Guarantee" name pos, [], expr) :: props

    | Ast.Mode (pos, name, reqs, enss) ->
      let reqs = List.map (fun (_, _, e) -> e) reqs in
      let props =
        enss |> List.fold_left (
          fun acc (e_pos, e_name, e_expr) ->
            (
              blah
                (Format.sprintf "%s from mode %s"
                  (blah_opt "Ensure" e_name e_pos)
                  (HString.string_of_hstring name)
                )
                pos,
              reqs,
              e_expr
            ) :: acc
        ) props
      in
      equations, locals, asserts, props

    | Ast.ContractCall (pos,_,_,_) ->
      Format.asprintf "\
        [contracts translator] %a: contract calls are unsupported\
      " pp_print_position pos
      |> failwith
  in

  collect_contracts quad tail
)

| [] -> List.rev equations, List.rev locals, List.rev asserts, List.rev props


let fmt_node_decl fmt (
  ident, params, ins, outs, locals, items
) (c_equations, c_locals, c_asserts, c_properties) =

  (* Header. *)
  Format.fprintf fmt "\
    node %a%a (@.  \
      @[<hov>%a@]@.\
    ) returns (@.  \
      @[<hov>%a@]@.\
    ) ;@.@?\
  " Ast.pp_print_ident ident
    Ast.pp_print_node_param_list params
    (pp_print_list Ast.pp_print_const_clocked_typed_ident " ;@ ") ins
    (pp_print_list Ast.pp_print_clocked_typed_ident " ;@ ") outs ;

  (* Locals. *)
  let locals_empty, c_locals_empty = locals = [], c_locals = [] in
  if not locals_empty || not c_locals_empty then (

    (
      if locals_empty then
        Format.fprintf fmt "var@."
      else
        Format.fprintf fmt "  @[<v>%a@]@." Ast.pp_print_node_local_decl locals
    ) ;

    if not c_locals_empty then
      c_locals |> List.iter (
        fun (blah, (id,_,typ)) ->
          Format.fprintf fmt "  -- %s@.  %a: %a ;@."
            blah
            Ast.pp_print_ident id
            Ast.pp_print_lustre_type typ
      )
  ) ;

  (* body. *)
  Format.fprintf fmt "let@." ;
  Format.fprintf fmt "  @[<v>%a@]@.@?"
    (pp_print_list Ast.pp_print_node_item "@ ") items ;

  if items <> [] then Format.fprintf fmt "@." ;

  c_equations |> List.iter (
    fun (blah, (lhs,expr)) ->
      Format.fprintf fmt "  -- %s@.  %a = %a ;@."
        blah
        Ast.pp_print_contract_eq_lhs lhs
        Ast.pp_print_expr expr
  ) ;
  if c_equations <> [] then Format.fprintf fmt "@." ;
  
  c_asserts |> List.iter (
    fun (blah, ass) ->
      Format.fprintf fmt "  -- %s@.  %a@."
        blah Ast.pp_print_node_item (LustreAst.Body ass)
  ) ;
  if c_asserts <> [] then Format.fprintf fmt "@." ;

  c_properties |> List.iter (
    fun (blah, lhs, rhs) ->
      Format.fprintf fmt "  -- %s@.  --%%PROPERTY " blah ;
      ( match lhs with
        | [] -> ()
        | _ ->
          Format.fprintf fmt "(not (%a)) or "
            (pp_print_list Ast.pp_print_expr " and ") lhs
      ) ;
      Format.fprintf fmt "(%a) ;@." Ast.pp_print_expr rhs
  ) ;
  if c_properties <> [] then Format.fprintf fmt "@." ;

  Format.fprintf fmt "tel@."



let rec fmt_declarations fmt = function
| dec :: tail -> (
  ( match dec with

    | Ast.ContractNodeDecl ({Ast.start_pos = spos}, _) ->
      Format.asprintf "\
        [contracts translator] %a: contract node declarations are unsupported\
      " pp_print_position spos
      |> failwith

    | Ast.NodeDecl (_, (wan, _, two,tri,far,fiv,six,contract)) -> (
      let contract_info = match contract with
        | None -> ([],[],[],[])
        | Some c -> collect_contracts ([],[],[],[]) c
      in
      fmt_node_decl fmt (wan,two,tri,far,fiv,six) contract_info
    )

    | dec -> Ast.pp_print_declaration fmt dec
  ) ;
  Format.fprintf fmt "@.@.@?" ;
  fmt_declarations fmt tail
)
| [] -> ()

let translate ast target =
  let tgt = open_out target in
  let fmt = Format.formatter_of_out_channel tgt in
  fmt_declarations fmt ast

let translate_file file target =
  match LustreInput.ast_of_file file with
  | Ok ast -> translate ast target
  | Error e -> LustreReporting.fail_at_position_pt (LE.error_position e) (LE.error_message e)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
