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


(* Translator from Lustre to NuSMV input language *)

open Lib;;

module H = HoasTree;;

(* NuSMV only supports bounded integers, in range (-2^31, 2^31). 
  Bounds for this range are specified here. *)
let int_lowerbound = ref (-1000);;
let int_upperbound = ref   1000;;

(* Pretty-print a symbol in NuSMV format *)
let rec pp_print_nusmv_symbol_node ppf = function

  | `TRUE -> Format.pp_print_string ppf "TRUE"
  | `FALSE -> Format.pp_print_string ppf "FALSE"
  | `NOT -> Format.pp_print_string ppf "!"
  | `IMPLIES -> Format.pp_print_string ppf "->"
  | `AND  -> Format.pp_print_string ppf "&"
  | `OR -> Format.pp_print_string ppf "|"
  | `XOR -> Format.pp_print_string ppf "xor"

  | `EQ -> Format.pp_print_string ppf "="
  (*| `DISTINCT -> Format.pp_print_string ppf ""*)
  (*| `ITE -> Format.pp_print_string ppf "" *)

  | `NUMERAL i -> pp_print_numeral ppf i
  | `DECIMAL f -> pp_print_decimal ppf f
  (*| `BV b -> pp_print_bitvector_b ppf b *)

  | `MINUS -> Format.pp_print_string ppf "-"
  | `PLUS -> Format.pp_print_string ppf "+"
  | `TIMES -> Format.pp_print_string ppf "*"
  (*| `DIV -> Format.pp_print_string ppf ""*)
  | `INTDIV -> Format.pp_print_string ppf "/"
  | `MOD -> Format.pp_print_string ppf "mod"
  (*| `ABS -> Format.pp_print_string ppf ""*)

  | `LEQ -> Format.pp_print_string ppf "<="
  | `LT -> Format.pp_print_string ppf "<"
  | `GEQ -> Format.pp_print_string ppf ">="
  | `GT -> Format.pp_print_string ppf ">"
  | _ -> failwith "unimplemented symbol"

and pp_print_nusmv_symbol ppf s =
  pp_print_nusmv_symbol_node ppf (Symbol.node_of_symbol s)


(* Pretty-print a type in NuSMV format *)
let rec pp_print_nusmv_type_node ppf = function

  | Type.Bool -> Format.pp_print_string ppf "boolean"

  (* NuSMV only supports bounded integers *)
  | Type.Int -> pp_print_nusmv_type ppf 
                (Type.mk_int_range ( numeral_of_int !int_lowerbound) 
                                   ( numeral_of_int !int_upperbound));
  
  | Type.IntRange (i, j) -> 
    Format.fprintf
      ppf 
      "%a .. %a" 
      pp_print_numeral i 
      pp_print_numeral j
  
  (*
  | Real -> Format.pp_print_string ppf "Real"

  | BV i -> 
    Format.fprintf
      ppf 
      "BitVec %a" 
      pp_print_numeral i 
  *)
  
  | Type.Array (s, t) -> 
      Format.fprintf
      ppf 
      "array %a of %a" 
      (* need to have a range and a type, ie 'array 0..3 of boolean' *)
      pp_print_nusmv_type_node s (* print the integer range *)
      pp_print_nusmv_type_node t (* print the type *)
 
  | t -> 
      Format.fprintf
      ppf
      "unsupported type: %a\n"
      Type.pp_print_type_node t; 
      assert false;

and pp_print_nusmv_type ppf t = 
  pp_print_nusmv_type_node ppf (Type.node_of_type t)
;;  


(* pretty-print a var *)
let pp_print_nusmv_var ofs ppf term =

  match Term.destruct term with 

    | H.Var v when ofs = (numeral_of_int 0) ->
      StateVar.pp_print_state_var ppf (Var.state_var_of_state_var_instance v)

    | H.Var v when ofs = (numeral_of_int 1) ->
      Format.fprintf
      ppf 
      "next(%a)"
       StateVar.pp_print_state_var (Var.state_var_of_state_var_instance v)

    | H.Var v -> failwith ("Invalid offset " ^ (string_of_numeral ofs)) 

    | _ -> print_endline "\n Error: couldn't print term:\n"; 
           print_endline (Term.string_of_term term); 
           assert false;
;;


(* pretty-print a term in nusmv format *)
let rec pp_print_nusmv_term ppf term =
  
  match Term.destruct term with 

  | H.App (s, l) when s = (Symbol.mk_symbol `PLUS) ->
 
    (match (List.map Term.mk_term l) with
   
      | [] -> ()
   
      | h::[] ->
        Format.fprintf 
          ppf 
          "%a"
          pp_print_nusmv_term h

      | h::t ->
        Format.fprintf 
          ppf 
          "%a + %a"
          (* lhs *)
          pp_print_nusmv_term h
          (* rhs *)
          pp_print_nusmv_term (Term.mk_plus t) 
    );

  | H.App (s, l) when s = (Symbol.mk_symbol `AND) ->

    (match (List.map Term.mk_term (List.rev l)) with
   
      | [] ->
        Format.fprintf
          ppf
          "%a"
          pp_print_nusmv_term (Term.mk_false ())
   
      | [t] ->
        Format.fprintf 
          ppf 
          "%a"
          pp_print_nusmv_term t
    
      | h::t ->
        Format.fprintf 
          ppf 
          "(%a & %a)"
          pp_print_nusmv_term (Term.mk_and (List.rev t))
          pp_print_nusmv_term h);

   | H.App (s, l) when s = (Symbol.mk_symbol `OR) ->

    (match (List.map Term.mk_term (List.rev l)) with
    
      | [] ->
        Format.fprintf
          ppf
          "%a"
          pp_print_nusmv_term (Term.mk_false ())
    
      | [t] ->
        Format.fprintf 
          ppf 
          "%a"
          pp_print_nusmv_term t
      
      | h::t ->
        Format.fprintf 
          ppf 
          "(%a | %a)"
          (* lhs *)
          pp_print_nusmv_term h
          (* rhs *)
          pp_print_nusmv_term (Term.mk_or t));

  | H.App (s, l) when s = (Symbol.mk_symbol `IMPLIES) ->
    
    (match (List.map Term.mk_term l) with
      | [] ->
        Format.fprintf
          ppf
          "%a"
          (* Implication is a disjunction, empty implication is false *)
          pp_print_nusmv_term (Term.mk_false ())
 
      | [t] ->
        Format.fprintf 
          ppf 
          "%a"
          (* An implication without premises is true if the conclusion is true *)
          pp_print_nusmv_term t

      | h::t ->
        Format.fprintf 
          ppf 
          "(%a -> %a)"
          (* lhs *)
          pp_print_nusmv_term h
          (* rhs *)
          pp_print_nusmv_term (Term.mk_implies t) 
    );

  | H.App (s, l) when s = (Symbol.mk_symbol `LEQ) ->

    (match (List.map Term.mk_term l) with
  
      | [] -> ()
  
      | h::[] ->
        Format.fprintf 
          ppf 
          "%a"
          (* lhs *)
          pp_print_nusmv_term h
  
      | h::t ->
        Format.fprintf 
          ppf 
          "%a <= %a"
          (* lhs *)
          pp_print_nusmv_term h
          (* rhs *)
          pp_print_nusmv_term (Term.mk_leq t) 
    );

  | H.App (s, l) when s = (Symbol.mk_symbol `GEQ) ->

    (match (List.map Term.mk_term l) with

      | [] -> ()

      | h::[] ->
        Format.fprintf 
          ppf 
          "%a"
          pp_print_nusmv_term h
      
      | h::t ->
        Format.fprintf 
          ppf 
          "%a >= %a"
          (* lhs *)
          pp_print_nusmv_term h
          (* rhs *)
          pp_print_nusmv_term (Term.mk_leq t) 
    );

  | H.App (s, l) -> 

    (match (List.map Term.mk_term l) with
     
     | [cond; cons; alt] ->
        (match (Symbol.node_of_symbol s) with 

         | `ITE ->
          (* if then else *)
          Format.fprintf 
          ppf 
          "(%a ? %a : %a)"
          (* condition *)
          pp_print_nusmv_term cond
          (* consequent *)
          pp_print_nusmv_term cons
          (* alternative *) 
          pp_print_nusmv_term alt
         
         | s ->

          Format.fprintf 
          ppf 
          "invalid symbol: %a"
          Symbol.pp_print_symbol (Symbol.mk_symbol s);
          assert false;

        );

      | [lhs; rhs] -> 
        Format.fprintf 
        ppf 
        "(%a %a %a)" 
        (* print left hand side *)
        pp_print_nusmv_term lhs
        (* print symbol *)
        pp_print_nusmv_symbol s 
        (* print right hand side *)
        pp_print_nusmv_term rhs

     | [t] -> 
        pp_print_nusmv_symbol ppf s;
        pp_print_nusmv_term ppf t
    
     | [ ] -> ()

     | _ -> 

        Format.fprintf 
        ppf 
        "invalid term %a" 
        Term.pp_print_term term; 
        assert false;
    );

  | H.Var v -> pp_print_nusmv_var (Var.offset_of_state_var_instance v) ppf term

  | H.Const s -> pp_print_nusmv_symbol ppf s

;;


let pp_print_nusmv_var_declaration ppf sv =
  Format.fprintf 
    ppf 
    "\t%a : %a;\n" 
    StateVar.pp_print_state_var sv
    pp_print_nusmv_type (StateVar.type_of_state_var sv)
;;


let rec pp_print_nusmv_init ppf init = 
  match init with 

  | [] -> ()

  | h :: tl -> 
    (*print_endline ("printing init: " ^ (Term.string_of_term h));*)
    match Term.destruct h with 
      
      | H.App (s, l) when s == Symbol.s_and -> 
        (*print_endline "and call";*)
        pp_print_nusmv_init ppf ((List.map Term.mk_term l) @ tl)

      | H.App (s, [l; r]) when (s = Symbol.mk_symbol `EQ) -> 

        Format.fprintf ppf "\tinit(%a) := %a;\n" 
          (pp_print_nusmv_var (numeral_of_int 0)) (Term.mk_term l) 
          pp_print_nusmv_term (Term.mk_term r);
        
        pp_print_nusmv_init ppf tl

      | _ -> 

        Format.fprintf 
        ppf 
        "invalid term %a" 
        Term.pp_print_term h; 
        assert false;
;;


let rec pp_print_nusmv_constr ppf constr = 
  match constr with 

  | [] -> ()

  | h :: tl -> 
    (*print_endline ("printing next: " ^ (Term.string_of_term h));*)
    match Term.destruct h with 
      
      | H.App (s, l) when s == Symbol.s_and -> 
        pp_print_nusmv_constr ppf ((List.map Term.mk_term l) @ tl)

      | H.App (s, [l; r]) when s == (Symbol.mk_symbol `EQ) -> 
        Format.fprintf ppf "\tnext(%a) := %a;\n" 
          (pp_print_nusmv_var (numeral_of_int 0)) (Term.mk_term l) 
          pp_print_nusmv_term (Term.mk_term r);
        
        pp_print_nusmv_constr ppf tl

      | _ -> 

        Format.fprintf 
        ppf 
        "invalid term %a" 
        Term.pp_print_term h; 
        assert false;
;;


let pp_print_nusmv_prop ppf (s, t) =
  (*print_endline (Term.string_of_term t);*)
  Format.fprintf
  ppf
  "@[<hv 1>(%a)@]"
  pp_print_nusmv_term t
;;

let pp_print_nusmv_trans_sys ppf { TransSys.init = i; 
                                   TransSys.constr = c; 
                                   TransSys.trans = g; 
                                   TransSys.props = p;
                                   TransSys.invars = pv;
                                   TransSys.props_invalid = pi  } =

  (* Collect declared state variables *)
  let v = StateVar.fold (fun v a -> v :: a) [] in

  (Format.fprintf 
    ppf
    "MODULE main\nVAR@\n@[<v>%a@]@\nASSIGN@\n@[<v>%a@]@[<v>%a@]@\n"
    (pp_print_list pp_print_nusmv_var_declaration "") v
    (pp_print_list pp_print_nusmv_init "") [i]
    (pp_print_list pp_print_nusmv_constr "") [c]
  );
  if (p <> []) then (
    Format.fprintf
      ppf 
      "LTLSPEC G@\n(@[<v>%a@]);\n"
      (pp_print_list pp_print_nusmv_prop " & ") p );

;;


let help_message = "Usage: \n" ^
                   "nusmv [--int-lowerbound lb] [--int-upperbound ub] [FILE]";;

(* Entry Point *)

let rec parse_argv argv fn = 
  match argv with
  | h1::h2::tl ->
    (match h1 with
      | "--int-lowerbound" ->
        int_lowerbound := (int_of_string h2);
        parse_argv tl fn;
      
      | "--int-upperbound" ->
        int_upperbound := (int_of_string h2);
        parse_argv tl fn;
      
      | _                  -> 
        if (fn <> "") then (
          print_endline help_message;
          assert false;
        ) else (
          parse_argv (h2::tl) h1;
        )
    )
  
  | h::tl ->
    (match h, fn with
      | "--help", "" ->
        print_endline help_message;
        exit 0;
      | h, ""       ->
        h;
      | _, _        ->
        print_endline help_message;
        exit 1;
    )

  | [] -> fn

in  

match parse_argv (Array.to_list (Array.sub Sys.argv 1 ((Array.length Sys.argv) - 1))) "" with
| "" -> 
  let ts = OldParser.of_channel stdin in
  pp_print_nusmv_trans_sys Format.std_formatter ts;
| fn ->
  let ts = OldParser.of_file fn in
  pp_print_nusmv_trans_sys Format.std_formatter ts;
;;

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
