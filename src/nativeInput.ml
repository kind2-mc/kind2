(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

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

module S = SExprBase.Make(HStringSExpr.HStringAtom)

(* Distingushed strings in input *)
let s_define_pred = HString.mk_hstring "define-pred"
let s_init = HString.mk_hstring "init"
let s_trans = HString.mk_hstring "trans"
let s_opt_const = HString.mk_hstring ":const"
let s_prime = HString.mk_hstring "prime"
let s_check_prop = HString.mk_hstring "check-prop"
let s_int = HString.mk_hstring "Int"
let s_real = HString.mk_hstring "Real"
let s_bool = HString.mk_hstring "Bool"
let s_intrange = HString.mk_hstring "IntRange"
let s_let = HString.mk_hstring "let"

let top_scope = ["__top"]

(* Suffix of initial state predicate *)
let init_pred_suff = ".init"

(* Suffix of transition relation predicate *)
let trans_pred_suff = ".trans"

(* Return the name of the initial state constraint predicate *)
let init_pred_name pred = Format.sprintf "%s%s" pred init_pred_suff

(* Return the name of the transition relation predicate *)
let trans_pred_name pred = Format.sprintf "%s%s" pred trans_pred_suff

(* Return a type of an S-expression *)
let type_of_sexpr = function 

  (* Integer type *)
  | HStringSExpr.Atom c when c == s_int -> Type.t_int

  (* Real type  *)
  | HStringSExpr.Atom c when c == s_real -> Type.t_real

  (* Boolean type *)
  | HStringSExpr.Atom c when c == s_bool -> Type.t_bool

  (* Integer range type *)
  | HStringSExpr.List [HStringSExpr.Atom c; HStringSExpr.Atom l; HStringSExpr.Atom u] when c == s_intrange -> 

    (* Numeral of lower bound *)
    let nl = 
      try Numeral.of_string (HString.string_of_hstring l) with 
        | Invalid_argument _ -> 
          failwith "Invalid argument for integer range type"
    in
    
    (* Numeral of lower upper bound *)
    let nu = 
      try Numeral.of_string (HString.string_of_hstring u) with 
        | Invalid_argument _ -> 
          failwith "Invalid argument for integer range type"
    in
    
    (* Create integer range type *)
    Type.mk_int_range nl nu

  | _ -> failwith "Invalid type"

(* Create a state variable with the given scope from the S-expression *)
let state_var_of_sexpr scope = function 

  (* State variable definition is the name, its type and options *)
  | HStringSExpr.List (HStringSExpr.Atom v :: t :: opts) -> 

    (* Name of the variable *)
    let var_name = HString.string_of_hstring v in

    (* Type of the variable *)
    let var_type = type_of_sexpr t in

    (* Options of the variable *)
    let is_const, is_input = 
      List.fold_left 

        (* Parse input and modify options *)
        (fun (is_const, is_input) -> function 
           | HStringSExpr.Atom c when c == s_opt_const -> (true, is_input)
           | _ -> failwith "Invalid option for state variable")

        (* Defaults for the options *)
        (false, false)

        opts
    in

    (* Create state variable and return *)
    StateVar.mk_state_var ~is_input ~is_const var_name scope var_type []

  | _ -> failwith "Invalid state variable declaration"


(* Association list of strings to function symbols *) 
let string_symbol_list =
  [("not", Symbol.mk_symbol `NOT);
   ("=>", Symbol.mk_symbol `IMPLIES);
   ("and", Symbol.mk_symbol `AND);
   ("or", Symbol.mk_symbol `OR);
   ("xor", Symbol.mk_symbol `XOR);
   ("=", Symbol.mk_symbol `EQ);
   ("distinct", Symbol.mk_symbol `DISTINCT);
   ("ite", Symbol.mk_symbol `ITE);
   ("-", Symbol.mk_symbol `MINUS);
   ("+", Symbol.mk_symbol `PLUS);
   ("*", Symbol.mk_symbol `TIMES);
   ("/", Symbol.mk_symbol `DIV);
   ("div", Symbol.mk_symbol `INTDIV);
   ("mod", Symbol.mk_symbol `MOD);
   ("abs", Symbol.mk_symbol `ABS);
   ("<=", Symbol.mk_symbol `LEQ);
   ("<", Symbol.mk_symbol `LT);
   (">=", Symbol.mk_symbol `GEQ);
   (">", Symbol.mk_symbol `GT);
   ("to_real", Symbol.mk_symbol `TO_REAL);
   ("to_int", Symbol.mk_symbol `TO_INT);
   ("is_int", Symbol.mk_symbol `IS_INT);
   ("concat", Symbol.mk_symbol `CONCAT);
   ("bvnot", Symbol.mk_symbol `BVNOT);
   ("bvneg", Symbol.mk_symbol `BVNEG);
   ("bvand", Symbol.mk_symbol `BVAND);
   ("bvor", Symbol.mk_symbol `BVOR);
   ("bvadd", Symbol.mk_symbol `BVADD);
   ("bvmul", Symbol.mk_symbol `BVMUL);
   ("bvdiv", Symbol.mk_symbol `BVDIV);
   ("bvurem", Symbol.mk_symbol `BVUREM);
   ("bvshl", Symbol.mk_symbol `BVSHL);
   ("bvlshr", Symbol.mk_symbol `BVLSHR);
   ("bvult", Symbol.mk_symbol `BVULT);
   ("select", Symbol.mk_symbol `SELECT);
   ("store", Symbol.mk_symbol `STORE)]

(* Hashtable for hashconsed strings to function symbols *)
let hstring_symbol_table = HString.HStringHashtbl.create 50 


(* Populate hashtable with hashconsed strings and their symbol *)
let _ = 
  List.iter
    (function (s, v) -> 
      HString.HStringHashtbl.add 
        hstring_symbol_table 
        (HString.mk_hstring s)
        v)
    string_symbol_list 


(* Reserved words that cannot be a symbol *)
let reserved_word_list = 
  List.map 
    HString.mk_hstring 
    ["par"; "_"; "!"; "as"; "let"; "forall"; "exists" ]


(* Lookup symbol of a hashconsed string *)
let symbol_of_hstring s = 

  try 

    (* Map hashconsed string to symbol *)
    HString.HStringHashtbl.find hstring_symbol_table s

  (* String is not one of our symbols *)
  with Not_found -> 

    (* Check if string is a reserved word *)
    if List.memq s reserved_word_list then 
      
      (* Cannot parse S-expression *)
      raise 
        (Invalid_argument 
           (Format.sprintf 
              "Unsupported reserved word '%s' in expression"
              (HString.string_of_hstring s)))

    else

      (* String is not a symbol *)
      raise Not_found 


(* Convert an atom to a term *)
let term_of_hstring scope bound_vars t = 
  
  (* Empty strings are invalid *)
  if HString.length t = 0 then
    
    (* String is empty *)
    raise (Invalid_argument "const_of_hstring")
      
  else

    try

      (* Return numeral of string *)
      Term.mk_num (Numeral.of_string (HString.string_of_hstring t))

    (* String is not a decimal *)
    with Invalid_argument _ -> 

      try 

        (* Return decimal of string *)
        Term.mk_dec (Decimal.of_string (HString.string_of_hstring t))
          
      with Invalid_argument _ -> 

        try 

          (* Return bitvector of string *)
          Term.mk_bv (bitvector_of_hstring t)
            
        with Invalid_argument _ -> 
          
          try 
            
            (* Return propositional constant of string *)
            Term.mk_bool (bool_of_hstring t)

          (* String is not an interpreted symbol *)
          with Invalid_argument _ -> 

            try 
              
              (* Return bound symbol *)
              Term.mk_var (List.assq t bound_vars)

            (* String is not a bound variable *)
            with Not_found -> 
              
              try 

                (* Name of state variable *)
                let state_var_name = HString.string_of_hstring t in

                (* State variable of name and given scope *)
                let state_var = 
                  StateVar.state_var_of_string
                    (state_var_name, scope) 
                in
                
                (* State variable at instant zero *)
                let var = 
                  Var.mk_state_var_instance state_var Numeral.zero
                in

                (* Return term *)
                Term.mk_var var

              with Not_found -> 
                
                (* Cannot convert to an expression *)
                failwith 
                  (Format.asprintf 
                     "Invalid expression %a" 
                     HString.pp_print_hstring t)


let rec term_of_sexpr scope bound_vars = function 

  | HStringSExpr.List [] -> failwith "Invalid nil in expression"
  | HStringSExpr.List [_] -> failwith "Invalid singleton list in expression"

  (* Let binding *)
  | HStringSExpr.List [HStringSExpr.Atom a; HStringSExpr.List v; t] when a == s_let -> 

    (* Convert bindings and obtain a list of bound variables *)
    let bindings = bindings_of_sexpr scope bound_vars [] v in

    (* Convert bindings to an association list from strings to
       variables *)
    let bound_vars' = 
      List.map 
        (function (v, _) -> (Var.hstring_of_free_var v, v))
        bindings 
    in

    (* Parse the subterm, giving an association list of bound
       variables and return a let bound term *)
    Term.mk_let 
      bindings
      (term_of_sexpr scope (bound_vars @ bound_vars') t)

  (* Not a valid let binding *)
  | HStringSExpr.List (HStringSExpr.Atom a :: _) when a == s_let -> 
    failwith "Invalid let binding in expression"

  (* Atom *)
  | HStringSExpr.Atom a -> term_of_hstring scope bound_vars a 

  (* A primed variable *)
  | HStringSExpr.List [HStringSExpr.Atom c; HStringSExpr.Atom a] when c == s_prime -> 

    (* Term of primed atom *)
    let t = term_of_hstring scope bound_vars a in

    (* Prime term if it is a variable *)
    if Term.is_free_var t then Term.bump_state Numeral.one t else

      failwith "Prime only applies to variables"

  (* A function application *)
  | HStringSExpr.List (HStringSExpr.Atom h :: tl) -> 

    (try 

       (* Built-in symbol of string *)
       Term.mk_app
         (symbol_of_hstring h)
         (List.map (term_of_sexpr scope bound_vars) tl)

     with Not_found -> 

       (* String of hashconsed string *)
       let s = HString.string_of_hstring h in

       (* Length of suffix for initial state predicate name  *)
       let init_len = String.length init_pred_suff in

       (* String must be longer than suffix *)
       if String.length s > init_len then 

         if 

           (* String has suffix of initial state predicate? *)
           String.sub
             s
             (String.length s - init_len)
             init_len 
           = init_pred_suff

         then

           (* Uninterpreted function symbol *)
           let uf_symbol = 

             try 

               UfSymbol.uf_symbol_of_string s 

             with Not_found -> 

               failwith
                 (Format.sprintf "Predicate %s not defined" s)

           in

           if 

             (* Number of arguments must match definition *)
             (List.length (UfSymbol.arg_type_of_uf_symbol uf_symbol))
             = List.length tl 

           then

             (* Application of predicate symbol *)
             Term.mk_uf 
               uf_symbol
               (List.map (term_of_sexpr scope bound_vars) tl)

           else

             failwith "Wrong number of arguments"

         else

           (* Length of suffix for transition relation predicate name  *)
           let trans_len = String.length trans_pred_suff in

           (* String must be longer than suffix *)
           if String.length s > trans_len then 

             if 

               (* String has suffix of transition relation predicate? *)
               String.sub
                 s
                 (String.length s - trans_len)
                 trans_len 
               = trans_pred_suff

             then

               (* Uninterpreted function symbol *)
               let uf_symbol = 

                 try 

                   UfSymbol.uf_symbol_of_string s 

                 with Not_found -> 

                   failwith "Predicate not defined"

               in

               if 

                 (* Number of arguments must match definition *)
                 (List.length (UfSymbol.arg_type_of_uf_symbol uf_symbol))
                 = List.length tl 

               then

                 (* Application of predicate symbol *)
                 Term.mk_uf 
                   uf_symbol
                   (List.map (term_of_sexpr scope bound_vars) tl)

               else

                 failwith "Wrong number of arguments"

             else

               failwith "Undefined function symbol" 

           else

             failwith "Undefined function symbol" 

       else

         failwith "Undefined function symbol") 


  | _ -> Term.t_false


(* Convert a list of bindings *)
and bindings_of_sexpr scope b accum = function 

  (* All bindings consumed: return accumulator in original order *)
  | [] -> List.rev accum

  (* Take first binding *)
  | HStringSExpr.List [HStringSExpr.Atom v; t] :: tl -> 

    (* Convert to an expression *)
    let term = term_of_sexpr scope b t in

    (* Get the type of the expression *)
    let term_type = Term.type_of_term term in

    (* Create a variable of the identifier and the type of the expression *)
    let var = Var.mk_free_var v term_type in

    (* Add bound expresssion to accumulator *)
    bindings_of_sexpr scope b ((var, term) :: accum) tl

  (* Expression must be a pair *)
  | e :: _ -> 

    failwith "Invalid expression in let binding"
      

(* Convert a predicate definition *)
let pred_def_of_sexpr = function

  (* (define-pred NAME (VARS) (init INIT) (trans TRANS)) *)
  | HStringSExpr.List 
      [HStringSExpr.Atom c; 
       HStringSExpr.Atom p; 
       HStringSExpr.List v; 
       HStringSExpr.List [HStringSExpr.Atom ci; i]; 
       HStringSExpr.List [HStringSExpr.Atom ct; t]] 
    when c == s_define_pred && ci == s_init && ct = s_trans -> 

    (* Get name of defined predicate *)
    let pred_name = HString.string_of_hstring p in

    (* Create state variables *)
    let state_vars = List.map (state_var_of_sexpr [pred_name]) v in

    (* Arguments of initial state predicate *)
    let init_args = 
      List.map
        (fun sv -> Var.mk_state_var_instance sv Numeral.zero)
        state_vars
    in

    (* Arguments of transition relation predicate *)
    let trans_args = 
      init_args @
      List.map 
        (fun sv -> Var.mk_state_var_instance sv Numeral.one)
        (List.filter (fun sv -> not (StateVar.is_const sv)) state_vars)
    in

    (* Types of initial state predicate arguments *)
    let init_args_types = List.map Var.type_of_var init_args in

    (* Types of transition relation predicate arguments *)
    let trans_args_types = List.map Var.type_of_var trans_args in

    (* Predicate symbol for initial state predicate *)
    let init_uf_symbol = 
      UfSymbol.mk_uf_symbol
        (init_pred_name pred_name) 
        init_args_types
        Type.t_bool 
    in

    (* Predicate symbol for transition relation predicate *)
    let trans_uf_symbol = 
      UfSymbol.mk_uf_symbol
        (trans_pred_name pred_name) 
        trans_args_types
        Type.t_bool 
    in
    
    (* Initial state constraint *)
    let init_term = term_of_sexpr [pred_name] [] i in

    (* Transition relation *)
    let trans_term = term_of_sexpr [pred_name] [] t in

    (* Definitions of initial state and transition relation *)
    ((init_uf_symbol, (init_args, init_term)), 
     (trans_uf_symbol, (trans_args, trans_term)))

  | HStringSExpr.Atom _ 
  | HStringSExpr.List _ -> failwith "Invalid format of predicate definition"


(* Create a copy of the state variable at the top level *)
let state_var_of_top_scope state_var =
  
  (* Create state variable with same parameters except scope *)
  StateVar.mk_state_var
    ~is_input:(StateVar.is_input state_var)
    ~is_const:(StateVar.is_const state_var)
    (StateVar.name_of_state_var state_var)
    top_scope
    (StateVar.type_of_state_var state_var)
    []


(* Create a copy of the state variable instance at the top level *)
let var_of_top_scope var = 

  (* State variable *)
  let state_var = Var.state_var_of_state_var_instance var in

  (* State variable of top scope *)
  let state_var' = state_var_of_top_scope state_var in

  (* Create state variable instance of top scope *)
  Var.mk_state_var_instance 
    state_var'
    (Var.offset_of_state_var_instance var)


(* Parse from input channel *)
let of_channel in_ch = 

  (* Create a lexing buffer on solver's stdout *)
  let lexbuf = Lexing.from_channel in_ch in

  (* Parse S-expression and return *)
  let sexps = SExprParser.sexps SExprLexer.main lexbuf in

  (* Create definitions of expressions, last expression is list of
     properties *)
  let rec aux defs = function 

    | [] -> failwith "Empty input"

    (* List must end with check-prop atom *)
    | [HStringSExpr.List [HStringSExpr.Atom s; HStringSExpr.List p]] 
      when s == s_check_prop -> 

      (* Last element in (reversed list) is topmost definition *)
      let top_init, top_trans = match defs with
        | [] -> failwith "Empty definitions"
        | h :: _ -> h
      in
      
      (* Predicate symbol and arguments of initial state constraint *)
      let (top_init_uf_symbol, (top_init_vars, _)) = top_init in

      (* Predicate symbol and arguments of transition relation *)
      let (top_trans_uf_symbol, (top_trans_vars, _)) = top_trans in

      (* Copy state variables of top node to new scope

         Must do this first, because variables in property are of top
         scope. *)
      let state_vars = 
        List.map 
          (fun v -> 
             state_var_of_top_scope 
           (Var.state_var_of_state_var_instance v))
          top_init_vars
      in
  
      (* Copy variables in signature of top node to new scope *)
      let init_vars = 
        List.map var_of_top_scope top_init_vars 
      in
      
      (* Copy variables in signature of top node to new scope *)
      let trans_vars = 
        List.map var_of_top_scope top_trans_vars 
      in
      
      (* Expression for initial state constraint *)
      let init_term = 
        Term.mk_uf 
          top_init_uf_symbol 
          (List.map Term.mk_var init_vars)
      in
      
      (* Expression for transition relation *)
      let trans_term = 
        Term.mk_uf
          top_trans_uf_symbol
          (List.map Term.mk_var trans_vars)
      in

      let init = 
        (top_init_uf_symbol, 
         (List.combine 
            top_init_vars 
            (List.map Term.mk_var init_vars)))
      in

      let trans =
        (top_trans_uf_symbol, 
         (List.combine 
            top_trans_vars
            (List.map Term.mk_var trans_vars)))
      in

      (* Collect all properties to prove *)
      let props = 
        List.fold_left 
          (function accum -> function

             (* Property must be a pair of name and term *)
             | HStringSExpr.List [HStringSExpr.Atom p; t] -> 

               (* Convert S-expression to term *)
               (HString.string_of_hstring p, 
                term_of_sexpr top_scope  [] t) 
               :: accum

             | _ -> failwith "Invalid format of property")
          []
          p
      in

      (* Return definititons in original order and properties *)
      List.rev defs, state_vars, init, trans, props

    | [HStringSExpr.List (HStringSExpr.Atom s :: _)] when s == s_check_prop -> 

      failwith "Invalid format of check-prop statement"

    | [_] -> failwith "Definitions must end with check-prop statement"
               
    (* First element of a list of at least two elements is a predicate
       definition *)
    | h :: tl -> aux ((pred_def_of_sexpr h) :: defs) tl
                   
  in

  (* Definitions and properties in input *)
  let defs, state_vars, init, trans, props = aux [] sexps in

  let res = 
    TransSys.mk_trans_sys 
      defs
      state_vars
      init
      trans
      props
      TransSys.Native
  in

  debug nativeInput
    "%a"
    TransSys.pp_print_trans_sys res
  in

  res



(* Open and parse from file *)
let of_file filename = 

    (* Open the given file for reading *)
    let use_file = open_in filename in
    let in_ch = use_file in

    of_channel in_ch

(* ************************************************************ *)
(* Counterexample output in plain text                          *)
(* ************************************************************ *)


(* Return width of widest identifier and widest value *)
let rec widths_of_model max_ident_width max_val_width = function 
  
  | [] -> (max_ident_width, max_val_width)

  | (state_var, values) :: tl -> 

    (* Maximal print width of state variable *)
    let max_ident_width' = 
      max
        max_ident_width
        (String.length 
           (string_of_t StateVar.pp_print_state_var state_var))
    in
    
    (* Maximal print width of values *)
    let max_val_width' =
      List.fold_left 
        (fun m v -> 
           max
             m
             (String.length
                (string_of_t Term.pp_print_term v)))
        max_val_width
        values
    in

    (* Return new maximum widths *)
    widths_of_model max_ident_width' max_val_width' tl

(* Pretty-print a value in a model *)
let pp_print_value_pt val_width ppf value = 

  Format.fprintf
    ppf
    "%-*s"
    val_width
    (string_of_t Term.pp_print_term value)

(* Pretty-print a state variable and its values *)
let pp_print_state_var_pt state_var_width val_width ppf (state_var, values) =

  Format.fprintf 
    ppf
    "@[<h>%-*s: %a@]"
    state_var_width
    (string_of_t StateVar.pp_print_state_var state_var)
    (pp_print_list
       (pp_print_value_pt val_width)
       " ")
    values

(* Pretty-print a model *)
let pp_print_path_pt ppf model = 

  let state_var_width, val_width = widths_of_model 0 0 model in

  Format.fprintf
    ppf
    "@[<v>%a@]"
    (pp_print_list
       (pp_print_state_var_pt state_var_width val_width)
       "@,")
    model
       
(* ************************************************************ *)
(* Counterexample output in XML                                 *)
(* ************************************************************ *)

let pp_print_path_xml ppf model = ()

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
