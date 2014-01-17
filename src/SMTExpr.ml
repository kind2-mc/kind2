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


(* An SMT expression is a term *)
type t = Term.t


(* Pretty-print an expression *)
let pp_print_expr = Term.pp_print_term


(* Pretty-print an expression to the standard formatter *)
let print_expr = pp_print_expr Format.std_formatter


(* Return a string representation of an expression *)
let string_of_expr t = 
  string_of_t pp_print_expr t
  


(* ********************************************************************* *)
(* Logics                                                                *)
(* ********************************************************************* *)


(* The defined logics in SMTLIB *)
type logic = 
  [ `detect
  | `AUFLIA
  | `AUFLIRA
  | `AUFNIRA
  | `LRA 
  | `LIA
  | `QF_ABV
  | `QF_AUFBV
  | `QF_AUFLIA
  | `QF_AX
  | `QF_BV
  | `QF_IDL
  | `QF_LIA
  | `QF_LRA
  | `QF_NIA
  | `QF_NRA
  | `QF_RDL
  | `QF_UF
  | `QF_UFBV
  | `QF_UFIDL
  | `QF_UFLIA
  | `QF_UFLRA
  | `QF_UFNRA
  | `UFLRA
  | `UFLIA
  | `UFNIA
  ]

(* Convert a logic to a string *)
let string_of_logic = function
  | `AUFLIA -> "AUFLIA"
  | `AUFLIRA -> "AUFLIRA"
  | `AUFNIRA -> "AUFNIRA"
  | `LRA -> "LRA"
  | `LIA -> "LIA"
  | `QF_ABV -> "QF_ABV"
  | `QF_AUFBV -> "QF_AUFBV"
  | `QF_AUFLIA -> "QF_AUFLIA"
  | `QF_AX -> "QF_AX"
  | `QF_BV -> "QF_BV"
  | `QF_IDL -> "QF_IDL"
  | `QF_LIA -> "QF_LIA"
  | `QF_LRA -> "QF_LRA"
  | `QF_NIA -> "QF_NIA"
  | `QF_NRA -> "QF_NRA"
  | `QF_RDL -> "QF_RDL"
  | `QF_UF -> "QF_UF"
  | `QF_UFBV -> "QF_UFBV"
  | `QF_UFIDL -> "QF_UFIDL"
  | `QF_UFLIA -> "QF_UFLIA"
  | `QF_UFLRA -> "QF_UFLRA"
  | `QF_UFNRA -> "QF_UFNRA"
  | `UFLIA -> "UFLIA"
  | `UFLRA -> "UFLRA"
  | `UFNIA -> "UFNIA"
  | _ -> raise (Invalid_argument "Unsupported logic")


(* Pretty-print a logic identifier *)
let pp_print_logic ppf l = 
  Format.pp_print_string ppf (string_of_logic l) 


(* ********************************************************************* *)
(* Sorts                                                                 *)
(* ********************************************************************* *)

(* An SMT sort is a type *)
type sort = Type.t

(*

(* A defined sort *)
type sort = 
  | Bool
  | Real
  | Int
  | BV of numeral
  | Array of sort * sort


(* Pretty-print a sort *)
let rec pp_print_sort ppf = function

  | Bool -> 
    Format.pp_print_string ppf "Bool"

  | Int -> 
    Format.pp_print_string ppf "Int"

  | Real -> 
    Format.pp_print_string ppf "Real"

  | BV m -> 
    Format.fprintf ppf "BitVec %a" pp_print_numeral m

  | Array (s1, s2) -> 
    Format.fprintf ppf "Array %a %a" pp_print_sort s1 pp_print_sort s2


(* Return string representation of sort *)
let string_of_sort s = string_of_t pp_print_sort s

*)

let pp_print_sort = Type.pp_print_type 

let string_of_sort = string_of_t Type.pp_print_type



(* Convert a type to an SMT sort *)
let rec smtsort_of_type t = match Type.node_of_type t with
  
  (* Convert integer range to integer type *)
  | Type.IntRange _ -> Type.mk_int ()

  (* Recursively convert index and value type of array type *)
  | Type.Array (i, t) -> 
    Type.mk_array (smtsort_of_type i) (smtsort_of_type t)

  (* Keep basic types unchanged *)
  | Type.Bool -> t
  | Type.Int -> t
  | Type.Real -> t
  | Type.BV m -> t


(* ********************************************************************* *)
(* Responses from solver instances                                       *)
(* ********************************************************************* *)


(* Arguments to a custom command *)
type custom_arg = 
  | ArgString of string  (* String argument *)
  | ArgExpr of t         (* Expression argument *)

(* Response from the solver *)
type response =
  | NoResponse
  | Unsupported
  | Success 
  | Error of string
      

(* Response from the solver to a (check-sat) command *)
type check_sat_response =
  | Response of response
  | Sat
  | Unsat
  | Unknown

(* Pretty-print a custom argument *)
let pp_print_custom_arg ppf = function 
  | ArgString s -> Format.pp_print_string ppf s
  | ArgExpr e -> pp_print_expr ppf e


(* Return a string representation of a custom argument *)
let string_of_custom_arg t = 
  string_of_t pp_print_custom_arg t


(* ********************************************************************* *)
(* Conversions from S-expressions to terms                               *)
(* ********************************************************************* *)


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


(* Reserved words that we don't support *)
let reserved_word_list = 
  List.map 
    HString.mk_hstring 
    ["par"; "_"; "!"; "as"; "let"; "forall"; "exists" ]


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


(* Static hashconsed strings *)
let s_let = HString.mk_hstring "let"
let s_success = HString.mk_hstring "success"
let s_unsupported = HString.mk_hstring "unsupported"
let s_error = HString.mk_hstring "error"
let s_sat = HString.mk_hstring "sat"
let s_unsat = HString.mk_hstring "unsat"
let s_unknown = HString.mk_hstring "unknown"


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
              "Unsupported reserved word '%s' in S-expression"
              (HString.string_of_hstring s)))

    else

      (* String is not a symbol *)
      raise Not_found 


(* Convert a string to a postive numeral or decimal

   The first argument is an association list of strings to variables
   that are currently bound to distinguish between uninterpreted
   function symbols and variables. *)
let const_of_smtlib_token b t = 

  (* Empty strings are invalid *)
  if HString.length t = 0 then

    (* String is empty *)
    raise (Invalid_argument "num_expr_of_smtlib_token")

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
            
            (* Return symbol of string *)
            Term.mk_bool (bool_of_hstring t)

          (* String is not an interpreted symbol *)
          with Invalid_argument _ -> 

            try 

              (* Return bound symbol *)
              Term.mk_var (List.assq t b)
                
            (* String is not a bound variable *)
            with Not_found -> 
              
              try 
                
                (* Return uninterpreted constant *)
                Term.mk_uf 
                  (UfSymbol.uf_symbol_of_string (HString.string_of_hstring t))
                  []

              with Not_found -> 

                (* Cannot convert to an expression *)
                failwith "Invalid constant symbol in S-expression"

                

(* Convert a string S-expression to an expression *)
let rec expr_of_string_sexpr' b = function 

  (* An empty list *)
  | HStringSExpr.List [] -> 

    (* Cannot convert to an expression *)
    failwith "Invalid Nil in S-expression"

  (*  A let binding *)
  | HStringSExpr.List 
      ((HStringSExpr.Atom s) :: [HStringSExpr.List v; t]) 
    when s == s_let -> 

    (* Convert bindings and obtain a list of bound variables *)
    let bindings = bindings_of_string_sexpr b [] v in

    (* Convert bindings to an association list from strings to
       variables *)
    let b' = 
      List.map 
        (function (v, _) -> (Var.hstring_of_temp_var v, v))
        bindings 
    in

    (* Parse the subterm, giving an association list of bound
       variables and return a let bound term *)
    Term.mk_let bindings (expr_of_string_sexpr' (b @ b') t)

  (* A singleton list *)
  | HStringSExpr.List [_] as e -> 

    (* Cannot convert to an expression *)
    failwith 
      ("Invalid singleton list in S-expression " ^ 
         (string_of_t HStringSExpr.pp_print_sexpr e))

  (* A list with a non-atom at the head *)
  | HStringSExpr.List (HStringSExpr.List _ :: _) -> 

    (* Cannot convert to an expression *)
    failwith "Invalid list element at head in S-expression"

  (* Atom or singleton list *)
  | HStringSExpr.Atom s ->

    (* Leaf in the symbol tree *)
    (const_of_smtlib_token b s)

  (*  A list with more than one element *)
  | HStringSExpr.List ((HStringSExpr.Atom h) :: tl) -> 

    (

      (* Symbol from string *)
      let s = 

        try 

          (* Map the string to an interpreted function symbol *)
          symbol_of_hstring h 

        with 

          (* Function symbol is uninterpreted *)
          | Not_found -> 

            (* Uninterpreted symbol from string *)
            let u = 

              try 

                UfSymbol.uf_symbol_of_string (HString.string_of_hstring h)

              with Not_found -> 

                (* Cannot convert to an expression *)
                failwith 
                  (Format.sprintf 
                     "Undeclared uninterpreted function symbol %s in \
                      S-expression"
                     (HString.string_of_hstring h))
            in

            (* Get the uninterpreted symbol of the string *)
            Symbol.mk_symbol (`UF u)


      in

      (* Create an application of the function symbol to the subterms *)
      let t = 
        Term.mk_app s (List.map (expr_of_string_sexpr' b) tl)
      in

      (* Convert (= 0 (mod t n)) to (t divisible n) *)
      Term.mod_to_divisible t

    )

(* Convert a list of bindings *)
and bindings_of_string_sexpr b accum = function 

  (* All bindings consumed: return accumulator in original order *)
  | [] -> List.rev accum

  (* Take first binding *)
  | HStringSExpr.List [HStringSExpr.Atom var; expr] :: tl -> 

    (* Convert to an expression *)
    let expr = expr_of_string_sexpr' b expr in

    (* Get the type of the expression *)
    let expr_type = Term.type_of_term expr in

    (* Create a variable of the identifier and the type of the expression *)
    let tvar = Var.mk_temp_var var expr_type in

    (* Add bound expresssion to accumulator *)
    bindings_of_string_sexpr b ((tvar, expr) :: accum) tl

  (* Expression must be a pair *)
  | e :: _ -> 

    failwith 
      ("Invalid expression in let binding: " ^
         (string_of_t HStringSExpr.pp_print_sexpr e))
      

(* Call function with an empty list of bound variables *)      
let expr_of_string_sexpr = expr_of_string_sexpr' []


(* ********************************************************************* *)
(* Conversions from terms to SMT expressions                             *)
(* ********************************************************************* *)


(* Convert a variable to an SMT expression *)
let smtexpr_of_var v =

  (* Get the state variable contained in the variable *) 
  let sv = Var.state_var_of_state_var_instance v in
  
  (* Get the offset of the state variable instance *)
  let o = Var.offset_of_state_var_instance v in

  (* Get the uninterpreted function symbol associated with the state
     variable *)
  let u = StateVar.uf_symbol_of_state_var sv in 

  (* Convert a state variable instance to a uninterpreted function *) 
  Term.mk_uf u [Term.mk_num o] 


(* Convert an SMT expression to a variable *)
let rec var_of_smtexpr e = 

  (* Keep bound variables untouched *)
  if Term.is_bound_var e then               

    invalid_arg 
      "var_of_smtexpr: Bound variable"

  else

    (* Check top symbol of SMT expression *)
    match Term.destruct e with

      (* Unary uninterpreted function *)
      | Term.T.App (su, [a]) when Symbol.is_uf su -> 

        (

          (* Check argument of uninterpreted function *)
          match Term.destruct a with

            (* Unary uninterpreted function with a numeral argument *)
            | Term.T.Const sn when Symbol.is_numeral sn -> 

              let sv = 

                try 

                  (* Get state variable associated with function symbol *)
                  StateVar.state_var_of_uf_symbol (Symbol.uf_of_symbol su)

                with Not_found -> 

                  invalid_arg 
                    (Format.asprintf 
                       "var_of_smtexpr: %a\
                        No state variable found for uninterpreted function symbol"
                       Term.pp_print_term e)
              in

              (* Create state variable instance *)
              Var.mk_state_var_instance sv (Symbol.numeral_of_symbol sn)

            (* Unary uninterpreted function with a non-numeral argument *)
            | _ -> 

              invalid_arg 
                (Format.asprintf 
                   "var_of_smtexpr: %a\
                    Invalid argument to uninterpreted function"
                   Term.pp_print_term e)

        )

      (* Uninterpreted function symbol with invalid arity *)
      | Term.T.Const s
      | Term.T.App (s, _) when Symbol.is_uf s -> 

        invalid_arg 
          "var_of_smtexpr: \
           Invalid arity of uninterpreted function"

      (* Annotated term *)
      | Term.T.Attr (t, _) -> var_of_smtexpr t

      (* Other expressions *)
      | Term.T.Const _
      | Term.T.App _ 
      | Term.T.Var _ -> 

        invalid_arg 
          "var_of_smtexpr: \
           Must be an uninterpreted function"


(* Convert a term to an expression for the SMT solver *)
let term_of_smtexpr term =

  Term.map
    (function _ -> function t -> 
       try Term.mk_var (var_of_smtexpr t) with Invalid_argument _ -> t)
    term


(* Convert a term to an SMT expression *)
let quantified_smtexpr_of_term quantifier vars term = 

  (* Map all variables to temporary variables and convert types to SMT
     sorts, in particular convert IntRange types to Ints *)
  let var_to_temp_var = 
    List.fold_left 
      (function accum -> function v -> 

         (* Get name of state variable *)
         let sv = 
           StateVar.name_of_state_var (Var.state_var_of_state_var_instance v)
         in

         (* Get offset of state variable instance *)
         let o = Var.offset_of_state_var_instance v in

         (* Convert type of variable to SMT sort *)
         let t' = smtsort_of_type (Var.type_of_var v) in

         (* Create temporary variable of state variable instance with
            type converted to an SMT sort *)
         let v' = 
           Var.mk_temp_var 
             (HString.mk_hstring (sv ^ Numeral.string_of_numeral o))
             t'
         in

         (* Add pair of variable and temporary variable to association list *)
         (v, v') :: accum)
      []
      vars
  in

  (* Convert variables to uninterpreted functions for SMT solver and
     variables to be quantified over to variables of SMT sorts *)
  let term' = 
    Term.map
      (function _ -> function

         (* Term is a free variable *)
         | t when Term.is_free_var t -> 

           (* Get variable of term *)
           let v = Term.free_var_of_term t in

           (* Try to convert free variable to temporary variable for
              quantification, otherwise convert variable to
              uninterpreted function *)
           (try 
              Term.mk_var (List.assq v var_to_temp_var) 
            with Not_found -> smtexpr_of_var v)

         (* Change divisibility symbol to modulus operator *)
         | t -> Term.divisible_to_mod t)

      term
  in

  (* Return if list of variables is empty *)
  if vars = [] then term' else

    (* Quantify all variables *)
    (if quantifier then Term.mk_exists else Term.mk_forall)
      (List.map snd var_to_temp_var)
      term'


(* Convert an expression from the SMT solver to a term *)
let smtexpr_of_term term = 
  quantified_smtexpr_of_term false [] term


(* Declare uninterpreted symbols in the SMT solver

   TODO: Flag declarations to avoid redeclaring symbols and enable
   incremental declarations
*)
let declare_smt_symbols declare_fun =

  UfSymbol.fold_uf_declarations 
    (fun symbol arg_type res_type error ->
      
      if error = Success then
        declare_fun 
          symbol
          (List.map smtsort_of_type arg_type)
          (smtsort_of_type res_type)
      else 
        error)
    Success


(* ********************************************************************* *)
(* Responses from solver instances                                       *)
(* ********************************************************************* *)


(* Pretty-print a command response *)
let pp_print_response ppf = function
  | NoResponse -> Format.pp_print_string ppf "NoResponse"
  | Unsupported -> Format.pp_print_string ppf "Unsupported"
  | Success -> Format.pp_print_string ppf "Success"
  | Error e -> 
    Format.pp_print_string ppf "Error: "; 
    Format.pp_print_string ppf e
      

(* Pretty-print a response to a (chek-sat) command *)
let pp_print_check_sat_response ppf = function
  | Response r -> pp_print_response ppf r
  | Sat -> Format.pp_print_string ppf "Sat"
  | Unsat -> Format.pp_print_string ppf "Unsat"
  | Unknown -> Format.pp_print_string ppf "Unknown"
    

(* Pretty-print a response to a list of expression pairs *)
let rec pp_print_values ppf = function 

  | [] -> ()

  | (e, v) :: [] -> 
    
    Format.pp_open_hvbox ppf 2;
    Format.pp_print_string ppf "(";
    pp_print_expr ppf e;
    Format.pp_print_space ppf ();
    pp_print_expr ppf v;
    Format.pp_print_string ppf ")";
    Format.pp_close_box ppf ()

  | (e, v) :: tl -> 

    pp_print_values ppf [(e,v)];
    Format.pp_print_space ppf ();
    pp_print_values ppf tl


(* Pretty-print a response to a (get-value) command *)
let pp_print_get_value_response ppf = function

  | Success, v -> 
    pp_print_response ppf Success; 
    Format.pp_print_space ppf ();
    Format.pp_open_hvbox ppf 1;
    Format.pp_print_string ppf "(";
    pp_print_values ppf v;
    Format.pp_print_string ppf ")";
    Format.pp_close_box ppf ()

  | r, _ -> 
    pp_print_response ppf r


(* Pretty-print a response to a (get-unsat-core) command *)
let pp_print_get_unsat_core_response ppf = function

  | Success, c -> 

    Format.fprintf 
      ppf 
      "@[<v>%a@,@[<hv 1>(%a)@]"
      pp_print_response Success
      (pp_print_list Format.pp_print_string "@ ") c

  | r, _ -> 
    pp_print_response ppf r


(* Pretty-print a response to a custom command *)
let pp_print_custom_command_response ppf = function 

  | Success, r -> 
    pp_print_response ppf Success; 
    Format.pp_print_newline ppf ();
    Format.pp_open_vbox ppf 0;
    pp_print_list HStringSExpr.pp_print_sexpr "" ppf r;
    Format.pp_close_box ppf ()
    
  | r, _ -> 
    pp_print_response ppf r


    
(* Return a solver response of an S-expression *)
let response_of_sexpr = function 

  (* Successful command *)
  | HStringSExpr.Atom s when s == s_success -> Success 

  (* Unsupported command *)
  | HStringSExpr.Atom s when s == s_unsupported -> Unsupported

  (* Error *)
  | HStringSExpr.List 
      [HStringSExpr.Atom s; HStringSExpr.Atom e ] when s == s_error -> 
    Error (HString.string_of_hstring e)

  (* Invalid response *)
  | e -> 

    raise 
      (Failure 
         ("Invalid solver response " ^ HStringSExpr.string_of_sexpr e))


(* Return a solver response to a check-sat command of an S-expression *)
let check_sat_response_of_sexpr = function 

  | HStringSExpr.Atom s when s == s_sat -> Sat
  | HStringSExpr.Atom s when s == s_unsat -> Unsat
  | HStringSExpr.Atom s when s == s_unknown -> Unknown
  | r -> Response (response_of_sexpr r)


(* Helper function to return a solver response to a get-value command
   as expression pairs *)
let rec get_value_response_of_sexpr' accum = function 
  | [] -> (Success, List.rev accum)
  | HStringSExpr.List [ e; v ] :: tl -> 
    get_value_response_of_sexpr' 
      ((((expr_of_string_sexpr e) :> t), 
        ((expr_of_string_sexpr v :> t))) :: 
          accum) 
      tl
  | _ -> invalid_arg "get_value_response_of_sexpr"

(* Return a solver response to a get-value command as expression pairs *)
let get_value_response_of_sexpr = function 

  (* Solver returned error message 

     Must match for error first, because we may get (error "xxx") or
     ((x 1)) which are both lists *)
  | HStringSExpr.List 
      [HStringSExpr.Atom s; 
       HStringSExpr.Atom e ] when s == s_error -> 
    (Error (HString.string_of_hstring e), [])

  (* Solver returned a list not starting with an error atom  *)
  | HStringSExpr.List l -> get_value_response_of_sexpr' [] l

  (* Solver returned other response *)
  | r -> (response_of_sexpr r, [])


(* Return a solver response to a get-unsat-core command as list of strings *)
let get_unsat_core_response_of_sexpr = function 

  (* Solver returned error message 

     Must match for error first *)
  | HStringSExpr.List 
      [HStringSExpr.Atom s; HStringSExpr.Atom e ]
    when s == s_error -> 
    (Error (HString.string_of_hstring e), [])

  (* Solver returned a list not starting with an error atom *)
  | HStringSExpr.List l -> 

    (* Convert list of atoms to list of strings *)
    (Success,
     List.map
       (function 
         | HStringSExpr.Atom n -> (HString.string_of_hstring n)
         | _ -> invalid_arg "get_unsat_core_response_of_sexpr")
       l)

  (* Solver returned other response *)
  | r -> (response_of_sexpr r, [])


(* Return a solver response to a custom command *)
let get_custom_command_response_of_sexpr = function 

  (* Solver returned error message 

     Must match for error first, because we may get (error "xxx") or
     ((x 1)) which are both lists *)
  | HStringSExpr.List 
      [HStringSExpr.Atom s; HStringSExpr.Atom e ] 
    when s == s_error -> 
    Error (HString.string_of_hstring e)

  (* Solver returned unsupported message *)
  | HStringSExpr.Atom s when s == s_unsupported -> Unsupported

  (* Solver returned success message *)
  | HStringSExpr.Atom s when s == s_success -> Success 

  | _ -> NoResponse



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
