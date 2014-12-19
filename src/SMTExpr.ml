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
open SolverResponse

(* An SMT expression is a term *)
type t = Term.t

(* An SMT variable is a variable *)
type var = Var.t


type custom_arg = 
  | ArgString of string
  | ArgExpr of t



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

(* Static hashconsed strings *)
let s_let = HString.mk_hstring "let"
let s_forall = HString.mk_hstring "forall"
let s_exists = HString.mk_hstring "exists"



(* ********************************************************************* *)
(* Conversions from S-expressions to terms                               *)
(* ********************************************************************* *)

module type Conv =
  sig 

    val smtsort_of_type : Type.t -> sort

    val smtexpr_of_var : (UfSymbol.t -> unit) -> Var.t -> t

    val type_of_string_sexpr : HStringSExpr.t -> sort
                                                   
    val expr_of_string_sexpr : HStringSExpr.t -> t

    val string_of_logic : Term.logic -> string 

    val pp_print_logic : Format.formatter -> Term.logic -> unit

    val pp_print_sort : Format.formatter -> sort -> unit

    val string_of_sort : sort -> string

    val pp_print_expr : Format.formatter -> t -> unit

    val print_expr : t -> unit

    val string_of_expr : t -> string

    val smtexpr_of_term : (UfSymbol.t -> unit) -> t -> t

    val quantified_smtexpr_of_term : (UfSymbol.t -> unit) -> bool -> Var.t list -> t -> t

    val var_of_smtexpr : t -> Var.t

    val term_of_smtexpr : t -> t

    val pp_print_custom_arg : Format.formatter -> custom_arg -> unit

    val string_of_custom_arg : custom_arg -> string
                                
  end

module Converter ( Driver : SolverDriver.S ) : Conv =
  struct

    include Driver
    
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



    let pp_print_term ppf t =  Term.T.pp_print_term_w Driver.pp_print_symbol ppf t
        
    
    
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

      let res = 

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

              (* Return decimal of string *)
              Term.mk_dec (Decimal.of_num (Num.num_of_string
                                             (HString.string_of_hstring t)))

            with Invalid_argument _ | Failure "num_of_string" -> 

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
                        (UfSymbol.uf_symbol_of_string
                           (HString.string_of_hstring t))
                        []

                    with Not_found -> 

                      debug smtexpr 
                        "const_of_smtlib_token %s failed" 
                        (HString.string_of_hstring t)
      in

      (* Cannot convert to an expression *)
      failwith "Invalid constant symbol in S-expression"

        in

        debug smtexpr 
              "const_of_smtlib_token %s is %a" 
              (HString.string_of_hstring t)
              pp_print_term res
        in

        res

    (* Convert a string S-expression to an expression *)
    let rec expr_of_string_sexpr' bound_vars = function 

      (* An empty list *)
      | HStringSExpr.List [] -> 

         (* Cannot convert to an expression *)
         failwith "Invalid Nil in S-expression"

      (*  A let binding *)
      | HStringSExpr.List 
          ((HStringSExpr.Atom s) :: [HStringSExpr.List v; t]) 
           when s == s_let -> 

         (* Convert bindings and obtain a list of bound variables *)
         let bindings = bindings_of_string_sexpr bound_vars [] v in

         (* Convert bindings to an association list from strings to
       variables *)
         let bound_vars' = 
           List.map 
             (function (v, _) -> (Var.hstring_of_temp_var v, v))
             bindings 
         in

         (* Parse the subterm, giving an association list of bound
       variables and return a let bound term *)
         Term.mk_let 
           bindings
           (expr_of_string_sexpr' (bound_vars @ bound_vars') t)

      (*  A universal or existential quantifier *)
      | HStringSExpr.List 
          ((HStringSExpr.Atom s) :: [HStringSExpr.List v; t]) 
           when s == s_forall || s == s_exists -> 

         (* Get list of variables bound by the quantifier *)
         let quantified_vars = bound_vars_of_string_sexpr bound_vars [] v in

         (* Convert bindings to an association list from strings to
            variables *)
         let bound_vars' = 
           List.map 
             (function v -> (Var.hstring_of_temp_var v, v))
             quantified_vars
         in

         (* Parse the subterm, giving an association list of bound variables
            and return a universally or existenially quantified term *)
         (if s == s_forall then Term.mk_forall 
          else if s == s_exists then Term.mk_exists
          else assert false)
           quantified_vars
           (expr_of_string_sexpr' (bound_vars @ bound_vars') t)

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
         (const_of_smtlib_token bound_vars s)

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
             Term.mk_app s (List.map (expr_of_string_sexpr' bound_vars) tl)
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

         (* Create a variable of the identifier and the type of
            the expression *)
         let tvar = Var.mk_temp_var var expr_type in

         (* Add bound expresssion to accumulator *)
         bindings_of_string_sexpr b ((tvar, expr) :: accum) tl

      (* Expression must be a pair *)
      | e :: _ -> 

         failwith 
           ("Invalid expression in let binding: " ^
              (string_of_t HStringSExpr.pp_print_sexpr e))
           

    (* Convert a list of typed variables *)
    and bound_vars_of_string_sexpr b accum = function 

      (* All bindings consumed: return accumulator in original order *)
      | [] -> List.rev accum

      (* Take first binding *)
      | HStringSExpr.List [HStringSExpr.Atom v; t] :: tl -> 

         (* Get the type of the expression *)
         let var_type = type_of_string_sexpr t in

         (* Create a variable of the identifier and the type of the expression *)
         let tvar = Var.mk_temp_var v var_type in

         (* Add bound expresssion to accumulator *)
         bound_vars_of_string_sexpr b (tvar :: accum) tl

      (* Expression must be a pair *)
      | e :: _ -> 

         failwith 
           ("Invalid expression in let binding: " ^
              (string_of_t HStringSExpr.pp_print_sexpr e))
           

    (* Call function with an empty list of bound variables *)      
    let expr_of_string_sexpr = expr_of_string_sexpr' []



    (* Pretty-print an expression *)
    let pp_print_expr = pp_print_term


    (* Pretty-print an expression to the standard formatter *)
    let print_expr = pp_print_expr Format.std_formatter


    (* Return a string representation of an expression *)
    let string_of_expr t = 
      string_of_t pp_print_expr t



    (* ********************************************************************* *)
    (* Conversions from terms to SMT expressions                             *)
    (* ********************************************************************* *)

    (* Convert a type to an SMT sort : no conversion for yices *)
    let rec smtsort_of_type t = interpr_type t


    (* Convert a variable to an SMT expression *)
    let smtexpr_of_var declare var =

      (* Building the uf application. *)
      Term.mk_uf
        (* Getting the unrolled uf corresponding to the state var
           instance. *)
        (Var.unrolled_uf_of_state_var_instance var declare)
        (* No arguments. *)
        []


    (* Convert a variable to an SMT expression *)
    let smtexpr_of_var declare var =

      (* Building the uf application. *)
      Term.mk_uf
        (* Getting the unrolled uf corresponding to the state var
           instance. *)
        (Var.unrolled_uf_of_state_var_instance var declare)
        (* No arguments. *)
        []


    (* Convert an SMT expression to a variable *)
    let rec var_of_smtexpr e = 

      (* Keep bound variables untouched *)
      if Term.is_bound_var e then               

        invalid_arg 
          "var_of_smtexpr: Bound variable"

      else

        (* Check top symbol of SMT expression *)
        match Term.destruct e with

        (* An unrolled variable is a constant term if it is not an
           array. *)
        | Term.T.Const sym -> (

            try
              (* Retrieving unrolled and constant state vars. *)
              Var.state_var_instance_of_symbol sym
            with
            | Not_found ->

              invalid_arg
                (Format.asprintf
                   "var_of_smtexpr: %a\
                    No state variable found for uninterpreted function symbol"
                   Term.pp_print_term e)
          )

        (* An unrolled variable might be an array in which case it would
           show up as an application. *)
        | Term.T.App (su, args) when Symbol.is_uf su ->

          (* Array are unsupported atm. *)

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
  let quantified_smtexpr_of_term declare quantifier vars term = 

      (* Map all variables to temporary variables and convert types to SMT
     sorts, in particular convert IntRange types to Ints *)
      let var_to_temp_var = 
        List.fold_left 
          (function accum -> function v -> 

             (* Get name of state variable *)
             let sv = 
               StateVar.name_of_state_var
                 (Var.state_var_of_state_var_instance v)
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

             (* Add pair of variable and temporary variable
                to association list *)
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
            with Not_found -> smtexpr_of_var declare v)

         (* Change divisibility symbol to modulus operator *)
         | t -> Term.divisible_to_mod (Term.nums_to_pos_nums t)

      )


      term
  in

  (* Return if list of variables is empty *)
  if vars = [] then term' else

    (* Quantify all variables *)
    (if quantifier then Term.mk_exists else Term.mk_forall)
      (List.map snd var_to_temp_var)
      term'


  (* Convert an expression from the SMT solver to a term *)
  let smtexpr_of_term declare term = 
  quantified_smtexpr_of_term declare false [] term

    (* Pretty-print a custom argument *)
    let pp_print_custom_arg ppf = function 
    | ArgString s -> Format.pp_print_string ppf s
    | ArgExpr e -> pp_print_expr ppf e
                     

    (* Return a string representation of a custom argument *)
    let string_of_custom_arg t = 
      string_of_t pp_print_custom_arg t












end


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
