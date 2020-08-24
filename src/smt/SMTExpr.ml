(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015-2017 by the Board of Trustees of the University of Iowa

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

(* ********************************************************************* *)
(* Conversions from S-expressions to terms                               *)
(* ********************************************************************* *)

module type Conv =
  sig 

    val smtsort_of_type : Type.t -> sort

    val smtexpr_of_var : Var.t -> Term.t list -> t

    val string_of_logic : TermLib.logic -> string 

    val pp_print_logic : Format.formatter -> TermLib.logic -> unit

    val pp_print_sort : Format.formatter -> sort -> unit

    val string_of_sort : sort -> string

    val pp_print_expr : Format.formatter -> t -> unit

    val print_expr : t -> unit

    val string_of_expr : t -> string

    val smtexpr_of_term : t -> t

    val quantified_smtexpr_of_term : bool -> Var.t list -> t -> t

    val var_term_of_smtexpr : t -> t

    val term_of_smtexpr : t -> t

    val pp_print_custom_arg : Format.formatter -> custom_arg -> unit

    val string_of_custom_arg : custom_arg -> string
                                
  end

module Converter ( Driver : SolverDriver.S ) : Conv =
struct

  include Driver

  (* ********************************************************************* *)
  (* Conversions from terms to SMT expressions                             *)
  (* ********************************************************************* *)

  (* Convert a type to an SMT sort : no conversion for yices *)
  let rec smtsort_of_type t = Driver.interpr_type t


  (* Convert a variable to an SMT expression *)
  let smtexpr_of_var var args =

    (* Building the uf application. *)
    Term.mk_uf
      (* Getting the unrolled uf corresponding to the state var
         instance. *)
      (Var.unrolled_uf_of_state_var_instance var)
      (* No arguments. *)
      args


  (* Convert an SMT expression to a variable *)
  let rec var_term_of_smtexpr e = 

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

              (* Retrieve unrolled and constant state vars *)
              Term.mk_var (Var.state_var_instance_of_symbol sym)

            with Not_found ->

              invalid_arg
                (Format.asprintf
                   "var_of_smtexpr: %a\
                    No state variable found for uninterpreted function symbol"
                   Term.pp_print_term e)
          )

        (* An unrolled variable might be an array in which case it would
           show up as an application. *)
        | Term.T.App (uf_sym, args) when Symbol.is_uf uf_sym ->

          (try

             (* Retrieving unrolled and constant state vars. *)
             let v = Var.state_var_instance_of_symbol uf_sym in

             List.fold_left 
               Term.mk_select
               (Term.mk_var v)
               args

           with Not_found ->

             invalid_arg
               (Format.asprintf
                  "var_of_smtexpr: %a\
                   No state variable found for uninterpreted function symbol"
                  Term.pp_print_term e)

          )

        (* Annotated term *)
        (* | Term.T.Attr (t, _) -> var_term_of_smtexpr t *)

        (* Already variables *)
        | Term.T.Var _ -> e
  
        (* Other expressions *)
        | Term.T.App _ -> 

          invalid_arg 
            "var_of_smtexpr: \
             Must be an uninterpreted function"


  (* Convert a term to an expression for the SMT solver *)
  let term_of_smtexpr term =

    Term.map
      (function _ -> function t -> 
         try var_term_of_smtexpr t with Invalid_argument _ -> t)
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
             Var.mk_free_var 
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
              with Not_found -> smtexpr_of_var v [])

           (* (\* Term is a select operation *\) *)
           (* | t when Term.is_select t ->  *)

           (*   (\* Get variable and indexes *\) *)
           (*   let v, i = Term.indexes_and_var_of_select t in *)

           (*   (\* Create uninterpreted function with indexes as *)
           (*      arguments from variable *\) *)
           (*   smtexpr_of_var v i *)

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
  let smtexpr_of_term term = 
    quantified_smtexpr_of_term false [] term

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
