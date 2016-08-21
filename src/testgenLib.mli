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


type sys = TransSys.t
type svar = StateVar.t
type actlit = UfSymbol.t
type term = Term.t
type model = Model.t
type values = (Term.t * Term.t) list
type k = Numeral.t



(* |===| Helper functions. *)


(** Turns an actlit uf in a term. *)
val term_of: actlit -> term


(** Compares two lists using physical equality. *)
val list_eq: 'a list -> 'a list -> bool



(* |===| Context of a strategy. *)


(** Gathers the contracts, the actions a strategy can perform on the
     underlying smt solver used for test generation, and some data a
     strategy generates tests from. *)
type 'data context = {

  (** System we are generating tests for. *)
  sys: sys ;

  (** Declares a UF. *)
  declare: actlit -> unit ;

  (** Asserts implications between some state variables --actlits-- and some
      terms. Typically:

      function l -> assert(
        and(
          map(l, (fun (sv,t) -> implies(sv,t)))
        )
      ) *)
  actlit_implications: ?eq:bool -> (actlit * term) list -> unit ;

  (** Checksats assuming some activation literals. Returns Some of the
     values of the input terms if sat and None otherwise. *)
  checksat_getvalues: actlit list -> term list -> values option ;

  (** Prints a comment in the trace of the smt solver. *)
  trace_comment: string -> unit ;

  (** Strategy specific data. *)
  mutable data: 'data ;

}


(** Construction helper for [context]. *)
val mk_context:
  'data ->
  (** Transition system we are generating tests for. *)
  sys ->
  (** Declares a UF. *)
  ( actlit -> unit ) ->
  (** Asserts actlit implications function. *)
  ( ?eq:bool -> (actlit * term) list -> unit ) ->
  (** Checksat and get-values function. *)
  ( actlit list -> term list -> values option ) ->
  (** Trace comment function. *)
  ( string -> unit ) ->
  (** Result is a strategy-specific context. *)
  'data context



(* |===| Deconstruction helpers for [context]. *)


(** Calls the [declare] field of a [context] on its input list of actlit / term
    pair. *)
val declare: 'data context -> ( actlit -> unit )

(** Calls the [actlit_implications] field of a [context] on its input list of
    actlit / term pair. *)
val activate:
  'data context -> ( ?eq:bool -> (actlit * term) list -> unit )

(** Calls the [checksat_getvalues] field of a [context] on its input list of
    actlits. *)
val get_values:
  'data context ->
  ( actlit list -> term list -> values option )

(** Calls the [trace_comment] field of a [context] on its input string. *)
val comment: 'data context -> ( string -> unit )



(* |===| Counterexample to inputs csv. *)


(** Converts a model to the system's input values in csv. *)
val cex_to_inputs_csv:
  Format.formatter -> sys -> model -> k -> unit


(** Converts a model to the system's output values in csv. *)
val cex_to_outputs_csv:
  Format.formatter -> sys -> model -> k -> unit



(* |===| Structures and helper functions for testgen strategies. *)


(** A contract test case is a list of numeral / term pairs such that
    - the list is sorted by descending numerals,
    - two succeeding pairs (k2, contracts2) and (k1, contracts1) represent
      the fact that contracts1 hold from k1 to k2 (exclusive), at which point
      contracts2 hold. *)
type contract_testcase = (k * svar list) list

(** A map from actlits to contract test cases. *)
type contract_testcases = (actlit * k * contract_testcase) list


(** Pretty prints a test case. *)
val pp_print_contract_testcase:
  Format.formatter -> contract_testcase -> unit

(** Pretty prints a test case with the name of the modes it triggers. *)
val pp_print_contract_testcase_named:
  sys -> Format.formatter -> contract_testcase -> unit

(** Pretty prints a list of test cases. *)
val pp_print_contract_testcases:
  Format.formatter -> contract_testcases -> unit

(** Pretty prints a list of test cases with the name of the modes they
    trigger. *)
val pp_print_contract_testcases_named:
  sys -> Format.formatter -> contract_testcases -> unit

(** Constructs the text description of a test case. *)
val description_of_contract_testcase:
  sys -> (actlit * k * contract_testcase) -> string list

(** Tree structure to display the tree of activable modes. *)
type tree =
  | Branch of (string list * tree) list
  | Leaf of string list list

(** Pretty printer for the tree structure. *)
val pp_print_tree: Format.formatter -> tree -> unit

(** Converts some test cases to a tree. *)
val testcases_to_tree: sys -> contract_testcases -> tree

(** Constructs the explicit unrolling of a test case. *)
val unroll_test_case:
  contract_testcase -> k -> contract_testcase -> contract_testcase


(** Extends some test cases: creates the new test cases made of the input ones
    extended with one transition to whatever mode they can activate.

    The input is a context, where the data is the tree of activable modes in
    [k] transitions from the initial state. A test case is a path in this tree.
    This function considers each test case and checks which modes it can reach
    in one transition. A new test case is created for each mode each test case
    can reach. *)
val extend_contract_testcases:
  contract_testcases context -> k -> contract_testcases


(** Generates the actual test cases in csv using a [get-model] function.
    Arguments:
    - the directory to write the test case in,
    - a formatter to the xml file aggregating the test cases,
    - the context of the test generation strategy,
    - the [get-model] function. *)
val testcase_gen : string -> string -> (
  string -> string -> string -> string list -> 'a
) -> contract_testcases context -> (
  actlit list -> model option
) -> unit


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
