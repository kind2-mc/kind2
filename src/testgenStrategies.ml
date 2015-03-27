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

module Svar = StateVar
type svar = Svar.t
type actlit = UfSymbol.t
type term = Term.t
type model = Model.t
type values = (Term.t * Term.t) list
type k = Numeral.t
type contract = term





(* Turns an actlit uf in a term. *)
let term_of = Actlit.term_of_actlit



(* Compares two lists using physical equality. *)
let rec list_eq l1 l2 = match l1, l2 with
  | [], [] -> true
  | h1 :: t1, h2 :: t2 ->
    if h1 != h2 then false else list_eq t1 t2
  | _ -> false






(* Gathers the contracts, the actions a strategy can perform on the
   underlying smt solver used for test generation, and some data a
   strategy generates tests from. *)
type 'data context = {

  (* System we are generating tests for. *)
  sys : TransSys.t ;

  (* Declares a UF. *)
  declare : actlit -> unit ;

  (* Asserts implications between some state variables --actlits--
     and some terms. Typically:
     function l -> assert(
       and(
         map(l, (fun (sv,t) -> implies(sv,t)))
       )
     ) *)
  actlit_implications : (actlit * term) list -> unit ;

  (* Checksats assuming some activation literals. Returns Some of the
     values of the input terms if sat and None otherwise. *)
  checksat_getvalues : actlit list -> term list -> values option ;

  (* Prints a comment in the trace of the smt solver. *)
  trace_comment : string -> unit ;

  (* Strategy specific data. *)
  data : 'data ;

}

(* Construction helper for [context]. *)
let mk_context
  data
  sys
  declare
  actlit_implications
  checksat_getvalues
  trace_comment =
{ sys = sys;
  declare = declare ;
  actlit_implications = actlit_implications ;
  checksat_getvalues = checksat_getvalues ;
  trace_comment = trace_comment ;
  data = data ; }



(* |===| Deconstruction helpers for [context]. *)


(* Calls the [declare] field of a [context] on its input list of actlit / term
   pair. *)
let declare { declare } = declare

(* Calls the [actlit_implications] field of a [context] on its input list of
   actlit / term pair. *)
let activate { actlit_implications } = actlit_implications

(* Calls the [checksat_getvalues] field of a [context] on its input list of
   actlits. *)
let get_values { checksat_getvalues } = checksat_getvalues

(* Calls the [trace_comment] field of a [context] on its input string. *)
let comment { trace_comment } = trace_comment




(* |===| Counterexample to inputs csv. *)

let cex_to_inputs_csv sys cex k = match TransSys.get_source sys with
  | TransSys.Lustre nodes ->
    let path =
      Model.path_from_model (TransSys.state_vars sys) cex k
    in
    Format.printf
      "  @[<v>%a@]@."
      (LustrePath.pp_print_path_inputs_csv nodes true) path
  (* Not supporting non lustre sources. *)
  | _ -> assert false


(* Signature for test generation strategies.
   The idea is let the strategy work on the solver ([work] function)
   using the actions on the solver given by an [actions] record.
   Function [work] returns [false] if it is ot done, i.e. the system
   should be unrolled and [work] called again. *)
module type Sig = sig

  (* Type for the data of the strategy. *)
  type data

  (* Prefix which should be unique to a strategy. The supervisor
     should check that no two strategy have the same prefix to avoid
     test-case filename collisions. *)
  val prefix : string

  (* The name of the strategy, used for logging. *)
  val name : string

  (* Returns true if the strategy requires succeeding input tuples
     to be different. *)
  val no_stuttering : bool

  (* Returns true if the strategy requires subsystems to be abstracted. *)
  val abstract_subsystems : bool


  (* Creates a context for this strategy. *)
  val mk_context :
    (* Transition system. *)
    TransSys.t ->
    (* Declares a UF. *)
    ( actlit -> unit ) ->
    (* Asserts actlit implications function. *)
    ( (actlit * term) list -> unit ) ->
    (* Checksat and get-values function. *)
    ( actlit list -> term list -> values option ) ->
    (* Trace comment function. *)
    ( string -> unit ) ->
    (* Result is a strategy-specific context. *)
    data context


  (* Works on the k^th unrolling of the system. Returns [false] if
     the strategy is not done, i.e. its handler should unroll the
     system further and call this function again. *)
  val work : data context -> k -> bool

  (* Generates test cases using a get_model function. *)
  val testcase_gen : data context -> (
    actlit list -> model option
  ) -> unit

end


(* Dummy strategy module. *)
module Dummy : Sig = struct

  let prefix = "dummy"
  let name = "dummy"
  let no_stuttering = false
  let abstract_subsystems = false

  (* No data. *)
  type data = unit

  (* We'll just do nothing for 5 steps. *)
  let five = Numeral.of_int(5)

  (* Passing stuff to the context constructor helper. *)
  let mk_context = mk_context ()

  let last_k = ref Numeral.zero

  (* Dummy work function. *)
  let work context k =
    last_k := k ;
    Numeral.( k >= five )

  let testcase_gen context get_model =
    match get_model [] with
    | None ->
      Format.printf "No test case generated.@."
    | Some(model) ->
      Format.printf
        "Test case:@." ;
      cex_to_inputs_csv context.sys model !last_k


end

(* First class dummy strategy module. *)
let dummy = (module Dummy : Sig)









(* A contract test case is a list of numeral / term pairs such that
   - the list is sorted by descending numerals,
   - two succeeding pairs (k2, contracts2) and (k1, contracts1) represent
     the fact that contracts1 hold from k1 to k2 (exclusive), at which point
     contracts2 hold. *)
type contract_testcase = (k * contract list) list

(* A map from actlits to contract test cases. *)
type contract_testcases = (actlit * contract_testcase) list



(* *)
let extend_contract_testcases ( {sys ; data} as context ) k =

  (* Basic solver things. *)
  let declare, activate, get_values, comment =
    declare context, activate context, get_values context, comment context
  in

  (* Retrieving the contracts. *)
  let contracts = [] in

  let contracts_k = [] in

  (* Splits [branches] in the list of pairwise distince conjunctions of terms
     activable at the same time as [path_actlit].

     The idea is that [branches] are contracts of a system at the current step
     ([k]), and [path_actlit] activates a trace of contracts from [0] to [k-1].
     The function then returns the lists of branches that can be activated
     simultaneously from that trace at [k]. *)
  let split path_actlit branches =

    (* Fresh actlit to activate the disjunction of the branches. *)
    let split_actlit = Actlit.fresh_actlit () in
    (* Declaring it. *)
    declare split_actlit ;
    (* Constraining it. *)
    activate [ (split_actlit, Term.mk_or branches) ] ;

    (* Extracts all the conjunction of branches it is possible to go to from
       [path_actlit]. *)
    let rec split_branches paths = match
      get_values [ path_actlit ; split_actlit ] contracts_k
    with

      (* Cannot split anymore, returning paths generated. *)
      | None -> paths

      (* Can split. *)
      | Some(values) ->

        (* Filtering branches evaluating to true. *)
        let active_branches = branches |> List.filter
          ( fun branche ->
            (* Bump at k. *)
            let branche_k = Term.bump_state k branche in
            (* Check the value. *)
            List.assq branche_k values == Term.t_true )
        in

        (* Should not be empty. *)
        assert (active_branches <> []) ;

        (* Forbidding this conjunction of branches. *)
        activate [(
          split_actlit,
          Term.mk_and active_branches |> Term.mk_not |> Term.bump_state k
        )] ;

        (* Looping. *)
        active_branches :: paths |> split_branches

    in

    split_branches []

  in

  (* Test case level version of [split]. *)
  let split_testcase (actlit, path) =

    (* Getting the new branches activable from this path. *)
    let branches = split actlit contracts in

    (* Creating new test case(s). *)
    match path, branches with

    (* The branch is the one this testcase is already in. *)
    | (_, contracts) :: _, [ contracts' ]
      when list_eq contracts contracts' ->
      (* Not changing anything. *)
      [ actlit, path ]

    (* Only one branch, but the contracts are different. *)
    | _, [ contracts' ] ->
      (* Recycling actlit and extending path. *)
      [ actlit, (k, contracts') :: path ]

    (* More than one branch. *)
    | _, _ ->
      branches
      |> List.map (fun contracts ->
        (* Getting a fresh actlit for this branch. *)
        let actlit' = Actlit.fresh_actlit () in
        (* It should activate the path so far. *)
        activate [ (actlit', term_of actlit) ] ;
        (* New actlit and path pair. *)
        actlit', (k, contracts) :: path
      )
  in

  data |> List.fold_left
    ( fun nu_data testcase ->
      List.rev_append
        (split_testcase testcase)
        nu_data )
    data


(* Generates test cases activating different contracts of a system. *)
module Unit_ModeSwitch : Sig = struct

  let prefix = "unit_mode_switch"
  let name = "[unit] mode switch"

  let no_stuttering = false
  let abstract_subsystems = false

  type data = contract_testcases

  let mk_context =
    (* We start with a fresh actlit for the empty path. *)
    mk_context [ (Actlit.fresh_actlit (), []) ]

  let max_k = Numeral.of_int 10



  let work context k =
    Numeral.( k >= max_k )

  let testcase_gen _ _ = ()

end

(* First class unit mode switch module. *)
let unit_mode_switch = (module Unit_ModeSwitch : Sig)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
