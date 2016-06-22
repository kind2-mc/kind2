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


(* Turns an actlit uf in a term. *)
let term_of = Actlit.term_of_actlit


(* Compares two lists using physical equality. *)
let rec list_eq l1 l2 = match l1, l2 with
  | [], [] -> true
  | h1 :: t1, h2 :: t2 ->
    if h1 != h2 then false else list_eq t1 t2
  | _ -> false



(* |===| Context of a strategy. *)


(* Gathers the contracts, the actions a strategy can perform on the
   underlying smt solver used for test generation, and some data a
   strategy generates tests from. *)
type 'data context = {

  (* System we are generating tests for. *)
  sys : sys ;

  (* Declares a UF. *)
  declare : actlit -> unit ;

  (* Asserts implications between some state variables --actlits--
     and some terms. Typically:
     function l -> assert(
       and(
         map(l, (fun (sv,t) -> implies(sv,t)))
       )
     ) *)
  actlit_implications : ?eq:bool -> (actlit * term) list -> unit ;

  (* Checksats assuming some activation literals. Returns Some of the
     values of the input terms if sat and None otherwise. *)
  checksat_getvalues : actlit list -> term list -> values option ;

  (* Prints a comment in the trace of the smt solver. *)
  trace_comment : string -> unit ;

  (* Strategy specific data. *)
  mutable data : 'data ;

}


(* Construction helper for [context]. *)
let mk_context
  data sys declare actlit_implications checksat_getvalues trace_comment = {
  sys ;
  declare ;
  actlit_implications ;
  checksat_getvalues ;
  trace_comment ;
  data ;
}



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

(* Converts a model to the system's input values in csv. *)
let cex_to_inputs_csv fmt sys cex k = match TransSys.get_source sys with
  | TransSys.Lustre nodes ->
    let path =
      Model.path_from_model (TransSys.state_vars sys) cex k
    in
    Format.fprintf fmt
      "@[<v>%a@]"
      (LustrePath.pp_print_path_inputs_csv nodes true) path
  (* Not supporting non lustre sources. *)
  | _ -> assert false


(* Converts a model to the system's output values in csv. *)
let cex_to_outputs_csv fmt sys cex k = match TransSys.get_source sys with
  | TransSys.Lustre nodes ->
    let path =
      Model.path_from_model (TransSys.state_vars sys) cex k
    in
    Format.fprintf fmt
      "@[<v>%a@]@."
      (LustrePath.pp_print_path_outputs_csv nodes true) path
  (* Not supporting non lustre sources. *)
  | _ -> assert false



(* |===| Structures and helper functions for testgen strategies. *)


(* A contract test case is a list of numeral / term pairs such that
   - the list is sorted by descending numerals,
   - two succeeding pairs (k2, contracts2) and (k1, contracts1) represent
     the fact that contracts1 hold from k1 to k2 (exclusive), at which point
     contracts2 hold. *)
type contract_testcase = (k * svar list) list

(* A map from actlits to contract test cases. *)
type contract_testcases = (actlit * k * contract_testcase) list

(* Pretty prints a test case. *)
let pp_print_contract_testcase fmt testcase =
  Format.fprintf
    fmt
    "@[<v>%a@]"
    (pp_print_list
      ( fun fmt (k,svar_list) ->
        Format.fprintf
          fmt "%3a | %a"
          Numeral.pp_print_numeral k
          (pp_print_list StateVar.pp_print_state_var ", ")
          svar_list )
      "@,")
    testcase

(* Pretty prints a test case with the name of the modes it triggers. *)
let pp_print_contract_testcase_named sys fmt testcase =
  Format.fprintf
    fmt
    "@[<v>%a@]"
    (pp_print_list
      (fun fmt (k,svars) ->
        let names =
          svars |> List.fold_left (fun l svar ->
            match TransSys.mode_names_of_req_svar sys svar with
            | None -> assert false
            | Some l' -> l' @ l
          ) []
        in
        Format.fprintf
          fmt "%3a | %a"
          Numeral.pp_print_numeral k
          (pp_print_list Format.pp_print_string ", ")
          names)
      "@,")
    testcase

(* Pretty prints a list of test cases. *)
let pp_print_contract_testcases fmt testcases =
  Format.fprintf
    fmt
    "%a"
    (pp_print_list
      (fun fmt (actlit, k, testcase) ->
        Format.fprintf
          fmt "(%a) %a | @[<v>%a@]"
          Numeral.pp_print_numeral k
          UfSymbol.pp_print_uf_symbol actlit
          pp_print_contract_testcase testcase)
      "@,")
    testcases

(* Pretty prints a list of test cases with the name of the modes they
   trigger. *)
let pp_print_contract_testcases_named sys fmt testcases =
  Format.fprintf
    fmt
    "%a"
    (pp_print_list
      (fun fmt (actlit, k, testcase) ->
        Format.fprintf
          fmt "length: %a | @[<v>%a@]"
          Numeral.pp_print_numeral k
          (pp_print_contract_testcase_named sys) testcase)
      "@,")
    testcases

(* Constructs the text description of a test case. *)
let description_of_contract_testcase sys (_, k, trace) =
  let names_of = List.fold_left
    ( fun l svar -> match
        TransSys.mode_names_of_req_svar sys svar
      with
      | None -> assert false
      | Some names -> names @ l )
    []
  in
  let pp_names fmt svars =
    Format.fprintf
      fmt "%a"
      (pp_print_list Format.pp_print_string ", ")
      (names_of svars)
  in
  let rec testcase_tail_to_strings res last_k = function
    | [ (k,svars) ] when Numeral.(k = last_k) ->
      ( ( Format.asprintf
            "and at last step (%a), activates %a"
            Numeral.pp_print_numeral k
            pp_names svars )
        :: res )
      |> List.rev
    | (k,svars) :: tail ->
      testcase_tail_to_strings
        ( ( Format.asprintf
              "then at step %a, activates %a"
              Numeral.pp_print_numeral k
              pp_names svars )
          :: res )
        last_k
        tail
    | [] ->
      ( ( Format.asprintf
          "until the last step (%a)" 
          Numeral.pp_print_numeral last_k )
        :: res ) |> List.rev
  in

  match trace |> List.rev with
  | [] -> assert false
  | (head_k, head_svars) :: tail ->
    assert Numeral.(head_k = zero) ;
    ( Format.asprintf
        "initial state: activates %a" pp_names head_svars ) ::
    testcase_tail_to_strings [] k tail

(* Tree structure to display the tree of activable modes. *)
type tree =
  | Branch of (string list * tree) list
  | Leaf of string list list

(* Pretty printer for the tree structure. *)
let rec pp_print_tree_pair ppf = function
  | (key, Leaf []) ->
    Format.fprintf ppf "[%a]" (pp_print_list Format.pp_print_string ", ") key
  | (key, (Branch [ _ ] as value)) ->
    Format.fprintf
      ppf "[%a], %a"
      (pp_print_list Format.pp_print_string ",") key
      pp_print_tree value
  | (key, value) ->
    Format.fprintf
      ppf "@[<v 3>[%a],@,%a@]"
      (pp_print_list Format.pp_print_string ",") key
      pp_print_tree value
and pp_print_tree ppf = function
| Branch map ->
  Format.fprintf
    ppf "%a"
    (pp_print_list pp_print_tree_pair "@,") map
| Leaf [] -> ()
| Leaf l ->
  Format.fprintf
    ppf "%a"
    (pp_print_list
      ( fun ppf l ->
          Format.fprintf
            ppf "[%a]" (pp_print_list Format.pp_print_string ",") l )
      ", ")
    l

(* Converts some test cases to a tree. *)
let testcases_to_tree sys testcases =

  let names_of = List.fold_left
    ( fun l svar -> match
        TransSys.mode_names_of_req_svar sys svar
      with
      | None -> assert false
      | Some names -> names @ l )
    []
  in

  let rec list_unord_eq l1 l2 = match l1,l2 with
    | h1::t1, _::_ ->
      if l2 |> List.mem h1
      then l2 |> List.filter (fun s -> s <> h1) |> list_unord_eq t1
      else false
    | [], [] -> true
    | _ -> false
  in

  let rec update_assoc pref key value = function
    | (key',_) :: tail when list_unord_eq key key' ->
      ( key, value ) :: tail
      |> List.rev_append pref
    | head :: tail -> update_assoc (head :: pref) key value tail
    | [] -> (key, value) :: pref |> List.rev
  in

  let rec insert todo t l = match t,l with

    | Branch map, h::tail ->
      ( try
          let sub_t = map |> List.assoc h in
          insert ( (h, map) :: todo ) sub_t tail
        with Not_found ->
          Branch (update_assoc [] h (Leaf tail) map) |> zip_up todo )

    | Leaf (h1::t1), h2::t2 ->
      if list_unord_eq h1 h2 then
        insert ( (h1, []) :: todo ) (Leaf t1) t2
      else
        Branch [ (h1, Leaf t1) ; (h2, Leaf t2) ] |> zip_up todo

    | Leaf [], _ -> Leaf l

    | _ ->
      Format.printf "List length is %d, tree:@.%a@."
        (List.length l) pp_print_tree t ;
      assert false

  and zip_up todo tree = match todo with
    | [] -> tree
    | (key, map) :: tail ->
      Branch (update_assoc [] key tree map) |> zip_up tail
  in

  testcases
  |> List.fold_left (fun tree (_,_,tc) ->
      (* Format.printf "Inserting@.  %a@.in@.  %a@."
        (pp_print_contract_testcase_named sys) tc
        pp_print_tree tree ;
      let tree = *)
        tc |> List.map (fun (k,svars) -> names_of svars ) |> insert [] tree
      (* in
      Format.printf "Result:@.  %a@." pp_print_tree tree ;
      tree *)
    )
    (Leaf [])

(* Constructs the explicit unrolling of a test case. *)
let rec unroll_test_case pref prev = function
  | ((k,svars) :: tail) as l ->
    if Numeral.(k = prev - one) then
      unroll_test_case ((k,svars) :: pref) k tail
    else (
      let prev = Numeral.(prev - one) in
      unroll_test_case ((prev, svars) :: pref) prev l )
  | [] -> List.rev pref


(* Extends some test cases: creates the new test cases made of the input ones
   extended with one transition to whatever mode they can activate.

   The input is a context, where the data is the tree of activable modes in
   [k] transitions from the initial state. A test case is a path in this tree.
   This function considers each test case and checks which modes it can reach
   in one transition. A new test case is created for each mode each test case
   can reach. *)
let extend_contract_testcases ( {sys ; data} as context ) k =

  (* Basic solver things. *)
  let declare, activate, get_values, comment =
    declare context, activate context, get_values context, comment context
  in

  (* Retrieving the contracts. *)
  let contracts = match TransSys.mode_req_svars sys with
    | None -> assert false
    | Some l -> l |> List.fold_left
      ( fun l svar ->
          if l |> List.exists ( fun (sv,_,_) -> StateVar.equal_state_vars svar sv )
          then l
          else
            let term0 =
              Var.mk_state_var_instance svar Numeral.zero |> Term.mk_var
            in
            let termk = term0 |> Term.bump_state k in
            ( svar, term0, termk ) :: l )
      []
  in
  let contracts_k = contracts |> List.map (fun (_,_,termk) -> termk) in

  let conj_of_contracts l =
    l |> List.map (fun svar ->
      Var.mk_state_var_instance svar k |> Term.mk_var
    ) |> Term.mk_and
  in

  (* Splits [branches] in the list of pairwise distince conjunctions of terms
     activable at the same time as [path_actlit].

     The idea is that [branches] are contracts of a system at the current step
     ([k]), and [path_actlit] activates a trace of contracts from [0] to [k-1].
     The function then returns the lists of branches that can be activated
     simultaneously from that trace at [k]. *)
  let split path_actlit =

    (* Fresh actlit to activate the disjunction of the contracts. *)
    let split_actlit = Actlit.fresh_actlit () in
    Format.asprintf
      "Declaring and constraining split actlit at %a."
      Numeral.pp_print_numeral k
    |> comment ;
    (* Declaring it. *)
    declare split_actlit ;
    (* Constraining it. *)
    activate [ (split_actlit, Term.mk_or contracts_k) ] ;

    (* Extracts all the conjunction of branches it is possible to go to from
       [path_actlit]. *)
    let rec split_branches paths = match
      get_values [ path_actlit ; split_actlit ] contracts_k
    with

      (* Cannot split anymore, returning paths generated. *)
      | None -> paths

      (* Can split. *)
      | Some(values) ->

        (* Filtering contracts evaluating to true. *)
        let active_contracts_svars, active_contracts_terms =
          contracts |> List.fold_left
            ( fun (l_svar, l_k) (svar,term0,termk) ->
              (* Check the value. *)
              if List.assq termk values == Term.t_true
              then svar :: l_svar, termk :: l_k
              else l_svar, l_k )
            ( [], [] )
        in

        (* Should not be empty. *)
        assert (active_contracts_svars <> []) ;

        (* Forbidding this conjunction of branches. *)
        activate [(
          split_actlit,
          Term.mk_and active_contracts_terms |> Term.mk_not
        )] ;

        (* Looping. *)
        active_contracts_svars :: paths |> split_branches

    in

    split_branches []

  in

  (* Test case level version of [split]. *)
  let split_testcase (actlit, old_k, path) =

    assert Numeral.( old_k + one = k ) ;

    (* Getting the new branches activable from this path. *)
    let branches = split actlit in

    (* Creating new test case(s). *)
    match path, branches with

    (* The branch is the one this testcase is already in. *)
    | (_, contracts) :: _, [ contracts' ]
      when list_eq contracts contracts' ->
      comment "Staying in the same contract." ;
      (* No need to constrain the actlit at this step, only one branch is
         possible anyway. *)
      [ actlit, k, path ]

    (* Only one branch, but the contracts are different. *)
    | _, [ contracts' ] ->
      comment "Only one contract can be activated." ;
      (* Keeping actlit and extending path. Only one branch is possible so no
         need to constrain the actlit. *)
      [ actlit, k, (k, contracts') :: path ]

    (* More than one branch. *)
    | path, _ :: _ ->
      (* Need to create one new actlit per branch, activating the same path
         than [actlit] and its own branch. *)
      branches |> List.map (fun contracts ->
        (* Getting a fresh actlit for this branch. *)
        let actlit' = Actlit.fresh_actlit () in
        comment "Declaring branch actlit." ;
        (* Declaring it. *)
        declare actlit' ;
        Format.asprintf
          "Activates the same path as %a."
          UfSymbol.pp_print_uf_symbol actlit
        |> comment ;
        (* It should activate the path so far. *)
        activate [ (actlit', term_of actlit) ] ;
        comment "Plus the following contract(s)." ;
        (* And the contracts it corresponds to at this step. *)
        activate [ (actlit', conj_of_contracts contracts) ] ;

        match path with
        | (_, contracts') :: _ when list_eq contracts' contracts ->
          (* We are actually continuing the same path. *)
          actlit', k, path
        | _ ->
          (* We are activating a new contract. *)
          actlit', k, (k, contracts) :: path
      )
    (* Cannot activate any mode from this path. *)
    | path, [] ->
      Format.asprintf
        "the following path cannot take any more transitions:@,@[<hv>%a@]@,"
        (pp_print_contract_testcase_named sys) path
      |> failwith
  in

  data |> List.fold_left
    ( fun nu_data testcase ->
      List.rev_append
        (split_testcase testcase)
        nu_data )
    []


(* Generates the actual test cases in csv. Also produces a graph of the tree of
   modes. *)
let testcase_gen strat_out_dir dir pp_testcase context get_model =

(*     let testcase_tree =
    context.data |> List.map (fun (act,k,tc) ->
      act, k, (
        unroll_test_case [] Numeral.(k + one) tc |> List.rev
      )
    ) |> testcases_to_tree context.sys
  in

  let stdfmt = Format.formatter_of_out_channel stdout in
  Format.pp_set_margin stdfmt 1000000000 ;
  Format.pp_set_max_indent stdfmt 100000000000 ;

  Format.fprintf
    stdfmt "Reachable contracts:@,@[<v>%a@]@.@."
    pp_print_tree testcase_tree ; *)

  let gv_file_out_name = Format.sprintf "%s/graph.pdf" dir in
  let gv_file_name = Format.sprintf "%s/graph.dot" dir in
  let gv_file =
    Unix.openfile
      gv_file_name [ Unix.O_TRUNC ; Unix.O_WRONLY ; Unix.O_CREAT ] 0o640
  in
  let gv_fmt =
    Unix.out_channel_of_descr gv_file |> Format.formatter_of_out_channel
  in

  Format.fprintf gv_fmt
    "strict digraph mode_graph {@.  \
     @[<v>" ;

  let names_of = List.fold_left
    ( fun l svar -> match
        TransSys.mode_names_of_req_svar context.sys svar
      with
      | None -> assert false
      | Some names -> names @ l )
    []
  in

  context.data |> List.fold_left (fun cpt ( (actlit,k,testcase) as tc) ->
    (* Format.printf "Test case number %d:@." cpt ; *)

    let to_graph testcase =
      let rec loop (kay, svars) = function
      | ((kay', svars') as pair) :: tail ->
        let name = names_of svars |> String.concat "__" in
        if Numeral.(kay = pred kay') then (
          let name' = names_of svars' |> String.concat "__" in
          Format.fprintf gv_fmt
            "  %s__%a -> %s__%a [label = \"%d\"];@,"
            name Numeral.pp_print_numeral kay
            name' Numeral.pp_print_numeral kay' cpt ;
          loop pair tail
        ) else (
          let kay' = Numeral.succ kay in
          Format.fprintf gv_fmt
            "  %s__%a -> %s__%a [label = \"%d\"];@,"
            name Numeral.pp_print_numeral kay
            name Numeral.pp_print_numeral kay' cpt ;
          loop (kay', svars) (pair :: tail)
        )
      | [] ->
        if Numeral.(kay = k) then () else (
          let kay' = Numeral.succ kay in
          let name = names_of svars |> String.concat "__" in
          Format.fprintf gv_fmt
            "  %s__%a -> %s__%a [label = \"%d\"];@,"
            name Numeral.pp_print_numeral kay
            name Numeral.pp_print_numeral kay' cpt ;
          loop (kay', svars) []
        )
      in

      match List.rev testcase with
      | [] -> failwith "empty testcase"
      | head :: tail -> loop head tail
    in

    (* Format.printf "to graph (%a)@." Numeral.pp_print_numeral k; *)
    to_graph testcase ;
    (* Format.printf "done@." ; *)

    let name = Format.sprintf "test_case_%d" cpt in

    let out_file = Format.sprintf "%s/%s.csv" dir name in

    description_of_contract_testcase context.sys tc
    |> pp_testcase (strat_out_dir ^ "/" ^ name ^ ".csv") name "csv" ;

    let file =
      Unix.openfile
        out_file [ Unix.O_TRUNC ; Unix.O_WRONLY ; Unix.O_CREAT ] 0o640
    in

    let out_fmt =
      Unix.out_channel_of_descr file |> Format.formatter_of_out_channel
    in

    ( match get_model [ actlit ] with
      | None -> assert false
      | Some model ->
        (* Format.printf
          "Test case of length %a activating@. @[<v>%a@]@."
          Numeral.pp_print_numeral k
          (pp_print_contract_testcase_named context.sys) testcase ;
        Format.printf "is@." ; *)
        (* Format.printf "Inputs:@." ; *)
        cex_to_inputs_csv out_fmt context.sys model k
        (* Format.printf "Outputs:@." ; *)
        (* cex_to_outputs_csv context.sys model k ; *)
        (* Format.printf "@." ; *) ) ;

    Format.fprintf out_fmt "@?" ;
    Unix.close file ;

    cpt + 1
  ) 0 |> ignore ;

  Format.fprintf gv_fmt "@]@.}@.@.@?" ;

  Unix.close gv_file ;

  (* Creating the graph for the mode tree. *)
  let cmd =
    Format.sprintf "dot -Tpdf %s -o %s" gv_file_name gv_file_out_name
  in

  Format.printf "  Generating graph:@,  > %s@." cmd ;
  ( match Unix.system cmd with
    | Unix.WEXITED 0 ->
      Format.printf "  > done.@."
    | Unix.WEXITED n ->
      Format.printf "  > error (%d).@." n
    | Unix.WSIGNALED n ->
      Format.printf "  > /!\\ killed by signal %d.@." n
    | Unix.WSTOPPED n ->
      Format.printf "  > /!\\ stopped by signal %d.@." n ) ;

(*     let testcase_tree =
    context.data |> List.map (fun (act,k,tc) ->
      act, k, (
        unroll_test_case [] Numeral.(k + one) tc |> List.rev
      )
    ) |> testcases_to_tree context.sys
  in

  let stdfmt = Format.formatter_of_out_channel stdout in
  Format.pp_set_margin stdfmt 1000000000 ;
  Format.pp_set_max_indent stdfmt 100000000000 ;

  Format.fprintf
    stdfmt "Reachable contracts:@,@[<v>%a@]@.@."
    pp_print_tree testcase_tree ; *)

  ()


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
