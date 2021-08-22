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


(* TODO:
  - not sure the way to deal with partial models is fine in [model_equal].
  - don't [failwith] when [white \cap black \not = \emptyset].
  - communicate non-strengthening invariants (when no black models).
*)



(*

Implementation of
@incollection{
  year={2014},
  isbn={978-3-319-08866-2},
  booktitle={Computer Aided Verification},
  volume={8559},
  series={Lecture Notes in Computer Science},
  editor={Biere, Armin and Bloem, Roderick},
  doi={10.1007/978-3-319-08867-9_6},
  title={
    From Invariant Checking to Invariant Inference Using Randomized Search
  },
  url={http://dx.doi.org/10.1007/978-3-319-08867-9_6},
  publisher={Springer International Publishing},
  author={Sharma, Rahul and Aiken, Alex},
  pages={88-105},
  language={English}
}


The idea of the approach follows. Let (Init, Trans) be the init and transition
predicates of the transition system. Assume there's only one property to prove,
P. Let Inv be the set of strengthening, (0-)inductive invariants for P, i.e.
              | Init \land \neg I is unsat       (1)
I \in Inv <=> | I \land \neg P is unsat          (2)
              | I \land T \land \neg I' is unsat (3)

The algorithm consists in finding one such I by starting from some candidate
C_0 and minimizing a cost function c over a series of C_i's.

The algorithm is a loop iterating on
* the current candidate C_i,
* a set of "white" (good) states W,
* a set of "grey" pairs of states G, and
* a set of "black" (bad) states B.

Function c returns costs >= 0 and does not query a solver to compute a cost. If
c(C) = 0, then C is "close enough" to being an invariant and a solver is used
to query (1), (2) and (3). If all are unsat then a strengthening invariant has
been found.
In practice (2) is changed to "I \land T \land \neg P' is unsat". Thus when we
find a strengthening invariant I we don't set the property as invariant, but
instead simply communicate I and let k-induction do the work. The reason is
that there might be a problem with the initial state, i.e. Init \land \neg P
is sat.

If (1) is sat we have an initial state and add it to W, since it is a white
state. If (2) is sat we have a black state (falsifying P) and add it to B. If
(3) is sat, we have pair of (grey) states and add it to G.

The cost function returns a cost inversely proportional to "how well" a
candidate C verifies the following constraints:
c1: it should separate the white states from the black ones:
    \forall w \in W, \forall b \in B, \neg (C(w) <=> C(b))
c2: it should contain the white states:
    \forall w \in W, C(w)
c3: it should exclude the black states:
    \forall b \in B, \neg C(b)
c4: it should satisfy all pairs:
    \forall (s,s') \in G, C(s) => C(s')
Note that c2 \land c3 => c1. We keep c1 however so that the cost function is
better in its ranking of the candidates.
Note also that weight can be assigned to the constraints, we omit this for now.

Interpreting "true" as 1 and "false" as 0, the cost function is
c(C) = (
  \sigma_{(w,b) \in (W,B)}
    (\neg C(w)) * (\neg C(b)) + C(w) * C(b)
) + (
  \sigma_{w \in W}
    \neg C(w)
) + (
  \sigma_{b \in B}
    C(b)
) + (
  \sigma_{(s,s') \in G}
    C(s) * (\neg C(s'))
)

It is possible to enforce a somewhat IC3-ish behavior by doing the following.
Say c(C) = 0, we check the satisfiability of (1), (2) and (3). Assume (3) is
sat, we get a pair of states (s,s'). Now, it can the case that
* s \in W, so s' is a successor of a white state, meaning we can add it to W.
* s' \in B, so s is a predecessor of a black state, and we can add it to B.
If both cases apply, then P is invalid.

*)

open Lib
open Actlit

module Candidate = C2ICandidate

(* Output statistics *)
let print_stats () = KEvent.stat [
  Stat.misc_stats_title, Stat.misc_stats ;
  Stat.c2i_stats_title, Stat.c2i_stats ;
  Stat.smt_stats_title, Stat.smt_stats
]

let stop () =
  (* Stop all timers. *)
  Stat.c2i_stop_timers ()

let on_exit _ =
  stop () ;
  (* Output statistics. *)
  print_stats ()


type context = {
  sys: TransSys.t ;
  prop: string ;
  mutable white: Model.t list ;
  mutable grey: (Model.t * Model.t) list ;
  mutable black: Model.t list ;
  solver1: SMTSolver.t ;
  solver2: SMTSolver.t ;
  solver3: SMTSolver.t ;
  mutable k: int;
}

(* Creates two solvers for the context. Initializes them and updates the
   solver references (deletes the previous solvers. *)
let mk_solvers sys =
  (* Destroy all existing solvers. *)
  let solver1 =
    SMTSolver.create_instance
      ~produce_assignments:true
      (TransSys.get_logic sys) (Flags.Smt.solver ())
  in

  let solver2 =
    SMTSolver.create_instance
      ~produce_assignments:true
      (TransSys.get_logic sys) (Flags.Smt.solver ())
  in

  let solver3 =
    SMTSolver.create_instance
      ~produce_assignments:true
      (TransSys.get_logic sys) (Flags.Smt.solver ())
  in

  (* Defining uf's and declaring variables. *)
  TransSys.define_and_declare_of_bounds
    sys
    (SMTSolver.define_fun solver1)
    (SMTSolver.declare_fun solver1)
    (SMTSolver.declare_sort solver1)
    Numeral.zero Numeral.zero ;

  (* Defining uf's and declaring variables. *)
  TransSys.define_and_declare_of_bounds
    sys
    (SMTSolver.define_fun solver2)
    (SMTSolver.declare_fun solver2)
    (SMTSolver.declare_sort solver2)
    Numeral.zero Numeral.one ;

  (* Defining uf's and declaring variables. *)
  TransSys.define_and_declare_of_bounds
    sys
    (SMTSolver.define_fun solver3)
    (SMTSolver.declare_fun solver3)
    (SMTSolver.declare_sort solver3)
    Numeral.zero Numeral.one ;

  (* Asserting init in [solver1]. *)
  TransSys.init_of_bound (Some (SMTSolver.declare_fun solver1)) sys Numeral.zero
  |> SMTSolver.assert_term solver1 ;

  (* Asserting trans in [solver2]. *)
  TransSys.trans_of_bound (Some (SMTSolver.declare_fun solver2)) sys Numeral.one
  |> SMTSolver.assert_term solver2 ;

  (* Asserting trans in [solver3]. *)
  TransSys.trans_of_bound (Some (SMTSolver.declare_fun solver3)) sys Numeral.one
  |> SMTSolver.assert_term solver3 ;

  (* Retrieving invariants @0. *)
  let invs0 = TransSys.invars_of_bound sys Numeral.zero in
  (* Asserting in all solvers. *)
  invs0 |> Term.mk_and |> SMTSolver.assert_term solver1 ;
  invs0 |> Term.mk_and |> SMTSolver.assert_term solver2 ;
  invs0 |> Term.mk_and |> SMTSolver.assert_term solver3 ;
  (* Retrieving invariant @1. *)
  let invs1 = TransSys.invars_of_bound sys Numeral.one in
  (* Asserting invariants @1 in 2 and 3. *)
  invs1 |> Term.mk_and |> SMTSolver.assert_term solver2 ;
  invs1 |> Term.mk_and |> SMTSolver.assert_term solver3 ;

  solver1, solver2, solver3

(* Initializes the solvers, creates the context. *)
let mk_context sys prop =
  let solver1, solver2, solver3 = mk_solvers sys in
  { sys ; prop ;
    k = 1;
    white = [] ; grey = [] ; black = [] ;
    solver1 ; solver2 ; solver3 }


(* Resets a context with a new prop. Changes [prop] and resets [black]. *)
let reset_prop_of context prop =
  { context with prop = prop; black = [] }

(* Resets the grey sets of a context. *)
let reset_grey_of context = { context with grey = [] }

(* Resets the solvers of a context every 20 checks. *)
let reset_solvers_of ({ sys } as context) =
  if (Actlit.fresh_actlit_count () / 3) mod 10 = 0 then (
    (* Reset solvers. *)
    let solver1, solver2, solver3 = mk_solvers sys in
    (* Reset actlits. *)
    Actlit.reset_fresh_actlit_count () ;
    { context with solver1 ; solver2 ; solver3 }
  ) else context

(* Variable hash table. *)
module VHT = Var.VarHashtbl

(* Offset of a variable. *)
let offset_of = Var.offset_of_state_var_instance
(* Sets the offset of a variable. *)
let set_offset = Var.set_offset_of_state_var_instance
(* Returns true iff a variable is a constant. *)
let is_const = Var.is_const_state_var
(* Creates a _non randomized_ variable hash table. They need to be
   deterministic for equality of models. *)
let mk_vht = VHT.create (* ~random:false *)
(* Adds a binding to a variable hash table. *)
let vht_add = VHT.add

(* Iterates over a model M for variables at 0 and possibly at 1.
   Returns two models (hashtables): one containing the bindings for the
   variables @0 in M, and one containing the bindings for the variables @1 in M
   with the offset of these variables changed to 0.

   Argument [n] is the capacity new hash tables are created with. Should be the
   number of state variables in the system. *)
let model_split n model =
  (* Creating result hash tables. *)
  let m0, m1 = mk_vht n, mk_vht n in
  (* Time for side-effects. Would be better to iterate backwards so that
     insertion is O(1), but I don't know how to do that. *)
  model
  |> VHT.iter (fun var va1 ->
    if is_const var then (
      vht_add m0 var va1 ;
      vht_add m1 var va1 ;
    ) else match offset_of var |> Numeral.to_int with
    | -1 ->
      (* Ignoring that. *)
      ()
    | 0 -> vht_add m0 var va1
    | 1 -> let var = set_offset var Numeral.zero in vht_add m1 var va1
    | n -> Format.sprintf "unexpected offset of variable %d > 1" n |> failwith
  ) ;
  (* Returning hash tables. *)
  m0, m1

(* Exception thrown inside [model_equal], if they're not equal. This allows to
   break the iteration on the bindings asap. *)
exception Not_equal

(* Checks if two models are equal. *)
let model_equal m1 m2 =
  try
    m1 |> VHT.iter (fun var va1 ->
      try
        if (VHT.find m2 var) == va1 then () else raise Not_equal
      with Not_found -> raise Not_equal
        (* Format.printf "m1 = @[<hv>%a@]@." Model.pp_print_model m1 ;
        Format.printf "m2 = @[<hv>%a@]@." Model.pp_print_model m2 ;
        Format.asprintf
          "could not find variable %a in rhs model" Var.pp_print_var var
        |> failwith *)
    ) ;
    true
  with Not_equal -> false

(* Checks if a model is in a list of models. *)
let contains model models =
  try
    List.find (model_equal model) models |> ignore ;
    true
  with Not_found -> false


(* Asserts a new invariant in both solvers of the context. *)
let assert_invariant { solver1 ; solver2 } (inv, is_one_state) =
  (* Asserting invariant @0 in both solvers. *)
  if is_one_state then (
    SMTSolver.assert_term solver1 inv ;
    SMTSolver.assert_term solver2 inv
  ) ;
  (* Asserting invariant @1 in [solver2]. *)
  Term.bump_state Numeral.one inv |> SMTSolver.assert_term solver2

(* Asserts new invariants in both solvers of the context. *)
let assert_invariants { solver1 ; solver2 } invs =
  Unroller.assert_new_invs_to solver1 Numeral.one invs ;
  Unroller.assert_new_invs_to solver2 Numeral.(succ one) invs


(* Check-sat with assumption, returns [Some] of the model if sat, [None]
   otherwise. *)
let get_model_option solver =
  SMTSolver.check_sat_assuming
    solver
    (fun s ->
      (* KEvent.log L_info "C2I Getting model" ; *)
      Some (SMTSolver.get_model s) )
    (fun _ -> None)

(* Checks (1), (2) and (3) for a candidate invariant. Returns a triple of
   [Model option]. *)
let query_solvers { sys ; prop ; solver1 ; solver2 ; solver3 } candidate =

  Stat.start_timer Stat.c2i_query_time ;

  (* Getting actlit for this candidate. *)
  let actlit_uf = fresh_actlit () in
  (* Getting its term. *)
  let actlit = term_of_actlit actlit_uf in

  (* KEvent.log L_info "C2I Checking 1)." ; *)
  (* Checking (1). *)
  SMTSolver.declare_fun solver1 actlit_uf ;
  (* Can the candidate be false in the initial state? *)
  Term.mk_implies [ actlit ; candidate |> Term.mk_not ]
  |> SMTSolver.assert_term solver1 ;
  let model_opt_1 = get_model_option solver1 [ actlit ] in

  (* KEvent.log L_info "C2I Checking 2)." ; *)
  (* Checking (2). Reusing same actlit as solver is different. *)
  SMTSolver.declare_fun solver2 actlit_uf ;
  (* Does the candidate imply the property after a transition? *)
  Term.mk_implies [ actlit ;
    Term.mk_and [
      candidate ;
      TransSys.get_prop_term sys prop
      |> Term.bump_state Numeral.one |> Term.mk_not
    ]
  ] |> SMTSolver.assert_term solver2 ;
  let model_opt_2 = get_model_option solver2 [ actlit ] in

  (* KEvent.log L_info "C2I Checking 3)." ; *)
  (* Checking (3). Reusing same actlit as solver is different. *)
  SMTSolver.declare_fun solver3 actlit_uf ;
  (* Is the candidate inductive? *)
  Term.mk_implies [ actlit ;
    Term.mk_and [
      candidate ; candidate |> Term.bump_state Numeral.one |> Term.mk_not
    ]
  ] |> SMTSolver.assert_term solver3 ;
  let model_opt_3 = get_model_option solver3 [ actlit ] in

  (* Deactivating actlit. *)
  let nactlit = Term.mk_not actlit in
  SMTSolver.assert_term solver1 nactlit ;
  SMTSolver.assert_term solver2 nactlit ;
  SMTSolver.assert_term solver3 nactlit ;

  Stat.record_time Stat.c2i_query_time ;

  model_opt_1, model_opt_2, model_opt_3


(* Exception thrown when [white \cap black \not = \emptyset]. *)
exception PropIsFalse

(* Updates the white, grey and black lists. *)
let update_colors ({white ; grey ; black} as t) (check1, check2, check3) =
  Debug.c2i "Updating colors";
  let white = match check1 with
    | None -> white
    | Some m ->
      Debug.c2i "| white";
      (model_split 0 m |> fst) :: white
  in
  let black = match check2 with
    | None -> black
    | Some m ->
      Debug.c2i "| black";
      (model_split 0 m |> fst) :: black
  in
  let white, grey, black = 
    match check3 with
    | None -> white, grey, black
    | Some m ->
      (* First, split m. *)
      Debug.c2i "| grey";
      (* TODO: change the [0] in the number of state variables. *)
      let m, m' = model_split 0 m in

      match contains m white, contains m' black with
      | true, false ->
        Debug.c2i " \\ to white";
        (* [m] is white, so is [m']. *)
        m' :: white, grey, black
      | false, true ->
        Debug.c2i " \\ to black";
        (* [m'] is black, so is [m]. *)
        white, grey, m :: black
      | false, false ->
        Debug.c2i " \\ to grey";
        (* None of the above, adding to grey. *)
        white, (m,m') :: grey, black
      | true, true ->
        Debug.c2i " \\ invalid";
        (* Property is invalid. *)
        raise PropIsFalse
  in
  t.white <- white ;
  t.grey <- grey ;
  t.black <- black ;

  ()

(* Gamma constant, used to set the probability with which a candidate with
   higher cost is still kept. *)
let gamma = log 2.0

(* Returns a candidate with a cost of zero. *)
let zero_cost_candidate {white ; grey ; black} candidate =
  Debug.c2i "\
        |=====| generating zero cost candidate (%d white, %d grey, %d black)\
      " (List.length white) (List.length grey) (List.length black);

  let rec loop rated_candidate =
    Debug.c2i "|===| loop (%d white, %d grey, %d black)"
        (List.length white) (List.length grey) (List.length black);
    Debug.c2i "candidate: @[<v>%a@]"
        Term.pp_print_term (
          Candidate.candidate_of_rated rated_candidate |> Candidate.term_of
        );
    KEvent.check_termination () ;
    let cost = Candidate.cost_of_rated rated_candidate in
    (* If zero we're done. *)
    if cost = 0 then
      Candidate.candidate_of_rated rated_candidate
    else (
      (* Check for termination. *)
      KEvent.check_termination () ;
      (* Otherwise, make a move. *)
      let candidate = Candidate.rated_move rated_candidate in
      Stat.incr Stat.c2i_moves ;
      
      Debug.c2i
        "new candidate: @[<v>%a@]"
          Term.pp_print_term (Candidate.term_of candidate);
      (* Get its cost. *)
      let rated_candidate' =
        Candidate.rated_cost_function candidate white grey black
      in

      let cost' = Candidate.cost_of_rated rated_candidate' in

      (* Keeping [candidate'] if *)
      if
        (* its cost is lower. *)
        (cost' < cost) ||
        (* or some random thing from the paper. *)
        ( exp (-. gamma *. ( float_of_int (
          cost' - cost
        ) ))
          > (Random.float max_float) /. max_float )
      then (
        (* KEvent.log L_info
          "C2I   | new cost %d" cost' ; *)
        loop rated_candidate'
      (* Otherwise keep the previous one. *)
      ) else (
        (* KEvent.log L_info
          "C2I   | skipping cost %d@." cost' ; *)
        loop rated_candidate
      )
    )
  in

  (* Getting cost of initial candidate. *)
  let rated_candidate = 
    Candidate.rated_cost_function candidate white grey black
  in
  Debug.c2i
    "| initial cost %d@." (Candidate.cost_of_rated rated_candidate);
  (* Loop. *)
  loop rated_candidate


(* Gets a 0-cost candidate and then queries the solvers.
   Returns a strengthening invariant as a term. *)
let rec loop in_sys param ({sys} as context) candidate =

  Stat.update_time Stat.c2i_total_time ;

  (* KEvent.log L_info "C2I Getting zero cost candidate" ; *)
  (* Getting zero cost candidate. *)
  Stat.start_timer Stat.c2i_move_time ;
  let candidate = zero_cost_candidate context candidate in
  Stat.record_time Stat.c2i_move_time ;
  Stat.incr Stat.c2i_zero_cost ;
  (* Extracting term. *)
  let term = Candidate.term_of candidate in
  (* Format.printf "@.  Candidate @[<hv>%a@]@." Term.pp_print_term term ; *)
  (* KEvent.log L_info
    "C2I @[<v>Found zero-cost candidate, querying solvers context:@ \
                @[<hv>white: %d,@ black: %d,@ grey: %d@]@]"
    (List.length context.white)
    (List.length context.black)
    (List.length context.grey) ; *)

  (* KEvent.log L_info
    "C2I %d actlits so far"
    (Actlit.fresh_actlit_count ()) ; *)

  (* KEvent.log L_info "C2I Found zero-cost candidate." ; *)

  let models = query_solvers context term in
  let context = reset_solvers_of context in

  (* Checking if candidate is a strengthening invariant. *)
  match models with

  | None, None, None ->
    (* Found a strengthening invariant. *)
    Some term

  | models ->

    (* Checking if the current candidate is an invariant. *)
    ( match models with
      | None, _, None ->
        (* It is, communicating. *)
        KEvent.log L_info "C2I Candidate is invariant (non-strengthening)" ;
        (* k-inductive certificate from context *)
        let cert = context.k, term in
        let term =
          TransSys.add_invariant context.sys term cert false
        in
        assert_invariant context (term, false) ;
        (* Broadcasting invariant. *)
        KEvent.invariant (
          TransSys.scope_of_trans_sys context.sys
        ) term cert false ;
      | _ -> () ) ;

    (* Counterexample, updating context. *)
    Stat.start_timer Stat.c2i_model_comp_time ;
    update_colors context models ;
    Stat.record_time Stat.c2i_model_comp_time ;
    (* Format.printf "@." ; *)

    (* Communicating. *)
    let new_invs, is_done =
      KEvent.recv ()
      |> KEvent.update_trans_sys in_sys param sys
      |> fun (invs,props) ->
        invs,
        props |> List.exists (function
          | _, (name, Property.PropInvariant _)
          | _, (name, Property.PropFalse _) ->
            name = context.prop
          | _ -> false
        )
    in
    (* Asserting invariants if any. *)
    assert_invariants context new_invs ;
    let rcved_new_invs =
      ( new_invs |> fst |> Term.TermSet.is_empty |> not ) ||
      ( new_invs |> snd |> Term.TermSet.is_empty |> not )
    in
    let context = if rcved_new_invs then reset_grey_of context else context in
    (* increasing k *)
    context.k <- context.k + 1;
    (* If done, return [None]. *)
    if is_done then None
    (* Looping. *)
    else loop in_sys param context candidate

(* Runs invariant hunting on each property of a list of ([string *
   prop_status]). *)
let rec run in_sys param context_option candidate sys =
  match TransSys.get_split_properties sys with
  (* No more properties, done. *)
  | _, _, [] -> ()

  | _, _, prop :: _ -> ( match Property.get_prop_status prop with
    | Property.PropInvariant _ | Property.PropFalse _ ->
      (* We don't care about this one .*)
      run in_sys param context_option candidate sys

    | _ ->
      let prop = prop.Property.prop_name in
      (* Check for termination. *)
      KEvent.check_termination () ;
      (* Let's do this. *)
      KEvent.log L_info "C2I @[<v>Running on property %s@]" prop ;
      (* New context. *)
      let context = match context_option with
        | None -> mk_context sys prop
        | Some context ->
          reset_prop_of context prop |> reset_grey_of
      in
      let candidate = Candidate.reset candidate in
      (* Let's do random stuff now. *)
      ( try
        ( match loop in_sys param context candidate with
          | Some str_inv ->
            KEvent.log L_info
              "C2I @[<v>Strengthening invariant found for %s@]" prop ;
            Stat.incr Stat.c2i_str_invs ;
            let cert = context.k, str_inv in
            let str_inv =
              TransSys.add_invariant context.sys str_inv cert false
            in
            assert_invariant context (str_inv, false) ;
            (* Broadcasting strengthening invariant. *)
            KEvent.invariant (
              TransSys.scope_of_trans_sys context.sys
            ) str_inv cert false ;

            (* Communicating. *)
            let new_invs, _ (* is_done *) =
              KEvent.recv ()
              |> KEvent.update_trans_sys in_sys param sys
              |> fun (invs,props) ->
                invs,
                props |> List.exists (function
                  | _, (name, Property.PropInvariant _)
                  | _, (name, Property.PropFalse _) ->
                    name = context.prop
                  | _ -> false
                )
            in
            (* Asserting invariants if any. *)
            assert_invariants context new_invs ;

            (* Updating local system. *)
            ( match TransSys.get_prop_status context.sys context.prop with
              | Property.PropUnknown -> ()
              | _ ->
                TransSys.set_prop_invariant context.sys context.prop cert (* TODO check*);
                TransSys.get_prop_term context.sys context.prop
                |> fun t ->
                  (TransSys.add_invariant context.sys t cert false, false)
                  |> assert_invariant context
            )
          | None ->
            (* Proved or disproved by another technique, or termination was
               requested. *)
            if TransSys.is_proved sys prop then
              KEvent.log L_info
                "C2I %s proved by another technique"
                prop
            else if TransSys.is_disproved sys prop then
              KEvent.log L_info
                "C2I %s disproved by another technique"
                prop ) ;
      with PropIsFalse ->
        KEvent.log L_info "C2I @[<v>Falsification for %s detected@]" prop ) ;
      (* Looping. *)
      run in_sys param (Some context) candidate sys
    )

(* Entry point. *)
let main input_sys aparam sys =

  (* Start timers. *)
  Stat.start_timer Stat.c2i_total_time ;
  (* New candidate. *)
  let candidate = Candidate.mk sys in

  (* Format.printf "|===| candidate:@.@." ; *)

  (* Candidate.terms_of candidate |> List.iter (fun disj ->
    Format.printf "\\/ | @[<v>%a@]@.@."
      (pp_print_list
        (fun fmt t -> Format.fprintf fmt "@[<h>%a@]" Term.pp_print_term t)
        "@ ")
      disj
  ) ; *)

  (* Running. *)
  run input_sys aparam None candidate sys ;

  (* Done. *)
  stop ()





(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
