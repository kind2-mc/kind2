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

(* The mutable state of a statistics item. Statistics are domain-local:
   each engine domain updates its own copy of every item, as each engine
   process did when engines were separate processes. *)
type 'a cell =
  { mutable value : 'a;
    mutable temp : 'a }

(* A generic statistics item: a global handle whose mutable state is
   domain-local *)
type 'a item =
  { display : string;
    default : 'a;
    cell : 'a cell Domain.DLS.key }

(* An integer statistics item *)
type int_item = int item

(* A float statistics item *)
type float_item = float item

(* An integer statistics list *)
type int_list_item = int list item

(* A statistics item of a certain type *)
type stat_item =
  | I of int_item
  | F of float_item
  | L of int_list_item

(* An immutable snapshot of the value of a statistics item, taken in
   the domain that owns the values. This is what is sent to the
   supervisor and printed. *)
type 'a snapshot_value =
  { display : string;
    value : 'a }

(* A snapshot of a statistics item of a certain type *)
type snapshot =
  | SI of int snapshot_value
  | SF of float snapshot_value
  | SL of int list snapshot_value

(* Create a statistics item. A domain spawned while values have already
   been recorded starts from a copy of the values of the spawning
   domain, like a forked process would. *)
let empty_item (display : string) (default : 'a) : 'a item =
  { display;
    default;
    cell =
      Domain.DLS.new_key
        ~split_from_parent:(fun (c : 'a cell) ->
          ({ value = c.value; temp = c.temp } : 'a cell))
        (fun () -> ({ value = default; temp = default } : 'a cell)) }

(* The domain-local state of an item *)
let cell_of_item (item : 'a item) : 'a cell = Domain.DLS.get item.cell


(* ********************************************************************** *)
(* Accessors                                                              *)
(* ********************************************************************** *)

(* Set the value of a generic statistics item *)
let set_value value item = (cell_of_item item).value <- value

(* Set an integer statistics item *)
let set = set_value

(* Set a float statistics item *)
let set_float = set_value

(* Set an integer statistics list *)
let set_int_list = set_value

(* Increment an integers statistics item *)
let incr ?(by = 1) item =
  let c = cell_of_item item in
  c.value <- c.value + by

(* Increment the last element of an integers statistics list *)
let incr_last ?(by = 1) item =

  let rec aux =
    function
      | [] -> []
      | [l] -> [l + by]
      | h :: tl -> h :: aux tl
  in

  let c = cell_of_item item in
  c.value <- aux c.value

(*
(* Increment an integers statistics item *)
let incr_float by item =
  let c = cell_of_item item in
  c.value <- c.value +. by
*)

(* Append at the end of an integers statistics list *)
let append elem item =
  let c = cell_of_item item in
  c.value <- c.value @ [elem]

(* Reset the value of a generic statistics item *)
let reset_value item = (cell_of_item item).value <- item.default

(* Reset the value of an integer statistics item *)
let reset item = reset_value item

(* Reset a float statistics item to its initial value *)
let reset_float item = reset_value item

(* Reset an integer list statistics item to its initial value *)
let reset_int_list item = reset_value item

(* Get the value of a generic statistics item *)
let get_value item = (cell_of_item item).value

(* Get the value of an integer statistics item *)
let get item = get_value item

(* Get the value of a float statistics item *)
let get_float item = get_value item

(* Get the value of an integer statistics list *)
let get_int_list item = get_value item

(* Start the timer for the statistics item *)
let start_timer item =

  let c = cell_of_item item in
  c.temp <- (Unix.gettimeofday ()) ;
  c.value <- 0.

(* Record the time since the call to {!start_timer} of this item, stop
   the timer *)
let record_time item =

  let c = cell_of_item item in
  if c.temp > 0. then
    (c.value <- c.value +. (Unix.gettimeofday () -. c.temp);
     c.temp <- 0.)

(* Unpauses a timer previously paused by [record_time]. *)
let unpause_time item =
  (cell_of_item item).temp <- (Unix.gettimeofday ())

(* Record the time since the call to {!start_timer} of this item, do
   not stop the timer *)
let update_time item =

  let c = cell_of_item item in
  if c.temp > 0. then
    (let t = Unix.gettimeofday () in
     c.value <- c.value +. (t -. c.temp);
     c.temp <- t)

(* Time a function call and add to the statistics item *)
let time_fun item f = 

  start_timer item;
  
  let res = f () in

  record_time item;

  res


(* Stop and record all timers *)
let stop_all_timers stats = 

  List.iter 
    (function 
      | F i -> record_time i
      | _ -> ())
    stats


(* ********************************************************************** *)
(* Statistics output                                                      *)
(* ********************************************************************** *)

(* Take a snapshot of the domain-local value of an item *)
let snapshot_of_item = function
  | I item -> SI { display = item.display; value = get_value item }
  | F item -> SF { display = item.display; value = get_value item }
  | L item -> SL { display = item.display; value = get_value item }

(* Take a snapshot of a group of items *)
let snapshot_of_group items = List.map snapshot_of_item items

(* Take a snapshot of titled groups of items, as sent to the
   supervisor *)
let snapshot_of_stats stats =
  List.map (fun (title, items) -> (title, snapshot_of_group items)) stats

(* Width of display name of statistics item *)
let display_width = function
  | SI { display } | SF { display } | SL { display } -> String.length display

(* Maximal Width of display names *)
let max_display_width stats =
  List.fold_left (fun a i -> max (display_width i) a) 1 stats

(* Pretty-print one statistics item *)
let pp_print_item width ppf = function

  | SI { display; value } -> Format.fprintf ppf "%-*s: %d" width display value

  | SF { display; value } -> Format.fprintf ppf "%-*s: %.3f" width display value

  | SL { display; value } ->

    Format.fprintf ppf
      "%-*s: @[<hov>%a@]"
      width
      display
      (Lib.pp_print_list Format.pp_print_int "@ ")
      value


(* Pretty-print a group of snapshots *)
let pp_print_snapshots ppf stats =

  (* Get the maximal display width *)
  let w = max_display_width stats in

  pp_print_list (pp_print_item w) "@," ppf stats


(* Pretty-print a group of statistics items, reading the values of the
   calling domain *)
let pp_print_stats ppf stats =
  pp_print_snapshots ppf (snapshot_of_group stats)


(* Pretty-print one statistics item *)
let pp_print_item_xml ppf = function 

  | SI { display; value } -> 

    Format.fprintf ppf 
      "@[<hv 2><item>@,\
       <name>%s</name>@,\
       <value type=\"int\">%d</value>@;<0 -2>\
       </item>@]" 
      display 
      value

  | SF { display; value } -> 

    Format.fprintf ppf
      "@[<hv 2><item>@,\
       <name>%s</name>@,\
       <value type=\"float\">%.3f</value>@;<0 -2>\
       </item>@]" 
      display 
      value

  | SL { display; value } -> 

    Format.fprintf ppf 
      "@[<hv 2><item>@,\
       <name>%s</name>@,\
       @[<hv 2><valuelist>@,%a@;<0 -2></valuelist>@]@;<0 -2>\
       </item>@]" 
      display 
      (Lib.pp_print_list 
         (function ppf -> Format.fprintf ppf "<value type=\"int\">%d</value>")
         "@,") 
      value

  
(* Pretty-print a group of statistics items in XML *)
let pp_print_snapshots_xml ppf stats = 

  pp_print_list pp_print_item_xml "@," ppf stats


let pp_print_list_attrib pp ppf = function
  | [] -> Format.fprintf ppf " []"
  | lst -> Format.fprintf ppf
    "@,[@[<v 1>@,%a@]@,]" (pp_print_list pp ",@,") lst


(* Pretty-print one statistics item *)
let pp_print_item_json ppf = function

  | SI { display; value } ->

    Format.fprintf ppf
      "{@[<v 1>@,\
        \"name\" : \"%s\",@,\
        \"type\" : \"int\",@,\
        \"value\" : %d\
       @]@,}\
      "
      display value

  | SF { display; value } ->

    Format.fprintf ppf
      "{@[<v 1>@,\
        \"name\" : \"%s\",@,\
        \"type\" : \"float\",@,\
        \"value\" : %.3f\
       @]@,}\
      "
      display value

  | SL { display; value } ->

    let pp_print_value_json ppf value =
      Format.fprintf ppf
        "{@[<v 1>@,\
          \"type\" : \"int\",@,\
          \"value\" : %d\
         @]@,}\
        "
        value
    in

    Format.fprintf ppf
      "{@[<v 1>@,\
        \"name\" : \"%s\",@,\
        \"type\" : \"list\",@,\
        \"valueList\" :%a\
       @]@,}\
      "
      display
      (pp_print_list_attrib pp_print_value_json) value


(* Pretty-print a group of statistics items in JSON *)
let pp_print_snapshots_json ppf stats =

  (pp_print_list_attrib pp_print_item_json ppf) stats


(* ********************************************************************** *)
(* Statistics items                                                       *)
(* ********************************************************************** *)

(* ********** BMC statistics ********** *)

let bmc_k = 
  empty_item "k" 0

let bmc_total_time = 
  empty_item "Total time" 0.

(* Title for BMC statistics *)
let bmc_stats_title = "BMC"

(* All BMC statistics *)
let bmc_stats = 
  [ I bmc_k;
    F bmc_total_time ] 

(* Stop and record all times *)
let bmc_stop_timers () = stop_all_timers bmc_stats

(* Pretty-print BMC statistics items *)
let pp_print_bmc_stats ppf = 

  Format.fprintf ppf "@[<v>@,[%s]@,%a@]"
    bmc_stats_title
    pp_print_stats bmc_stats


(* ********** Inductive step statistics ********** *)

let ind_k = 
  empty_item "k" 0

let ind_compress_equal_mod_input =
  empty_item "Compressed states pairs (equality)" 0

let ind_compress_same_successors =
  empty_item "Compressed states pairs (same successors)" 0

let ind_compress_same_predecessors =
  empty_item "Compressed states pairs (same predecessors)" 0

let ind_restarts = 
  empty_item "Restarts" 0

let ind_lazy_invariants_count = 
  empty_item "Asserted invariants at one state" 0

let ind_lazy_invariants_time = 
  empty_item "Lazy invariants time" 0.

let ind_total_time = 
  empty_item "Total time" 0.

(* Title for inductive step statistics *)
let ind_stats_title = "Inductive step"

(* All inductive step statistics *)
let ind_stats = 
  [ I ind_k;
    I ind_compress_equal_mod_input;
    I ind_compress_same_successors;
    I ind_compress_same_predecessors;
    I ind_restarts;
    I ind_lazy_invariants_count;
    F ind_lazy_invariants_time;
    F ind_total_time ] 

(* Stop and record all times *)
let ind_stop_timers () = stop_all_timers ind_stats

(* Pretty-print inductive step statistics items *)
let pp_print_ind_stats ppf = 

  Format.fprintf ppf "@[<v>@,[%s]@,%a@]"
    ind_stats_title
    pp_print_stats ind_stats


(* ********** IC3 statistics ********** *)

let ic3_k = 
  empty_item "k" 0

let ic3_restarts = 
  empty_item "Restarts" 0

let ic3_frame_sizes = 
  empty_item "Frame sizes" []

let ic3_fwd_propagated = 
  empty_item "Forward propagations" 0

let ic3_fwd_gen_propagated = 
  empty_item "Forward propagations before generalization" 0

let ic3_fwd_subsumed = 
  empty_item "Forward subsumed clauses" 0

let ic3_back_subsumed = 
  empty_item "Backward subsumed clauses" 0

let ic3_inductive_blocking_clauses = 
  empty_item "Inductive blocking clauses" 0

let ic3_fwd_fixpoint = 
  empty_item "Fixpoint at" 0

let ic3_total_time = 
  empty_item "Total time" 0.

let ic3_fwd_prop_time = 
  empty_item "Forward propagation time" 0.

let ic3_strengthen_time = 
  empty_item "Frame strengthening time" 0.

let ic3_generalize_time = 
  empty_item "Generalization time" 0.

let ic3_find_cex_time = 
  empty_item "Counterexample search time" 0.

let ic3_ind_gen_time = 
  empty_item "Inductive generalization time" 0.

let ic3_inductive_check_time = 
  empty_item "Inductiveness check time" 0.

let ic3_activation_literals =
  empty_item "Activation literals" 0

let ic3_stale_activation_literals =
  empty_item "Stale activation literals" 0

(* Title for IC3 statistics *)
let ic3_stats_title = "IC3"

(* All IC3 statistics *)
let ic3_stats = 
  [ I ic3_k; 
    I ic3_restarts;
    L ic3_frame_sizes; 
    I ic3_fwd_propagated; 
    I ic3_fwd_gen_propagated; 
    I ic3_fwd_subsumed; 
    I ic3_back_subsumed; 
    I ic3_fwd_fixpoint; 
    I ic3_inductive_blocking_clauses; 
    I ic3_activation_literals;
    I ic3_stale_activation_literals;
    F ic3_total_time;
    F ic3_fwd_prop_time;
    F ic3_strengthen_time;
    F ic3_generalize_time; 
    F ic3_find_cex_time; 
    F ic3_ind_gen_time; 
    F ic3_inductive_check_time ] 

(* Stop and record all timers *)
let ic3_stop_timers () = stop_all_timers ic3_stats

(* Pretty-print IC3 statistics items *)
let pp_print_ic3_stats ppf = 

  Format.fprintf ppf "@[<v>@,[%s]@,%a@]"
    ic3_stats_title
    pp_print_stats ic3_stats


let ic3ia_refinements =
  empty_item "Refinements per index" []

let ic3ia_refinements_end =
  empty_item "Refinenements per index relative to end" []
             
let ic3ia_num_simulations =
  empty_item "Number of concrete simulations" 0

let ic3ia_interpolation_time =
  empty_item "Total time for interpolation" 0.

let ic3ia_stats_title = "IC3+IA"

  
let ic3ia_stats =
  [ L ic3ia_refinements;
    L ic3ia_refinements_end;
    I ic3ia_num_simulations;
    F ic3ia_interpolation_time;
  ]

let pp_print_ic3ia_stats ppf =

  Format.fprintf ppf "@[<v>@,[%s]@,%a@]"
                 ic3ia_stats_title
                 pp_print_stats ic3ia_stats

(* ********** INVGENOS statistics ********** *)

let invgengraph_os_k = 
  empty_item "k" 0

let invgengraph_os_candidate_term_count = 
  empty_item "Total number of candidate terms" 0

let invgengraph_os_invariant_count =
  empty_item "Total number of (sub)invariants discovered" 0

let invgengraph_os_implication_count =
  empty_item "Number of (sub)invariants which were implications" 0

let invgengraph_os_graph_rewriting_time = 
  empty_item "Graph rewriting time" 0.

let invgengraph_os_total_time = 
  empty_item "Total time" 0.

(* Title for INVGENOS statistics *)
let invgengraph_os_stats_title = "INVGENOS"

(* All INVGENOS statistics *)
let invgengraph_os_stats = 
  [ I invgengraph_os_k ;
    I invgengraph_os_candidate_term_count ;
    I invgengraph_os_invariant_count ;
    I invgengraph_os_implication_count ;
    F invgengraph_os_graph_rewriting_time ;
    F invgengraph_os_total_time ] 

(* Stop and record all timers *)
let invgengraph_os_stop_timers () = stop_all_timers invgengraph_os_stats

(* Pretty-print INVGENOS statistics items *)
let pp_print_invgengraph_os_stats ppf = 

  Format.fprintf ppf "@[<v>@,[%s]@,%a@]"
    invgengraph_os_stats_title
    pp_print_stats invgengraph_os_stats


(* ********** INVGENTS statistics ********** *)

let invgengraph_ts_k = 
  empty_item "k" 0

let invgengraph_ts_candidate_term_count = 
  empty_item "Total number of candidate terms" 0

let invgengraph_ts_invariant_count =
  empty_item "Total number of (sub)invariants discovered" 0

let invgengraph_ts_implication_count =
  empty_item "Number of (sub)invariants which were implications" 0

let invgengraph_ts_graph_rewriting_time = 
  empty_item "Graph rewriting time" 0.

let invgengraph_ts_total_time = 
  empty_item "Total time" 0.

(* Title for INVGENTS statistics *)
let invgengraph_ts_stats_title = "INVGENTS"

(* All INVGENTS statistics *)
let invgengraph_ts_stats = 
  [ I invgengraph_ts_k ;
    I invgengraph_ts_candidate_term_count ;
    I invgengraph_ts_invariant_count ;
    I invgengraph_ts_implication_count ;
    F invgengraph_ts_graph_rewriting_time ;
    F invgengraph_ts_total_time ] 

(* Stop and record all timers *)
let invgengraph_ts_stop_timers () = stop_all_timers invgengraph_ts_stats

(* Pretty-print INVGENTS statistics items *)
let pp_print_invgengraph_ts_stats ppf = 

  Format.fprintf ppf "@[<v>@,[%s]@,%a@]"
    invgengraph_ts_stats_title
    pp_print_stats invgengraph_ts_stats

(* ********** C2I statistics *********** *)
let c2i_str_invs = empty_item "Number of strengthening invariants" 0

let c2i_zero_cost = empty_item "Number of zero-cost candidates" 0

let c2i_moves = empty_item "Number of random moves" 0

let c2i_model_comp_time = empty_item "Time spent comparing models" 0.

let c2i_move_time = empty_item "Time spent moving and evaluating" 0.

let c2i_query_time = empty_item "Time spent querying solvers" 0.

let c2i_total_time = empty_item "Total time" 0.

(* Title for C2I statistics. *)
let c2i_stats_title = "C2I"

(* All C2I statistics. *)
let c2i_stats = [
  I c2i_str_invs ; I c2i_zero_cost ; I c2i_moves ;
  F c2i_move_time ; F c2i_query_time ; F c2i_model_comp_time ;
  F c2i_total_time
]

(* Stop and record all timers. *)
let c2i_stop_timers () = stop_all_timers c2i_stats

(* Pretty-print C2I statistics item. *)
let pp_print_c2i_stats ppf =
  Format.fprintf ppf "@[<v>@,[%s]@,%a@]"
    c2i_stats_title pp_print_stats c2i_stats

(* ********** Testgen statistics ********** *)

(* Number of testcases generated. *)
let testgen_testcases = 
  empty_item "testcases" 0

(* Number of deadlocks found. *)
let testgen_deadlocks = 
  empty_item "deadlocks" 0

(* Number of restarts performed. *)
let testgen_restarts = 
  empty_item "restarts" 0

(* Time spent going forward. *)
let testgen_forward_time = 
  empty_item "forward" 0.

(* Time spent going backward. *)
let testgen_backward_time = 
  empty_item "backward" 0.

(* Time spent enumerating. *)
let testgen_enumerate_time = 
  empty_item "enumerate" 0.

(* Total runtime for testgen. *)
let testgen_total_time = 
  empty_item "Total time" 0.

(* Title for testgen statistics *)
let testgen_stats_title = "TestGen"

(* All testgen statistics *)
let testgen_stats = 
  [ I testgen_testcases ;
    I testgen_deadlocks ;
    I testgen_restarts ;
    F testgen_forward_time ;
    F testgen_backward_time ;
    F testgen_enumerate_time ;
    F testgen_total_time ]

(* Stop and record all times *)
let testgen_stop_timers () = stop_all_timers testgen_stats

(* Pretty-print testgen statistics items *)
let pp_print_testgen_stats ppf = 

  Format.fprintf ppf "@[<v>@,[%s]@,%a@]"
    testgen_stats_title
    pp_print_stats testgen_stats


(* ********** SMT statistics ********** *)

let smt_check_sat_time = 
  empty_item "check-sat time" 0.

let smt_get_value_time = 
  empty_item "get-value time" 0.

let smt_get_unsat_core_time = 
  empty_item "get-unsat-core time" 0.

(* Title for SMT statistics *)
let smt_stats_title = "SMT"

(* All SMT statistics *)
let smt_stats = 
  [ F smt_check_sat_time;
    F smt_get_value_time;
    F smt_get_unsat_core_time ] 

(* Stop and record all times *)
let smt_stop_timers () = stop_all_timers smt_stats

(* Pretty-print SMT statistics items *)
let pp_print_smt_stats ppf = 

  Format.fprintf ppf "@[<v>@,[%s]@,%a@]"
    smt_stats_title
    pp_print_stats smt_stats



(* ********** Certificate statistics ********** *)

let certif_gen_time = 
  empty_item "generation time" 0.

let certif_min_time = 
  empty_item "minimization time" 0.

let certif_frontend_time = 
  empty_item "frontend time" 0.

let certif_slice_time =
  empty_item "slicing time" 0.

let certif_cvc5_time = 
  empty_item "cvc5 proof-gen time" 0.

let certif_k =
  empty_item "k" (-1)

let certif_size = 
  empty_item "size" 0

let certif_old_k =
  empty_item "Old k" (-1)

let certif_old_size = 
  empty_item "Old size" 0

(* Title for Certificate statistics *)
let certif_stats_title = "Certificate"

(* All SMT statistics *)
let certif_stats = 
  [ F certif_gen_time;
    F certif_min_time;
    F certif_frontend_time;
    I certif_k;
    I certif_size;
    I certif_old_k;
    I certif_old_size;
    F certif_cvc5_time;
  ] 

(* Stop and record all times *)
let certif_stop_timers () = stop_all_timers certif_stats

(* Pretty-print SMT statistics items *)
let pp_print_certif_stats ppf = 

  Format.fprintf ppf "@[<v>@,[%s]@,%a@]"
    certif_stats_title
    pp_print_stats certif_stats



(* ********** Misc statistics ********** *)

let total_time = 
  empty_item "Total time" 0.

let analysis_time =
  empty_item "Analysis time" 0.

let clause_of_term_time =
  empty_item "clause_of_term time" 0.

let smtexpr_of_term_time =
  empty_item "smtexpr_of_term time" 0.

let term_of_smtexpr_time =
  empty_item "term_of_smtexpr time" 0.

let misc_stats_title = "General"

let misc_stats =
  [ F total_time;
    F analysis_time;
    F clause_of_term_time;
    F smtexpr_of_term_time; 
    F term_of_smtexpr_time ]

(* Stop and record all times *)
let misc_stop_timers () = stop_all_timers misc_stats

(* Pretty-print misc statistics items *)
let pp_print_misc_stats ppf = 

  Format.fprintf ppf "@[<v>%a@]"
    pp_print_stats misc_stats

let remaining_timeout () =
  let elapsed = get_float total_time in
  if Flags.timeout_wall () < elapsed then 0.
  else Flags.timeout_wall () -. elapsed

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

