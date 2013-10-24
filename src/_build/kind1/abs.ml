(*
This file is part of the Kind verifier

* Copyright (c) 2007-2009 by the Board of Trustees of the University of Iowa, 
* hereafter designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(* Abstraction refinement strategies *)
open Types
open Exceptions
open Globals
open Lus_convert


(* note: we must refine state variables in the step case if they are
refined in the base case!  If not, path compression may falsely claim
the step case valid! *)

let toss x = () (* toss outputs *)


let refined_step_as_well = ref []

let get_refined_step_as_well () = !refined_step_as_well

let set_refined id defline index abstr_val =
  if !OldFlags.only_1_abstraction then
    begin
      defline.abstr.(base_abstr) <- abstr_val;
      defline.abstr.(step_abstr) <- abstr_val
    end
  else 
    begin
      defline.abstr.(index) <- abstr_val;
      if !OldFlags.loopfree_mode && Tables.var_is_stateful id &&
        defline.abstr.(step_abstr) = NOT_REFINED
      then
        begin
          refined_step_as_well := id::!refined_step_as_well;
          defline.abstr.(step_abstr) <- abstr_val
        end
    end

let rec get_def_score id =
  try 
    match Deftable.get_def id "get_def:get_def_score" with
        DEF_REF y -> get_def_score y
      | DEF_STR y -> y.score
  with IdNotFound x -> (* this should be safe *)
    0

(* do this to a list of unsat cores *)
let set_def_score x n = 
  try
    match Deftable.get_def x "get_def:set_def_score" with
        DEF_REF y -> ()
      | DEF_STR y -> y.score <- n
  with IdNotFound x -> ()(* this should be safe *)

(* do this to a list of unsat cores *)
let incr_def_score x = 
  try
    match Deftable.get_def x "get_def:incr_def_score" with
        DEF_REF y -> ()
      | DEF_STR y -> y.score <- y.score + 1
  with IdNotFound x -> ()(* this should be safe *)

let rec get_deplist x = 
  try
    match Deftable.get_def x "get_def:get_deplist" with
        DEF_REF y -> get_deplist y
      | DEF_STR z -> z.deps
  with IdNotFound x -> [](* this should be safe *)

let compare_defs x y =  compare (get_def_score x) (get_def_score y)
let rev_compare_defs x y =  -(compare (get_def_score x) (get_def_score y))

let compare_ids_by_score (x,_) (y,_) = compare_defs x y


let rec def_sort neg_polarity idlist = 
  if neg_polarity then
    List.stable_sort rev_compare_defs idlist
  else
    List.stable_sort compare_defs idlist

let rec get_def_status id index =
  try 
    match Deftable.get_def id "get_def:get_def_status" with
        DEF_REF y -> get_def_status y index
      | DEF_STR y -> y.abstr.(index)
  with IdNotFound x -> SUBTREE_DONE


let confirm_subtree_done deps index =
  List.fold_left (fun acc x -> 
    acc && (get_def_status x index = SUBTREE_DONE)
  ) true deps


(* dfs search for below, returns None or Some id *)
(* this actually sets the next to-be-refined variable *)
let rec def_dfs hash ids count index =
    match ids with
        [] -> None (* done *)
      | h::t ->
        try 
          (* skip input vars *)
          if Tables.is_input_var h then 
            begin
              def_dfs hash t count index
            end
          else
            begin
              match Tables.safe_find hash h ("def_dfs:2:"^(string_of_int h)) with
                  DEF_REF x -> def_dfs hash (x::t) count index
                | DEF_STR defline ->
                    begin
                      match defline.abstr.(index) with
                          NOT_REFINED -> 
                            set_refined h defline index (REFINED(count));
                            Some h (* done *)
                        | REFINED(x) -> 
                            if x = count then (* try siblings *)
                              def_dfs hash t count index
                            else (* try children *)
                              begin
                                set_refined h defline index (REFINED(count));
                                let b_res = 
                                  def_dfs hash defline.deps count index 
                                in
                                match b_res with
                                    None -> 
                                      if confirm_subtree_done defline.deps index then
                                         set_refined h defline index SUBTREE_DONE;
                                      def_dfs hash t count index
                                  | Some _ -> b_res
                              end
                        | _ ->  def_dfs hash t count index
                    end
           end
         with Not_found -> raise (Def_Not_Found h)

(* heuristic dfs *)
let rec def_hdfs full_b rev_pol hash ids count index =
let ids2 =
  if full_b then 
    def_sort rev_pol ids (* full_b = true for 'pure' heuristc search *)
  else
    ids
in
    match ids2 with
        [] -> None (* done *)
      | h::t ->
        try 
          (* skip input vars *)
          let (_,_,_,c) = Tables.safe_find_varinfo h "def_hdfs:1" in
          if c = INPUT then 
            begin
              def_hdfs full_b rev_pol hash t count index
            end
          else
            begin
              match Tables.safe_find hash h "dfs+hdfs:2" with
                  DEF_REF x -> def_hdfs full_b rev_pol hash (x::t) count index
                | DEF_STR defline ->
                    begin
                      match defline.abstr.(index) with
                          NOT_REFINED -> 
                            set_refined h defline index (REFINED(count));
                            Some h (* done *)
                        | REFINED(x) -> 
                            if x = count then (* try siblings *)
                              def_hdfs full_b rev_pol hash t count index
                            else (* try children *)
                              begin
                                set_refined h defline index (REFINED(count));
                                let b_res = def_hdfs full_b rev_pol hash  
                                  (def_sort rev_pol defline.deps) count index
                                in
                                match b_res with
                                    None -> 
                                      if confirm_subtree_done defline.deps index then
                                       set_refined h defline index SUBTREE_DONE;
                                      def_hdfs full_b rev_pol hash t count index
                                  | Some _ -> b_res
                              end
                        | _ ->  def_hdfs full_b rev_pol hash t count index
                    end
           end
         with Not_found -> raise (Def_Not_Found h)



(* hash is def_hash table, id lookup, count = coloring round *)
(* returns None (if all refined) or Some [id] *)
(* sets the abs field as a side effect *)
let next_unrefined_def hash start_ids index =
  refined_step_as_well := [];
  Deftable.incr_def_counter();
  match def_dfs hash start_ids (Deftable.get_def_counter()) index with
      None -> None
    | Some x -> Some [x]

(* only works on core list; returns None if no core vars were refined *)
let next_unrefined_core_defs hash start_ids index =
  refined_step_as_well := [];
  Deftable.incr_def_counter();
  match List.fold_left (fun acc z -> 
    let rec getnext x = 
      let (_,_,_,c) = Tables.safe_find_varinfo x "core:1" in
      if c = INPUT then 
        acc
      else
        begin
          match Tables.safe_find hash x "core:2" with
              DEF_REF y -> getnext y
            | DEF_STR defline ->
                begin
                  match defline.abstr.(index) with
                      NOT_REFINED ->
                       set_refined x defline index (REFINED(Deftable.get_def_counter()));
                        x::acc
                    | _ -> 
                           acc
                end
        end
    in
    getnext z
  ) [] start_ids with
 
      [] -> None
    | ls -> Some ls



(* returns None (if all refined) or Some [ids] *)
(* sets the abs field as a side effect *)
let next_unrefined_def_path hash start_ids index =
  refined_step_as_well := [];
  let rec dfs_path ins outs =
    Deftable.incr_def_counter();
    match def_dfs hash ins (Deftable.get_def_counter()) index with
        None -> outs
      | Some x -> 
          let xh = 
             match Tables.safe_find hash x "next_unrefined_def_path:1" with
               DEF_STR xh -> xh
               | _ -> raise Lus_convert_error
          in
          begin
            match xh.deps with
                h::t -> 
                     let (_,_,_,c) = Tables.safe_find_varinfo h "next_unrefined_def_path:1" in
                     if c = INPUT then 
(*                     if confirm_subtree_done [h] index then *)
                       x::outs
                     else
                       dfs_path ins (x::outs)
              | _ -> dfs_path ins (x::outs)
          end
  in
  match dfs_path start_ids [] with
      [] -> None
    | l -> Some l


let fringe = ref []
let w1 = ref 1 (* number of inputs *)
let w2 = ref 1 (* distance from leaf *)
let rec fringe_score hash x = 
  try 
    match Hashtbl.find hash x with
        DEF_STR y -> y.score * !w1 - y.score2 * !w2
      | DEF_REF y -> fringe_score hash y
  with Not_found ->
    max_int (* inputs are always prefferable *)

let fringe_compare hash x y =
-(  (fringe_score hash x) - (fringe_score hash y))

let fringe_sort hash =
  fringe := List.fast_sort (fringe_compare hash) (!fringe)

  

(* extra stuff for best1st *)
(* mark traversed nodes with stamp = -2 *)
(* score is the number of incomming links *)
(* scroe2 is the dist to leaf *)
let setup_best_scores hash plist =
  let rec dfs x =  (* returns shortest distance to leaf *)
    try
      match Hashtbl.find hash x with
          DEF_REF y -> dfs y
        | DEF_STR y ->
            if y.stamp != -2 then
              begin
                y.stamp <- -2; (* mark as visited *)
                let min = List.fold_left (fun acc z ->
                    let rec set_score1 w =
                      try
                        match Hashtbl.find hash w with
                            DEF_REF v -> set_score1 v
                          | DEF_STR v -> v.score <- v.score + 1
                      with Not_found ->
                        ()
                    in
                    set_score1 z;
                    let tmpdst = dfs z in
                    if tmpdst < acc then
                      tmpdst
                    else
                      acc
                  ) max_int y.deps
                in
                if min = max_int then
                  y.score2 <- 0 (* case without inputs but still leaf *)
                else
                  y.score2 <- min+1;
                if y.abstr.(base_abstr) != NOT_REFINED || 
                   y.abstr.(step_abstr) != NOT_REFINED 
                then
                  fringe := List.rev_append y.deps !fringe
              end;
            y.score2
    with Not_found ->
      0 (* inputs would be here *)
  in
  List.iter (fun x -> toss(dfs x)) plist;
  fringe_sort hash


(* take best from fringe *)
(* score is w1*number of parents - w2*dist from leaf *)
let next_unrefined_def_bfpath hash index =
  refined_step_as_well := [];
  Deftable.incr_def_counter();
  (* find the first unrefined node on the fringe *)
  let rec bestfirst outlist =
    match !fringe with
        [] -> outlist
      | h::t ->
        fringe := t;
        let rec nextbest x =
          try
            match Hashtbl.find hash x with
                DEF_REF y -> nextbest y
              | DEF_STR y ->
                   begin
                     match y.abstr.(index) with
                         NOT_REFINED -> 
                            set_refined h y index (REFINED(Deftable.get_def_counter()));
                            List.iter (fun z -> 
                              if not (List.mem z !fringe) then
                                fringe := z ::(!fringe)
                            ) y.deps;
                            fringe_sort hash;
                            bestfirst (h::outlist)
                       | _ -> bestfirst outlist
                   end 
          with Not_found -> (* stop on input, unless it's the first thing we've seen *)
            if outlist = [] then
              bestfirst outlist
            else
              outlist
        in
        nextbest h
  in
  let res = bestfirst [] in
  if res = [] then
    None
  else
    Some res

(* do this to a list of unsat cores *)
let def_incr_scores idlist = 
  List.iter (fun x -> 
    match Deftable.get_def x "get_def:def_incr_scores" with
        DEF_REF y -> ()
      | DEF_STR y -> y.score <- y.score - 1
  ) idlist

(* heuristic version of above *)
let next_unrefined_def_hpath full_b neg_polarity hash start_ids index =
  refined_step_as_well := [];
  def_incr_scores start_ids;
  let rec dfs_path ins outs =
    Deftable.incr_def_counter();
    match def_hdfs full_b neg_polarity hash start_ids (Deftable.get_def_counter()) index with
        None -> outs
      | Some x -> 
          let xh = 
            match Tables.safe_find hash x "next_unrefined_def_hpath:1" with
              DEF_STR xh -> xh
              | _ -> raise Lus_convert_error
          in
          begin
            match xh.deps with
                h::t -> 
                     let (_,_,_,c) = Tables.safe_find_varinfo h "next_unrefined_def_hpath:1" in
                     if c = INPUT then 
                       x::outs
                     else
                       dfs_path start_ids (x::outs)
              | _ -> dfs_path start_ids (x::outs)
          end
  in
  match dfs_path start_ids [] with
      [] -> None
    | l -> Some l


(* as next unrefined core, but has increasing min return size *)
let cores_to_date = ref []
let next_unrefined_defs_incr hash start_ids index =
  refined_step_as_well := [];
  cores_to_date := List.rev_append start_ids !cores_to_date;
  next_unrefined_core_defs hash !cores_to_date index





(* keep track of which steps are refined (id,pos) -> t/f, Not_found = false *)
let step_refined_hash = Hashtbl.create 10
let has_been_refined x l = Hashtbl.mem step_refined_hash (x,l)

(* bfs expansion at this level, returns None or Some id *)
(* this actually sets the next to-be-refined variable *)
let rec def_bfs1 hash ids_steps outlist =
    match ids_steps with
        [] -> outlist
      | ((h,level) as hl)::t ->
        try 
          (* skip input vars *)
          let (_,_,_,c) = Tables.safe_find_varinfo h "def_bfs1:1" in
          if c = INPUT then 
            def_bfs1 hash t outlist
          else if has_been_refined h level then
            def_bfs1 hash t outlist
          else
            begin
              match Tables.safe_find hash h "def_dfs1:2" with
                  DEF_REF x -> def_bfs1 hash ((x,level)::t) outlist
                | DEF_STR defline ->
                    begin
                      Hashtbl.add step_refined_hash hl true;
                      let tmpout = 
                        def_bfs1 hash (defline.dep_offsets) (hl::outlist) 
                      in
                      def_bfs1 hash t tmpout
                    end
           end
         with Not_found -> raise (Def_Not_Found h)

(* refine subtree based on list *)
(* match as refined at level *)
(* returns a list of new id/level pairs *)
let next_unrefined_fine_core_defs hash ids_steps =
  refined_step_as_well := [];
  let newlist = def_bfs1 hash ids_steps [] in
  match newlist with
      [] -> None
    | l -> Some l



(* DEPTH_CHANGE id, old, new *)
(* bfs search for below, returns None or Some id *)
(* this actually sets the next to-be-refined variables *)
let rec def_bfs hash ids_steps outlist index =
    match ids_steps with
        [] -> outlist
      | (h,level)::t ->
        try 
          (* skip input vars *)
          let (_,_,_,c) = Tables.safe_find_varinfo h "def_bfs:1" in
          if c = INPUT then 
            begin
              def_bfs hash t outlist index
            end
          else
            begin
              match Tables.safe_find hash h "def_bfs:2" with
                  DEF_REF x -> def_bfs hash ((x,level)::t) outlist index
                | DEF_STR defline ->
                    begin
                      match defline.abstr.(index) with
                          NOT_REFINED -> 
                            set_refined h defline index (REFINED(level));
                            let tmpout = 
                              (* initially it's the current level *)
                              def_bfs hash 
                                (List.map(fun x -> (x,level)) defline.deps)
                                (h::outlist) index
                            in
                            def_bfs hash t tmpout index
                        | SUBTREE_DONE ->  def_bfs hash t outlist index
                        | REFINED(x) -> 
                            if x < level then
                              begin
                                set_refined h defline index (REFINED_MORE(x,level));
                                def_bfs hash t (h::outlist) index
                              end
                            else
                              def_bfs hash t outlist index
                        | REFINED_MORE(z,x) -> 
                            (* this should only happen if we've encountered it before, so it should already be in the outlist *)
                            if x < level then
                              begin
                                set_refined h defline index (REFINED_MORE(z,level));
                                def_bfs hash t outlist index
                              end
                            else
                              def_bfs hash t outlist index
                    end
           end
         with Not_found -> raise (Def_Not_Found h)


(* used for both subtree and the hybrid core version *)
let next_unrefined_hybrid_core hash ids_steps index =
  refined_step_as_well := [];
  let newlist = def_bfs hash ids_steps [] index in
  match newlist with
      [] -> None
    | l -> Some l


(* used for both subtree and the hybrid core version *)
let next_unrefined_full_subtree hash ids index =
  refined_step_as_well := [];
  let rec startnode ins =
    match ins with
        [] -> []
      | h::t ->
         begin
              match Tables.safe_find hash h "def_subtree:2" with
                  DEF_REF x -> startnode (x::t)
                | DEF_STR defline ->
                   begin
                     match defline.abstr.(index) with
                         NOT_REFINED -> [h]
                       | _ -> startnode t
                   end
         end
  in
  let rec dfs_subtree ins outs =
    Deftable.incr_def_counter();
    match def_dfs hash ins (Deftable.get_def_counter()) index with
        None -> outs
      | Some x -> 
          let xh = 
            match Tables.safe_find hash x "next_unrefined_def_subtree:1" with
              DEF_STR xh -> xh
              | _ -> raise Lus_convert_error
          in
          begin
            match xh.deps with
                h::t -> dfs_subtree ids (x::outs)
              | _ -> dfs_subtree ids (x::outs)
          end
  in
  match dfs_subtree (startnode ids) [] with
      [] -> None
    | l -> Some l

