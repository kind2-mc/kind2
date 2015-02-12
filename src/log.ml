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

(* Type for the info related to a valid property. *)
type prop_valid =
  { (* Proved by [modul]... *)
    modul: kind_module ;
    (* ...at [k]... *)
    k: Numeral.t ;
    (* ...in conjunction with other properties [in_conj_with] (scope
       list)... *)
    in_conj_with: string list list ;
    (* ...with valid properties [valid_props] (scope list)... *)
    valid_props: string list list ;
    (* ...with invariants [invars]. *)
    invars: Term.t list }

(* Aggregating property info type in an enum. *)
type prop_info =
  | PropValid of (string list) * prop_valid
  | PropKTrue of  string       * Numeral.t
  | PropFalse of  string       * kind_module * Numeral.t

(* Sublog on an abstraction depth for a system. *)
type depth_sublog =
  { (* Abstraction depth of the sub analysis. *)
    depth: int ;
    (* Property-related events. *)
    mutable prop_info: prop_info list }

(* Sublog on a (sub)system. *)
type sys_sublog =
  { (* (Sub)system of the sub analysis. *)
    sys: TransSys.t ;
    (* Subanalyses on the abstraction depth. *)
    mutable depth_sublogs: depth_sublog list }

(* Log of a whole analysis. *)
type t =
  { (* Top most system of the analysis. *)
    sys: TransSys.t ;
    (* Sub analysis on the (sub)systems. *)
    sys_sublogs: sys_sublog list }

(* Creates an analysis log from the list of all systems analysis will
   be ran on.  So, if only analyzing [top], do [mk_log
   top]. Otherwise, one would typically do something like
   [TransSys.get_all_subsystems top |> mk_log]. *)
let mk_log all_sys =
  all_sys
  (* Building the list of [sys_sublogs] and retrieving top
     system. *)
  |> List.fold_left
       ( fun (sublogs, top_opt) sys ->
         (* New top sys option. *)
         let top_opt' =
           (* Is this system top? *)
           if TransSys.is_top sys then
             (* [sys] is top level, making sure it's the only one. *)
             ( match top_opt with
               (* It is, as it should be. *)
               | None -> Some sys
               (* More than one top sys, failing. *)
               | Some sys' ->
                  Format.sprintf
                    "[Log.mk_log] Multiple top level systems \
                     detected: (%s) and (%s)."
                    (TransSys.get_name sys')
                    (TransSys.get_name sys )
                  |> failwith )
           else
             (* It is not top, propagating current value. *)
             top_opt
         in
         ( { sys = sys ; depth_sublogs = [] } :: sublogs,
           top_opt' ) )
       ([], None)
  (* Making sure we found a top level system. *)
  |> ( function
       | sublogs, Some top ->
          (* Everything's fine, creating log. *)
          { sys = top ;
            sys_sublogs = sublogs }
       | _, None ->
          (* No top node detected, crashing. *)
          failwith
            "[Log.mk_log] No top level system found." )

(* |===| Accessors. *)

(* Finds the sublog of a system. Throws [Not_found] if [sys'] is not
   present. *)
let sys_sublog { sys_sublogs } sys' =
  List.find
    (fun ({ sys }: sys_sublog) -> sys' == sys)
    sys_sublogs

(* The depth sublogs of a system sublog. *)
let depth_sublogs { depth_sublogs } = depth_sublogs

(* Finds the sublog of an abstraction depth from the sublog of a
   system. Throws [Not_found] if [depth'] is not present. *)
let depth_sublog { depth_sublogs } depth' =
  List.find
    (fun { depth } -> depth' = depth)
    depth_sublogs

(* Finds the sublog of an abstraction depth for a system from a
   log. Throws [Not_found] if [sys] or [depth] is not present. *)
let sys_depth_sublog log sys depth =
  sys_sublog log sys
  |> (fun depth_sublog' ->
      depth_sublog depth_sublog' depth)

(* Adds an empty abstraction depth sublog to a (sub)system sublog of
   an analysis log. Throws [Not_found] if [sys] is not present. *)
let add_depth_sublog log sys depth =
  sys_sublog log sys
  |> ( fun ({ depth_sublogs } as sys_sublog) ->
       match depth_sublog sys_sublog depth with
       | _ ->
          (* Sublog for depth already exists, crashing. *)
          TransSys.get_name sys
          |> Format.sprintf
               "[add_depth_sublog] Log already has a sublog \
                at %d for (%s)."
               depth
          |> invalid_arg
       | exception
         Not_found ->
         (* No sublog for depth, adding it. *)
         sys_sublog.depth_sublogs <-
           { depth = depth ; prop_info = [] }
           :: depth_sublogs )    

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
