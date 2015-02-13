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
type valid_props_info =
  { (* Proved by [modul]... *)
    modul: kind_module ;
    (* ...at [k]... *)
    k: Numeral.t ;
    (* ...with valid properties [valid_props] (scope list)... *)
    valid_props: string list ;
    (* ...with invariants [invars]. *)
    invars: Term.t list }

(* Aggregating property info type in an enum. *)
type prop_info =
  (* Mutually valid properties with info. *)
  | PropsValid of (string list) * valid_props_info
  (* Ktrue property with info. *)
  | PropKTrue  of  string       * Numeral.t
  (* Falsified property with info. *)
  | PropFalse  of  string       * kind_module * Numeral.t
                                * (StateVar.t * Term.t list) list

(* Sublog on an abstraction depth for a system. *)
type depth_sublog =
  { (* Abstraction depth of the sub analysis. *)
    depth: int ;
    (* Property-related events. *)
    mutable prop_infos: prop_info list }

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

(* |===| Constructors. *)

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

(* Creates a mutually valid poperty info.
   - [modul] is the module which proved,
   - [k] the k for which the property was proved,
   - [valid_props] valid properties at the time of proving,
   - [invars] invariants known at that time,
   - [proved_props] the actual properties found mutually valid. *)
let mk_valid_props
      modul k valid_props invars proved_props =
  PropsValid
    ( proved_props,
      { modul = modul ;
        k = k ;
        valid_props = valid_props ;
        invars = invars } )

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
           { depth = depth ; prop_infos = [] }
           :: depth_sublogs )

(* Adds a property info to a depth sublog of a sys sublog of a log. *)
let add_prop_info log sys depth prop_info =
  sys_depth_sublog log sys depth
  |> ( fun ({ prop_infos } as sublog) ->
       sublog.prop_infos <- prop_info :: prop_infos )

(* Updates a log from a list of events. *)
let rec update_of_events log sys depth = function
  | (modul, Event.PropStatus (prop, TransSys.PropInvariant))
    :: tail ->

     (* Building valid property info. *)
     mk_valid_props
       modul
       Numeral.zero
       (* Filtering valid properties different from this one. *)
       ( TransSys.get_prop_status_all sys
         |> List.filter
              ( function
                | (prop', TransSys.PropInvariant)
                     when prop <> prop' ->
                   Event.log
                     L_warn
                     "[update_log] not ignoring %s" ;
                   true
                | (p,s) ->
                   Event.log
                     L_warn
                     "[update_log] ignoring %s (%a)"
                     p
                     TransSys.pp_print_prop_status_pt s ;
                   false )
         |> List.map fst )
       ( TransSys.get_invars sys )
       [ prop ]
     |> add_prop_info log sys depth ;

     update_of_events log sys depth tail

  | (modul, Event.PropStatus (prop, TransSys.PropKTrue k))
    :: tail ->

     (* PropKTrue (prop, Numeral.of_int k) *)
     (* |> add_prop_info log sys depth ; *)

     update_of_events log sys depth tail

  | (modul, Event.PropStatus (prop, TransSys.PropFalse cex))
    :: tail ->

     PropFalse
       ( prop,
         modul,
         (List.length cex) - 1
         |> Numeral.of_int,
         cex )
     |> add_prop_info log sys depth ;

     update_of_events log sys depth tail

  | _ :: tail -> update_of_events log sys depth tail

  | _ -> ()


(* |===| Pretty printers. *)

(* Pretty prints a [valid_props_info]. *)
let pp_print_valid_props_info
      ppf { modul ; k ; valid_props ; invars } =
  Format.fprintf
    ppf
    "@[<v>\
     module: %a@ \
     k: %a@ \
     valid props: @[<v>%a@]@ \
     invariants: @[<v>%a@]\
     @]"
    pp_print_kind_module modul
    Numeral.pp_print_numeral k
    ( pp_print_list
        (fun ppf s -> Format.fprintf ppf "%s" s)
        "@ " )
    valid_props
    ( pp_print_list Term.pp_print_term ",@ " )
    invars

(* Pretty prints a [prop_info]. *)
let pp_print_prop_info ppf = function
  | PropsValid (props, valid_props_info) ->
     Format.fprintf
       ppf "@[<hv 4>\
            PropsValid @[<v>%a@]@ \
            %a\
            @]"
       (pp_print_list
          (fun ppf s -> Format.fprintf ppf "%s" s)
          ",@ ")
       props
       pp_print_valid_props_info valid_props_info
  | PropKTrue (prop, k) ->
     Format.fprintf
       ppf "@[<v 4>PropKTrue [%s]@ at %a@]"
       prop
       Numeral.pp_print_numeral k
  | PropFalse (prop, modul, k, _) ->
     Format.fprintf
       ppf "@[<v 4>PropFalse [%s]@ at %a@ \
            by module %a@]"
       prop
       Numeral.pp_print_numeral k
       pp_print_kind_module modul

(* Pretty prints a [depth_sublog]. *)
let pp_print_depth_sublog ppf { depth ; prop_infos } =
  Format.fprintf
    ppf "@[<hv 2>\
         at depth %d@ \
         %a\
         @]"
    depth
    (pp_print_list pp_print_prop_info "@ ") prop_infos

(* Pretty prints a [sys_sublog]. *)
let pp_print_sys_sublog ppf { sys ; depth_sublogs } =
  Format.fprintf
    ppf "@[<hv 2>\
         system %s {@ \
         %a\
         @;<1 -2>}@]"
    (TransSys.get_name sys)
    (pp_print_list pp_print_depth_sublog "@ ") depth_sublogs

(* Pretty prints a [t] log. *)
let pp_print_log ppf { sys ; sys_sublogs } =
  Format.fprintf
    ppf "@[<hv 2>\
         log starting at root [%s] {@ \
         %a\
         @;<1 -2>}@]"
    (TransSys.get_name sys)
    (pp_print_list pp_print_sys_sublog "@ ") sys_sublogs

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
