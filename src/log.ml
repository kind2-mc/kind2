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

(* A log is a tree of depth 4.

   The first level is the root and contains the top node as well as
   the kids at depth 2. They represent analyses of a specific
   system. In non modular analysis, depth 2 will only have one node,
   the top level. In modular analysis, then eventually depth 2 will
   have a node for all systems of the hierarchy.

   Nodes at depth 2 contain the system the analysis of which they
   correspond to, and kids at depth 3. These distinguish analyses with
   different subsystem, contract-based abstractions. They contain the
   list of the subsystems (of their depth 2 parent) which have been
   abstracted for the analysis they represent. When not running in
   compositional mode, a depth 2 node can only have one kid with an
   empty list of abstracted nodes.

   The kids of a depth 3 node store detail about property related
   events during the analysis their path corresponds to. They log
   information about invariant and falsified property, as well as
   k-true properties at the end of their analysis. *)

   

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

(* Type for identifying abstraction sublogs. Hidden to the user so
   that the order does not change. Upon creation of an asbtraction
   sublog, the key to this sublog is returned. *)
type abstraction_key = string list list

(* String representation of a key. *)
let string_of_abstraction key =
  key
  |> List.map (String.concat ".")
  |> String.concat ", "

(* Sublog on an abstraction for a system. *)
type abstraction_sublog =
  { (* Abstracted nodes of the sub analysis as a set of string
       lists (scopes of transition systems). *)
    abstraction: abstraction_key ;
    (* Property-related events. *)
    mutable prop_infos: prop_info list }

(* Sublog on a (sub)system. *)
type sys_sublog =
  { (* (Sub)system of the sub analysis. *)
    sys: TransSys.t ;
    (* Subanalyses on the abstracted subsystems. *)
    mutable abstraction_sublogs: abstraction_sublog list }

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
         ( { sys = sys ; abstraction_sublogs = [] } :: sublogs,
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

(* Creates a mutually valid property info.
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

(* Returns the list of abstracted systems from an abstraction key. *)
let abstracted_systems_of_abstraction_key = identity

let key_of_list = identity

(* Finds the sublog of a system. Throws [Not_found] if [sys'] is not
   present. *)
let sys_sublog { sys_sublogs } sys' =
  List.find
    (fun ({ sys }: sys_sublog) -> sys' == sys)
    sys_sublogs

(* The abstraction sublogs of a system sublog. *)
let abstraction_sublogs { abstraction_sublogs } =
  abstraction_sublogs

(* Finds the sublog of an abstraction from the sublog of a
   system. Throws [Not_found] if [abstraction] is not present for this
   system. *)
let abstraction_sublog { abstraction_sublogs } abstraction_key =
  List.find
    ( fun { abstraction } ->
      abstraction = abstraction_key )
    abstraction_sublogs

(* Finds the sublog of an abstraction key for a system from a
   log. Throws [Not_found] if [sys] or [abstraction_key] is not
   present. *)
let sys_abstraction_sublog log sys abstraction_key =
  sys_sublog log sys
  |> (fun abstraction_sublog' ->
      abstraction_sublog abstraction_sublog' abstraction_key)

(* Adds an empty abstraction sublog to a (sub)system sublog of an
   analysis log. Throws [Not_found] if [sys] is not present and
   [Illegal_argumen] if the abstraction sublog already exists.
   Returns the abstraction key to the sublog created. *)
let add_abstraction_sublog log sys strings_list =
  sys_sublog log sys
  |> ( fun ({ abstraction_sublogs } as sys_sublog) ->
       match abstraction_sublog sys_sublog strings_list with
       | _ ->
          (* Sublog for key already exists, crashing. *)
          Format.sprintf
            "Log already has a sublog for %s with abstraction %s."
            (TransSys.get_name sys)
            ( strings_list
              |> List.map (String.concat ".")
              |> String.concat ", " )
          |> invalid_arg
       | exception
         Not_found ->
         (* No sublog for this key, adding it. *)
         sys_sublog.abstraction_sublogs <-
           { abstraction = strings_list ; prop_infos = [] }
           :: abstraction_sublogs ) ;
  (* Returning abstraction key. *)
  strings_list

(* Adds a property info to an abstraction sublog of a sys sublog of a
   log. *)
let add_prop_info log sys abstraction_key prop_info =
  sys_abstraction_sublog log sys abstraction_key
  |> ( fun ({ prop_infos } as sublog) ->
       sublog.prop_infos <- prop_info :: prop_infos )

(* Updates a log from a list of events. *)
let rec update_of_events log sys abstraction_key = function
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
     |> add_prop_info log sys abstraction_key ;

     update_of_events log sys abstraction_key tail

  | (modul, Event.PropStatus (prop, TransSys.PropFalse cex))
    :: tail ->

     PropFalse
       ( prop,
         modul,
         (List.length cex) - 1
         |> Numeral.of_int,
         cex )
     |> add_prop_info log sys abstraction_key ;

     update_of_events log sys abstraction_key tail

  | _ :: tail ->

     update_of_events log sys abstraction_key tail

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

(* Pretty prints an abstraction key. *)
let pp_print_abstraction_key ppf key =
  Format.fprintf
    ppf
    "@[<v>%a@]"
    (pp_print_list
       (pp_print_list
          Format.pp_print_string ".")
       ",@ ")
    key

(* Pretty prints a [abstraction_sublog]. *)
let pp_print_abstraction_sublog ppf { abstraction ; prop_infos } =
  Format.fprintf
    ppf "@[<hv 2>\
         abstraction: [%a]@ \
         %a\
         @]"
    pp_print_abstraction_key abstraction
    (pp_print_list pp_print_prop_info "@ ") prop_infos

let pp_print_abstraction_sublog_shy
      ppf { abstraction ; prop_infos } =
  Format.fprintf
    ppf "@[<hv 2>\
         abstraction: [%a]@.\
         @[<hv>%a@]\
         @]"
    pp_print_abstraction_key abstraction
    (pp_print_list
       ( fun ppf ->
         function
         | PropsValid (props,_) ->
            Format.fprintf
              ppf "Valid: [ @[<v>%a@] ]"
              (pp_print_list
                 Format.pp_print_string
                 ",@ ")
              props
         | PropFalse (prop,_,_,_) ->
            Format.fprintf
              ppf "False: %s" prop
         | _ -> () )
       "@.")
    prop_infos

(* Pretty prints a [sys_sublog]. *)
let pp_print_sys_sublog ppf { sys ; abstraction_sublogs } =
  Format.fprintf
    ppf "@[<hv 2>\
         system %s {@ \
         %a\
         @;<1 -2>}@]"
    (TransSys.get_name sys)
    (pp_print_list pp_print_abstraction_sublog "@ ") abstraction_sublogs

let pp_print_sys_sublog_shy ppf {sys ; abstraction_sublogs} =
  Format.fprintf
    ppf "@[<hv 2>\
         system %s {@ \
         %a\
         @;<1 -2>}@]"
    (TransSys.get_name sys)
    (pp_print_list pp_print_abstraction_sublog_shy "@ ") abstraction_sublogs

(* Pretty prints a [t] log. *)
let pp_print_log ppf { sys ; sys_sublogs } =
  Format.fprintf
    ppf "@[<hv 2>\
         log starting at root [%s] {@ \
         %a\
         @;<1 -2>}@]"
    (TransSys.get_name sys)
    (pp_print_list pp_print_sys_sublog "@ ") sys_sublogs

(* Pretty prints a [t] log. *)
let pp_print_log_shy ppf { sys ; sys_sublogs } =
  Format.fprintf
    ppf "@[<hv 2>\
         log starting at root [%s] {@ \
         %a\
         @;<1 -2>}@]"
    (TransSys.get_name sys)
    (pp_print_list pp_print_sys_sublog_shy "@ ") sys_sublogs

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
