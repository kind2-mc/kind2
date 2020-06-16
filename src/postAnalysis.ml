(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015-2019 by the Board of Trustees of the University of Iowa

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

module TestGen = TestgenDF
module Num = Numeral
module TSys = TransSys
module ISys = InputSystem
module SVar = StateVar

module SVS = StateVar.StateVarSet
module SVM = StateVar.StateVarMap

open Res


(** TSys name formatter. *)
let fmt_sys = TSys.pp_print_trans_sys_name

(** Last analysis result corresponding to a scope. *)
let last_result results scope =
  try
    Ok (Analysis.results_last scope results)
  with
  | Not_found -> Err (
    fun fmt ->
      Format.fprintf fmt "No result available for component %a."
        Scope.pp_print_scope scope
  )

(** Signature of modules for post-analysis treatment. *)
module type PostAnalysis = sig
  (** Name of the treatment. (For xml logging.) *)
  val name: string
  (** Title of the treatment. (For plain text logging.) *)
  val title: string
  (** Indicates whether the module is active. *)
  val is_active: unit -> bool
  (** Performs the treatment. *)
  val run:
    (** Input system. *)
    'a ISys.t ->
    (** Analysis parameter. *)
    Analysis.param ->
    (** A function running an analysis with some modules. *)
    (
      bool -> Lib.kind_module list -> 'a ISys.t -> Analysis.param -> TSys.t -> unit
    ) ->
    (** Results for the current system. *)
    Analysis.results
    (** Can fail. *)
    -> unit res
end

(** Test generation.
Generates tests for a system if system's was proved correct under the maximal
abstraction. *)
module RunTestGen: PostAnalysis = struct
  let name = "testgen"
  let title = "test generation"
  (** Error head. *)
  let head sys fmt =
    Format.fprintf fmt "Not generating tests for component %a." fmt_sys sys
  (** Checks that system was proved with the maximal abstraction. *)
  let gen_param_and_check in_sys param sys =
    let top = TSys.scope_of_trans_sys sys in

    match param with
    | Analysis.Interpreter _ -> Err (
      fun fmt ->
        Format.fprintf fmt
          "%t@ Test generation is not compatible with interpreter mode." (head sys)
    )
    (* Contract check, node must be abstract. *)
    | Analysis.ContractCheck _ -> Err (
      fun fmt ->
        Format.fprintf fmt
          "%t@ Cannot generate tests unless implementation is safe." (head sys)
    )
    | Analysis.Refinement _ -> Err (
      fun fmt ->
        Format.fprintf fmt
          "%t@ Component was not proven correct under its maximal abstraction."
          (head sys)
    )
    | Analysis.First _ ->

      if TSys.all_props_proved sys |> not then Err (
        fun fmt ->
          Format.fprintf fmt
            "%t@ Component has not been proved safe." (head sys)
      ) else (
        match
          InputSystem.maximal_abstraction_for_testgen
            in_sys top Analysis.assumptions_empty
        with
        | None -> Err (
          fun fmt ->
            Format.fprintf fmt
              "System %a has no contracts, skipping test generation."
              fmt_sys sys
        )
        | Some param -> Ok param
      )

  let is_active () = Flags.Testgen.active ()
  let run in_sys param _ results =
    (* Retrieve system from scope. *)
    let top = (Analysis.info_of_param param).Analysis.top in
    last_result results top
    |> Res.chain (fun { Analysis.sys } ->
      (* Make sure there's at least one mode. *)
      match TSys.get_mode_requires sys |> snd with
      | [] -> (
        match TSys.props_list_of_bound sys Num.zero with
        | [] -> Err (
          fun fmt ->
            Format.fprintf fmt "%t@ Component has no contract." (head sys)
        )
        | _ -> Err (
          fun fmt ->
            Format.fprintf fmt "%t@ Component has no modes." (head sys)
        )
      )
      | _ -> Ok sys
    )
    |> Res.chain (gen_param_and_check in_sys param)
    |> Res.chain (
      fun param ->
        (* Create root dir if needed. *)
        Flags.output_dir () |> mk_dir ;
        let target = Flags.subdir_for top in
        (* Create system dir if needed. *)
        mk_dir target ;

        (* Tweak analysis uid to avoid clashes with future analyses. *)
        let param = Analysis.param_clone param in

        (* Extracting transition system. *)
        let sys, input_sys_sliced =
          InputSystem.trans_sys_of_analysis
            ~preserve_sig:true in_sys param
        in

        (* Let's do this. *)
        try (
          let tests_target = Format.sprintf "%s/%s" target Paths.testgen in
          mk_dir tests_target ;
          KEvent.log_uncond
            "%sGenerating tests for node '%a' to '%s'."
            TestGen.log_prefix Scope.pp_print_scope top tests_target ;
          let testgen_xmls =
            TestGen.main param input_sys_sliced sys tests_target
          in
          (* Yay, done. Killing stuff. *)
          TestGen.on_exit "yay" ;
          (* Generate oracle. *)
          let oracle_target = Format.sprintf "%s/%s" target Paths.oracle in
          mk_dir oracle_target ;
          KEvent.log_uncond
            "%sCompiling oracle to Rust for node '%a' to '%s'."
            TestGen.log_prefix Scope.pp_print_scope top oracle_target ;
          let name, guarantees, modes =
            InputSystem.compile_oracle_to_rust in_sys top oracle_target
          in
          KEvent.log_uncond
            "%sGenerating glue xml file to `%s/.`." TestGen.log_prefix target ;
          testgen_xmls
          |> List.map (fun xml -> Format.sprintf "%s/%s" Paths.testgen xml)
          |> TestGen.log_test_glue_file
            target name (Paths.oracle, guarantees, modes) Paths.implem ;
          KEvent.log_uncond
            "%sDone with test generation." TestGen.log_prefix ;
          Ok ()
        ) with e -> (
          TestGen.on_exit "T_T" ;
          Err (
            fun fmt ->
              Printexc.to_string e
              |> Format.fprintf fmt "during test generation:@ %s"
          )
        )
    )
end

(** Contract generation.
Generates contracts by running invariant generation techniques. *)
module RunContractGen: PostAnalysis = struct
  let name = "contractgen"
  let title = "contract generation"
  let is_active () = Flags.Contracts.contract_gen ()
  let run in_sys param analyze results =
    let top = (Analysis.info_of_param param).Analysis.top in
    KEvent.log L_note
      "Contract generation is a very experimental feature:@ \
      in particular, the modes it generates might not be exhaustive,@ \
      which means that Kind 2 will consider the contract unsafe.@ \
      This can be dealt with by adding a wild card mode:@ \
      mode wildcard () ;" ;
    (* Building transition system and slicing info. *)
    let sys, in_sys_sliced =
      ISys.trans_sys_of_analysis
        ~preserve_sig:true ~slice_nodes:false in_sys param
    in
    let target = Flags.subdir_for top in
    (* Create directories if they don't exist. *)
    Flags.output_dir () |> mk_dir ;
    mk_dir target ;
    let target =
      Format.asprintf "%s/%s" target Names.contract_gen_file
    in
    (* Format.printf "system: %a@.  %a@.@."
      Scope.pp_print_scope (TSys.scope_of_trans_sys top)
      Invs.fmt (TSys.get_invariants top) ; *)
    (* Analysis with all invariant generation techniques. *)
    (* Remember previous max depth for invgen. *)
    let old_max_depth = Flags.Invgen.max_depth () in
    (* Set contract generation max depth. *)
    Some (Flags.Contracts.contract_gen_depth ())
    |> Flags.Invgen.set_max_depth ;
    (* Disable logging. *)
    let old_log_level = Lib.get_log_level () in
    Lib.set_log_level L_off ;

    (* Things to backtrack when we're done. *)
    let and_then () =
      Flags.Invgen.set_max_depth old_max_depth ;
      Lib.set_log_level old_log_level
    in

    ( match Flags.invgen_enabled () with
      | [] -> Err (
        fun fmt -> Format.printf "No invariant generation technique enabled."
      )
      | teks -> Ok teks
    )
    |> Res.chain (
      fun teks ->
        Flags.Contracts.contract_gen_depth ()
        |> KEvent.log_uncond "  @[<v>\
          Discovering invariants by running@   @[<v>%a@]@ \
          to depth %d...\
        @]" (
          pp_print_list (
            fun fmt ->
              Format.fprintf fmt "- %a" pp_print_kind_module
          ) "@ "
        ) teks ;
        try
          analyze true
            teks
            (* [
              `INVGEN ; `INVGENOS ;
              `INVGENINT ; `INVGENINTOS ;
              `INVGENREAL ; `INVGENREALOS ;
            ] *)
            in_sys_sliced param sys ;
          and_then () ;
          Ok ()
        with e -> and_then () ; Err (
          fun fmt ->
            Format.fprintf fmt "Could not run invariant generation:@ %s"
              (Printexc.to_string e)
        )
    )
    |> Res.chain (
      fun () ->
      (* Format.printf "system: %a@.  %a@.@."
        Scope.pp_print_scope (TSys.scope_of_trans_sys top)
        Invs.fmt (TSys.get_invariants top) ; *)
      try (
        LustreContractGen.generate_contracts
          in_sys_sliced param sys target (Names.contract_name top) ;
        Ok ()
      ) with e -> Err (
          fun fmt ->
            Format.fprintf fmt "Could not generate contract:@ %s"
              (Printexc.to_string e)
      )
    )
end

(** Rust generation.
Compiles lustre as Rust. *)
module RunRustGen: PostAnalysis = struct
  let name = "rustgen"
  let title = "rust generation"
  let is_active () = Flags.lus_compile ()
  let run in_sys param _ results =
    KEvent.log L_note
      "Compilation to Rust is still a rather experimental feature:@ \
      in particular, arrays are not supported." ;
    let top = (Analysis.info_of_param param).Analysis.top in
    let target = Flags.subdir_for top in
    (* Creating directories if needed. *)
    Flags.output_dir () |> mk_dir ;
    mk_dir target ;
    (* Implementation directory. *)
    let target = Format.sprintf "%s/%s" target Paths.implem in
    KEvent.log_uncond
      "  Compiling node '%a' to Rust in '%s'."
      Scope.pp_print_scope top target ;
    InputSystem.compile_to_rust in_sys top target ;
    KEvent.log_uncond "  Done compiling." ;
    Ok ()
end

(** Invariant log.
Minimizes and logs invariants used in the proof. *)
module RunInvLog: PostAnalysis = struct
  let name = "invlog"
  let title = "invariant logging"


  let is_active () = Flags.log_invs ()
  let run in_sys param _ results =
    KEvent.log L_note "\
    In some cases, invariant logging can fail because it is not able to@ \
    translate the invariants found by Kind 2 internally back to Lustre level.\
    " ;
    let top = (Analysis.info_of_param param).Analysis.top in
    let target = Flags.subdir_for top in
    (* Create directories if they don't exist. *)
    Flags.output_dir () |> mk_dir ;
    mk_dir target ;
    let target =
      Format.asprintf "%s/%s" target Names.inv_log_file
    in
    last_result results top
    |> Res.chain (fun { Analysis.sys } ->
      (* Check all properties are valid. *)
      match TSys.get_split_properties sys with
      | [], [], [] -> Err (
        fun fmt ->
          Format.fprintf fmt
            "No properties, no strengthening invariant to log."
      )
      | _, [], _ -> Ok sys
      | _, invalid, _ -> Err (
        fun fmt ->
          let len = List.length invalid in
          Format.fprintf fmt
            "Not logging invariants: \
            %d invalid propert%s, system is unsafe."
            len (if len = 1 then "y" else "ies")
      )
    )
    |> Res.chain (fun sys ->
      (* Returns [false] iff term passed mentions node call svars. *)
      let _, node_of_scope =
        InputSystem.contract_gen_param in_sys
      in
      let node = node_of_scope top in
(*       node.LustreNode.state_var_source_map
      |> StateVar.StateVarMap.bindings
      |> Format.printf "node's svars: @[<v>%a@]@.@."
        (pp_print_list
          (fun fmt (svar, source) ->
            Format.fprintf fmt "%a -> %a"
              SVar.pp_print_state_var svar
              LustreNode.pp_print_state_var_source source ;
            if source = LustreNode.Call then
              LustreNode.get_state_var_instances svar
              |> Format.fprintf fmt "@     -> @[<v>%a@]"
                (pp_print_list
                  (fun fmt (_,_,sv) -> StateVar.pp_print_state_var fmt sv)
                  "@ "
                )
          ) "@ "
        ) ;
      node.LustreNode.equations
      |> Format.printf "node's equations: @[<v>%a@]@.@."
        (pp_print_list
          (fun fmt eq ->
            Format.fprintf fmt "%a"
              (LustreNode.pp_print_node_equation false) eq
          ) "@ "
        ) ; *)
      let nice_invariants term =
        Term.state_vars_of_term term
        |> SVS.exists (
          fun svar -> try (
            match
              StateVar.StateVarMap.find
                svar node.LustreNode.state_var_source_map
            with
            | LustreNode.Call ->
              Format.printf "discarding %a@.  %a -> call@.@."
                Term.pp_print_term term
                StateVar.pp_print_state_var svar ;
              true
            | _ -> false
          ) with Not_found ->
            (* Format.printf "discarding %a@.  %a -> not found@.@."
              Term.pp_print_term term
              StateVar.pp_print_state_var svar ; *)
            true
        )
        |> not
      in
      try (
        let k_min, invs_min =
          CertifChecker.minimize_invariants sys None (Some nice_invariants)
        in
        KEvent.log_uncond
          "Minimization result: \
            @[<v>\
              all properties valid by %d-induction@ \
              using %d invariant(s)\
            @]\
          "
          k_min (List.length invs_min) ;
        Ok (sys, k_min, invs_min)
      ) with
      | CertifChecker.CouldNotProve blah -> Err(
        fun fmt ->
          (* Format.fprintf fmt
            "@[<v>Some necessary invariants cannot be translated \
            back to lustre level.@ %s@]"
            (Printexc.to_string e) *)
          Format.fprintf fmt
            "Some necessary invariants cannot be translated \
            back to lustre level."
      )
      | e -> Err (
        fun fmt -> Format.fprintf fmt
          "Could not minimize invariants:@ %s"
          (Printexc.to_string e)
      )
    )
    |> Res.chain (fun (sys, _, invs) ->
      try Ok (
        LustreContractGen.generate_contract_for
          in_sys param sys target invs (Names.inv_log_contract_name top)
      ) with e -> Err (
        fun fmt ->
          Format.fprintf fmt "Could not generate strengthening contract:@ %s"
            (Printexc.to_string e)
      )
    )
    |> Res.map (
      fun () ->
        KEvent.log_uncond
          "Done logging strengthening invariants to@ `%s`."
          target
    )
end

(** Invariant print.
Prints invariants used in the proof. *)
module RunInvPrint: PostAnalysis = struct
  let name = "invprint"
  let title = "invariant printing"

  let is_active () = Flags.print_invs ()

  let run in_sys param _ results =
    let top = (Analysis.info_of_param param).Analysis.top in

    last_result results top
    |> Res.chain (fun { Analysis.sys } ->
      let var_map =
        let aux_vars =
          let usr_name =
            assert (List.length LustreIdent.user_scope = 1) ;
            List.hd LustreIdent.user_scope
          in
          List.filter
            (fun sv ->
              not ( List.mem usr_name (StateVar.scope_of_state_var sv) )
            )
            (TSys.state_vars sys)
        in
        ISys.mk_state_var_to_lustre_name_map in_sys aux_vars
      in

      try (
        let k_min, invs_min =
          CertifChecker.minimize_invariants sys None None
        in
        KEvent.log_uncond
          "Minimization result: \
            @[<v>\
              all properties valid by %d-induction@ \
              using %d invariant(s)\
            @]\
          "
          k_min (List.length invs_min) ;
        List.iter
          (fun inv ->
            let fmt_inv =
              LustreExpr.pp_print_term_as_expr_mvar false var_map
            in
            KEvent.log_uncond "%a" fmt_inv inv
          )
        invs_min ;
        Ok ()
      ) with
      | CertifChecker.CouldNotProve err -> Err(
        fun fmt ->
          Format.fprintf fmt
            "Could not minimize invariants:@ %a" (fun fmt () -> err fmt) ()
      )
      | e -> Err (
        fun fmt -> Format.fprintf fmt
          "Could not minimize invariants:@ %s"
          (Printexc.to_string e)
      )
    )
end

(** Certifies the last proof. *)
module RunCertif: PostAnalysis = struct
  let name = "certification"
  let title = name
  let is_active () = Flags.Certif.certif ()
  let run in_sys param _ results =
    let top = (Analysis.info_of_param param).Analysis.top in
    last_result results top |> chain (
      fun result ->
        let sys = result.Analysis.sys in
        let uid = (Analysis.info_of_param param).Analysis.uid in
        ( if Flags.Certif.proof () then
            CertifChecker.generate_all_proofs uid in_sys sys
          else
            CertifChecker.generate_smt2_certificates uid in_sys sys
        ) ;
        Ok ()
    )
end

(** Inductive validity core computation *)
module RunIVC: PostAnalysis = struct
  let name = "ivc"
  let title = "inductive validity core"
  let is_active () = Flags.IVC.compute_ivc ()

  let rec pp_print_properties fmt = function
  | [] -> ()
  | _::_::_ -> Format.fprintf fmt "all"
  | [{ Property.prop_name = n }] -> Format.fprintf fmt "%s" n

  let run in_sys param analyze results =
    let top = (Analysis.info_of_param param).Analysis.top in
    last_result results top
    |> Res.chain (fun { Analysis.sys } ->
      try (
        (*Format.printf "%a\n" ISys.pp_print_subsystems_debug in_sys;*)
        (*Format.printf "%a\n" ISys.pp_print_state_var_instances_debug in_sys;*)
        (*Format.printf "%a\n" ISys.pp_print_state_var_defs_debug in_sys;*)
        (*TSys.iter_subsystems (fun sys ->
          let (_,_,trans) = TSys.init_trans_open sys in
          Format.printf "---------- %a ----------\n" Scope.pp_print_scope (TSys.scope_of_trans_sys sys) ;
          Term.print_term trans ; Format.printf "\n"
        ) sys ;*)
        (*(TSys.get_real_properties sys) |> List.iter (Format.printf "%a@." Property.pp_print_property) ;*)
        (*Format.print_flush ();*)

        let nb = ref 0 in
        let time = ref (Unix.gettimeofday ()) in

        let props =
          TransSys.get_real_properties sys
          |> List.filter
            (function
            | { Property.prop_status = Property.PropInvariant _ } -> true
            | { Property.prop_name } ->
              KEvent.log L_info "Skipping unproved property %s" prop_name ; false)
        in
        let props =
          if Flags.IVC.ivc_per_property ()
          then List.map (fun x -> [x]) props
          else [props]
        in
        
        let treat_props props =
          if List.length props > 0
          then begin
            let use_umivc = Flags.IVC.ivc_all () || Flags.IVC.ivc_smallest_first () in
            let stop_after = if Flags.IVC.ivc_all () then 0 else 1 in
            let k =
              if Flags.IVC.ivc_smallest_first ()
              then -1
              else Flags.IVC.ivc_precomputed_mcs ()
            in

            let treat_ivc is_must_set ivc =

              let ntime = Unix.gettimeofday () in
              let elapsed = ntime -. !time in
              time := ntime ;

              KEvent.log_with_tag L_warn Pretty.success_tag
                (Format.asprintf "%s generated after %.3fs."
                (if use_umivc || not (Flags.IVC.ivc_approximate ())
                then "Minimal IVC" else "Approximate minimal IVC") elapsed) ;

              let pt = ModelElement.pp_print_core_data in_sys param sys in
              let xml = ModelElement.pp_print_core_data_xml in_sys param sys in
              let json fmt = Format.fprintf fmt ",\n%a"
                (ModelElement.pp_print_core_data_json in_sys param sys) in

              if Flags.IVC.print_ivc ()
              then begin
                let (filtered_ivc,_) = Ivc.separate_ivc_by_category in_sys ivc in
                let cpd = Ivc.ivc_to_print_data in_sys sys
                  (if is_must_set then "must" else "ivc") (Some elapsed) filtered_ivc in
                KEvent.log_result pt xml json cpd
              end ;

              if Flags.IVC.print_ivc_compl ()
              then begin
                let not_ivc = Ivc.complement_of_ivc in_sys sys ivc in
                let (filtered_not_ivc,_) = Ivc.separate_ivc_by_category in_sys not_ivc in
                let cpd = Ivc.ivc_to_print_data in_sys sys
                  (if is_must_set then "must complement" else "ivc complement")
                  (Some elapsed) filtered_not_ivc in
                KEvent.log_result pt xml json cpd
              end ;

              if Flags.IVC.minimize_program () <> `DO_NOT_MINIMIZE && not is_must_set
              then begin
                let minimized =
                  ISys.lustre_source_ast in_sys
                  |> Ivc.minimize_lustre_ast
                    ~valid_lustre:(Flags.IVC.minimize_program () = `VALID_LUSTRE) in_sys ivc
                in
                let dir =
                  match Flags.IVC.minimized_program_dir () with
                  | "" ->
                    Flags.input_file ()
                    |> Filename.remove_extension
                  | str -> str
                in
                (try Unix.mkdir dir 0o755 with _ -> ()) ;
                let filename = Filename.concat dir (Format.asprintf "%a_%n.lus" pp_print_properties props !nb) in
                let print_channel out =
                  let fmt = Format.formatter_of_out_channel out in
                  LustreAst.pp_print_program fmt
                in
                let oc = open_out filename in
                print_channel oc minimized ;
                close_out oc
              end ;

              if not is_must_set then nb := !nb + 1
            in

            let use_must_set =
              if Flags.IVC.ivc_must_set ()
              then Some (treat_ivc true)
              else if Flags.IVC.ivc_all ()
              then Some (fun _ -> ())
              else None
            in

            let treat_and_return_lst = function
              | Ivc.Solution e -> treat_ivc false e ; [e]
              | _ -> [] in
            let res = match (use_umivc, Flags.IVC.ivc_approximate ()) with
              | (false, true) -> treat_and_return_lst (Ivc.ivc_uc in_sys ~approximate:false sys props)
              | (false, false) -> treat_and_return_lst (Ivc.ivc_ucbf in_sys ~use_must_set param analyze sys props)
              | (true, _) -> Ivc.umivc in_sys ~use_must_set ~stop_after param analyze sys props k (treat_ivc false)
            in
            if Flags.IVC.ivc_all ()
            then
              KEvent.log_with_tag L_note Pretty.note_tag
                (Format.asprintf "Number of minimal IVCs found: %n" (List.length res))
          end
        in
        List.iter treat_props props ;
        Ok ()
      )
      with
      | e -> Err (
        fun fmt -> Format.fprintf fmt
          "An error occured:@ %s"
          (Printexc.to_string e)
      )
    )
end

let run_mcs_post_analysis in_sys param analyze sys =
  try (
    let props =
      if Flags.MCS.mcs_per_property ()
      then List.map (fun x -> [x]) (TransSys.get_real_properties sys)
      else [TransSys.get_real_properties sys]
    in
    let time = ref (Unix.gettimeofday ()) in
    
    let treat_props props =

      if List.length props > 0
      then begin
        let treat_mua mua =

          let ntime = Unix.gettimeofday () in
          let elapsed = ntime -. !time in
          time := ntime ;

          KEvent.log_with_tag L_warn Pretty.success_tag
            (Format.asprintf "Minimal Cut Set generated after %.3fs." elapsed) ;

          let not_mua = Ivc.complement_of_mua in_sys sys mua in

          if Flags.MCS.print_mcs_legacy ()
          then begin
            Ivc.pp_print_mcs_legacy in_sys param sys not_mua mua
          end else begin

            let pt = ModelElement.pp_print_core_data in_sys param sys in
            let xml = ModelElement.pp_print_core_data_xml in_sys param sys in
            let json fmt = Format.fprintf fmt ",\n%a"
              (ModelElement.pp_print_core_data_json in_sys param sys) in

            if Flags.MCS.print_mcs ()
            then begin
              let (filtered_mcs,_) = Ivc.separate_mua_by_category in_sys not_mua in
              let cpd = Ivc.mcs_to_print_data in_sys sys "mcs" (Some elapsed) filtered_mcs in
              KEvent.log_result pt xml json cpd
            end ;

            if Flags.MCS.print_mcs_compl ()
            then begin
              let (filtered_mua,_) = Ivc.separate_mua_by_category in_sys mua in
              let cpd = Ivc.mcs_to_print_data in_sys sys "mcs complement"
                (Some elapsed) filtered_mua in
              KEvent.log_result pt xml json cpd
            end
          end
        in

        let max_mcs_cardinality = Flags.MCS.mcs_max_cardinality () in
        let mcs_all = Flags.MCS.mcs_all () in
        let res = Ivc.mua in_sys param analyze sys props ~max_mcs_cardinality mcs_all treat_mua in
        if Flags.MCS.mcs_all ()
        then
          KEvent.log_with_tag L_note Pretty.note_tag
            (Format.asprintf "Number of MCS found%s: %n"
            (match props with [{prop_name}] -> " for property "^prop_name | _ -> "")
            (List.length res))
      end
    in
    List.iter treat_props props ;
    Ok ()
  )
  with
  | e -> Err (
    fun fmt -> Format.fprintf fmt
      "An error occured:@ %s"
      (Printexc.to_string e)
  )


(** Minimal Cut Set computation *)
module RunMCS: PostAnalysis = struct
  let name = "mcs"
  let title = "minimal cut set"
  let is_active () = Flags.MCS.compute_mcs ()

  let run in_sys param analyze results =
    let top = (Analysis.info_of_param param).Analysis.top in
    last_result results top
    |> Res.chain (fun { Analysis.sys } ->
      run_mcs_post_analysis in_sys param analyze sys
    )
end

(** List of post-analysis modules. *)
let post_analysis = [
  (module RunTestGen: PostAnalysis) ;
  (module RunContractGen: PostAnalysis) ;
  (module RunRustGen: PostAnalysis) ;
  (module RunInvLog: PostAnalysis) ;
  (module RunInvPrint: PostAnalysis) ;
  (module RunCertif: PostAnalysis) ;
  (module RunIVC: PostAnalysis) ;
  (module RunMCS: PostAnalysis) ;
]

(** Runs the post-analysis things on a system and its results.

Stops analysis time count. *)
let run i_sys top analyze results =
  Stat.record_time Stat.analysis_time ;
  let post () = Stat.unpause_time Stat.analysis_time in
  try (
    let param = (Analysis.results_last top results).Analysis.param in
    post_analysis |> List.iter (
      fun m ->
        let module Module = (val m: PostAnalysis) in
        if Module.is_active () then (
          KEvent.log_post_analysis_start Module.name Module.title ;
          (* KEvent.log_uncond "Running @{<b>%s@}." Module.title ; *)
          ( try
              ( match
                  Module.run
                    i_sys (Analysis.param_clone param) analyze results
                with
                | Ok () -> ()
                | Err err -> KEvent.log L_warn "@[<v>%t@]" err
              ) ;
              KEvent.log_post_analysis_end ()
            with e ->
              KEvent.log_post_analysis_end () ;
              raise e
          ) ;
          (* Kill all solvers just in case. *)
          SMTSolver.destroy_all ()
        )
    )
  ) with e -> (
      KEvent.log L_fatal
        "Caught %s in post-analysis treatment."
        (Printexc.to_string e)
  ) ;
  post () ;
  SMTSolver.destroy_all ()

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
