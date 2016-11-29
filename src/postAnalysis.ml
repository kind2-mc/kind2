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

module TestGen = TestgenDF
module Num = Numeral
module TSys = TransSys
module ISys = InputSystem

module SSet = StateVar.StateVarSet

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
        match InputSystem.maximal_abstraction_for_testgen in_sys top [] with
        | None -> Err (
          fun fmt ->
            Format.fprintf fmt
              "System %a has no contracts, skipping test generation."
              fmt_sys sys
        )
        | Some param -> Ok param
      )

  let is_active () = Flags.Testgen.active ()
  let run in_sys param results =
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
        let param = match param with
          | Analysis.ContractCheck info -> Analysis.ContractCheck {
            info with Analysis.uid = info.Analysis.uid * 10000
          }
          | Analysis.First info -> Analysis.First {
            info with Analysis.uid = info.Analysis.uid * 10000
          }
          | Analysis.Refinement (info, res) -> Analysis.Refinement (
            { info with Analysis.uid = info.Analysis.uid * 10000 },
            res
          )
        in

        (* Extracting transition system. *)
        let sys, input_sys_sliced =
          InputSystem.trans_sys_of_analysis
            ~preserve_sig:true in_sys param
        in

        (* Let's do this. *)
        try (
          let tests_target = Format.sprintf "%s/%s" target Paths.testgen in
          mk_dir tests_target ;
          Event.log_uncond
            "%sGenerating tests for node \"%a\" to `%s`."
            TestGen.log_prefix Scope.pp_print_scope top tests_target ;
          let testgen_xmls =
            TestGen.main param input_sys_sliced sys tests_target
          in
          (* Yay, done. Killing stuff. *)
          TestGen.on_exit "yay" ;
          (* Generate oracle. *)
          let oracle_target = Format.sprintf "%s/%s" target Paths.oracle in
          mk_dir oracle_target ;
          Event.log_uncond
            "%sCompiling oracle to Rust for node \"%a\" to `%s`."
            TestGen.log_prefix Scope.pp_print_scope top oracle_target ;
          let name, guarantees, modes =
            InputSystem.compile_oracle_to_rust in_sys top oracle_target
          in
          Event.log_uncond
            "%sGenerating glue xml file to `%s/.`." TestGen.log_prefix target ;
          testgen_xmls
          |> List.map (fun xml -> Format.sprintf "%s/%s" Paths.testgen xml)
          |> TestGen.log_test_glue_file
            target name (Paths.oracle, guarantees, modes) Paths.implem ;
          Event.log_uncond
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
  let run in_sys param results =
    let top = (Analysis.info_of_param param).Analysis.top in
    Event.log L_warn
      "Contract generation is a very experimental feature:@ \
      in particular, the modes it generates might not be exhaustive,@ \
      which means that Kind 2 will consider the contract unsafe.@ \
      This can be dealt with by adding a wild card mode:@ \
      mode wildcard () ;" ;
    (* Building transition system and slicing info. *)
    let sys, in_sys_sliced =
      ISys.contract_gen_trans_sys_of ~preserve_sig:true in_sys param
    in
    let target = Flags.subdir_for top in
    (* Create directories if they don't exist. *)
    Flags.output_dir () |> mk_dir ;
    mk_dir target ;
    let target =
      Format.asprintf "%s/kind2_contract.lus" target
    in
    LustreContractGen.generate_contracts
      in_sys_sliced param sys target ;
    Ok ()
end

(** Rust generation.
Compiles lustre as Rust. *)
module RunRustGen: PostAnalysis = struct
  let name = "rustgen"
  let title = "rust generation"
  let is_active () = Flags.lus_compile ()
  let run in_sys param results =
    Event.log L_warn
      "Compilation to Rust is still a rather experimental feature:@ \
      in particular, arrays are not supported." ;
    let top = (Analysis.info_of_param param).Analysis.top in
    let target = Flags.subdir_for top in
    (* Creating directories if needed. *)
    Flags.output_dir () |> mk_dir ;
    mk_dir target ;
    (* Implementation directory. *)
    let target = Format.sprintf "%s/%s" target Paths.implem in
    Event.log_uncond
      "  Compiling node \"%a\" to Rust in `%s`."
      Scope.pp_print_scope top target ;
    InputSystem.compile_to_rust in_sys top target ;
    Event.log_uncond "  Done compiling." ;
    Ok ()
end

(** Invariant log.
Minimizes and logs invariants used in the proof. *)
module RunInvLog: PostAnalysis = struct
  let name = "invlog"
  let title = "invariant logging"


  let is_active () = Flags.log_invs ()
  let run in_sys param results =
    let top = (Analysis.info_of_param param).Analysis.top in
    let target = Flags.subdir_for top in
    (* Create directories if they don't exist. *)
    Flags.output_dir () |> mk_dir ;
    mk_dir target ;
    let target =
      Format.asprintf "%s/kind2_strengthening_contract.lus" target
    in
    last_result results top
    |> Res.chain (fun { Analysis.sys } ->
      (* Returns [false] iff term passed mentions node call svars. *)
      let _, node_of_scope =
        InputSystem.contract_gen_param in_sys
      in
      let node = node_of_scope top in
      let nice_invariants term =
        Term.state_vars_of_term term
        |> SSet.exists (
          fun svar -> try (
            match
              StateVar.StateVarMap.find
                svar node.LustreNode.state_var_source_map
            with
            | LustreNode.Call -> true
            | _ -> false
          ) with Not_found -> true
        )
        |> not
      in
      try (
        let k_min, invs_min =
          TSys.invars_of_bound sys Num.zero
          |> List.filter nice_invariants
          |> fun a -> Some a
          |> CertifChecker.minimize_invariants sys
        in
        Format.printf "Minimization result:@.  @[<v>min k: %d@ %d min invs@]@."
          k_min (List.length invs_min) ;
        Ok (sys, k_min, invs_min)
      ) with _ -> Err (
        fun fmt ->
          Format.fprintf fmt
            "Some necessary invariants cannot be translated \
            back to lustre level."
      )
    )
    |> Res.map (fun (sys, _, invs) ->
      LustreContractGen.generate_contract_for
        in_sys param sys target invs
    )
end

(** Invariant log.
Certifies the last proof. *)
module RunCertif: PostAnalysis = struct
  let name = "certification"
  let title = name
  let is_active () = Flags.Certif.certif ()
  let run in_sys param results =
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

(** List of post-analysis modules. *)
let post_analysis = [
  (module RunTestGen: PostAnalysis) ;
  (module RunContractGen: PostAnalysis) ;
  (module RunRustGen: PostAnalysis) ;
  (module RunInvLog: PostAnalysis) ;
  (module RunCertif: PostAnalysis) ;
]

(** Runs the post-analysis things on a system and its results. *)
let run i_sys param results =
  post_analysis |> List.iter (
    fun m ->
      let module Module = (val m: PostAnalysis) in
      if Module.is_active () then (
        Event.log_post_analysis_start Module.name Module.title ;
        (* Event.log_uncond "Running @{<b>%s@}." Module.title ; *)
        try
          ( match Module.run i_sys param results with
            | Ok () -> ()
            | Err err -> Event.log L_warn "@[<v>%t@]" err
          ) ;
          Event.log_post_analysis_end ()
        with e ->
          Event.log_post_analysis_end () ;
          raise e
      )
  )

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)