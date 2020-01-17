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

(** Signature of modules for post-analysis treatment. *)
module type PostAnalysis = sig
  (** Name of the treatment. (For xml logging.) *)
  val name: string
  (** Title of the treatment. (For plain text logging.) *)
  val title: string
  (** Indicates whether the module is active. *)
  val is_active: unit -> bool
  (** Performs the treatment.

  Note that the [param] passed is not exactly the one used for the analysis.
  The uid of the [param] was changed so that it is safe to use it to generate
  systems. (No name clashes.) *)
  val run:
    (** Input system. *)
    'a InputSystem.t ->
    (** Analysis parameter. *)
    Analysis.param ->
    (** A function running an analysis with some modules. *)
    (
      bool -> Lib.kind_module list -> 'a InputSystem.t -> Analysis.param -> TransSys.t
      -> unit
    ) ->
    (** Results for the current system. *)
    Analysis.results
    (** Can fail. *)
    -> unit Res.res
end

module RunTestGen: PostAnalysis
module RunContractGen: PostAnalysis
module RunRustGen: PostAnalysis
module RunInvLog: PostAnalysis
module RunInvPrint: PostAnalysis
module RunCertif: PostAnalysis
module RunIVC: PostAnalysis
module RunMUA: PostAnalysis

(** Runs the post-analysis things on a system and its results. *)
val run: 'a InputSystem.t -> Scope.t ->
    (** A function running an analysis with some modules. *)
    (
      bool -> Lib.kind_module list -> 'a InputSystem.t -> Analysis.param -> TransSys.t
      -> unit
    ) ->
    Analysis.results -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
