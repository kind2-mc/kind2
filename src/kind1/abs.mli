(*
This file is part of the Kind verifier

* Copyright (c) 2007-2009 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
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

(** Abstraction refinement strategies.  See [Kind_refine]. *)

(** {6 Functions} *)

(** Returns a list of recently refined variables. Set via [set_refined]. *)
val get_refined_step_as_well : unit -> Types.idtype list

(** Given a variable's entry in the {!Deftable.get_defhash}, sets its {!Types.abstraction_status}. *)
val set_refined : Types.idtype -> Types.defstrtype -> Types.checkindex -> Types.abstraction_status -> unit

(** Used for heuristic refinements *)
val set_def_score : Types.idtype -> int -> unit 

(** Used for heuristic refinements *)
val incr_def_score : Types.idtype -> unit

(** Return the list of dependant vaiables of a given variable. *)
val get_deplist : Types.idtype -> Types.idtype list 

(** Used for heuristic refinements *)
val compare_defs : Types.idtype -> Types.idtype -> int

(** Used for heuristic refinements *)
val rev_compare_defs : Types.idtype -> Types.idtype -> int

(** Return the {!Types.abstraction_status} of a variable *)
val get_def_status : Types.idtype -> Types.checkindex -> Types.abstraction_status

(** Returns the next unrefined variable (DFS) based on the list of starting
variables. ("basic refinement") *)
val next_unrefined_def : 
  Types.defhashtable -> Types.idtype list -> Types.checkindex -> Types.idtype list option

(** Returns the next n unrefined variable (DFS) based on the list of starting
variables. ("core refinement") *)
val next_unrefined_core_defs :
  Types.defhashtable -> Types.idtype list -> Types.checkindex -> Types.idtype list option

(** Returns the next n unrefined variable (DFS) based on the list of starting
variables. ("path refinement") *)
val next_unrefined_def_path :
  Types.defhashtable -> Types.idtype list -> Types.checkindex -> Types.idtype list option

(** Used for heuristic refinements (initialization) *)
val setup_best_scores : Types.defhashtable -> Types.idtype list -> unit

(** Returns the next n unrefined variable (best first) based on the list of 
starting variables.  Sorts all by score.  ("best-first refinement") *)
val next_unrefined_def_bfpath :
  Types.defhashtable -> Types.checkindex -> Types.idtype list option

(** Returns the next n unrefined variable (DFS variant) based on the list of 
starting variables.  Used DFS, but chooses children best-first.  ("heuristic path refinement") *)
val next_unrefined_def_hpath :
  bool -> bool -> Types.defhashtable -> Types.idtype list -> Types.checkindex -> Types.idtype list option

(** As [next_unrefined_core_defs], but gradually increase the number returned *)
val next_unrefined_defs_incr :
  Types.defhashtable -> Types.idtype list -> Types.checkindex -> Types.idtype list option

(** Return both variable and level.  Only refine variable instances specifically mentioned in analysis. *)
val next_unrefined_fine_core_defs :
  Types.defhashtable -> Types.found_ids_and_steps -> Types.found_ids_and_steps option

(** Return both variable and level.  Only refine current & future variable instances specifically mentioned in analysis. (past instances may remain unrefined) *)
val next_unrefined_hybrid_core :
  Types.defhashtable -> Types.found_ids_and_steps -> Types.checkindex -> Types.idtype list option

(** Return a full subtree of variables that have not yet been refined. *)
val next_unrefined_full_subtree :
  Types.defhashtable -> Types.idtype list -> Types.checkindex -> Types.idtype list option
