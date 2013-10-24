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

(** Various support functions *)

(** This attempts to print out a longer formula to the solvers, ensuring
    that OS pipe limitations are not exceeded *)
val print_to_both_limited : in_channel -> in_channel -> in_channel -> string -> unit

(** Print all the definitions in to solver 2 and solver 3 *)
val  print_defs_to_solver1 : in_channel -> in_channel -> string -> unit

(** Print all the definitions in to solver 2*)
val print_defs_to_solver2 : in_channel -> in_channel -> string -> unit

(** Print all the definitions in to solver 3*)
val print_defs_to_solver3 : in_channel -> in_channel -> string -> unit

(** Print all the definitions in to solver 4*)
val print_defs_to_solver_bmc_checker : in_channel  -> string -> unit

(** Print all the definitions in to solver 5*)
val print_defs_to_solver_induct_checker : in_channel -> string -> unit

(** Prints the current counterexample, from step x to step y *)
val print_countermodel : Types.foundvarstable -> int -> int -> unit

(** Saves the current counterexample *)
val save_countermodel : Types.foundvarstable -> int -> int -> string

(** Print header for XML document *)
val print_header_xml : string -> string

(** Print the result in XML format *)
val print_resultProp_xml : Types.xml_result -> string

(** Check to see if any assignments are "bad" *)
val check_for_bad_assignments : in_channel -> Types.foundvarstable -> Types.idtype list -> int -> bool

(** Query the checker to see if a counterexample is spurious *)
val query_checker : in_channel -> Types.foundvarstable -> Types.check_type -> int -> Types.checker_return

(** Definition assertion for initilization of main loop. *)
val def_assert_initial : Types.defhashtable -> string -> Types.addtype -> Types.idtype -> unit

(** Print out definition assertion initializations for a single variable *)
val print_initialization_single : Types.defhashtable -> int -> Types.addtype -> Types.idtype -> unit

(** Assert a variable definition to both solver 1 and checker. *)
val def_assert_both1 : Types.defhashtable -> string -> Types.paramtype -> int -> in_channel -> unit

(** Assert a variable definition to both solver 2 and checker. *)
val def_assert_both2 : Types.defhashtable -> string -> Types.paramtype -> int -> in_channel -> unit

(** Assert a variable definition to both solver 2 and checker. *)
val def_assert_both3 : Types.defhashtable -> string -> Types.paramtype -> int -> in_channel -> unit

(** Assert a variable definition to both solver 2 and checker. *)
val def_assert_both4 : Types.defhashtable -> string -> Types.paramtype -> int -> in_channel -> unit

(** Assert a variable definition to both solver 2 and checker. *)
val def_assert_both5 : Types.defhashtable -> string -> Types.paramtype -> int -> in_channel -> unit

(** Note when the last assertion was made *)
val set_last_level_asserted : int -> unit

(** Assertions to solver 1 & checker following a successful inductin step check *)
val persistent_step_asserts_concrete : Types.defhashtable -> int -> Types.addtype -> int -> in_channel -> unit

(** Assertions to solver 4 & checker following a successful inductin step check *)
val persistent_assert_bmc : Types.defhashtable -> int -> Types.addtype -> int -> in_channel -> unit

(** Assertions to solver 3 & checker following a successful inductin step check *)
val persistent_step_asserts_concrete_inv : Types.defhashtable -> int -> Types.addtype -> int -> in_channel -> unit

(** Assertions to solver 2 & checker following a successful inductin step check *)
val persistent_step_asserts_symbolic : Types.defhashtable -> int -> Types.addtype -> int -> in_channel -> unit

(** Assertions to solver 2 after following a successful inductin step check *)
val asserts_inductive: Types.defhashtable -> int -> Types.addtype -> int -> in_channel -> unit

(** Assertions for a single variable following a successful base or induction step check *)
val persistent_step_single_assert : Types.defhashtable -> int -> Types.addtype -> Types.check_type -> int -> Types.idtype -> unit

(** Assertions for a single variable at a single level ([k] step) as part of a refinement process *)
val persistent_step_single_level_assert : Types.defhashtable -> int -> Types.addtype -> Types.check_type -> int -> Types.idtype -> int -> unit

(** Print out definitions as part of (re-)initialization of the main loop *)
val print_initialization : Types.defhashtable -> int -> Types.addtype -> in_channel -> unit

(** Print initialization of TS, given a solver *)
val print_init : int -> Types.defhashtable -> int -> Types.addtype -> in_channel -> unit 

(** Print out some generic info about the current configuration *)
val print_stat_headers : unit -> unit

(** translate {!Flags.do_negative_index} to a [1] or [-1] to acount for positive or negative indices *)
val get_add : unit -> Types.addtype 

(** Open channels to the solvers.  Returns their input channels *)
val setup_channels : unit -> in_channel * in_channel * in_channel

(** Open channels to the solvers.  Returns their input channels. SOLVER 1 *)
val setup_solver1 : unit -> in_channel * in_channel

(** Open channels to the solvers.  Returns their input channels. SOLVER 2 *)
val setup_solver2 : unit -> in_channel * in_channel

(** Open channels to the solvers.  Returns their input channels. SOLVER 3 *)
val setup_solver3 : unit -> in_channel * in_channel

(** Open channels to the solvers.  Used for the BMC extra checker *)
val setup_solver_bmc_checker : unit -> in_channel * in_channel

(** Open channels to the solvers.  Used for the BMC extra checker *)
val setup_solver_induct_checker : unit -> in_channel * in_channel

(** Open channels to the solvers.  Returns their input channels. SOLVER 4 and 5 for the incaremental invariant solver *)
val setup_channels_inv : unit -> in_channel * in_channel * in_channel 

