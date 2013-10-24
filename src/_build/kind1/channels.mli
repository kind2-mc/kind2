(*
This file is part of the Kind verifier

* Copyright (c) 2007-2011 by the Board of Trustees of the University of Iowa, 
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


(** Global declaration of input/ouput channnels and basi printing*)

(** 
@author Jed Hagen
@author Temesghen Kahsai

*)


(** to reference th invariant produced*)
val inv_file : out_channel ref

(** to reference th invariant produced*)
val file_plus_invariant : out_channel ref

(** sent to solver 1 reference file *)
val main_ch : out_channel ref

(** sent to solver 2 reference file *)
val main2_ch : out_channel ref

(** Scratch file for the base process *)
val base_ch : out_channel ref

(** Scratch file for the inductive process *)
val induct_ch : out_channel ref

(** Scratch file for the extra check in the inductive process *)
val extra_ch : out_channel ref

(** Scratch file for the invariant generator process *)
val inv_ch : out_channel ref

(** sent to checker reference file *)
val check_ch : out_channel ref

(** For generation of XML document *)
val xml_ch : out_channel ref

(** sent to checker *)
val to_checker_ch : out_channel ref

(** Print to solver 1 *)
val to_solver_ch : out_channel ref

(** Print to solver 2 *)
val to_solver2_ch : out_channel ref

(** Print to solver 3 *)
val to_solver3_ch : out_channel ref

(** Print to solver 4 *)
val to_solver4_ch : out_channel ref

(** Print to solver 5 *)
val to_solver5_ch : out_channel ref

(** A dummy channel *)
val dummy : in_channel 

(** which channel to use for debug info (usually main_ch) *)
val debug_ch : out_channel ref

(** {6 Functions} *)

(** send a string to solver 1 channel *)
val print_to_solver : string -> unit

(** send a string to solver 2 channel *)
val print_to_solver2 : string -> unit

(** send a string to solver 3 channel *)
val print_to_solver3 : string -> unit

(** send a string to solver 4 channel *)
val print_to_solver4 : string -> unit

(** send a string to solver 5 channel *)
val print_to_solver5 : string -> unit

(** A general send string to solver *)
val send_to_solver : Types.solver_type -> string -> unit

(** send a string to checker channel *)
val print_to_checker : string -> unit

(** send a string to both solver 1 and checker channels *)
val print_to_both : string -> unit

(** send a string to both solver 2 and checker channels *)
val print_to_both2 : string -> unit


(** send a string to the user (also copied to solver 1), even in "quiet" mode ({!Flags.loud}=[false]) *)
val print_to_user_final : string -> unit

val print_to_user : string -> unit

(** send a string to the user (also copied to solver 1), if in "debug" mode({!Flags.debug}=[true]). Prepends a comment character and appends a newline. *)
val debug_to_user : string -> unit

(**  Debug information of the various processes *)
val debug_proc : Types.proc -> bool option -> string  -> unit

(** Debug list of properties in multi-prop verification *)
val debug_prop_var : Types.proc -> string list -> unit

val debug_prop_id : Types.proc -> int list -> unit

val print_xml : string -> unit
