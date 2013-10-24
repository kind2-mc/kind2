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

(** Subclass of {!Solver_base.solver_base} *)

(** The Yices wrapper solver interface object *)
  class solver_yices :
    object
      val assertion_hash : (int, Types.idtype * int) Hashtbl.t
      val mutable current_n_value : int option
      method aggdef_header : Buffer.t -> Buffer.t -> unit
      method assert_buffer : Buffer.t -> Buffer.t -> unit
      method assert_plus_buffer : Buffer.t -> Buffer.t -> unit
      method assert_plus_string : string -> string
      method assert_string : string -> string
      method assertions : string
      method assertions_inv : string
      method b_and_string : string
      method b_iff_string : string
      method b_impl_string : string
      method b_not_string : string
      method b_or_string : string
      method b_xor_string : string
      method boolean_connectives_strictly_binary : bool
      method buffer_of_binary :
        Buffer.t -> string -> Buffer.t -> Buffer.t -> unit
      method buffer_of_ite :
        Buffer.t -> Buffer.t -> Buffer.t -> Buffer.t -> unit
      method buffer_of_list_op : Buffer.t -> string -> Buffer.t list -> unit
      method buffer_of_nary : Buffer.t -> string -> Buffer.t list -> unit
      method buffer_of_num : Buffer.t -> int -> unit
      method buffer_of_pred : Buffer.t -> string -> Buffer.t list -> unit
      method buffer_of_record : Buffer.t -> (string * Buffer.t) list -> unit
      method buffer_of_record_ref : Buffer.t -> Buffer.t -> string -> unit
      method buffer_of_tuple : Buffer.t -> Buffer.t list -> unit
      method buffer_of_tuple_ref : Buffer.t -> Buffer.t -> int -> unit
      method buffer_of_unary : Buffer.t -> string -> Buffer.t -> unit
      method can_redefine : bool
      method cc : string
      method checker_setup_string : string
      method define_fun_buffer : Buffer.t -> string -> Types.lustre_type ->
        (string * Types.lustre_type) list -> Buffer.t -> unit
      method define_var_string : string -> Types.lustre_type -> string
      method define_const_string : string -> Types.lustre_type -> string
       method define_trans: Buffer.t -> string list -> Buffer.t
      method div_string : string
      method done_string : string
      method eq_string : string
      method neq_string : string
      method f_and_string : string
      method f_eq_string : string
      method f_iff_string : string
      method f_impl_string : string
      method f_not_string : string
      method f_or_string : string
      method false_string : string
      method file_extension : string
      method fresh_varname_string : string -> int -> string
      method get_assert_id : string -> Types.idtype -> int -> unit
      method get_countermodel : string -> (string -> unit) -> in_channel -> Types.foundvarstable
      method get_simulation_value_hash : string -> (string -> unit) -> in_channel -> (string, string) Hashtbl.t
      method get_cex : Types.proc -> string -> (string -> unit) -> in_channel -> Types.foundvarstable
      method get_simulation_cex : Types.proc -> string -> (string -> unit) -> in_channel -> (string, string) Hashtbl.t
      method get_current_n_value : int option
      method get_output : in_channel -> string
      method get_solver_output : Types.proc -> in_channel -> string
      method get_unsat_core : string -> (string -> unit) -> in_channel -> (Types.idtype * int) list
      method gt_string : string
      method gte_string : string
      method header_string : string
      method intdiv_string : string
      method k_position_string : string
      method lt_string : string
      method lte_string : string
      method minus_string : string
      method mod_string : string
      method mult_string : string
      method one_string : string
      method plus_string : string
      method pop_string : string
      method position_var1 : string
      method position_var2 : string
      method property_header : string -> string -> string
      method property_header_new : string -> string -> string
      method push_string : string
      method query_buffer : Buffer.t -> Buffer.t -> unit
      method result_is_error : string -> bool
      method result_is_sat : string -> bool
      method result_is_unknown : string -> bool
      method result_is_unsat : string -> bool
      method safe_pop : string
      method safe_push : string
      method solver_call : string -> string
      method state_vars : string
      method state_vars_r : string
      method step_base_string : string
      method string_of_binary : string -> string -> string -> string
      method string_of_ite : string -> string -> string -> string
      method string_of_list_op : string -> string list -> string
      method string_of_nary : string -> string list -> string
      method string_of_num : int -> string
      method string_of_record : (string * string) list -> string
      method string_of_record_ref : string -> string -> string
      method string_of_tuple : string list -> string
      method string_of_tuple_ref : string -> string -> string
      method string_of_unary : string -> string -> string
      method string_of_var_ref : string -> string -> string
      method supports_unary_minus : bool
      method term_impl_available : bool
      method true_string : string
      method type_string : Types.lustre_type -> Types.typename
      method uminus_string : string
      method zero_string : string
    end

