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

(** Types used in KIND. 
*  Ocaml types used elsewhere. 
*)

(**
@author Jed Hagen 
@author Temesghen Kahsai
*)

(* how we are identifying variables *)

(** The type of an internal variable identifier *)
type idtype = int

(** Type for user-defined types *)
type typename = string

(** Type for record field identifiers *)
type fieldname = string

(** This is used to (try to) be consistent with indexing. The value should
be +/-1 only.  It is multiplied against the current position index. *)
type addtype = int

(** Used to be able to keep the current name of a variable. *)
type mutable_string = {mutable s:string}

(** Type of identifiers for nodes. *)
type node_id_t = int

(** Used to modify translation (mostly how relative positions are handled).
Currently only [GENERAL] and [STATE_VARS_GEN] are used. *)
type modetype =
  | GENERAL (** general case, used in step case only *)
  | STATE_VAR_GEN (** general case for state var defs only *)
  | FRESH_INPUTS of int (** general case but with fresh input vars *)
  | N_STEP (** general case with n > maxdepth, used in both cases *)
  | DEPTH of int (** n <= maxdepth, used in base case only *)

(** Types for terms in the formulas -- mostly for typechecking and some translation. [L]-types are native Lustre types (and some extensions).  [M]-types are
used to generate the various meta-formulas in a consistent fashion. *)
type lustre_type =
  | L_INT
  | L_REAL
  | L_BOOL (** term boolean *)
  | L_TUPLE of lustre_type list
  | L_RECORD of (fieldname*lustre_type) list
  | L_TYPEDEF of typename
  | L_INT_RANGE of int * int
  | L_UNDET (* used for nodes *)
  | M_BOOL (** formula boolean (CVC3 differentiates these) *)
  | M_NAT (** meta-type for natural numbers *)
  | M_FUNC of lustre_type list (* meta-type for funcs -- arrow typelist *)

(** the general classification of a variable (input,output,etc) *)
type varclass =
  | INPUT
  | OUTPUT
  | LOCAL
  | ABSTRACT (** is also LOCAL *)
  | STATE of int (** state var indexed at depth x *)

(** Stream (lustre) expressions.  Not all are supported yet. Used in parser and lus_convert.ml *)
type streamterm =
  | S_AND of typed_stream * typed_stream
  | S_OR of typed_stream * typed_stream
  | S_XOR of typed_stream * typed_stream
  | S_IMPL of typed_stream * typed_stream
  | S_ATMOSTONE of typed_stream list
  | S_NOT of typed_stream
  | S_ITE of typed_stream * typed_stream * typed_stream
  | S_EQ of typed_stream * typed_stream
  | S_LT of typed_stream * typed_stream
  | S_LTE of typed_stream * typed_stream
  | S_GT of typed_stream * typed_stream
  | S_GTE of typed_stream * typed_stream
  | S_PLUS of typed_stream * typed_stream
  | S_MINUS of typed_stream * typed_stream
  | S_UMINUS of typed_stream
  | S_MULT of typed_stream * typed_stream
  | S_DIV of typed_stream * typed_stream
  | S_INTDIV of typed_stream * typed_stream
  | S_MOD of typed_stream * typed_stream
  | S_COERCE_TO_INT of typed_stream
  | S_COERCE_TO_REAL of typed_stream
  | S_PRE of typed_stream
  | S_FBY of typed_stream * int * typed_stream (** expr, num steps, init value *)
  | S_FOLLOWEDBY of typed_stream * typed_stream
  | S_WHEN of typed_stream * typed_stream
  | S_CURRENT of typed_stream
  | S_CONDACT of typed_stream * typed_stream * typed_stream * typed_stream (** clock, expression, defaults, backreference *)
  | S_TUPLELIT of typed_stream list
  | S_TUPLEREF of typed_stream * int
  | S_RECORDLIT of (fieldname * typed_stream) list
  | S_RECORDREF of typed_stream * fieldname
  | S_VAR of string * int (** name_string (a), id (k) *)
  | S_NODE of node_id_t * int * int * typed_stream list (** name, line num, pos num, parameters *)
  | S_TRUE
  | S_FALSE
  | S_INT of int
  | S_REAL of int * int * int (** integer,numerator,denominator (because solvers don't deal with floats) *)
  | S_DEF of node_id_t * typed_stream * typed_stream (** node id, lustre constraint definitions *)
  | S_ASSERT of node_id_t * typed_stream (** from ASSERT statements *)
  | S_PROPERTY of node_id_t * typed_stream (** user-marked properties *)
and typed_stream = streamterm * lustre_type

(** inputs,outputs,S_DEFS. These define a node. *)
type lustre_node = 
  (int*lustre_type) list * (int*lustre_type) list * typed_stream list

(** Relations *)
type relation =
   EQ
 | LT
 | GT
 | LTE
 | GTE
 | NEQ

(** IL-type intermmediate forms. *)
type il_expression =
  | ZERO (** term false *)
  | ONE (** term true *)
  | STEP_BASE
  | POSITION_VAR of string
  | INT_CONST of il_expression  
  | REAL_CONST of il_expression * float
  | STRING of string (* input variables, etc. *)
  | NUM of int
  | FLOAT of float
  | PLUS of il_expression * il_expression
  | MINUS of il_expression * il_expression
  | MULT of il_expression * il_expression
  | DIV of il_expression * il_expression
  | INTDIV of il_expression * il_expression
  | MOD of il_expression * il_expression
  | UMINUS of il_expression
  | REL of relation * il_expression * il_expression
  | ITE of il_expression * il_expression * il_expression
  | STREAM_ITE of il_expression * il_expression * il_expression (** (i,a,b) : if p=base-i then a else b *)
  | B_AND of il_expression * il_expression (** term and *)
  | B_OR of il_expression * il_expression (** term or *)
  | B_IFF of il_expression * il_expression (** term iff *)
  | B_IMPL of il_expression * il_expression (** term => *)
  | B_NOT of il_expression (** term not *)
  | VAR_GET of mutable_string * int * il_expression * il_expression (** symbol, depth, id, position *) 
  | RECORD_LIT of (string * il_expression) list
  | RECORDREF of il_expression * string
  | TUPLE_LIT of il_expression list
  | TUPLEREF of il_expression * int
  | PRED of string * il_expression list (** used when comparing symbolic positions *)

(** Intermediate IL-type formulas *)
and il_formula = 
  | F_TRUE (** formula false *)
  | F_FALSE (** formula true *)
  | F_STR of string
  | F_NOT of il_formula (** formula not *)
  | F_EQ of il_expression * il_expression * lustre_type (** equality at formula level *)
  | F_AND of il_formula * il_formula (** formula and *)
  | F_OR of il_formula * il_formula (** formula or *)
  | F_IMPL of il_formula * il_formula (** formula => *)
  | F_PRED of string * il_expression list (** formula-level predicate *)
(*  | F_TERM of il_expression (** By yeting, for simplicity *)*)
    
(** For variable & function declaration commands *)
type var_decl = string * lustre_type

(** Solver commands used *)
type solver_command =
  | PUSH
  | POP
  | DEFINE_VAR of var_decl
  | DEFINE_FUN of var_decl * var_decl list * il_formula (* name*type, lambda vars, formula *)
  | QUERY of il_formula
  | ASSERT of il_formula
  | ASSERT_PLUS of il_formula
 

(** Current status of a variable X's refinement *)
type abstraction_status =
    NOT_REFINED (** Abstracted *)
  | SUBTREE_DONE (** X and all children have been refined (or inputs) *)
  | REFINED of int (** Was refined at level n *)
  | REFINED_MORE of int*int (** old, new : Had been refined at old, refined again at new *)

(** Function parameters *)
type paramtype = il_expression list 

(** Stores a list of variable ids and a buffer representation of the translated definition, or else a reference to the appropriate LHS (if the variable was
unified).  *)
type defstrtype =
  {
    mutable abstr: abstraction_status array; (** Current abstraction status *)
    mutable score: int; (** Some score for heuristics (connecedness?) *)
    mutable score2: int; (** Some other score for heuristics (distance from leaf?) *)
    mutable stamp: int; (** Used in refinement process for coloring *)
    def: Buffer.t; (** The translated definition (RHS) *)
    deps: idtype list; (** variable ids that appear in the definition *)
    dep_offsets: (idtype*int) list (** dependent id & level offset (?) *)
  }

(** the defhash contains either a defintion string or a reference to another entry *)
type defhashtype =
    DEF_STR of defstrtype
  | DEF_REF of int

(** holds the variables definitions *)
type defhashtable = (idtype,defhashtype)Hashtbl.t

(** which solver are we using? *)
type solvertype = YICES | YICES_WRAPPER | CVC3 | Z3 | CVC4

(** Return value from the checker *)
type checker_return = CHECK_VALID 
                    | CHECK_INCORRECT of (idtype*int) list (** Core: id, level list *)

(** Refinement result *)
type refine_return  = CHECK_IS_VALID 
                    | CHECK_IS_INVALID of idtype list (** conflics: id, level list *)

(** which induction step are we in? *)
type check_type = BASE_INIT | BASE | STEP

(** Used to index which abstraction to use: 0=base or 1=step *)
type checkindex = int

(** Type for the main symbol table.
id: nodeid,string_representation,type,input/output/etc 
 *)
type varinfo_table = (int,node_id_t*string*lustre_type*varclass)Hashtbl.t

(** Entry type for the table keeping track of which variables are actually used. The expression is used for substitutions for inlining.  It is in the form [NUM k], where [k] is the id of the variable that replaces this one.  depths are the depths at which this variable was encountered. These are updated as part of
{!Lus_convert_yc.yc_expr_buffer}. *)
type used_vars_type = { ex : il_expression; mutable depths : int list}

(** This is used to return the variables found by the solvers. *)
type foundvarstable = (idtype * int, string) Hashtbl.t

(** List of ids and the position at which they were found to conflict *)
type found_ids_and_steps = (idtype * int) list

(** function used to output to some channel *)
type printout_fun = (out_channel -> unit)

(** Table used in the renaming of subnode expressions. *)
type transtable = (idtype, idtype) Hashtbl.t

(** Different processes *)
type proc = BASE_PROC | INDUCT_PROC | INV_GEN_PROC

(** Different property result *)
type prop_result = VALID | UNKNOWN | INVALID | INDUCT_CEX | TIMEOUT

(** Different solver type *)
type solver_type = BMC | INDUCT | BASE_CHECK | INDUCT_CHECK | INVR

(** Solver result*)
type solver_result = SAT | UNSAT | ERROR 

(** A type for printing results in XML format*)
type xml_result = 
    {
      result : prop_result;
      foundvars : foundvarstable option;
      minstep : int option;
      maxstep: int option;
      induct_cex:string option;
      name : string;
      k: string;
      time:string;
    }

(** A wrapper for various variables for the base/induct process *)
type base_solver_t =
    {
      cur_depth: int;
      startdepth : int;
      add: int;
      nstart: string;
      nvar:string;
      no_stateful:bool;
      from_solver_ch: in_channel;
      from_solver2_ch: in_channel;
      from_checker_ch: in_channel;
      def_hash : defhashtable;
      pvars : idtype list;
      prop_list : typed_stream list;
      defdoc: string;
    }



(* Message types comunicated between processes*)
type par_msg = 
    VALID_STEP of int  (*Step is valid*)
  | VALID_BASE of int  (*Base is valid*)
  | STOP           (* In case a cex is found, stop to be communicated to the inductive  process*)
  | STOP_INDUCT of string * string (* In case we want to send the cex for printing in case we have -induct_cex enabled*)
  | K_FROM_STEP of int  (*K from step process*)
  | INV_FULL of string  (*Actual invariant*)
  | INV  (*A message that an invariant has been produced*) 
  | M_STEP_VALID of string list * string list * string list * int  (* used to communicate a list of properties from the inductive step to the base processes *)
  | M_STEP_INVALID of string list  (* used to communicate a list of properties from the base processes to the inductive processes *)
