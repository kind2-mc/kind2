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

(* all exceptions *)

open Types

(* lus_convert.ml *)
exception ConversionError of string
exception IdNotFound of string
exception Def_Not_Found of int
exception SimplifyPositionException
exception COIException
exception TypeMismatch of string * lustre_type * lustre_type
exception IncorrectTypedConversion of string
exception NotSupportedType
exception TooManyOutputs
exception NoStatefulVars
exception AllStatefulVarsRefined
exception Reachable_space_explored


(* kind_support.ml *)
exception Error_found of string
exception Timeout
exception Incomplete_code of string
exception RefineAbstraction of check_type
exception No_next_refinement_step
exception Reachable_space_explored
exception SolverError of string
exception UNSAT_FOUND


(* coi.ml *)
exception Incorrect_formula
exception Expr_not_supported
exception Redefinition
exception EmptyLHS


(* defgen.ml *)
exception Lus_convert_error
exception Unguarded_PRE

(* inlining.ml, structural.ml  *)
exception Not_supported of string


(* Invariant generation *)

exception EQUIV_CLS_STABLE
exception SOLVER_ERROR

(* parallel kind *)
exception Wrong_number_of_proc of int * int
