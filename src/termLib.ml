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

(*

type invariants = Term.t list

type property = (string * Term.t)
type properties = property list
type cex = (property list * Model.path)
type cexs = cex list

*)


(* ********************************************************************** *)
(* Properties of transition systems                                       *)
(* ********************************************************************** *)

(* Source of a property *)
type prop_source =

  (* Property is from an annotation *)
  | PropAnnot of position

  (* Property is part of a contract *)
  | Contract of position

  (* Property was generated, for example, from a subrange
     constraint *)
  | Generated of StateVar.t list

  (* Property is an instance of a property in a called node

     Reference the instantiated property by the [scope] of the
     subsystem and the name of the property *)
  | Instantiated of string list * string 


(* Return the default value of the type *)
let default_of_type t = 

  match Type.node_of_type t with

    (* Booleans are false by default *)
    | Type.Bool -> Term.t_false

    (* Integers are zero by default *)
    | Type.Int -> Term.mk_num Numeral.zero

    (* Integer range values are their lower bound by default *)
    | Type.IntRange (l, _) -> Term.mk_num l

    (* Reals are zero by default *)
    | Type.Real -> Term.mk_dec Decimal.zero

    (* No defaults for scalars and arrays *)
    | Type.Scalar _
    | Type.Array _ -> invalid_arg "default_of_type"


