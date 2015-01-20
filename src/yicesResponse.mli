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

type yices_id

type yices_resp_p =
  | YNoResp
  | YSuccess
  | YCustom of string
  | YError
  | YRespSat of (HStringSExpr.t * HStringSExpr.t) list
  | YRespUnknown of (HStringSExpr.t * HStringSExpr.t) list
  | YRespUnsat of (yices_id list)


val success : string

val custom : string


val yices_id_of_int : int -> yices_id

val int_of_yices_id : yices_id -> int

val pp_print_yices_id : Format.formatter -> yices_id -> unit

