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

(** A result for some type. *)
type 'a res =
(** Everything went fine. *)
| Ok of 'a
(** There was a problem. *)
| Err of (Format.formatter -> unit)

(** Unwraps a result. *)
val unwrap : 'a res -> 'a

(** Maps functions to [Ok] or [Err]. *)
val map_res: ('a -> 'b) -> (
  (Format.formatter -> unit) -> Format.formatter -> unit
) -> 'a res -> 'b res

(** Maps a function to a result if it's [Ok]. *)
val map: ('a -> 'b) -> 'a res -> 'b res

(** Maps a function to a result if it's [Err]. *)
val map_err: (
  (Format.formatter -> unit) -> Format.formatter -> unit
) -> 'a res -> 'a res

(** Feeds a result to a function returning a result, propagates if argument's
an error. *)
val chain: ?fmt:(
  (Format.formatter -> unit) -> Format.formatter -> unit
) -> ('a -> 'b res) -> 'a res -> 'b res

(** Fold over a list of results. *)
val l_fold: ?fmt:(
  (Format.formatter -> unit) -> Format.formatter -> unit
) -> ('acc -> 'a -> 'acc res) -> 'acc -> 'a list -> 'acc res

(** Map over a list with a result-producing function. *)
val l_map: ?fmt:(
  (Format.formatter -> unit) -> Format.formatter -> unit
) -> ('a -> 'b res) -> 'a list -> 'b list res

(** Iterate over a list with a result-producing function. *)
val l_iter: ?fmt:(
  (Format.formatter -> unit) -> Format.formatter -> unit
) -> ('a -> unit res) -> 'a list -> unit res

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)