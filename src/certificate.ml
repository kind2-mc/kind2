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


(* The type of certificates *)
type t = int * Term.t

(* Merge certificates into one. The resulting certificate is a certificate for
   the conjunction of the original invariants. *)
let merge certs =
  let km, l =
    List.fold_left (fun (km, l) (k, phi) ->
        max k km, if List.exists (Term.equal phi) l then l else phi :: l
      ) (0, []) certs in
  km, Term.mk_and (List.rev l)


let s_and = Symbol.mk_symbol `AND

(* Split top level conjunctions in a given invariant. *)
let rec split_inv inv =
  match Term.destruct inv with
  | Term.T.App (s, l) when s == s_and ->
    List.flatten (List.map split_inv l)
  | _ -> [inv]

(* Split a certificate following the boolean strucutre of its inductive
   invariant *)
let split (k, c) = List.map (fun c' -> k, c') (split_inv c)

(* Split a list of certificates *)
let split_certs certs =
  List.fold_left (fun acc i ->
      List.rev_append (split i) acc
    ) [] certs


(* Gives a measure to compare the size of the inductive invariants contained in
    a certificate. *)
let size (_, inv) = List.length (split_inv inv)
