(*
This file is part of the Kind verifier

* Copyright (c) 2007-2013 by the Board of Trustees of the University of Iowa, 
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

open Lib

(* Set of clauses *)
module T = Set.Make (Clause)

(* Type of a set of clauses *)
type t = T.t


(* Pretty-print a set of clauses *)
let rec pp_print_clauses ppf = function 
  | [] -> ()
  | c :: tl -> 
    Format.fprintf 
      ppf 
      "@[<hv>%a@]%t" 
      Clause.pp_print_clause c
      (function ppf -> if not (tl = []) then Format.fprintf ppf "@\n" else ());
    pp_print_clauses ppf tl


(* Pretty-print a set of clauses or <empty> if the set is empty *)
let pp_print_cnf ppf cnf = match (T.elements cnf) with
  | [] -> Format.fprintf ppf "<empty>"
  | clauses -> pp_print_clauses ppf clauses


(* Pretty-print a set of clauses to the standard formatter *)
let print_cnf = pp_print_cnf Format.std_formatter


let empty = T.empty

let is_empty = T.is_empty

let mem = T.mem

let add = T.add

let singleton = T.singleton

let remove = T.remove

let union = T.union

let union_subsume s1 s2 = T.union s1 s2

let inter = T.inter

let diff = T.diff

let compare = T.compare

let equal = T.equal

let subset = T.subset

let iter = T.iter

let fold = T.fold

let for_all = T.for_all

let exists = T.exists

let filter = T.filter

let partition = T.partition

let cardinal = T.cardinal

let elements = T.elements

let choose = T.choose

let of_list l = List.fold_left (fun a e -> add e a) empty l

(* Forward subsumption: [fwd_subsume c s] returns [true] if a clause
   in [s] subsumes the new clause [c] *)
let fwd_subsume c s = 
  Stat.time_fun Stat.cnf_subsume_time
    (fun () -> exists (function c' -> Clause.subset c' c) s)


(* Backward subsumption: [bwd_subsume c s] returns the set [s] with
   the clauses removed that are subsumed by the new clause [c] *)
let bwd_subsume c s = 
  Stat.time_fun Stat.cnf_subsume_time
    (fun () -> filter (function c' -> not (Clause.subset c c')) s)


(* [add_subsume c s] adds the clause [c] to the set [s] unless [c] is
   subsumed by some clause in [c] and removes all clauses from [s] that
   are subsumed by [c]. *)
let add_subsume c s = 
  if fwd_subsume c s then s else add c (bwd_subsume c s)


(* [union_subsume c1 c2] adds all clauses of [c1] to the set [c2]
   unless a clause in [c1] is subsumed by some clause in [c2] and
   removes all clauses from [c2] that are subsumed by some clause in
   [c1]. *)
let union_subsume c1 c2 = 
  fold add_subsume c2 c1 


(* Convert a set of clauses to a term *)
let to_term s = Term.mk_and (List.map Clause.to_term (T.elements s))


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
