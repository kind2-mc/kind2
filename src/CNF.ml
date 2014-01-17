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
