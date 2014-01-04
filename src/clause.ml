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


(* Abbreviation for module name *)
module T = Term.TermSet


(* A clause is a set of terms *)
type t = T.t


(* Construct a clause of a set of literals *)
let of_literals l = 
  List.fold_left (fun a e -> T.add e a) T.empty l


(* Return the literals of a set of disjuncts *)
let rec literals_of_term accum = function 

  (* All disjuncts processed, return accumulator *)
  | [] -> accum 

  (* Take the first potential [h] disjunct and its polarity [p] *)
  | (p, t) :: tl -> 

    (* Flatten disjunct *)
    match Term.T.destruct t with 

      (* Term is a negation *)
      | Term.T.App (s, [t]) when s == Symbol.s_not -> 

        (* Get literals from positive term with opposite polarity *)
        literals_of_term accum ((not p, t) :: tl)

      (* Term is a disjunction with positive polarity *)
      | Term.T.App (s, l) when s == Symbol.s_or && p -> 

        (* Get the literals from each disjunct *)
        literals_of_term 
          accum 
          ((List.map (function e -> (true, e)) l) @ tl)
(*
      (* Disjunction with negative polarity is not a clause *)
      | Term.T.App (s, _) when s == Symbol.s_or -> 
        invalid_arg "of_term: not a clause" 
*)
      (* Term is a conjunction with negative polarity *)
      | Term.T.App (s, l) when s == Symbol.s_and && not p -> 

        (* Get the literals from each conjunct *)
        literals_of_term 
          accum 
          ((List.map (function e -> (false, e)) l) @ tl)
(*
      (* Conjunction with positive polarity is not a clause *)
      | Term.T.App (s, _) when s == Symbol.s_and -> 
        invalid_arg "of_term: not a clause" 
*)
      (* Term is neither conjunction nor disjunction and has negative
         polarity *)
      | _ when not p -> 

        (* Term must be a Boolean atom *)
        (* assert (Term.is_atom t); *)

        (* Add term to literals *)
        literals_of_term ((Term.negate t) :: accum) tl

      (* Term is neither conjunction nor disjunction and has positive
         polarity *)
      | _ -> 

        (* Term must be a Boolean atom *)
        (* assert (Term.is_atom t); *)

        (* Add term to literals *)
        literals_of_term (t :: accum) tl


(* Construct a clause of a term *)
let of_term t = 

  (* Construct a clause from the literals of the term *)
  Stat.time_fun Stat.clause_of_term_time  (fun () ->
      of_literals (literals_of_term [] [(true, t)])
    )

let elements = T.elements 

(*
(* Return the elements of a clause *)
let elements c = match Term.destruct c with 

  (* Clause is a disjunction of literals *)
  | Term.T.App (s, d) when s == Symbol.s_or -> d

  (* Clause is empty, then it is the Boolean false *)
  | Term.T.Const s when s == Symbol.s_false -> []

  (* Clause is unit *)
  | _ as t -> [Term.construct t]
*)

(* Pretty-print a clause as list of literals without parenthes *)
let rec pp_print_clause' ppf = function 

  | [] -> ()

  | l :: tl -> 

    Format.fprintf 
      ppf 
      "@[<hv>%a@]%t" 
      Term.pp_print_term l 
      (function ppf -> if not (tl = []) then Format.fprintf ppf ";@ " else ());

    pp_print_clause' ppf tl
      

(* Pretty-print a clause *)
let pp_print_clause ppf clause = 
  Format.fprintf ppf "@[<hv 1>{%a}@]" pp_print_clause' (elements clause)
  

(* Pretty-print a clause to the standard formatter *)
let print_clause = pp_print_clause Format.std_formatter


(* The empty clause *)
let empty = T.empty


(* The true clause *)
let top = T.singleton Term.t_true


(* A clause is empty if it is the Boolean false *)
let is_empty = T.is_empty


(* Literal is in a clause? *)
let mem = T.mem
   

(* Add a literal to a clause *)
let add = T.add


(* Construct a unit clause *)
let singleton = T.singleton


(* Remove a literal from a clause *)
let remove = T.remove


(* Construct the disjunction of two clauses *)
let union = T.union


(* Return a clause only containing literals in both clauses *)
let inter = T.inter
    

(* Return a clause only containing the literals in the first but not
   in the second clause *)
let diff = T.diff


(* Compare two clauses *)
let compare = T.compare


(* Equality of two clauses *)
let equal = T.equal


(* Return true if all literals in the second clause are in the first clause *)
let subset = T.subset


(* Apply function to each literal in the clause *)
let iter = T.iter


(* Fold literals in clause with function *)
let fold = T.fold


(* Return true if the predicate [f] returned true for all literals *)
let for_all = T.for_all


(* Return true if the predicate [f] returned true for some literal *)
let exists = T.exists


(* Return a clause containing only the literals the predicate [f] is true for *)
let filter = T.filter

(* Return a pair of clauses, where the literals in the first pair
   satify the predicate [f] and the literals in the second don't *)
let partition = T.partition


(* Return the number of literals in the clause *)
let cardinal = T.cardinal


(* Return one element of the clause *)
let choose = T.choose 


(* Apply [f] to each literal and return a new clause *)
let map f c = 
  of_literals (List.map f (elements c))


(* Convert a clause to a term *)
let to_term c = Term.mk_or (elements c)

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
