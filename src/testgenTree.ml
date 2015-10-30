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

module Num = Numeral

type model = Model.t
type term = Term.t
type num = Num.t

(* A depth is just a numeral. *)
type depth = num

(* A [mode] is just its name. *)
type mode = string

(*
  A conjunction of modes. First are the modes activated, then come the mode
  deactivated.
*)
type mode_conj = (mode list) * (mode list)

(*
  A [mode_path] stores the modes activated by the path in reverse order.
*)
type mode_path = mode_conj list

(*
  Reversed partial tree for depth first search. Stores the activable modes at
  k and the witnesses for each path. The tree is partial because the witnesses
  for subtrees are collapsed into a single [Witnesses] leaf. The tree is
  reversed because the entry point is the current depth, the last element is
  the root.

  The idea is that when hitting the maximal depth during the exploration of the
  tree of activable modes, a witness is generated. This witness is propagated
  upward the reverse partial tree when backtracking.
*)

(*
  The adt for a reversed partial tree. Does not store witnesses.
*)
type rev_tree_adt =
(*
  The root of the tree, i.e. the top most element here since the tree is
  reversed.
*)
| Top
(*
  A node is its depth, the node it comes from, the mode it corresponds to, and
  the mode conjunctions already explored from this node.
*)
| Node of depth * rev_tree_adt * mode_conj * (mode_conj list)

(*
  Stores the witnesses and the reversed tree.
  Also stores a mode to term function to construct constraints to activate or
  block mode paths / conjunctions of modes.
*)
type t = {
  mode_to_term: mode -> term ;
  mutable tree: rev_tree_adt ;
}

(*
  Exception raised when [Top] is reached.
*)
exception TopReached

(*
  Creates a reversed partial tree. [mode_conj] is a conjunction of modes
  activable in the initial state. [mode_to_term] is the function mapping mode
  names to their term @0.
  Originally there are no witnesses, some initial state mode, and no modes
  explored.
*)
let mk mode_to_term mode_conj =
  { mode_to_term; tree = Node (Num.zero, Top, mode_conj, []) }

(* Creates the term associated to a mode conjunction. *)
let term_of_mode_conj mode_to_term k (act, deact) =
  List.rev_append
    ( act |> List.map (fun m -> mode_to_term m |> Term.bump_state k) )
    ( deact |> List.map (fun m ->
        mode_to_term m |> Term.bump_state k |> Term.mk_not) )
  |> Term.mk_and

(*
  Returns the list of term the conjunction of which encodes the path of modes
  leading to the current node, including the current node.

  Result goes from current depth to 0.
*)
let term_of_path mode_to_term tree =
  let rec loop tree conj = match tree with
    | Node (k, kid, mode_conj, _) ->
      let mode_at_k = term_of_mode_conj mode_to_term k mode_conj in
      mode_at_k :: conj |> loop kid (* Looping. *)
    | Top -> (* Reversing for readability. *)
      List.rev conj
  in
  loop tree

(*
  Returns the list of mode conjunctions corresponding to a partial tree adt.
*)
let mode_path_of_adt tree =
  let rec loop tree prefix = match tree with
    | Node (_, kid, mode_conj, _) -> mode_conj :: prefix |> loop kid
    | Top -> List.rev prefix
  in
  loop tree []

(*
  Returns the list of mode conjunctions corresponding to a partial tree.
*)
let mode_path_of { tree } = mode_path_of_adt tree

(*
  Returns the term encoding the path of modes represented by a tree.

  Used to check which modes can be activated to extend the path being currently
  explored.
*)
let path_of { mode_to_term ; tree } =
  match tree with
  | Node _ -> term_of_path mode_to_term tree [] |> Term.mk_and
  | Top -> raise TopReached

(*
  Returns the term encoding the path of modes leading to the current node but
  blocking its mode conjunction and explored modes.

  Used when backtracking, to see if different modes can be activated at the
  current depth.
*)
let blocking_path_of { mode_to_term ; tree } =
  match tree with
  | Node (k, kid, mode_conj, explored) ->
    mode_conj :: explored
    |> List.map (fun mode_conj -> (* Negating each mode conjunction. *)
      term_of_mode_conj mode_to_term k mode_conj |> Term.mk_not
    ) |> term_of_path mode_to_term kid (* Building path. *)
    |> Term.mk_and
  | Top -> raise TopReached

(*
  Depth of the current node of a tree.
*)
let depth_of { tree } = match tree with
| Node (k, _, _, _) -> k
| Top -> raise TopReached

(*
  Pushes a node on top of the current one, activating a mode conjunction.
*)
let push ({ tree } as t) mode_conj = match tree with
| Node (k, _, _, _) ->
  t.tree <- Node (Num.succ k, tree, mode_conj, [])
| Top -> raise TopReached

(*
  Pops the current node.
*)
let pop ({ tree } as t) = match tree with
| Node (_, kid, _, _) -> t.tree <- kid
| Top -> raise TopReached

(*
  Updates the current mode.
*)
let update ({ tree } as t) mode_conj = match tree with
| Node (k, kid, mode_conj', explored) ->
  t.tree <- Node (k, kid, mode_conj, mode_conj' :: explored)
| Top  -> raise TopReached




(* |===| Pretty printers. *)
let pp_print_tree fmt ({ tree } as t) =
  Format.fprintf fmt "@[<v>at %a (%a)@]"
    Num.pp_print_numeral (match tree with
      | Top -> Num.(~- one) | Node (k,_,_,_) -> k
    )
    (fun fmt (act,_) ->
      Format.fprintf fmt "%a"
        (pp_print_list Format.pp_print_string ", ") act)
    (match tree with
      | Top -> ["top"], [] | Node(_,_,c,_) -> c)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
