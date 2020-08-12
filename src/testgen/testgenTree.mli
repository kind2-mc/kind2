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

type model = Model.t
type term = Term.t
type num = Numeral.t

(** A depth is just a numeral. *)
type depth = num

(** A [mode] is just its name. *)
type mode = Scope.t

(**
  A conjunction of modes. First are the modes activated, then come the mode
  deactivated.
*)
type mode_conj = (mode list) * (mode list)

(**
  A [mode_path] stores the modes activated by the path in reverse order.
*)
type mode_path = mode_conj list

(**
  Stores the witnesses and the reversed tree.
  Also stores a mode to term function to construct constraints to activate or
  block mode paths / conjunctions of modes.
*)
type t

(**
  Exception raised when [Top] is reached.
*)
exception TopReached

(**
  Creates a reversed partial tree. [mode_conj] is a conjunction of modes
  activable in the initial state. [mode_to_term] is the function mapping mode
  names to their term at offset zero.
  Originally there are no witnesses, some initial state mode, and no modes
  explored.
*)
val mk: (mode -> term) -> mode_conj -> t

(**
  Returns the list of mode conjunctions corresponding to a partial tree.
*)
val mode_path_of: t -> mode_path

(**
  Returns the term encoding the path of modes represented by a tree.

  Used to check which modes can be activated to extend the path being currently
  explored.
*)
val path_of: t -> Term.t

(**
  Returns the term encoding the path of modes leading to the current node but
  blocking its mode conjunction and explored modes.

  Used when backtracking, to see if different modes can be activated at the
  current depth.
*)
val blocking_path_of: t -> Term.t

(**
  Depth of the current node of a tree.
*)
val depth_of: t -> num

(**
  Pushes a node on top of the current one, activating a mode conjunction.
*)
val push: t -> mode_conj -> unit

(**
  Pops the current node.
*)
val pop: t -> unit

(**
  Updates the current mode.
*)
val update: t -> mode_conj -> unit

(**
  Quiet tree pretty printer.
*)
val pp_print_tree: Format.formatter -> t -> unit


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
