(* This file is part of the Kind 2 model checker.

   Copyright (c) 2022 by the Board of Trustees of the University of Iowa

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

type priority = int

type 'a t = Empty | Node of priority * 'a * 'a t * 'a t

let empty = Empty

let is_empty = function
  | Empty -> true
  | _ -> false

let rec insert queue prio elt =
  match queue with
  | Empty -> Node(prio, elt, Empty, Empty)
  | Node(p, e, left, right) ->
    if prio <= p
    then Node(prio, elt, insert right p e, left)
    else Node(p, e, insert right prio elt, left)
   
let rec remove_top = function
  | Empty -> Empty
  | Node(_, _, left, Empty) -> left
  | Node(_, _, Empty, right) -> right
  | Node(_, _, (Node(lprio, lelt, _, _) as left),
               (Node(rprio, relt, _, _) as right)) ->
    if lprio <= rprio
    then Node(lprio, lelt, remove_top left, right)
    else Node(rprio, relt, left, remove_top right)

let extract = function
  | Empty -> None
  | Node(prio, elt, _, _) as queue ->
    Some (prio, elt, remove_top queue)
