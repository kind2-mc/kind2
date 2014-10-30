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


(* Implementation inspired by Jean-Christophe Filliatre's at 
   https://www.lri.fr/~filliatr/ftp/ocaml/ds/trie.ml.html *)

(* A trie is a tree-like structure to implement dictionaries over keys
   which have list-like structures. The idea is that each node
   branches on an element of the list and stores the value associated
   to the path from the root, if any. Therefore, a trie can be defined
   as soon as a map over the elements of the list is given. *)

(* Input signature of a map *)
module type M = sig
  type key
  type +'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val add : key -> 'a -> 'a t -> 'a t
  val find : key -> 'a t -> 'a
  val remove : key -> 'a t -> 'a t
  val mem : key -> 'a t -> bool
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val map : ('a -> 'b) -> 'a t -> 'b t
  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
end

(* Output signature is map extended with find_prefix *)
module type S = sig
  include M 
  val find_prefix : key -> 'a t -> 'a t
end

module Make (M : M) = struct

  (* The keys in the trie are lists of keys of the input map module *)
  type key = M.key list


  (* This trie stores information at the leaves only. An inner node
     stores the subtries for each key in a map. An empty trie does
     have neither an inner node nor a leaf at the root, we need a
     special value for it. *)
  type 'a t =
    | Node of 'a t M.t
    | Leaf of 'a
    | Empty 

  (* An empty tree is an inner node with no children. *)
  let empty = Empty


  (* Return true if a trie is empty *)
  let is_empty = function
    | Empty -> true
    | Node m -> M.is_empty m
    | Leaf _ -> false

  
  (* Return the value for a list of keys *)
  let rec find l t = match (l,t) with

    (* Fail if we are in an empty trie, have the empty list of keys at
       an inner node or a non-empty list of keys at a leaf *)
    | _, Empty
    | [], Node _
    | _ :: _, Leaf _ -> raise Not_found

    (* Return if we have a leaf for an empty list of keys *)
    | [], Leaf v -> v

    (* Recurse to the sub-trie of the head element the keys *)
    | h :: tl, Node m -> find tl (M.find h m)


  (* Return [true] if there is a value for the list of keys *)
  let rec mem l t = match (l,t) with

    (* Return false if we are in an empty trie, have the empty list of
       keys at an inner node or a non-empty list of keys at a leaf *)
    | _, Empty 
    | [], Node _
    | _ :: _, Leaf _ -> false

    (* Return true if we have a leaf for an empty list of keys *)
    | [], Leaf v -> true

    (* Recurse to the sub-trie of the head element the keys *)
    | h :: tl, Node m -> try mem tl (M.find h m) with Not_found -> false

  
  (* Return the subtrie for list of keys *)
  let rec find_prefix l t = match (l,t) with

    (* Fail if we have a non-empty list of keys at a leaf *)
    | _, Empty
    | _ :: _, Leaf _ -> raise Not_found

    (* Return trie if we have a leaf for an empty list of keys *)
    | [], t -> t

    (* Recurse to the sub-trie of the head element the keys *)
    | h :: tl, Node m -> find_prefix tl (M.find h m)


  (* Insert value for a key sequence into the trie. Overwrite if the
     value if the leaf already exists, fail if the sequence of keys is
     a prefix of a previous sequence, or if a previous sequence is a
     prefix of the given sequence. *)
  let rec add l v t = match (l, t) with 

    (* Replace entry at leaf or in empty trie *)
    | [], Empty 
    | [], Leaf _ -> Leaf v

    (* Fail if we have to go below a leaf or insert into a node *)
    | _ :: _, Leaf _
    | [], Node _ -> raise (Invalid_argument "add")

    (* Insert into the empty trie *)
    | h :: tl, Empty -> 

      (* Insert into empy sub-trie *)
      let t = add tl v Empty in

      (* Add sub-trie to this trie *)
      Node (M.add h t M.empty)
          
      
    (* Insert into the sub-trie of the head of the key list *)
    | h :: tl, Node m ->

      (* Find sub-trie for the head of the key sequence, default to
         the empty trie *)
      let t' = try M.find h m with Not_found -> Empty in

      (* Insert into sub-trie *)
      let t'' = add tl v t' in

      (* Add sub-trie to this trie *)
      Node (M.add h t'' m)

  
  (* Remove key from trie. Do not fail if key does not exist. *)
  let rec remove l t = match (l, t) with

    (* Remove entry at leaf and leave empty trie *)
    | [], Leaf _ -> Empty

    (* Skip if removing from an inner node or below a leaf *)
    | _, Empty
    | _ :: _, Leaf _
    | [], Node _ -> t

    (* Remove from sub-trie *)
    | h :: tl, Node m ->

      try

        (* Remove from sub-trie of heaf of key sequence *)
        let t' = remove tl (M.find h m) in 

        (* If sub-trie has become empty, remove from map, otherwise
           replace *)
        let m' =
          if is_empty t' then M.remove h m else M.add h t' m
        in

        if M.is_empty m' then Empty else Node m'
        
      (* Skip if no sub-trie for head of key sequence *)
      with Not_found -> t

  
  (* Apply function to value at leaves *)
  let rec map f = function

    (* Recurse to sub-tries of inner node *)
    | Node m -> Node (M.map (map f) m)

    (* Return value after function application *)
    | Leaf v -> Leaf (f v)

    (* Return empty trie unchanged *)
    | Empty -> Empty

  (* Apply function to value at leaves and give keq sequence as first
     argument *)
  let mapi f t =

    (* Keys are pushed to revp in reverse order *)
    let rec mapi' revp = function

      (* Recurse to sub-tries of inner node *)
      | Node m -> Node (M.mapi (fun x -> mapi' (x :: revp)) m)

      (* Return value after function application *)
      | Leaf v -> Leaf (f (List.rev revp) v)
                    
      (* Return empty trie unchanged *)
      | Empty -> Empty

    in

    (* Evaluate recursive function with initially empty path *)
    mapi' [] t


  (* Apply unit-valued function to value at leaves *)
  let iter f t =

    (* Keys are pushed to revp in reverse order *)
    let rec iter' revp = function
      
      (* Recurse to sub-tries of inner node *)
      | Node m -> M.iter (fun x -> iter' (x :: revp)) m

      (* Return value after function application *)
      | Leaf v -> f (List.rev revp) v

      (* Skip on empty trie *)
      | Empty -> ()

    in

    (* Evaluate recursive function with initially empty path *)
    iter' [] t


  (* Fold over values at leaves *)
  let fold f t acc =

    (* Keys are pushed to revp in reverse order *)
    let rec fold' revp t acc = match t with

      (* Recurse to sub-tries of inner node *)
      | Node m -> M.fold (fun x -> fold' (x :: revp)) m acc

      (* Return value after function application *)
      | Leaf v -> f (List.rev revp) v acc

      (* Return accumulator on empty trie *)
      | Empty -> acc
        
    in

    (* Evaluate recursive function with initially empty path *)
    fold' [] t acc 


  (* Compare two tries given a comparison function on keys *)
  let rec compare cmp a b = match a, b with 

    (* A trie with children is greater than a trie of only a leaf and
       the empty trie *)
    | Node _, Leaf _
    | Node _, Empty
    | Leaf _, Empty -> 1

    (* A trie of only a leaf is smaller than a trie with children *)
    | Leaf _, Node _ 
    | Empty, Leaf _ 
    | Empty, Node _ -> -1
  
    (* Compare maps of inner nodes *)
    | Node m1, Node m2 -> M.compare (compare cmp) m1 m2
        
    (* Compare values at leaves *)
    | Leaf a, Leaf b -> cmp a b

    (* Two empty tries are equal *)
    | Empty, Empty -> 0
      

  (* Equality of tries given an equality function on keys *)
  let rec equal eq a b = match a, b with

    (* A trie with children is not equal to a trie of only a leaf or
       the emtpy trie *)
    | Node _, Leaf _
    | Node _, Empty
    | Leaf _, Node _
    | Leaf _, Empty
    | Empty, Node _
    | Empty, Leaf _ -> false
      
    (* Compare maps of inner nodes *)
    | Node m1, Node m2 -> M.equal (equal eq) m1 m2

    (* Compare values at leaves *)
    | Leaf a, Leaf b -> eq a b

    (* Two empty tries are equal *)
    | Empty, Empty -> true
      
end

(* Test code *)
(*
module CharMap = Map.Make(Char);;

module T = Make(CharMap);;

T.is_empty T.empty;;

T.is_empty (T.add ['a'] 1 T.empty);;

let a1 = T.add ['a'] 1 T.empty;;

T.find ['a'] a1;;

T.mem ['a'] a1;;

T.find_prefix ['a'] a1;;

T.remove ['a'] a1;;

let a1b2 = T.add ['b'] 2 a1;;

T.find ['a'] a1b2;;
T.find ['b'] a1b2;;

T.mem ['a'] a1b2;;
T.mem ['b'] a1b2;;

T.find_prefix ['a'] a1b2;;
T.find_prefix ['b'] a1b2;;

T.remove ['b'] (T.remove ['a'] a1b2);;
T.remove ['a'] (T.remove ['b'] a1b2);;

let a1b2cd3 = T.add ['c';'d'] 3 a1b2;;

T.find ['a'] a1b2cd3;;
T.find ['b'] a1b2cd3;;
T.find ['c'] a1b2cd3;;
T.find ['c'; 'd'] a1b2cd3;;

T.mem ['a'] a1b2cd3;;
T.mem ['b'] a1b2cd3;;
T.mem ['c'] a1b2cd3;;
T.mem ['c'; 'd'] a1b2cd3;;

T.find_prefix ['a'] a1b2cd3;;
T.find_prefix ['b'] a1b2cd3;;
T.find_prefix ['c'] a1b2cd3;;
T.find_prefix ['d'] a1b2cd3;;
T.find_prefix ['c';'d'] a1b2cd3;;

T.remove ['b'] (T.remove ['a'] a1b2cd3);;
T.remove ['a'] (T.remove ['b'] a1b2cd3);;
T.remove ['c'] (T.remove ['a'] (T.remove ['b'] a1b2cd3));;
T.remove ['c'; 'd'] (T.remove ['a'] (T.remove ['b'] a1b2cd3));;


let a1b2cd3ce4 = T.add ['c';'e'] 4 a1b2cd3;;

T.find ['a'] a1b2cd3ce4;;
T.find ['b'] a1b2cd3ce4;;
T.find ['c'] a1b2cd3ce4;;
T.find ['c'; 'd'] a1b2cd3ce4;;
T.find ['c'; 'e'] a1b2cd3ce4;;

T.mem ['a'] a1b2cd3ce4;;
T.mem ['b'] a1b2cd3ce4;;
T.mem ['c'] a1b2cd3ce4;;
T.mem ['c'; 'd'] a1b2cd3ce4;;
T.mem ['c'; 'e'; 'f'] a1b2cd3ce4;;

T.find_prefix ['a'] a1b2cd3ce4;;
T.find_prefix ['b'] a1b2cd3ce4;;
T.find_prefix ['d'] a1b2cd3ce4;;
T.find_prefix ['c';'d'] a1b2cd3ce4;;
T.mem ['d'] (T.find_prefix ['c'] a1b2cd3ce4);;

T.remove ['b'] (T.remove ['a'] a1b2cd3ce4);;
T.remove ['a'] (T.remove ['b'] a1b2cd3ce4);;
T.remove ['c'] (T.remove ['a'] (T.remove ['b'] a1b2cd3ce4));;
T.remove ['c'; 'd'] (T.remove ['a'] (T.remove ['b'] a1b2cd3ce4));;
T.remove ['c'; 'd'] (T.remove ['a'] (T.remove ['c';'e'] (T.remove ['b'] a1b2cd3ce4)));;


let a1b2cd3ce4' = T.map ((+) 1) a1b2cd3;;

T.find ['a'] a1b2cd3ce4';;
T.find ['b'] a1b2cd3ce4';;
T.find ['c'] a1b2cd3ce4';;
T.find ['c'; 'd'] a1b2cd3ce4';;
T.find ['c'; 'e'] a1b2cd3ce4';;

let a1b2cd3ce4' = T.mapi (fun k v -> Char.chr (97 + v) :: k) a1b2cd3ce4;;

T.find ['a'] a1b2cd3ce4';;
T.find ['b'] a1b2cd3ce4';;
T.find ['c'] a1b2cd3ce4';;
T.find ['c'; 'd'] a1b2cd3ce4';;
T.find ['c'; 'e'] a1b2cd3ce4';;

T.iter (fun k v -> Format.printf "%a: %d@." (pp_print_list Format.pp_print_char "") k v) a1b2;;

T.fold (fun k v a -> (k, v) :: a) T.empty [];;

T.equal (=) a1b2 T.empty;;

*)
