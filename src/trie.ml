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
  val mem : key -> 'a t -> bool
  val add : key -> 'a -> 'a t -> 'a t
  (* val singleton: key -> 'a -> 'a t *)
  val remove : key -> 'a t -> 'a t
  (* val merge: (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c *)
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val for_all : (key -> 'a -> bool) -> 'a t -> bool
  val exists : (key -> 'a -> bool) -> 'a t -> bool
  val filter: (key -> 'a -> bool) -> 'a t -> 'a t
  (* val partition: (key -> 'a -> bool) -> 'a t -> 'a t * 'a t *)
  val cardinal: 'a t -> int
  val bindings : 'a t -> (key * 'a) list
  val min_binding: 'a t -> (key * 'a)
  val max_binding: 'a t -> (key * 'a)
  (* val choose: 'a t -> (key * 'a) *)
  val split: key -> 'a t -> 'a t * 'a option * 'a t
  val find : key -> 'a t -> 'a 
  val map : ('a -> 'b) -> 'a t -> 'b t
  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
  
end

(* Output signature is a map extended with special functions *)
module type S = sig
  include M 
  val find_prefix : key -> 'a t -> 'a t
  val keys : 'a t -> key list
  val values : 'a t -> 'a list
  val fold2 : (key-> 'a -> 'b -> 'c -> 'c) -> 'a t -> 'b t -> 'c -> 'c
  val map2 : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val iter2 : (key -> 'a -> 'b -> unit) -> 'a t -> 'b t -> unit
  val for_all2 : (key -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool
  val exists2 : (key -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool
  val subsume : 'a t -> key -> 'a t
  val is_subsumed : 'a t -> key -> bool
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

        
  (* An empty tree is an inner node with no children *)
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
     value of the leaf already exists, fail if the sequence of keys is
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

  
  let keys t = fold (fun k _ a -> k :: a) t []

  let values t = fold (fun _ v a -> v :: a) t []

  let bindings t = fold (fun k v a -> (k, v) :: a) t []

  let cardinal t = fold (fun k v a -> succ a) t 0

  let exists p t =

    let rec exists' k p = function
      | Empty -> false
      | Leaf v -> p (List.rev k) v
      | Node m -> M.exists (fun k' t -> exists' (k' :: k) p t) m
                    
    in

    exists' [] p t

      
  let for_all p t =

    let rec for_all' k p = function
      | Empty -> true
      | Leaf v -> p (List.rev k) v
      | Node m -> M.for_all (fun k' t -> for_all' (k' :: k) p t) m
                    
    in

    for_all' [] p t


  let filter p t = 

    let rec filter' k p = function
      | Empty -> Empty
      | Leaf v -> if p (List.rev k) v then Leaf v else Empty
      | Node m -> 

        let m' = 
          M.fold
            (fun k' t m -> 
               let t' = filter' (k' :: k) p t in
               if t' = Empty then m else M.add k' t' m)
            m
            M.empty
        in

        if M.is_empty m' then Empty else Node m' 

    in


    filter' [] p t  


  let max_binding t = 
    
    let rec max_binding' k = function
      | Empty -> raise Not_found
      | Leaf v -> (List.rev k, v)
      | Node m -> let k', v = M.max_binding m in max_binding' (k' :: k) v
    in

    max_binding' [] t


  let min_binding t = 
    
    let rec min_binding' k = function
      | Empty -> raise Not_found
      | Leaf v -> (List.rev k, v)
      | Node m -> let k', v = M.min_binding m in min_binding' (k' :: k) v
    in

    min_binding' [] t


  let split _ = assert false

  (* TODO: Rewrite fold2, map2 and iter2 with Map.merge to avoid using
     Map.bindings *)

  (* Fold over values at leaves *)
  let fold2 f t1 t2 acc =

    (* Keys are pushed to revp in reverse order *)
    let rec fold2' revp t1 t2 acc = match t1, t2 with

      (* Recurse to sub-tries of inner node *)
      | Node m1, Node m2 -> 

        List.fold_left2 
          (fun acc (k1, t1) (k2, t2) -> 
             if k1 = k2 then 
               fold2' (k1 :: revp) t1 t2 acc
             else
               raise (Invalid_argument "Trie.fold2"))
          acc
          (M.bindings m1)
          (M.bindings m2)

      (* Return value after function application *)
      | Leaf v1, Leaf v2 -> f (List.rev revp) v1 v2 acc

      (* Return accumulator on empty trie *)
      | Empty, Empty -> acc
      
      | _ -> raise (Invalid_argument "Trie.fold2")
  
    in

    (* Evaluate recursive function with initially empty path *)
    fold2' [] t1 t2 acc 


  (* Map over two tries *)
  let map2 f t1 t2 =

    (* Keys are pushed to revp in reverse order *)
    let rec map2' revp t1 t2 = match t1, t2 with

      (* Recurse to sub-tries of inner node *)
      | Node m1, Node m2 -> 

        Node
          (List.fold_left2 
             (fun acc (k1, t1) (k2, t2) -> 
                if k1 = k2 then 
                  M.add k1 (map2' (k1 :: revp) t1 t2) acc
                else
                  raise (Invalid_argument "Trie.map2"))
             M.empty
             (M.bindings m1)
             (M.bindings m2))

      (* Return value after function application *)
      | Leaf v1, Leaf v2 -> Leaf (f (List.rev revp) v1 v2)

      (* Return accumulator on empty trie *)
      | Empty, Empty -> Empty

      | _ -> raise (Invalid_argument "Trie.map2")

    in

    (* Evaluate recursive function with initially empty path *)
    map2' [] t1 t2 


  (* Iterate over two tries *)
  let iter2 f t1 t2 =

    (* Keys are pushed to revp in reverse order *)
    let rec iter2' revp t1 t2 = match t1, t2 with

      (* Recurse to sub-tries of inner node *)
      | Node m1, Node m2 -> 

        List.iter2 
          (fun (k1, t1) (k2, t2) -> 
             if k1 = k2 then 
               (iter2' (k1 :: revp) t1 t2) 
             else
               raise (Invalid_argument "Trie.iter2"))
          (M.bindings m1)
          (M.bindings m2)

      (* Return value after function application *)
      | Leaf v1, Leaf v2 -> f (List.rev revp) v1 v2

      (* Return accumulator on empty trie *)
      | Empty, Empty -> ()

      | _ -> raise (Invalid_argument "Trie.iter2")

    in

    (* Evaluate recursive function with initially empty path *)
    iter2' [] t1 t2 

      
  let for_all2 p t1 t2 = 

    let rec for_all2' revp p t1 t2 = 

      match t1, t2 with

        | Empty, Empty -> true

        | Leaf v1, Leaf v2 -> p (List.rev revp) v1 v2 

        | Node m1, Node m2 -> 
          
          List.for_all2 
            (fun (k1, t1) (k2, t2) -> 
               if k1 = k2 then 
                 (for_all2' (k1 :: revp) p t1 t2) 
               else
                 raise (Invalid_argument "Trie.for_all2"))
            (M.bindings m1)
            (M.bindings m2)

        | _ -> raise (Invalid_argument "Trie.for_all2")

    in

    for_all2' [] p t1 t2 


  let exists2 p t1 t2 = 

    let rec exists2' revp p t1 t2 = 

      match t1, t2 with

        | Empty, Empty -> false

        | Leaf v1, Leaf v2 -> p (List.rev revp) v1 v2 

        | Node m1, Node m2 -> 
          
          List.exists2 
            (fun (k1, t1) (k2, t2) -> 
               if k1 = k2 then 
                 (exists2' (k1 :: revp) p t1 t2) 
               else
                 raise (Invalid_argument "Trie.exists2"))
            (M.bindings m1)
            (M.bindings m2)

        | _ -> raise (Invalid_argument "Trie.exists2")

    in

    exists2' [] p t1 t2 


  (* Subset subsumption: remove all entries that have the given key as
     a subset. Keys must be sorted *)
  let rec subsume t = function
  
    (* The empty key subsumes all subtries *)
    | [] -> Empty

    | h :: tl as s ->

      (match t with

        (* Nothing to subsume *)
        | Empty -> Empty

        (* Key to subsume is longer than subtrie *)
        | Leaf v -> Leaf v

        (* Subsume a node *)
        | Node m ->

          (* Left subtries may be subsumed by the whole key [s],
             skipping over the smaller elements in the key of
             potentially subsumed entries. The subtries below [h] may
             be subsumed by [tl], and right subtries are never
             subsumed. *)
          let ml, mc, mr = M.split h m in

          (* Subsume in center subtries and add to kept right
             subtries *)
          let mr' = match mc with
            | None -> mr
            | Some t -> M.add h (subsume t tl) mr
          in

          (* Subsume in left subtries and add to center and right subtries *)
          let m' =
            
            M.fold

              (fun k t a ->

                (* Subsume in subtrie with key *)
                match subsume t s with

                  (* Don't add to map if subtrie is empty *)
                  | Empty -> a
                    
                  | t' -> M.add k t' a)

              (* Subsume in left subtries *)
              ml

              (* Add to already filtered tries *)
              mr'
              
          in

          (* Return empty if all subsumed *)
          if M.is_empty m' then Empty else Node m')

	
  (* Subset subsumption: return true if there is a key in the trie that is a
     subset of the given key. Keys must be sorted *)
  let is_subsumed t k = 
	
    let rec is_subsumed' = function

      (* Could not subsume key in any subtrie *)
      | [] -> false

      (* No keys in trie, nothing subsumed *)
      | (Empty, _) :: tl -> is_subsumed' tl
	
      (* All keys are emtpty, subsume any key *)
      | (Leaf _, _) :: _ -> true

      (* Empty key is not subsumed in non-empty trie *)
      | (Node _, []) :: tl -> is_subsumed' tl
	
      (* Non-empty key is *)
      | (Node m, ((h :: ktl) as k)) :: tl ->

	(* *)
	let _, mc, mr = M.split h m in

	let tl' =
	  tl
      |> (fun l ->
	if M.is_empty mr then l else (Node mr, ktl) :: l)
      |> (fun l ->
	match mc with
	  | None -> l
	  | Some t -> (t, ktl) :: l)
	in

	is_subsumed' tl'

    in

    is_subsumed' [(t, k)]
	  

      
	
end





(*


(* Test code *)
module CharMap = Map.Make(Char);;

module T = Make(CharMap);;


let t1 : int T.t = T.empty;;
let t2 : int T.t = T.empty;;

let t1 = 
  T.add ['b'] 3 T.empty 
  |> T.add ['a'] 1
  |> T.add ['c';'a'] 2
  |> T.add ['c';'b'] 1
  |> T.add ['c';'c'] 2;;

let t2 = 
  T.add ['b'] 3 T.empty
  |> T.add ['a'] 1
  |> T.add ['c';'a'] 2
  |> T.add ['c';'b'] 2
  |> T.add ['c';'c'] 2;;


let p i v1 v2 = 
  Format.printf "%a: %d %d@." 
    (pp_print_list Format.pp_print_char "") i v1 v2; 
  v1 > v2;;

T.for_all2 p t1 t2;;
T.exists2 p t1 t2;;


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

T.keys a1;;
T.keys a1b2;;
T.keys a1b2cd3;;
T.keys a1b2cd3ce4;;

T.bindings a1;;
T.bindings a1b2;;
T.bindings a1b2cd3;;
T.bindings a1b2cd3ce4;;

T.min_binding a1;;
T.min_binding a1b2;;
T.min_binding a1b2cd3;;
T.min_binding a1b2cd3ce4;;

T.max_binding a1;;
T.max_binding a1b2;;
T.max_binding a1b2cd3;;
T.max_binding a1b2cd3ce4;;

let a2b3cd4ce5 = T.map ((+) 1) a1b2cd3ce4;;

T.exists (fun k v -> v > 2)  T.empty;;
T.for_all (fun k v -> v > 2)  T.empty;;
T.exists (fun k v -> v = 1)  a1b2cd3;;
T.for_all (fun k v -> v > 0)  a1b2cd3ce4;;

T.fold2 (fun k v1 v2 a -> (k, (v1, v2)) :: a) T.empty T.empty [];;
T.fold2 (fun k v1 v2 a -> (k, (v1, v2)) :: a) T.empty a1 [];;
T.fold2 (fun k v1 v2 a -> (k, (v1, v2)) :: a) a1 a1 [];;
T.fold2 (fun k v1 v2 a -> (k, (v1, v2)) :: a) a1b2cd3ce4 a2b3cd4ce5 [];;

T.map2 (fun k v1 v2 -> v1 + v2) T.empty T.empty;;
T.map2 (fun k v1 v2 -> v1 + v2) T.empty a1;;
T.bindings (T.map2 (fun k v1 v2 -> v1 + v2) a1 a1);;
T.bindings (T.map2 (fun k v1 v2 -> v1 + v2) a1b2cd3ce4 a1b2cd3ce4);;
T.bindings (T.map2 (fun k v1 v2 -> v1 + v2) a1b2cd3ce4 a2b3cd4ce5);;


T.iter2 (fun k v1 v2 -> Format.printf "%d, %d@." v1 v2) T.empty T.empty;;
T.iter2 (fun k v1 v2 -> Format.printf "%d, %d@." v1 v2) a1 T.empty;;
T.iter2 (fun k v1 v2 -> Format.printf "%d, %d@." v1 v2) a1 a1;;
T.iter2 (fun k v1 v2 -> Format.printf "%d, %d@." v1 v2) a1b2cd3ce4 a1b2cd3ce4;;
T.iter2 (fun k v1 v2 -> Format.printf "%d, %d@." v1 v2) a1b2cd3ce4 a2b3cd4ce5;;
T.map2 (fun k v1 v2 -> v1 + v2) T.empty a1;;
T.bindings (T.map2 (fun k v1 v2 -> v1 + v2) a1 a1);;
T.bindings (T.map2 (fun k v1 v2 -> v1 + v2) a1b2cd3ce4 a1b2cd3ce4);;
T.bindings (T.map2 (fun k v1 v2 -> v1 + v2) a1b2cd3ce4 a2b3cd4ce5);;

T.bindings (T.filter (fun k v -> v > 2) T.empty);;
T.filter (fun k v -> v > 2) a1;;
T.bindings (T.filter (fun k v -> v < 2) a1);;
T.bindings (T.filter (fun k v -> v >= 2) a1b2);;
T.bindings (T.filter (fun k v -> v < 2) a1b2);;
T.bindings (T.filter (fun k v -> v > 2) a1b2cd3ce4);;
T.bindings (T.filter (fun k v -> v < 2) a1b2cd3ce4);;

T.bindings (T.filter (fun k v -> k = ['a']) T.empty);;
T.bindings (T.filter (fun k v -> k = ['a']) a1);;
T.filter (fun k v -> k = ['b']) a1;;
T.bindings (T.filter (fun k v -> k = ['a']) a1b2);;
T.bindings (T.filter (fun k v -> k = ['b']) a1b2);;
T.bindings (T.filter (fun k v -> not (k = ['a'] || k = ['c';'e'])) a1b2cd3ce4);;
T.bindings (T.filter (fun k v -> k = ['a'] || k = ['c';'e']) a1b2cd3ce4);;
*)  
(*
  Format.printf "Testing subsumption";;

let t =
  List.fold_left
    (fun m (k, v) -> T.add k v m)
    T.empty
    [(['a';'b';'c'], "abc");
     (['a';'b';'d'], "abd");
     (['a';'c';'d'], "acd")];;

T.bindings t;;

T.bindings (T.subsume t ['a';'b']);;
T.bindings (T.subsume t ['b';'c']);;
T.bindings (T.subsume t ['a';'c']);;

T.is_subsumed t ['a'];;
T.is_subsumed t ['x'];;
T.is_subsumed t ['a';'b'];;
T.is_subsumed t ['a';'b';'c'];;
T.is_subsumed t ['a';'b';'c';'d'];;
T.is_subsumed t ['a';'c';'d';'e'];;

let t1 = T.add ['a';'c';'e'] "ace" T.empty;;

T.is_subsumed t1 ['a';'c';'e'];;
T.is_subsumed t1 ['a';'b';'c'];;
T.is_subsumed t1 ['a';'c';'e';'f'];;
T.is_subsumed t1 ['a';'b';'c';'e';'f'];;

T.is_subsumed T.empty ['a'];;

let t2 =
  List.fold_left
    (fun m (k, v) -> T.add k v m)
    T.empty
    [(['b'], "a");
     (['c';'d'], "bc")];;

T.bindings t2;;

T.is_subsumed t2 ['a'];;

*)
