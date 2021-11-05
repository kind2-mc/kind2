(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(*s Hash tables for hash-consing. (Some code is borrowed from the ocaml
    standard library, which is copyright 1996 INRIA.) *)

type ('a, 'b) hash_consed =  { 
  hkey : int;
  tag : int;
  node : 'a;
  prop : 'b }

(* Comparison based on tags *)
let compare { tag = t1 } { tag = t2 } = Int.compare t1 t2

(* Equality based on tags *)
let equal { tag = t1 } { tag = t2 } = t1 = t2

(* Hashing based on stored hash *)
let hash { hkey = h } = h


let gentag =
  let r = ref 0 in
  fun () -> incr r; !r

type ('a, 'b) t = {
  mutable table : ('a, 'b) hash_consed Weak.t array;
  mutable totsize : int;             (* sum of the bucket sizes *)
  mutable limit : int;               (* max ratio totsize/table length *)
}

let create sz =
  let sz = if sz < 7 then 7 else sz in
  let sz = if sz > Sys.max_array_length then Sys.max_array_length else sz in
  let emptybucket = Weak.create 0 in
  { table = Array.make sz emptybucket;
    totsize = 0;
    limit = 3; }

let clear t =
  let emptybucket = Weak.create 0 in
  for i = 0 to Array.length t.table - 1 do t.table.(i) <- emptybucket done;
  t.totsize <- 0;
  t.limit <- 3
  
let fold f t init =
  let rec fold_bucket i b accu =
    if i >= Weak.length b then accu else
      match Weak.get b i with
	| Some v -> fold_bucket (i+1) b (f v accu)
	| None -> fold_bucket (i+1) b accu
  in
  Array.fold_right (fold_bucket 0) t.table init

let iter f t =
  let rec iter_bucket i b =
    if i >= Weak.length b then () else
      match Weak.get b i with
	| Some v -> f v; iter_bucket (i+1) b
	| None -> iter_bucket (i+1) b
  in
  Array.iter (iter_bucket 0) t.table

let count t =
  let rec count_bucket i b accu =
    if i >= Weak.length b then accu else
      count_bucket (i+1) b (accu + (if Weak.check b i then 1 else 0))
  in
  Array.fold_right (count_bucket 0) t.table 0

let next_sz n = min (3*n/2 + 3) (Sys.max_array_length - 1)

let rec resize t =
  let oldlen = Array.length t.table in
  let newlen = next_sz oldlen in
  if newlen > oldlen then begin
    let newt = create newlen in
    newt.limit <- t.limit + 100;          (* prevent resizing of newt *)
    fold (fun d () -> add newt d) t ();
    t.table <- newt.table;
    t.limit <- t.limit + 2;
  end

and add t d =
  let index = d.hkey mod (Array.length t.table) in
  let bucket = t.table.(index) in
  let sz = Weak.length bucket in
  let rec loop i =
    if i >= sz then begin
      let newsz = min (sz + 3) (Sys.max_array_length - 1) in
      if newsz <= sz then 
	failwith "Hashcons.Make: hash bucket cannot grow more";
      let newbucket = Weak.create newsz in
      Weak.blit bucket 0 newbucket 0 sz;
      Weak.set newbucket i (Some d);
      t.table.(index) <- newbucket;
      t.totsize <- t.totsize + (newsz - sz);
      if t.totsize > t.limit * Array.length t.table then resize t;
    end else begin
      if Weak.check bucket i
      then loop (i+1)
      else Weak.set bucket i (Some d)
    end
  in
  loop 0

let hashcons t d p =
  let hkey = Hashtbl.hash d in
  let index = hkey mod (Array.length t.table) in
  let bucket = t.table.(index) in
  let sz = Weak.length bucket in
  let rec loop i =
    if i >= sz then begin
      let hnode = { hkey = hkey; tag = gentag (); node = d; prop = p } in
      add t hnode;
      hnode
    end else begin
      match Weak.get_copy bucket i with
        | Some v when v.node = d -> 
	    begin match Weak.get bucket i with
              | Some v -> v
              | None -> loop (i+1)
            end
        | _ -> loop (i+1)
    end
  in
  loop 0
  
let stats t =
  let len = Array.length t.table in
  let lens = Array.map Weak.length t.table in
  Array.sort Int.compare lens;
  let totlen = Array.fold_left ( + ) 0 lens in
  (len, count t, totlen, lens.(0), lens.(len/2), lens.(len-1))


(* Functorial interface *)

module type HashedType =
  sig
    type t
    type prop
    val equal : t -> t -> bool
    val hash : t -> int
  end

module type S =
  sig
    type key
    type prop
    type t
    val create : int -> t
    val clear : t -> unit
    val hashcons : t -> key -> prop -> (key, prop) hash_consed
    val find : t -> key -> (key, prop) hash_consed
    val iter : ((key, prop) hash_consed -> unit) -> t -> unit
    val fold : ((key, prop) hash_consed -> 'a -> 'a) -> t -> 'a -> 'a
    val stats : t -> int * int * int * int * int * int
  end

module Make(H : HashedType) : (S with type key = H.t and type prop = H.prop) = 
struct

  type key = H.t

  type prop = H.prop

  type data = (H.t, H.prop) hash_consed

  type t = {
    mutable table : data Weak.t array;
    mutable totsize : int;             (* sum of the bucket sizes *)
    mutable limit : int;               (* max ratio totsize/table length *)
  }

  let emptybucket = Weak.create 0

  let create sz =
    let sz = if sz < 7 then 7 else sz in
    let sz = if sz > Sys.max_array_length then Sys.max_array_length else sz in
    {
      table = Array.make sz emptybucket;
      totsize = 0;
      limit = 3;
    }

  let clear t =
    for i = 0 to Array.length t.table - 1 do
      t.table.(i) <- emptybucket
    done;
    t.totsize <- 0;
    t.limit <- 3
  
  let fold f t init =
    let rec fold_bucket i b accu =
      if i >= Weak.length b then accu else
      match Weak.get b i with
      | Some v -> fold_bucket (i+1) b (f v accu)
      | None -> fold_bucket (i+1) b accu
    in
    Array.fold_right (fold_bucket 0) t.table init

  let iter f t =
    let rec iter_bucket i b =
      if i >= Weak.length b then () else
      match Weak.get b i with
      | Some v -> f v; iter_bucket (i+1) b
      | None -> iter_bucket (i+1) b
    in
    Array.iter (iter_bucket 0) t.table

  let count t =
    let rec count_bucket i b accu =
      if i >= Weak.length b then accu else
      count_bucket (i+1) b (accu + (if Weak.check b i then 1 else 0))
    in
    Array.fold_right (count_bucket 0) t.table 0

  let next_sz n = min (3*n/2 + 3) (Sys.max_array_length - 1)

  let rec resize t =
    let oldlen = Array.length t.table in
    let newlen = next_sz oldlen in
    if newlen > oldlen then begin
      let newt = create newlen in
      newt.limit <- t.limit + 100;          (* prevent resizing of newt *)
      fold (fun d () -> add newt d) t ();
      t.table <- newt.table;
      t.limit <- t.limit + 2;
    end

  and add t d =
    let index = d.hkey mod (Array.length t.table) in
    let bucket = t.table.(index) in
    let sz = Weak.length bucket in
    let rec loop i =
      if i >= sz then begin
        let newsz = min (sz + 3) (Sys.max_array_length - 1) in
        if newsz <= sz then 
	  failwith "Hashcons.Make: hash bucket cannot grow more";
        let newbucket = Weak.create newsz in
        Weak.blit bucket 0 newbucket 0 sz;
        Weak.set newbucket i (Some d);
        t.table.(index) <- newbucket;
        t.totsize <- t.totsize + (newsz - sz);
        if t.totsize > t.limit * Array.length t.table then resize t;
      end else begin
        if Weak.check bucket i
        then loop (i+1)
        else Weak.set bucket i (Some d)
      end
    in
    loop 0

  let hashcons t d p =
    let hkey = H.hash d in
    let index = hkey mod (Array.length t.table) in
    let bucket = t.table.(index) in
    let sz = Weak.length bucket in
    let rec loop i =
      if i >= sz then begin
	let hnode = { hkey = hkey; tag = gentag (); node = d; prop = p } in
	add t hnode;
	hnode
      end else begin
        match Weak.get_copy bucket i with
        | Some v when H.equal v.node d -> 
	    begin match Weak.get bucket i with
              | Some v -> v
              | None -> loop (i+1)
            end
        | _ -> loop (i+1)
      end
    in
    loop 0
  
  (* A version of hashcons that returns existing values, but does not
     insert the value into the table *)
  let find t d =
    let hkey = H.hash d in
    let index = hkey mod (Array.length t.table) in
    let bucket = t.table.(index) in
    let sz = Weak.length bucket in
    let rec loop i =
      if i >= sz then begin
        (* [hashcons] inserts the value into the table here, but we
           raise and exception *)
	raise (Not_found)
      end else begin
        match Weak.get_copy bucket i with
          | Some v when H.equal v.node d -> 
	    begin match Weak.get bucket i with
              | Some v -> v
              | None -> loop (i+1)
            end
          | _ -> loop (i+1)
      end
    in
    loop 0
      
  let stats t =
    let len = Array.length t.table in
    let lens = Array.map Weak.length t.table in
    Array.sort Int.compare lens;
    let totlen = Array.fold_left ( + ) 0 lens in
    (len, count t, totlen, lens.(0), lens.(len/2), lens.(len-1))
      
end

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
