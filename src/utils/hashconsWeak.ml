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


(* Tag generation must be atomic: all hashcons tables of the process draw
   from this single counter, and tables are used concurrently by several
   domains. *)
let gentag =
  let r = Atomic.make 0 in
  fun () -> Atomic.fetch_and_add r 1 + 1

type ('a, 'b) t = {
  lock : Mutex.t;                    (* protects all mutable state below *)
  mutable table : ('a, 'b) hash_consed Weak.t array;
  mutable totsize : int;             (* sum of the bucket sizes *)
  mutable limit : int;               (* max ratio totsize/table length *)
}

let create sz =
  let sz = if sz < 7 then 7 else sz in
  let sz = if sz > Sys.max_array_length then Sys.max_array_length else sz in
  let emptybucket = Weak.create 0 in
  { lock = Mutex.create ();
    table = Array.make sz emptybucket;
    totsize = 0;
    limit = 3; }

let clear t =
  Mutex.protect t.lock (fun () ->
    let emptybucket = Weak.create 0 in
    for i = 0 to Array.length t.table - 1 do t.table.(i) <- emptybucket done;
    t.totsize <- 0;
    t.limit <- 3)

let unsafe_fold f t init =
  let rec fold_bucket i b accu =
    if i >= Weak.length b then accu else
      match Weak.get b i with
	| Some v -> fold_bucket (i+1) b (f v accu)
	| None -> fold_bucket (i+1) b accu
  in
  Array.fold_right (fold_bucket 0) t.table init

let fold f t init =
  Mutex.protect t.lock (fun () -> unsafe_fold f t init)

let iter f t =
  Mutex.protect t.lock (fun () ->
    let rec iter_bucket i b =
      if i >= Weak.length b then () else
        match Weak.get b i with
	  | Some v -> f v; iter_bucket (i+1) b
	  | None -> iter_bucket (i+1) b
    in
    Array.iter (iter_bucket 0) t.table)

let unsafe_count t =
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
    unsafe_fold (fun d () -> add newt d) t ();
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
  Mutex.protect t.lock (fun () ->
    let hkey = Hashtbl.hash d land max_int in
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
    loop 0)

let stats t =
  Mutex.protect t.lock (fun () ->
    let len = Array.length t.table in
    let lens = Array.map Weak.length t.table in
    Array.sort Int.compare lens;
    let totlen = Array.fold_left ( + ) 0 lens in
    (len, unsafe_count t, totlen, lens.(0), lens.(len/2), lens.(len-1)))


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

  (* The table is protected by an array of locks rather than a single
     one: every engine domain creates terms constantly, and a single
     lock per table serializes them all. A bucket of index [i] is
     protected by the lock of stripe [i land (nstripes - 1)]; replacing
     the bucket array itself, which [resize] does, requires all the
     stripes. [nstripes] is a power of two. *)
  let nstripes = 64

  type t = {
    locks : Mutex.t array;             (* one lock per stripe *)
    mutable table : data Weak.t array; (* replaced by [resize], which
                                          holds every stripe *)
    totsize : int Atomic.t;            (* sum of the bucket sizes *)
    mutable limit : int;               (* max ratio totsize/table length,
                                          only written by [resize] *)
  }

  let emptybucket = Weak.create 0

  let create sz =
    let sz = if sz < 7 then 7 else sz in
    let sz = if sz > Sys.max_array_length then Sys.max_array_length else sz in
    {
      locks = Array.init nstripes (fun _ -> Mutex.create ());
      table = Array.make sz emptybucket;
      totsize = Atomic.make 0;
      limit = 3;
    }

  (* Lock of the stripe protecting the bucket of index [i] *)
  let stripe t i = Array.unsafe_get t.locks (i land (nstripes - 1))

  (* Lock every stripe, in increasing order to avoid deadlocks. The
     caller must not hold a stripe already. *)
  let lock_all t = Array.iter Mutex.lock t.locks

  let unlock_all t =
    for i = Array.length t.locks - 1 downto 0 do
      Mutex.unlock (Array.unsafe_get t.locks i)
    done

  let with_all_stripes t f =
    lock_all t ;
    Fun.protect ~finally:(fun () -> unlock_all t) f

  let clear t =
    with_all_stripes t (fun () ->
      for i = 0 to Array.length t.table - 1 do
        t.table.(i) <- emptybucket
      done;
      Atomic.set t.totsize 0;
      t.limit <- 3)

  let unsafe_fold f t init =
    let rec fold_bucket i b accu =
      if i >= Weak.length b then accu else
      match Weak.get b i with
      | Some v -> fold_bucket (i+1) b (f v accu)
      | None -> fold_bucket (i+1) b accu
    in
    Array.fold_right (fold_bucket 0) t.table init

  let fold f t init =
    with_all_stripes t (fun () -> unsafe_fold f t init)

  let iter f t =
    with_all_stripes t (fun () ->
      let rec iter_bucket i b =
        if i >= Weak.length b then () else
        match Weak.get b i with
        | Some v -> f v; iter_bucket (i+1) b
        | None -> iter_bucket (i+1) b
      in
      Array.iter (iter_bucket 0) t.table)

  let unsafe_count t =
    let rec count_bucket i b accu =
      if i >= Weak.length b then accu else
      count_bucket (i+1) b (accu + (if Weak.check b i then 1 else 0))
    in
    Array.fold_right (count_bucket 0) t.table 0

  let next_sz n = min (3*n/2 + 3) (Sys.max_array_length - 1)

  (* Insert [d] in [table], which no other domain can reach yet. Only
     used to fill the new table of a resize. *)
  let raw_add table totsize d =
    let index = d.hkey mod (Array.length table) in
    let bucket = table.(index) in
    let sz = Weak.length bucket in
    let rec loop i =
      if i >= sz then begin
        let newsz = min (sz + 3) (Sys.max_array_length - 1) in
        if newsz <= sz then
          failwith "Hashcons.Make: hash bucket cannot grow more";
        let newbucket = Weak.create newsz in
        Weak.blit bucket 0 newbucket 0 sz;
        Weak.set newbucket i (Some d);
        table.(index) <- newbucket;
        totsize := !totsize + (newsz - sz)
      end else if Weak.check bucket i then loop (i+1)
      else Weak.set bucket i (Some d)
    in
    loop 0

  (* Grow the table if it is still too small. Called without holding
     any stripe, after an insertion said the table had grown too
     dense. *)
  let resize_if_needed t =
    with_all_stripes t (fun () ->
      let oldlen = Array.length t.table in
      if Atomic.get t.totsize > t.limit * oldlen then begin
        let newlen = next_sz oldlen in
        if newlen > oldlen then begin
          let newtable = Array.make newlen emptybucket in
          let newtotsize = ref 0 in
          (* Entries collected in the meantime are dropped *)
          Array.iter
            (fun b ->
              for i = 0 to Weak.length b - 1 do
                match Weak.get b i with
                | Some d -> raw_add newtable newtotsize d
                | None -> ()
              done)
            t.table ;
          t.table <- newtable ;
          Atomic.set t.totsize !newtotsize ;
          t.limit <- t.limit + 2
        end
      end)

  (* Insert [d] in the bucket of index [index]. The stripe of [index]
     must be held. Returns whether the table has become too dense. *)
  let add_at t index d =
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
        let totsize =
          Atomic.fetch_and_add t.totsize (newsz - sz) + (newsz - sz)
        in
        totsize > t.limit * Array.length t.table
      end else if Weak.check bucket i then loop (i+1)
      else (Weak.set bucket i (Some d); false)
    in
    loop 0

  (* Run [f index] holding the stripe of the bucket of [hkey].

     The table is read before the stripe is taken, so a resize may have
     replaced it in between; the check under the lock detects that and
     the operation is retried. A resize cannot happen while the stripe
     is held. *)
  let rec with_bucket : 'a. t -> int -> (int -> 'a) -> 'a =
    fun t hkey f ->
    let table = t.table in
    let index = hkey mod (Array.length table) in
    let m = stripe t index in
    Mutex.lock m ;
    if t.table != table then (
      Mutex.unlock m ;
      with_bucket t hkey f
    ) else
      match f index with
      | res -> Mutex.unlock m ; res
      | exception e -> Mutex.unlock m ; raise e

  let hashcons t d p =
    let hkey = H.hash d land max_int in
    let node, need_resize =
      with_bucket t hkey (fun index ->
        let bucket = t.table.(index) in
        let sz = Weak.length bucket in
        let rec loop i =
          if i >= sz then begin
            let hnode = { hkey = hkey; tag = gentag (); node = d; prop = p } in
            let need_resize = add_at t index hnode in
            hnode, need_resize
          end else begin
            match Weak.get_copy bucket i with
            | Some v when H.equal v.node d ->
              begin match Weak.get bucket i with
                | Some v -> v, false
                | None -> loop (i+1)
              end
            | _ -> loop (i+1)
          end
        in
        loop 0)
    in
    if need_resize then resize_if_needed t ;
    node

  (* A version of hashcons that returns existing values, but does not
     insert the value into the table *)
  let find t d =
    let hkey = H.hash d land max_int in
    with_bucket t hkey (fun index ->
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
      loop 0)

  let stats t =
    with_all_stripes t (fun () ->
      let len = Array.length t.table in
      let lens = Array.map Weak.length t.table in
      Array.sort Int.compare lens;
      let totlen = Array.fold_left ( + ) 0 lens in
      (len, unsafe_count t, totlen, lens.(0), lens.(len/2), lens.(len-1)))

end

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
