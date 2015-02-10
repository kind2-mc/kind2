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


(*s Hash tables for hash-consing. (Some code is borrowed from the ocaml
    standard library, which is copyright 1996 INRIA.) *)

(* Changes from the original version: 

   - Hashconsing of pairs node and prop 
   - Added compare, equal and hash functions
   - Using arrays instead of weak arrays
   - Added find function 
*)


type ('a, 'b) hash_consed =  { 
  hkey : int;
  tag : int;
  node : 'a;
  prop : 'b }

(* Comparison based on tags *)
let compare { tag = t1 } { tag = t2 } = Pervasives.compare t1 t2

(* Equality based on tags *)
let equal { tag = t1 } { tag = t2 } = t1 = t2

(* Hashing based on stored hash *)
let hash { hkey = h } = h

(* Generate a new tag *)
let gentag =
  let r = ref 0 in
  fun () -> incr r; !r

(* Hashcons table *)
type ('a, 'b) t = {

  (* Array of buckets: each bucket is an array of values and an
     integer giving the next free position in the bucket array. *)
  mutable table : (int * (('a, 'b) hash_consed array)) array;

  (* sum of the bucket sizes *)
  mutable totsize : int;             

  (* max ratio totsize/table length *)
  mutable limit : int;         
}


(* Create a hashcons table of given size *)
let create sz =

  (* Fix the table to have at least seven buckets *)
  let sz = if sz < 7 then 7 else sz in

  (* Do not resize above the maximum possible array length *)
  let sz = if sz > Sys.max_array_length then Sys.max_array_length else sz in
  
  (* An empty bucket, the next free element has index zero *)
  let emptybucket = (0, [| |]) in
  
  (* Create the hashcons table *)
  { table = Array.make sz emptybucket;
    totsize = 0;
    limit = 3; }


(* Clear the hashcons table *)
let clear t =

  (* An empty bucket, the next free element has index zero *)
  let emptybucket = (0, [| |]) in

  (* Fill all entries in the table with empty buckets *)
  for i = 0 to Array.length t.table - 1 do t.table.(i) <- emptybucket done;

  (* The table is empty *)
  t.totsize <- 0;

  (* Reset the maximum ratio of bucket sizes to length of the table *)
  t.limit <- 3
    

(* Fold the hashcons table *)
let fold f t init =

  (* Fold over the entries in a bucket *)
  let rec fold_bucket i (sz, b) accu =

    (* Return accumulator if at the first free index *)
    if i >= sz then accu else
      
      (* Get entry from bucket and apply function *)
      let v = Array.get b i in fold_bucket (i+1) (sz, b) (f v accu)

  in

  (* Iterate over the table starting with the first entry *)
  Array.fold_right (fold_bucket 0) t.table init


(* Iterate over the hashcons table *)
let iter f t =

  (* Iterate over the entries in a bucket *)
  let rec iter_bucket i (sz, b) =

    (* Skip if at the first free index *)
    if i >= sz then () else

      (* Get entry from bucket *)
      let v = Array.get b i in f v; iter_bucket (i+1) (sz, b)

  in

  (* Iterate over the table starting with the first entry *)
  Array.iter (iter_bucket 0) t.table


(* Count the number of entries in the hashcons table *)
let count t =

  (* Iterate over the table and sum up the values of the next free
     index of each bucket *)
  Array.fold_right (fun (sz, _) a -> sz + a) t.table 0
    

(* Calculate the next size of the table *)
let next_sz n = min (3 * n / 2 + 3) (Sys.max_array_length - 1)


(* Resize the hashcons table *)
let rec resize t =
  
  (* Current number of buckets in the table *)
  let oldlen = Array.length t.table in
  
  (* Compute next number of buckets in the table *)
  let newlen = next_sz oldlen in

  (* Only copy if table is actually resized *)
  if newlen > oldlen then 

    (

      (* Create new table of computed next size *)
      let newt = create newlen in

      (* Temporarily increase limit to prevent resizing of newt *)
      newt.limit <- t.limit + 100;

      (* Add all entries from the old table to the new *)
      fold (fun d () -> add newt d) t ();

      (* Replace the old table with new *)
      t.table <- newt.table;

      (* Increase limit of the old table *)
      t.limit <- t.limit + 2;

    )

(* Add an entry to the hashcons table *)
and add t d =

  (* Compute the index of the bucket for the valaue from its hash *)
  let index = d.hkey mod (Array.length t.table) in

  (* Bucket for the value to be stored in and its first free entry *)
  let i, bucket = t.table.(index) in

  (* Size of bucket array *)
  let sz = Array.length bucket in
  
  (* Next free entry is out of the bucket? *)
  if i >= Array.length bucket then 

    (

      (* Add three entries to bucket array, but don't grow bucket
         further than the maximum size *)
      let newsz = min (i + 3) (Sys.max_array_length - 1) in

      (* Fail if maximum size reached *)
      if newsz <= sz then 
        failwith "Hashcons.add: hash bucket cannot grow more";

      (* Create new bucket, initialize all entries with the new
         value *)
      let newbucket = Array.make newsz d in

      (* Copy entries from the old bucket to the new bucket, the
         appended entries in the new bucket still contain the value to
         be stored *)
      Array.blit bucket 0 newbucket 0 sz;

      (* Store new bucket in table, we have added one entry *)
      t.table.(index) <- (i + 1, newbucket);

      (* Update size of table *)
      t.totsize <- t.totsize + (newsz - sz);

      (* Resize table if ratio of entries to number of buckets is
         above the limit *)
      if t.totsize > t.limit * Array.length t.table then resize t
      
    )
      
  else 

    (
      
      (* Put the value in the next free entry *)
      Array.set bucket i d;

      (* Store modified bucket in table, we have added one entry *)
      t.table.(index) <- (i + 1, bucket)

    )
  

(* Hashcons a value *)
let hashcons t d p =

  (* Hash the value to be stored *)
  let hkey = Hashtbl.hash d in

  (* Negative hash values result in negative array indices *)
  assert (hkey >= 0);

  (* Compute the index of the bucket for the value from its hash *)
  let index = hkey mod (Array.length t.table) in
  
  (* Bucket for the value to be stored in and its first free entry *)
  let l, bucket = t.table.(index) in

  (* Return previous hashconsed entry or add new entry to table *)
  let rec loop i =

    (* Iterated over all entries without finding the value? *)
    if i >= l then 

      (

        (* Create hashconsing record for value *)
        let hnode = { hkey = hkey; tag = gentag (); node = d; prop = p } in

        (* Add entry to hashcons table, this may trigger a resizing *)
        add t hnode;

        (* Return hashconsed value *)
        hnode

      )
        
    else

      (
        
        (* Get the entry from the bucket *)
        let v = Array.get bucket i in

        (* If value of entry is the value to hashcons, return it,
           otherwise go to the next entry *)
        if v.node = d then v else loop (i + 1)
          
      )
        
  in

  (* Iterate over entries in the bucket *)
  loop 0
    

(* Statistics of the hashcons table *)
let stats t =

  (* Number of buckets *)
  let len = Array.length t.table in

  (* Length of each bucket *)
  let lens = Array.map (fun (_, b) -> Array.length b) t.table in

  (* Sort to find longest bucket *)
  Array.sort Pervasives.compare lens;

  (* Sum up lengths of all buckets *)
  let totlen = Array.fold_left ( + ) 0 lens in

  (* Return statistics *)
  (
    
    (* Number of buckets *)
    len, 

    (* Number of entries in table *)
    count t, 

    (* Sum of sizes of buckets *)
    totlen, 

    (* Size of smallest bucket *)
    lens.(0), 

    (* Median bucket size *)
    lens.(len/2), 

    (* Size of greatest bucket *)
    lens.(len-1))


(* Functorial interface *)

(* Input signature *)
module type HashedType =
  sig
    type t
    type prop
    val equal : t -> t -> bool
    val hash : t -> int
  end

(* Output signature *)
module type S =
  sig
    type key
    type prop
    type t
    exception Key_not_found of key
    val create : int -> t
    val clear : t -> unit
    val hashcons : t -> key -> prop -> (key, prop) hash_consed
    val find : t -> key -> (key, prop) hash_consed
    val iter : ((key, prop) hash_consed -> unit) -> t -> unit
    val fold : ((key, prop) hash_consed -> 'a -> 'a) -> t -> 'a -> 'a
    val stats : t -> int * int * int * int * int * int
  end

(* Functor *)
module Make(H : HashedType) : (S with type key = H.t and type prop = H.prop) = 
struct

  (* Type of key *)
  type key = H.t

  (* Type of property *)
  type prop = H.prop

  (* Hashconsed key *)
  type data = (H.t, H.prop) hash_consed

      
  (* Hashcons table *)
  type t = {

    (* Array of buckets: each bucket is an array of values and an
       integer giving the next free position in the bucket array. *)
    mutable table : (int * (data array)) array;
    
    (* sum of the bucket sizes *)
    mutable totsize : int;             

    (* max ratio totsize/table length *)
    mutable limit : int;         

  }
  
  (* Exception raised by {!find} *)
  exception Key_not_found of key

  (* An empty bucket, the next free element has index zero *)
  let emptybucket = (0, [| |])

  (* Create a hashcons table of given size *)
  let create sz =

    (* Fix the table to have at least seven buckets *)
    let sz = if sz < 7 then 7 else sz in

    (* Do not resize above the maximum possible array length *)
    let sz = if sz > Sys.max_array_length then Sys.max_array_length else sz in
    
    (* Create the hashcons table *)
    { table = Array.make sz emptybucket;
      totsize = 0;
      limit = 3; }

  (* Clear the hashcons table *)
  let clear t =

    (* Fill all entries in the table with empty buckets *)
    for i = 0 to Array.length t.table - 1 do t.table.(i) <- emptybucket done;

    (* The table is empty *)
    t.totsize <- 0;
    
    (* Reset the maximum ratio of bucket sizes to length of the table *)
    t.limit <- 3
      

  (* Fold the hashcons table *)
  let fold f t init =
  
    (* Fold over the entries in a bucket *)
    let rec fold_bucket i (sz, b) accu =
      
      (* Return accumulator if at the first free index *)
      if i >= sz then accu else
        
        (* Get entry from bucket and apply function *)
        let v =  Array.get b i in fold_bucket (i+1) (sz, b) (f v accu)

    in
    
    (* Iterate over the table starting with the first entry *)
    Array.fold_right (fold_bucket 0) t.table init


  (* Iterate over the hashcons table *)
  let iter f t =
    
    (* Iterate over the entries in a bucket *)
    let rec iter_bucket i (sz, b) =
      
      (* Skip if at the first free index *)
      if i >= sz then () else
        
      (* Get entry from bucket *)
      let v = Array.get b i in f v; iter_bucket (i+1) (sz, b)

    in
    
    (* Iterate over the table starting with the first entry *)
    Array.iter (iter_bucket 0) t.table


  (* Count the number of entries in the hashcons table *)
  let count t =

    (* Iterate over the table and sum up the values of the next free
       index of each bucket *)
    Array.fold_right (fun (sz, _) a -> sz + a) t.table 0


  (* Calculate the next size of the table *)  
  let next_sz n = min (3 * n / 2 + 3) (Sys.max_array_length - 1)

  (* Resize the hashcons table *)
  let rec resize t =

    (* Current number of buckets in the table *)
    let oldlen = Array.length t.table in

    (* Compute next number of buckets in the table *)
    let newlen = next_sz oldlen in
    
    (* Only copy if table is actually resized *)
    if newlen > oldlen then 

      (

        
        (* Create new table of computed next size *)
        let newt = create newlen in

        (* Temporarily increase limit to prevent resizing of newt *)
        newt.limit <- t.limit + 100;
        
        (* Add all entries from the old table to the new *)
        fold (fun d () -> add newt d) t ();
        
        (* Replace the old table with new *)
        t.table <- newt.table;
        
        (* Increase limit of the old table *)
        t.limit <- t.limit + 2;

      )

  (* Add an entry to the hashcons table *)
  and add t d =

    (* Compute the index of the bucket for the valaue from its hash *)
    let index = d.hkey mod (Array.length t.table) in
    
    (* Bucket for the value to be stored in and its first free entry *)
    let i, bucket = t.table.(index) in

    (* Size of bucket array *)
    let sz = Array.length bucket in
    
    (* Next free entry is out of the bucket? *)
    if i >= sz then 

      (

        (* Add three entries to bucket array, but don't grow bucket
           further than the maximum size *)
        let newsz = min (i + 3) (Sys.max_array_length - 1) in

        (* Fail if maximum size reached *)
        if newsz <= sz then 
	  failwith "Hashcons.Make: hash bucket cannot grow more";
        
        (* Create new bucket, initialize all entries with the new
           value *)
        let newbucket = Array.make newsz d in
        
        (* Copy entries from the old bucket to the new bucket, the
           appended entries in the new bucket still contain the value to
           be stored *)
        Array.blit bucket 0 newbucket 0 sz;
        
        (* Store new bucket in table, we have added one entry *)
        t.table.(index) <- (i + 1, newbucket);
        
        (* Update size of table *)
        t.totsize <- t.totsize + (newsz - sz);

        (* Resize table if ratio of entries to number of buckets is
           above the limit *)
        if t.totsize > t.limit * Array.length t.table then resize t

      )
        
    else 

      (

        (* Put the value in the next free entry *)
        Array.set bucket i d;

        (* Store modified bucket in table, we have added one entry *)
        t.table.(index) <- (i + 1, bucket)

      )


  (* Hashcons a value *)
  let hashcons t d p =

    (* Hash the value to be stored *)
    let hkey = H.hash d in

    (* Negative hash values result in negative array indices *)
    assert (hkey >= 0);

    (* Compute the index of the bucket for the value from its hash *)
    let index = hkey mod (Array.length t.table) in

    (* Bucket for the value to be stored in and its first free entry *)
    let l, bucket = t.table.(index) in

    (* Return previous hashconsed entry or add new entry to table *)
    let rec loop i =

      (* Iterated over all entries without finding the value? *)
      if i >= l then 

        (
          
          (* Create hashconsing record for value *)
	  let hnode = { hkey = hkey; tag = gentag (); node = d; prop = p } in
          
          (* Add entry to hashcons table, this may trigger a resizing *)
	  add t hnode;

          (* Return hashconsed value *)
	  hnode
            
        )

      else 

        (
          (* Get the entry from the bucket *)
          let v = Array.get bucket i in

          (* If value of entry is the value to hashcons, return it,
             otherwise go to the next entry *)
          if H.equal v.node d then v else loop (i + 1)
            
        )

    in
    
    (* Iterate over entries in the bucket *)
    loop 0


  (* Hashcons a value *)
  let find t d =

    (* Hash the value to be stored *)
    let hkey = H.hash d in

    (* Negative hash values result in negative array indices *)
    assert (hkey >= 0);

    (* Compute the index of the bucket for the value from its hash *)
    let index = hkey mod (Array.length t.table) in

    (* Bucket for the value to be stored in and its first free entry *)
    let l, bucket = t.table.(index) in

    (* Return previous hashconsed entry or add new entry to table *)
    let rec loop i =

      (* Iterated over all entries without finding the value? *)
      if i >= l then 

        (
          
          (* [hashcons] inserts the value into the table here, but we
             raise an exception *)
	  raise Not_found
            
        )

      else 

        (
          (* Get the entry from the bucket *)
          let v = Array.get bucket i in

          (* If value of entry is the value to hashcons, return it,
             otherwise go to the next entry *)
          if H.equal v.node d then v else loop (i + 1)
            
        )

    in
    
    (* Iterate over entries in the bucket *)
    loop 0


  
(*
  (* A version of hashcons that returns existing values, but does not
     insert the value into the table *)
  let find t d =
    let hkey = H.hash d in
    let index = hkey mod (Array.length t.table) in
    (* A bucket can only contain entries up to the index of the first free entry *)
    let limit, bucket = t.table.(index) in
    (* let sz = Array.length bucket in *)
    let rec loop i =
      if i >= sz then begin
        (* [hashcons] inserts the value into the table here, but we
           raise and exception *)
	raise (Key_not_found d)
      end else begin
        match Array.get bucket i with
          | Some v when H.equal v.node d -> v
          | _ -> loop (i+1)
      end
    in
    loop 0
*)

      
  (* Statistics of the hashcons table *)
  let stats t =
    
    (* Number of buckets *)
    let len = Array.length t.table in
    
    (* Length of each bucket *)
    let lens = Array.map (fun (_, b) -> Array.length b) t.table in
    
    (* Sort to find longest bucket *)
    Array.sort Pervasives.compare lens;
    
    (* Sum up lengths of all buckets *)
    let totlen = Array.fold_left ( + ) 0 lens in
    
    (* Return statistics *)
    (
      
      (* Number of buckets *)
      len, 
      
      (* Number of entries in table *)
      count t, 
      
      (* Sum of sizes of buckets *)
      totlen, 
      
      (* Size of smallest bucket *)
      lens.(0), 

      (* Median bucket size *)
      lens.(len/2), 
      
      (* Size of greatest bucket *)
      lens.(len-1))
      
end

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
