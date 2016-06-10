(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

(* Do not open the Lib module here, the lib module uses this module *)

(* ********************************************************************* *)
(* Types and hash-consing                                                *)
(* ********************************************************************* *)


(* A private type that cannot be constructed outside this module *)
type string_node = string 


(* Properties of a string *)
type string_prop = unit


(* Hashconsed string *)
type t = (string_node, string_prop) Hashcons.hash_consed


(* Hashing and equality on strings *)
module String_node = struct

  (* String type *)
  type t = string_node

  (* No properties for a string *)
  type prop = string_prop

  (* Test strings for equality *)
  let equal = (=)

  (* Return a hash of a string *)
  let hash = Hashtbl.hash

end


(* Hashconsed strings *)
module HString = Hashcons.Make(String_node)


(* Storage for hashconsed strings *)
let ht = HString.create 251


(* ********************************************************************* *)
(* Hashtables, maps and sets                                             *)
(* ********************************************************************* *)


(* Comparison function on strings *)
let compare = Hashcons.compare


(* Equality function on strings *)
let equal = Hashcons.equal


(* Hashing function on strings *)
let hash = Hashcons.hash 


(* Module as input to functors *)
module HashedString = struct 
    
  (* Dummy type to prevent writing [type t = t] which is cyclic *)
  type z = t
  type t = z

  (* Compare tags of hashconsed terms for equality *)
  let equal = equal
    
  (* Use hash of term *)
  let hash = hash

end


(* Module as input to functors *)
module OrderedString = struct 

  (* Dummy type to prevent writing [type t = t] which is cyclic *)
  type z = t
  type t = z

  (* Compare tags of hashconsed symbols *)
  let compare = compare

end


(* Hashtable *)
module HStringHashtbl = Hashtbl.Make (HashedString)


(* Set *)
module HStringSet = Set.Make (OrderedString)


(* Map *)
module HStringMap = Map.Make (OrderedString)


(* ********************************************************************* *)
(* Pretty-printing                                                       *)
(* ********************************************************************* *)


(* Pretty-print a string *)
let pp_print_string = Format.pp_print_string

(* Pretty-print a hashconsed string *)
let pp_print_hstring ppf { Hashcons.node = n } = pp_print_string ppf n

(* Pretty-print a hashconsed term to the standard formatter *)
let print_hstring = pp_print_hstring Format.std_formatter 

(* Pretty-print a term  to the standard formatter *)
let print_string = pp_print_string Format.std_formatter 

(* Return a string representation of a term *)
let string_of_hstring { Hashcons.node = n } = n


(* ********************************************************************* *)
(* Constructors                                                          *)
(* ********************************************************************* *)


(* Return an initialized property for the string *)
let mk_prop s = ()


(* Return a hashconsed string *)
let mk_hstring s = HString.hashcons ht s (mk_prop s)


(* Import a string from a different instance into this hashcons
   table *)
let import { Hashcons.node = s } = mk_hstring s

(* ********************************************************************* *)
(* String functions                                                      *)
(* ********************************************************************* *)

let length { Hashcons.node = n } = Bytes.length n 

let get { Hashcons.node = n } i = Bytes.get n i

let set { Hashcons.node = n } i c = 

  (* Copy to a fresh string *)
  let n' = Bytes.copy n in 

  Bytes.set n' i c;
  mk_hstring n' 

let create i = mk_hstring (Bytes.create i)

let make i c = mk_hstring (Bytes.make i c)

let sub { Hashcons.node = n } i j = Bytes.sub n i j

let fill { Hashcons.node = n } i j c = 

  (* Copy to a fresh string *)
  let n' = Bytes.copy n in 

  Bytes.fill n' i j c;
  mk_hstring n'

let blit { Hashcons.node = n } i { Hashcons.node = m } j k = 

  (* Copy to a fresh string *)
  let n' = Bytes.copy n in 
  
  Bytes.blit n' i m j k;
  mk_hstring n'

let concat { Hashcons.node = n } l =

  mk_hstring (Bytes.concat n (List.map string_of_hstring l))

let iter f { Hashcons.node = n } = Bytes.iter f n

let iteri f { Hashcons.node = n } = Bytes.iteri f n

let map f { Hashcons.node = n } = mk_hstring (Bytes.map f n)

let trim { Hashcons.node = n } = mk_hstring (Bytes.trim n)

let escaped { Hashcons.node = n } = mk_hstring (Bytes.escaped n)

let index { Hashcons.node = n } c = Bytes.index n c

let rindex { Hashcons.node = n } c = Bytes.rindex n c

let index_from { Hashcons.node = n } i c = Bytes.index_from n i c

let rindex_from { Hashcons.node = n } i c = Bytes.rindex_from n i c
 
let contains { Hashcons.node = n } c = Bytes.contains n c

let contains_from { Hashcons.node = n } i c = Bytes.contains_from n i c

let rcontains_from { Hashcons.node = n } i c = Bytes.rcontains_from n i c

let uppercase { Hashcons.node = n } = mk_hstring (Bytes.uppercase n)

let lowercase { Hashcons.node = n } = mk_hstring (Bytes.lowercase n)

let capitalize { Hashcons.node = n } = mk_hstring (Bytes.capitalize n)

let uncapitalize { Hashcons.node = n } = mk_hstring (Bytes.uncapitalize n)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
