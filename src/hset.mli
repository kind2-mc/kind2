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

(*s Sets of hash-consed values, implemented as Patricia trees. 
    See the modules [Hashcons] and [Ptset]. *)

type ('a, 'b) t

type ('a, 'b) elt = ('a, 'b) Hashcons.hash_consed

val empty : ('a, 'b) t

val is_empty : ('a, 'b) t -> bool

val mem : ('a, 'b) elt -> ('a, 'b) t -> bool

val add : ('a, 'b) elt -> ('a, 'b) t -> ('a, 'b) t

val singleton : ('a, 'b) elt -> ('a, 'b) t

val remove : ('a, 'b) elt -> ('a, 'b) t -> ('a, 'b) t

val union : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t

val subset : ('a, 'b) t -> ('a, 'b) t -> bool

val inter : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t

val diff : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t

val equal : ('a, 'b) t -> ('a, 'b) t -> bool

val compare : ('a, 'b) t -> ('a, 'b) t -> int

val elements : ('a, 'b) t -> ('a, 'b) elt list

val choose : ('a, 'b) t -> ('a, 'b) elt

val cardinal : ('a, 'b) t -> int

val iter : (('a, 'b) elt -> unit) -> ('a, 'b) t -> unit

val fold : (('a, 'b) elt -> 'b -> 'b) -> ('a, 'b) t -> 'b -> 'b

val for_all : (('a, 'b) elt -> bool) -> ('a, 'b) t -> bool

val exists : (('a, 'b) elt -> bool) -> ('a, 'b) t -> bool

val filter : (('a, 'b) elt -> bool) -> ('a, 'b) t -> ('a, 'b) t

val partition : (('a, 'b) elt -> bool) -> ('a, 'b) t -> ('a, 'b) t * ('a, 'b) t

(*s Warning: [min_elt] and [max_elt] are linear w.r.t. the size of the
    set. In other words, [min_elt t] is barely more efficient than [fold
    min t (choose t)]. *)

val min_elt : ('a, 'b) t -> ('a, 'b) elt
val max_elt : ('a, 'b) t -> ('a, 'b) elt

(*s Additional functions not appearing in the signature [Set.S] from ocaml
    standard library. *)

(* [intersect u v] determines if sets [u] and [v] have a non-empty 
   intersection. *) 

val intersect : ('a, 'b) t -> ('a, 'b) t -> bool

(* TODO: implement split to be compatible with the signature Set.S *)
val split : ('a, 'b) elt -> ('a, 'b) t -> ('a, 'b) t * bool * ('a, 'b) t


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
