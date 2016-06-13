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


module type HSig = sig
  type ('a, 'b) hash_consed = private {
    hkey : int;
    tag : int;
    node : 'a;
    prop : 'b }
  val compare : ('a, 'b) hash_consed -> ('a, 'b) hash_consed -> int
  val equal : ('a, 'b) hash_consed -> ('a, 'b) hash_consed -> bool
  val hash : ('a, 'b) hash_consed -> int
  type ('a, 'b) t
  val create : int -> ('a, 'b) t
  val clear : ('a, 'b) t -> unit
  val hashcons : ('a, 'b) t -> 'a -> 'b -> ('a, 'b) hash_consed
  val iter : (('a, 'b) hash_consed -> unit) -> ('a, 'b) t -> unit
  val fold : (('a, 'b) hash_consed -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c
  val stats : ('a, 'b) t -> int * int * int * int * int * int
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
  module Make(H : HashedType) : (S with type key = H.t and type prop = H.prop)
end



let selected =
  if Flags.weakhcons () then
    (module HashconsWeak : HSig)
  else
    (module HashconsStrong : HSig)


include (val (selected))

  
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
