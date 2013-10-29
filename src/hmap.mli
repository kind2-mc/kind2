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

(*i $Id: hmap.mli,v 1.5 2008-07-21 14:53:06 filliatr Exp $ i*)

(*s Maps over hash-consed values, implemented as Patricia trees.
    See the module [Hashcons] and [Ptmap]. *)

type ('a, 'b, 'c) t

type ('a, 'b) key = ('a, 'b) Hashcons.hash_consed

val empty : ('a, 'b, 'c) t

val add : ('a, 'b) key -> 'c -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t

val find : ('a, 'b) key -> ('a, 'b, 'c) t -> 'c

val remove : ('a, 'b) key -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t

val mem :  ('a, 'b) key -> ('a, 'b, 'c) t -> bool

val iter : (('a, 'b) key -> 'c -> unit) -> ('a, 'b, 'c) t -> unit

val map : ('c -> 'd) -> ('a, 'b, 'c) t -> ('a, 'b, 'd) t

val mapi : (('a, 'b) key -> 'c -> 'd) -> ('a, 'b, 'c) t -> ('a, 'b , 'd) t

val fold : (('a, 'b) key -> 'c -> 'd -> 'd) -> ('a, 'b, 'c) t -> 'd -> 'd

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
