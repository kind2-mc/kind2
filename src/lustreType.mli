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

(** Lustre types 

    @author Christoph Sticksel *)


(** A type *)
type t = private
  | Bool                                  (** The Boolean type *)
  | Int                                   (** The integer type *)
  | Real                                  (** The real type *)
  | IntRange of (Numeral.t * Numeral.t)   (** An integer range type *)
  | FreeType of LustreIdent.t             (** A free (uninterpreted) type *)
  | Enum of LustreIdent.t list            (** An enumeration type *)

(** Total ordering of types *)
val compare : t -> t -> int

(** Equality of types *)
val equal : t -> t -> bool

(** Pretty-print a type *)
val pp_print_lustre_type : bool -> Format.formatter -> t -> unit 

(** Return the Boolean type *)
val t_bool : t

(** Return the integer type *)
val t_int : t

(** Return the real type *)
val t_real : t

(** Construct an integer range type *)
val mk_int_range : Numeral.t -> Numeral.t -> t

(** Construct a free type *)
val mk_free_type : LustreIdent.t -> t

(** Construct an enumerated type *)
val mk_enum : LustreIdent.t list -> t

(** [check_type s t] returns [true] if [s] is a subtype of [t] *)
val check_type : t -> t -> bool

(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
