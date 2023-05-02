open Dolmen

module KindTerm = Term

(* Instantiate a module for parsing logic languages *)
module Loc = Std.Loc
module Id = Std.Id
module Term = Std.Term
module Statement = Std.Statement

type loc = Loc.t
type id = Id.t
type term = Term.t
type statement = Statement.t

type enum = {
  name: Dolmen.Std.Id.t;
  get_type: Type.t;
  to_int: (Dolmen.Std.Id.t * Numeral.t) list;
  to_str: (Numeral.t * Dolmen.Std.Id.t) list;
}

val empty_enum : id -> Type.t -> enum

val opt_list_to_list : 'a list option -> 'a list

val dolmen_id_to_string : id -> string

val dolmen_opt_id_to_string : id option -> string

val dolmen_binding_to_types : enum list -> term -> Type.t list * Type.t

val type_of_dolmen_term : enum list -> term -> Type.t

val dolmen_symbol_term_to_id : term -> id

val dolmen_id_to_kind_term : enum list -> (id * Var.t) list -> id -> KindTerm.t

val type_of_dolmen_builtin : Term.builtin -> Type.t

val dolmen_term_to_id_type : enum list -> term -> id * Type.t

val prepend_to_id : string -> id -> id

val append_to_id : id -> string -> id

val join_ids : id -> id -> id

val prime : id -> id

val dolmen_term_to_expr : enum list -> (Id.t * Var.t) list -> term -> KindTerm.t

val opt_dolmen_term_to_expr : enum list -> (Id.t * Var.t) list -> term option -> KindTerm.t

val print_enums : Format.formatter -> enum list -> unit

val process : string -> statement list

