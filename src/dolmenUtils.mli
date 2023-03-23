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

val opt_list_to_list : 'a list option -> 'a list

val dolmen_id_to_string : id -> string

val dolmen_opt_id_to_string : id option -> string

val dolmen_symbol_term_to_id : term -> id

val type_of_dolmen_builtin : Term.builtin -> Type.t

val dolmen_term_to_id_type : term -> id * Type.t

val prime : id -> id

val dolmen_term_to_expr : (Id.t * Var.t) list -> term -> KindTerm.t

val opt_dolmen_term_to_expr : (Id.t * Var.t) list -> term option -> KindTerm.t

