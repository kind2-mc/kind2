module ScMap = Scope.Map
module SVSet = StateVar.StateVarSet

type term_cat = NodeCall of string * SVSet.t
| ContractItem of StateVar.t
| Equation of StateVar.t
| Assertion of StateVar.t
| Unknown

type equation = {
  init_opened: Term.t ;
  init_closed: Term.t ;
  trans_opened: Term.t ;
  trans_closed: Term.t ;
}

type loc = {
  pos: Lib.position ;
  index: LustreIndex.index ;
}

type loc_equation = equation * (loc list) * term_cat

type ivc = loc_equation list ScMap.t

type ivc_result = {
  success: bool;
  ivc: ivc;
}

val pp_print_loc_eq : 'a InputSystem.t -> TransSys.t -> Format.formatter -> loc_equation -> unit
val pp_print_loc_eqs : 'a InputSystem.t -> TransSys.t -> Format.formatter -> loc_equation list -> unit

val pp_print_ivc : 'a InputSystem.t -> TransSys.t -> string -> Format.formatter -> ivc -> unit
val pp_print_ivc_xml : 'a InputSystem.t -> TransSys.t -> string -> Format.formatter -> ivc -> unit
val pp_print_ivc_json : 'a InputSystem.t -> TransSys.t -> string -> Format.formatter -> ivc -> unit

val error_result : ivc_result

val compare_loc : loc -> loc -> int

(** For a given transition system, returns the full initial inductive validity core
(not minimized, so that it contains all the equations of the transition system) *)
val all_eqs : 'a InputSystem.t -> TransSys.t -> ivc

(** Separate an IVC into two IVC, the second one containing elements from the categories selected
    by the user, and the first one containing the others elements *)
val separate_ivc_by_category : ivc -> (ivc * ivc)

(** [minimize_lustre_ast full_ivc ivc ast]
    Minimize the lustre AST [ast] according to the inductive validity core [ivc].
    [full_ivc] should be an IVC containing all the equations, it can be obtained by calling [all_eqs].
    The optional parameter valid_lustre (default: false) determine whether the generated AST must be
    a valid lustre program or not (in this case, it will be more concise). *)
val minimize_lustre_ast : ?valid_lustre:bool -> ivc -> ivc -> LustreAst.t -> LustreAst.t

(** Outputs a minized (not necessarily minimal) inductive validity core by computing an UNSAT core.
    It [approximate] is set to false, then the unsat core computed is not guaranteed to be minimal. *)
val ivc_uc :
  'a InputSystem.t ->
  ?approximate:bool ->
  TransSys.t ->
  ivc_result

(** Outputs a minimal inductive validity core by trying to remove all the equations one after another
    and running the whole analysis on the new system each time. *)
val ivc_bf :
  'a InputSystem.t ->
  Analysis.param ->
  (
    bool ->
    Lib.kind_module list -> 'a InputSystem.t -> Analysis.param -> TransSys.t
    -> unit
   ) ->
  TransSys.t ->
  ivc_result

(** Outputs a minimal inductive validity core by first computing an UNSAT core (ivc_uc),
    and then trying to remove the remaining equations with bruteforce (ivc_bf).
    This should be faster than ivc_bf. *)
val ivc_ucbf :
  'a InputSystem.t ->
  Analysis.param ->
  (
    bool ->
    Lib.kind_module list -> 'a InputSystem.t -> Analysis.param -> TransSys.t
    -> unit
   ) ->
  TransSys.t ->
  ivc_result
