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

type ivc = (equation * (loc list) * term_cat) list ScMap.t

type ivc_result = {
  success: bool;
  ivc: ivc;
}

val error_result : ivc_result

val all_eqs : 'a InputSystem.t -> TransSys.t -> ivc_result

val minimize_lustre_ast : ?valid_lustre:bool -> ivc_result -> ivc_result -> LustreAst.t -> LustreAst.t

val ivc_uc :
  'a InputSystem.t ->
  ?approximate:bool ->
  TransSys.t ->
  ivc_result

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
