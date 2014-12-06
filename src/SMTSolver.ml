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

open Lib


let gentag =
  let r = ref 0 in
  fun () -> incr r; !r



(* Input signature for the Make functor *)
module type Solver =
sig 

  type t

  val create_instance : 
    ?produce_assignments:bool -> 
    ?produce_models:bool -> 
    ?produce_proofs:bool -> 
    ?produce_cores:bool -> 
    SMTExpr.logic ->
    int ->
    t

  val delete_instance : t -> unit

  val declare_fun : t -> string -> SMTExpr.sort list -> SMTExpr.sort -> SMTExpr.response

  val define_fun : t -> string -> SMTExpr.var list -> SMTExpr.sort -> SMTExpr.t -> SMTExpr.response

  val assert_expr : t -> SMTExpr.t -> SMTExpr.response

  val push : t -> int -> SMTExpr.response 

  val pop : t -> int -> SMTExpr.response 

  val check_sat : ?timeout:int -> t -> SMTExpr.check_sat_response

  val check_sat_assuming : t -> SMTExpr.t list -> SMTExpr.check_sat_response

  val get_value : t -> SMTExpr.t list -> SMTExpr.response * (SMTExpr.t * SMTExpr.t) list

  val get_unsat_core : t -> SMTExpr.response * string list

  val execute_custom_command : t -> string -> SMTExpr.custom_arg list -> int -> SMTExpr.response * HStringSExpr.t list

  val execute_custom_check_sat_command : string -> t -> SMTExpr.check_sat_response

end

let smtsolver_module () = match Flags.smtsolver () with 

  | `Z3_SMTLIB
  | `CVC4_SMTLIB
  | `MathSat5_SMTLIB
  | `Yices_SMTLIB -> (module SMTLIBSolver : Solver)

  | `detect -> raise (Invalid_argument "smtsolver_module")


(* Output signature of the Make functor *)
module type S =
sig

  type solver_t 

  type t

  val create_instance : 
    ?produce_assignments:bool -> 
    ?produce_models:bool -> 
    ?produce_proofs:bool -> 
    ?produce_cores:bool -> 
    SMTExpr.logic -> 
    t

  val delete_instance : t -> unit

  val declare_fun : t -> string -> SMTExpr.sort list -> SMTExpr.sort -> SMTExpr.response

  val define_fun : t -> string -> SMTExpr.var list -> SMTExpr.sort -> SMTExpr.t -> SMTExpr.response

  val assert_expr : t -> SMTExpr.t -> SMTExpr.response

  val push : t -> int -> SMTExpr.response 

  val pop : t -> int -> SMTExpr.response 

  val check_sat : ?timeout:int -> t -> SMTExpr.check_sat_response

  val check_sat_assuming : t -> SMTExpr.t list -> SMTExpr.check_sat_response

  val get_value : t -> SMTExpr.t list -> SMTExpr.response * (SMTExpr.t * SMTExpr.t) list

  val get_unsat_core : t -> SMTExpr.response * string list

  val execute_custom_command : t -> string -> SMTExpr.custom_arg list -> int -> SMTExpr.response * HStringSExpr.t list

  val execute_custom_check_sat_command : string -> t -> SMTExpr.check_sat_response

end

(* Functor to create a generic SMT solver *)
module Make (S : Solver) : S with type solver_t = S.t = 
struct
  
  type solver_t = S.t

  type t = 
      { solver : solver_t; 
        id : int }

  type attr = [ `NAME of string ]

  type expr = SMTExpr.t

  type sort

  let create_instance 
      ?produce_assignments
      ?produce_models
      ?produce_proofs
      ?produce_cores
      l = 
    
    let id = gentag () in
    
    let s = 
      S.create_instance 
        ?produce_assignments 
        ?produce_models
        ?produce_proofs
        ?produce_cores
        l
        id
    in

    { solver = s;
      id = id } 

      
  let delete_instance { solver } = 

    S.delete_instance solver


  let declare_fun { solver } f a r = 

    S.declare_fun solver f a r


  let define_fun { solver } f a r d = 

    S.define_fun solver f a r d


  let assert_expr { solver } e = 
    
    S.assert_expr solver e


  let push { solver } i = 

    S.push solver i


  let pop { solver } i = 
    
    S.pop solver i

          
  let check_sat ?(timeout = 0) { solver } = 

    Stat.start_timer Stat.smt_check_sat_time;
    let res = S.check_sat ~timeout solver in
    Stat.record_time Stat.smt_check_sat_time;
    res


  let check_sat_assuming { solver } exprs = 

    Stat.start_timer Stat.smt_check_sat_time;
    let res = S.check_sat_assuming solver exprs in
    Stat.record_time Stat.smt_check_sat_time;
    res


  let get_value { solver } e = 

    Stat.start_timer Stat.smt_get_value_time;
    let res = S.get_value solver e in
    Stat.record_time Stat.smt_get_value_time;
    res


  let get_unsat_core { solver } = 

    S.get_unsat_core solver


  let execute_custom_command { solver } c a r = 
    
    S.execute_custom_command solver c a r

                             
  let execute_custom_check_sat_command c { solver } =

    S.execute_custom_check_sat_command c solver


end

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
