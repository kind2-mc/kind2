(*
This file is part of the Kind verifier

* Copyright (c) 2007-2013 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
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
    t

  val delete_instance : t -> unit

  val declare_fun : t -> string -> SMTExpr.sort list -> SMTExpr.sort -> SMTExpr.response

  val define_fun : t -> string -> SMTExpr.sort list -> SMTExpr.sort -> SMTExpr.t -> SMTExpr.response

  val assert_expr : t -> SMTExpr.t -> SMTExpr.response

  val push : t -> int -> SMTExpr.response 

  val pop : t -> int -> SMTExpr.response 

  val check_sat : ?timeout:int -> t -> SMTExpr.check_sat_response

  val get_value : t -> SMTExpr.t list -> SMTExpr.response * (SMTExpr.t * SMTExpr.t) list

  val get_unsat_core : t -> SMTExpr.response * string list

  val execute_custom_command : t -> string -> SMTExpr.custom_arg list -> int -> SMTExpr.response * HStringSExpr.t list

  val execute_custom_check_sat_command : string -> t -> SMTExpr.check_sat_response

end

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

  val define_fun : t -> string -> SMTExpr.sort list -> SMTExpr.sort -> SMTExpr.t -> SMTExpr.response

  val assert_expr : t -> SMTExpr.t -> SMTExpr.response

  val push : t -> int -> SMTExpr.response 

  val pop : t -> int -> SMTExpr.response 

  val check_sat : ?timeout:int -> t -> SMTExpr.check_sat_response

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
      ?(produce_assignments = false)
      ?(produce_models = false) 
      ?(produce_proofs = false) 
      ?(produce_cores = false)     
      l = 
    
    let id = gentag () in

    debug smt
      "@[<v>[%d]@,@[<hv 1>(set-option@ :print-success@ true)@]@,%t@[<hv 1>(set-option@ :produce-assignments@ %B)@]@,@[<hv 1>(set-option@ :produce-models@ %B)@]@,@[<hv 1>(set-option@ :produce-proofs@ %B)@]@,@[<hv 1>(set-option@ :produce-unsat-cores@ %B)@]@]"
      id
      (function ppf -> match l with
         | `detect -> ()
         | _ -> 
           Format.fprintf ppf
             "@[<hv 1>(set-logic@ %a)@]@," 
             SMTExpr.pp_print_logic l)
      produce_assignments
      produce_models 
      produce_proofs
      produce_cores
    in

  let s = 
    S.create_instance 
      ~produce_assignments 
      ~produce_models
      ~produce_proofs
      ~produce_cores
      l 
  in

  { solver = s;
    id = id } 

  let delete_instance { solver = s; id = id } = 

    debug smt
      "@[<v>[%d]@,@[<hv 1>(exit)@]@]" id
    in
    
    S.delete_instance s


  let declare_fun { solver = s; id = id } f a r = 

    debug smt
      "@[<v>[%d]@,@[<hv 1>(declare-fun@ %s@ @[<hv 1>(%a)@]@ %a)@]@]" 
      id
      f
      (pp_print_list SMTExpr.pp_print_sort "@ ") a
      SMTExpr.pp_print_sort r
    in

    let res = S.declare_fun s f a r in

    debug smt
      "@[<v>[%d]@,;; %a@]" 
      id
      SMTExpr.pp_print_response res
    in 

    res


  let define_fun { solver = s; id = id } f a r d = 

    debug smt
      "@[<v>[%d]@,@[<hv 1>(define-fun@ %s@ @[<hv 1>(%a)@]@ %a@ %a)@]@]" 
      id
      f
      (pp_print_list SMTExpr.pp_print_sort "@ ") a
      SMTExpr.pp_print_sort r
      SMTExpr.pp_print_expr d
    in

    let res = S.define_fun s f a r d in

    debug smt
      "@[<v>[%d]@,;; %a@]" 
      id
      SMTExpr.pp_print_response res
    in 

    res


  let assert_expr { solver = s; id = id } e = 
    
    debug smt "@[<v>[%d]@,@[<hv 1>(assert@ @[<hv>%a@])@]@]" 
      id 
      SMTExpr.pp_print_expr e 
    in 
    
    let res = S.assert_expr s e in

    debug smt
      "@[<v>[%d]@,;; %a@]" 
      id
      SMTExpr.pp_print_response res
    in 

    res


  let push { solver = s; id = id } i = 

    debug smt "@[<v>[%d]@,@[<hv 1>(push@ %i)@]@]" id i in
    
    let res = S.push s i in

    debug smt
      "@[<v>[%d]@,;; %a@]" 
      id
      SMTExpr.pp_print_response res
    in 

    res


  let pop { solver = s; id = id } i = 
    
    debug smt "@[<v>[%d]@,@[<hv 1>(pop@ %i)@]@]" id i in
    
    let res = S.pop s i in
 
    debug smt
      "@[<v>[%d]@,;; %a@]" 
      id
      SMTExpr.pp_print_response res
    in 

    res


  let check_sat ?(timeout = 0) { solver = s; id = id } = 

    debug smt "@[<v>[%d]@,@[<hv 1>(check-sat)@]@]" id in

    Stat.start_timer Stat.smt_check_sat_time;

    let res = S.check_sat ~timeout s in

    Stat.record_time Stat.smt_check_sat_time;

    (debug smt
        "@[<v>[%d]@,;; %a@]" 
        id
        SMTExpr.pp_print_check_sat_response res
     in 

     res)


  let get_value { solver = s; id = id } e = 
    
    debug smt 
      "@[<v>[%d]@,@[<hv 1>(get-value@ @[<hv 1>(%a)@])@]@]" 
      id
      (pp_print_list SMTExpr.pp_print_expr "@ ") e
    in

    Stat.start_timer Stat.smt_get_value_time;

    let res = S.get_value s e in

    Stat.record_time Stat.smt_get_value_time;

    (debug smt
      "@[<v>[%d]@,;; %a@]" 
      id
      SMTExpr.pp_print_get_value_response res
    in 

    res)


  let get_unsat_core { solver = s; id = id } = 
    
    debug smt 
      "@[<v>[%d]@,@[<hv 1>(get-unsat-core)@]@]" 
      id
    in

    let (r, c) as res = S.get_unsat_core s in

    debug smt
      "@[<v>[%d]@,;; %a@,(@[<hv 1>%a@])@]" 
      id
      SMTExpr.pp_print_response r
      (pp_print_list Format.pp_print_string "@ ") c
    in 

    res


  let execute_custom_command { solver = s; id = id } c a r = 
    
    debug smt
      "@[<v>[%d]@,@[<hv 1>(%s%t)@]@]" 
      id
      c 
      (function ppf -> 
        if a = [] then () else 
          Format.fprintf 
            ppf 
            "@ %a" 
            (pp_print_list SMTExpr.pp_print_custom_arg "@ ") a)
    in
    
    let (r, e) as res = S.execute_custom_command s c a r in

    debug smt
      "@[<v>[%d]@,;; %a@,(@[<hv 1>%a@])@]" 
      id
      SMTExpr.pp_print_response r
      (pp_print_list HStringSExpr.pp_print_sexpr "@ ") e
    in 

    res

  let execute_custom_check_sat_command c { solver = s; id = id } = 
    
    debug smt
      "@[<v>[%d]@,@[<hv 1>(%s)@]@]" 
      id
      c 
    in
    
    let res = S.execute_custom_check_sat_command c s in

    debug smt
      "@[<v>[%d]@,;; %a@]" 
      id
      SMTExpr.pp_print_check_sat_response res
    in 

    res


end

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
