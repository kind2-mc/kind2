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


type t = int * Term.t


  
let merge certs =
  let km, l =
    List.fold_left (fun (km, l) (k, phi) ->
        max k km, phi :: l
      ) (0, []) certs in
  km, Term.mk_and (List.rev l)



(*
let generate_certificate certs sys =

  let k, phi = merge certs in

  let prop_p = UfSymbol.mk_uf_symbol "__P__" [Type.t_int] Type.t_bool in
  let init_p = UfSymbol.mk_uf_symbol "__I__" [Type.t_int] Type.t_bool in
  let trans_p =
    UfSymbol.mk_uf_symbol "__T__" [Type.t_int; Type.t_int] Type.t_bool in

  let phi_p = UfSymbol.mk_uf_symbol "__PHI__" [Type.t_int] Type.t_bool in

  assert false
  *)
