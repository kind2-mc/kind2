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

(* Tsugi stands for Transition System Unroller for Generalized
   Induction. It is a functor designed to perform BMC checks in order
   to implement k-induction. *)

open Lib
open TypeLib

(* Private module for prototypical activation literal creation.
   Creates actlits by appending based on the hash of the input
   term. Positive literals are named 'pos_<hash>', negative ones at k
   are named 'neg_<hash>_at_k'. *)
module ActLitProto = struct

  (* Translates the hash of a term into a string .*)
  let string_of_term term = string_of_int (Term.tag term)

  (* Creates a positive actlit as a UF. *)
  let positive term =
    let string =
      String.concat "" [ "pos_" ; string_of_term term ]
    in
    UfSymbol.mk_uf_symbol string [] (Type.mk_bool ())

  (* Creates a negative actlit as a UF. *)
  let negative k term =
    let string =
      String.concat "" [ "neg_" ;
                         string_of_term term ;
                         "_at_" ;
                         string_of_int (Numeral.to_int k) ]
    in
    UfSymbol.mk_uf_symbol string [] (Type.mk_bool ())

end


module CexExtractorDummy = struct

  let generic trans get_model k = []
  let base trans get_model k = []
  let step trans get_model k = []

end


(* Prototypical communication protocol. *)
module CommunicationProto = struct

  let base trans k unfalsifiable falsifiable =
    let status_k_true = TransSys.PropKTrue(Numeral.to_int k) in

    (* Broadcast status of properties true in k steps. *)
    List.iter
      ( fun (s, _) -> Event.prop_status status_k_true trans s )
      unfalsifiable ;

    (* Broadcast status of properties falsified in k steps. *)
    List.iter
      ( fun (p, cex) ->
        List.iter
          ( fun (s, _) -> Event.prop_status (TransSys.PropFalse cex) trans s )
          p )
      falsifiable ;

    ()


  let step trans k unfalsifiable cexs = ()
  let new_invariants () = []

end


(* Prototypical communication protocol. *)
module CommunicationDummy = struct

  let base trans k unfalsifiable falsifiable = ()
  let step trans k unfalsifiable cexs = ()
  let new_invariants () = []

end


(* Instantiating tsugi on the prototypical activation literal
   generator. *)
module BmcProto = Tsugi.Make(ActLitProto)
                            (CommunicationProto)
                            (CexExtractorDummy)

module BmcDummy = Tsugi.Make(ActLitProto)
                            (CommunicationDummy)
                            (CexExtractorDummy)


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

