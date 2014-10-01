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
open Tsugi

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

  let debug_state mode k unfals fals invs prop_invs opt_prop prop_false =
    let l = List.length in
    debug tsugi
          "[%3i] %s:@\n> unfalsifiable: %i@\n> falsifiable  : %i@\n> new_invs     : %i@\n> new_inv_props: %i@\n> pending      : %i@\n> false_props  : %i" (Numeral.to_int k) mode (l unfals) (l fals) (l invs) (l prop_invs) (l opt_prop) (l prop_false)
    in
    ()

  let update_trans trans =
    Event.recv ()
    |> Event.update_trans_sys_tsugi trans

  let base trans k unfalsifiable falsifiable =

    (* Updating transition system and retrieving new things. *)
    let (new_invariants, new_valid_props, new_falsified_props) =
      update_trans trans
    in

    let status_k_true = TransSys.PropKTrue(Numeral.to_int k) in

    (* Broadcast status of properties true in k steps. *)
    List.iter
      ( fun (s, _) ->
        Event.prop_status status_k_true trans s )
      unfalsifiable ;

    (* Broadcast status of properties falsified in k steps. *)
    List.iter
      ( fun (p, cex) ->
        List.iter
          ( fun (s, _) -> Event.prop_status (TransSys.PropFalse cex) trans s )
          p )
      falsifiable ;

    debug_state
      "Base" k unfalsifiable falsifiable new_invariants new_valid_props [] new_falsified_props ;

    { (* New invariants. *)
      new_invariants = new_invariants ;
      (* New valid properties. *)
      new_valid = new_valid_props ;
      (* New falsified properties. *)
      new_falsified = new_falsified_props ;
      (* No new pending properties. *)
      new_pending = []  ;
      (* No pending properties. *)
      pending = false }


  (* List of properties for which step holds for some k, but not
     confirmed by base yet. *)
  let pending_props = ref []

  (* Checks if a property is true up to 'k_step'. *)
  let holds_in_base trans k_step (prop,_) =
    match TransSys.get_prop_status trans prop with
    | PropKTrue k' ->
       k' >= (Numeral.to_int k_step)
    | _ -> false

  (* Checks if some properties have been confirmed by base, broadcasts
     valid properties and keeps pending ones. *)
  let rec update_pending
            (* Transition system. *)
            trans
            (* The function is generic in its input list.  'f' returns
               the k for which this property is pending and the
               information about the property. *)
            f
            (* The new list of pending properties. *)
            new_pending
            (* Same as 'new_pending' but without the k for which this
               property is pending. *)
            new_pending_clean
            (* New valid properties as terms. *)
            new_invariants
            (* New valid properties as properties. *)
            new_valid_props = function
    | head :: tail ->
       (* Retrieving information on the pending property. *)
       let (k', string, term, prop) = f head in

       if holds_in_base trans k' prop then (

         (* Property is valid, broadcasting. *)
         Event.prop_status TransSys.PropInvariant trans string ;

         (* Looping with the redundant lists. *)
         update_pending trans f
                        new_pending
                        new_pending_clean
                        (term :: new_invariants)
                        (prop :: new_valid_props)
                        tail
       ) else

         (* Confirmation needed, adding to pending properties. *)
         update_pending trans f
                        ((k', prop) :: new_pending)
                        (prop :: new_pending_clean)
                        new_invariants
                        new_valid_props
                        tail
    | [] ->

       (* Updating the list of pending properties. *)
       pending_props := new_pending ;

       (* Returning the two redundant invariants lists. *)
       (new_invariants, new_valid_props, new_pending_clean, !pending_props <> [])

  (* Handles the pending unfalsifiable properties and the new ones.
     Broadcasts for properties confirmed by base, add to the list of
     pending properties if not. *)
  let check_proved_broadcast trans k invs prop_invs unfalsifiable =

    (* Checking if pending properties have been confirmed by base. *)
    let invs_tmp, prop_invs_tmp, _, _ =
      update_pending
        trans
        (fun (k',((s,t) as p)) -> (k',s,t,p))
        [] []
        invs
        prop_invs
        !pending_props
    in

    (* Checking if new unfalsifiable properties are invariants,
       adding them to the list of pending properties if they're not. *)
    update_pending
      trans
      (fun ((s,t) as p) -> (k,s,t,p))
      !pending_props
      []
      invs_tmp
      prop_invs_tmp
      unfalsifiable

  let step trans k unfalsifiable falsifiable =

    (* Updating transition system. *)
    let (invs_tmp, valid_tmp, new_falsified) =
      update_trans trans
    in

    let (new_invariants, new_valid, new_pending, pending_not_empty) =
      check_proved_broadcast trans k invs_tmp valid_tmp unfalsifiable
    in

    debug_state
      "Step" k unfalsifiable falsifiable new_invariants new_valid new_pending new_falsified;

    { (* New invariants. *)
      new_invariants = new_invariants ;
      (* New invariant properties. *)
      new_valid = new_valid ;
      (* New falsified properties. *)
      new_falsified = new_falsified ;
      (* New pending properties. *)
      new_pending = new_pending ;
      (* Pending properties. *)
      pending = pending_not_empty }

end


(* Prototypical communication protocol. *)
module CommunicationDummy = struct

  let base trans k unfalsifiable falsifiable =
    { new_invariants = [] ; new_valid = [] ;
      new_falsified = [] ; new_pending = [] ; pending = false }
  let step trans k unfalsifiable falsifiable =
    { new_invariants = [] ; new_valid = [] ;
      new_falsified = [] ; new_pending = [] ; pending = false }

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

