(* This file is part of the Kind 2 model checker.

   Copyright (c) 2026 by the Board of Trustees of the University of Iowa

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

module HSS = HString.HStringSet
module HSM = HString.HStringMap

let segments ~name ~free chain =
  let close segments segment =
    if segment = [] then segments else List.rev segment :: segments
  in
  (* [segment] is the current segment, its lets in reverse order, [levels]
     the levels of its symbols, and [outer] the symbols its terms take from
     the enclosing scope *)
  let rec split segments segment levels outer = function
    | [] -> List.rev (close segments segment)
    | lets :: chain ->
      let names = List.map (fun (s, _) -> name s) lets in
      let refs = List.map (fun (_, t) -> free t) lets in
      let own = HSS.of_list names in
      if HSS.cardinal own <> List.length names
         || List.exists (fun r -> not (HSS.disjoint r own)) refs
      then
        let alone = List.map (fun (s, t) -> s, 1, t) lets in
        split ([alone] :: close segments segment) [] HSM.empty HSS.empty chain
      else if
        segment <> []
        && List.exists (fun n -> HSM.mem n levels || HSS.mem n outer) names
      then
        split (close segments segment) [] HSM.empty HSS.empty (lets :: chain)
      else
        let leveled =
          List.map2 (fun (s, t) r ->
            let level =
              HSS.fold (fun n l ->
                match HSM.find_opt n levels with
                | Some l' -> max l (l' + 1)
                | None -> l)
                r 1
            in
            s, level, t)
            lets refs
        in
        let outer =
          List.fold_left (fun outer r ->
            HSS.union outer (HSS.filter (fun n -> not (HSM.mem n levels)) r))
            outer refs
        in
        let levels =
          List.fold_left (fun levels (s, l, _) -> HSM.add (name s) l levels)
            levels leveled
        in
        split segments (leveled :: segment) levels outer chain
  in
  split [] [] HSM.empty HSS.empty chain

let levels segments =
  List.concat_map (fun segment ->
    let bindings = List.concat segment in
    let depth = List.fold_left (fun d (_, l, _) -> max d l) 0 bindings in
    let at_level = Array.make depth [] in
    List.iter (fun (s, l, t) -> at_level.(l - 1) <- (s, t) :: at_level.(l - 1))
      bindings;
    Array.to_list at_level
    |> List.filter_map (function [] -> None | b -> Some (List.rev b)))
    segments
