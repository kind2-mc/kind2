(*
This file is part of the Kind verifier

* Copyright (c) 2007-2009 by the Board of Trustees of the University of Iowa, 
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

open Types
open Exceptions



let list_print ids = List.iter (fun x-> Printf.printf "%d " x) ids; Printf.printf "\n"
let list_print2 ids = List.iter (fun (x,y)-> Printf.printf "%d,%d " x y) ids; Printf.printf "\n"

let toss x = () (* toss output *)


(* definition hash *)
let defhash = (Hashtbl.create 10:Types.defhashtable)

(* special case with id = 1 *)
let assert_id = 1

let def_add id d idlist =
Channels.debug_to_user ("def_add "^(string_of_int id)^" "^(Buffer.contents d));
  let dlist = List.fold_left (fun acc (x,_) ->
                if not (List.mem x acc) then
                  x::acc
                else
                  acc
              ) [] idlist
  in
    Hashtbl.replace defhash id 
      (DEF_STR {abstr = [|NOT_REFINED;NOT_REFINED|];score=0;score2=0;
      stamp=0;def=d;deps=dlist;dep_offsets=idlist})

let def_add_ref id id2 =
Channels.debug_to_user ("def_add_ref "^(string_of_int id)^" "^(string_of_int id2));
  Hashtbl.replace defhash id (DEF_REF id2)


let print_defhash () =
  Printf.printf "DEFHASH:\n";
  Hashtbl.iter (fun x y ->
    match y with
        DEF_REF z -> Printf.printf "%d -> %d\n" x z
      | DEF_STR z -> Printf.printf "%d -> %s %d -%s- " x
                       (
                         match z.abstr.(Globals.base_abstr) with
                             NOT_REFINED -> "NOT_REFINED"
                           | SUBTREE_DONE -> "REFINED*"
                           | _ -> "REFINED"
                       )
                       z.score
                       (Buffer.contents z.def);
                     list_print z.deps
   ) defhash

let clear_defs () = Hashtbl.clear defhash


(* print DOT graph of defhash from a given source *)
let print_defhash_graph_curr output defhash boldlist =
  output_string output "\ndigraph G {\n";
  Hashtbl.iter (fun x (_,v,_,c) ->
    let buf = Buffer.create 10 in
    Buffer.add_string buf ("v"^(string_of_int x)^" [label=\""^v^"\"");
    if List.mem x boldlist then
     Buffer.add_string buf ",style=bold";
    begin
      try
        match Hashtbl.find defhash x with
          DEF_STR z ->
                    if z.abstr.(Globals.base_abstr) != NOT_REFINED then
                      Buffer.add_string buf ",style=filled";
                    Buffer.add_string buf "];\n";
                    output_string output (Buffer.contents buf);
                    List.iter (fun w ->
                      output_string output ("v"^(string_of_int x)^" -> v"
                        ^(string_of_int w)^";\n")
                    ) z.deps
          | DEF_REF z -> Buffer.add_string buf ",style=dashed];\n";
                      output_string output ((Buffer.contents buf)^"v"
                        ^(string_of_int x)^" -> v"
                        ^(string_of_int z)^";\n")
      with Not_found ->
        if c = INPUT then
          begin
            Buffer.add_string buf ",shape=polygon];\n";
            output_string output (Buffer.contents buf)
          end
    end;
  ) (Tables.get_varinfo());
  output_string output "}\n";
  flush output

(* prints dot graph of hash *)
let print_defhash_graph defhash =
  print_defhash_graph_curr stdout defhash []


let def_counter = ref 1
let incr_def_counter () = incr def_counter
let get_def_counter () = !def_counter


(* prints dot graph of hashi, highlighting core list *)
let print_curr_defhash_graph defhash coreids =
  let f = "graph"^(if !def_counter < 100 then "0" else "")
    ^(if !def_counter < 10 then "0" else "")^(string_of_int !def_counter)
  in
  let out = open_out (f^".dot") in
  print_defhash_graph_curr out defhash coreids;
  close_out_noerr out;
  toss(Unix.system ("dot -Tgif -o "^f^".gif "^f^".dot"))

(* make sure you run this before doing Abs.get_score *)
(*
let reload_defhash src_hash =
  Hashtbl.clear defhash;
  Hashtbl.iter (fun x y -> Hashtbl.replace defhash x y) src_hash
*)

let get_defhash () = defhash
let get_def x label = Tables.safe_find defhash x label
let num_abstract_in_def_hash (index) =
  Hashtbl.fold (fun _ x y -> 
    match x with
        DEF_REF _ -> y
      | DEF_STR d -> 
          if d.abstr.(index) = NOT_REFINED then y+1
          else y
  ) defhash 0
        

(********************************************************************)
(* include in prop_ids all property vars *)
(* sets property-referenced vars as being already "refined" *)
let rec initialize_defs dhash prop_ids =
Channels.debug_to_user ("initialize_defs");
  List.iter (fun id ->
    try
      let d1 = Hashtbl.find dhash id in
      match d1 with
          DEF_REF x -> initialize_defs dhash [x]
        | DEF_STR d ->
            d.abstr.(Globals.base_abstr) <- REFINED (0);
            d.abstr.(Globals.step_abstr) <- REFINED (0)
    with Not_found -> ()
  ) prop_ids

