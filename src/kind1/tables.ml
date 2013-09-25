(*
This file is part of the Kind verifier

* Copyright (c) 2007-2012 by the Board of Trustees of the University of Iowa, 
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


(** A module that keeps track of the internal tables of variable names and definitions *)

(** 
@author Jed Hagen
@author Temesghen Kahsai

*)

open Types
open Exceptions



(* a "safe" version of Hashtbl.find that raises a more informative exception *)
let safe_find ht x s = 
  try
    Hashtbl.find ht x
  with  Not_found -> 
    raise (IdNotFound s)


let reverse_varinfo = (Hashtbl.create 100:(string,idtype)Hashtbl.t)
let varid_name_add name id = Hashtbl.replace reverse_varinfo name id
let varid_lookup name = safe_find reverse_varinfo name "varid_lookup"


(* this renames long varnames internally so we don't get odd hashtable clashes *)
let renaming_counter = new Counter.counter

let sym_renaming_table = (Hashtbl.create 100:(string,string)Hashtbl.t)
(* the normal hashtbl does not behave as expected with long strings *)
  module LongStringHash = 
    Hashtbl.Make (
      struct
        type t = string
        let equal x y = ((compare (x:string) (y:string)) = 0)
        let hash x = Hashtbl.hash_param 200 200 (x:string)
      end
    )

let sym_truenaming_table = LongStringHash.create 1

let rename_sym s =
  if (!OldFlags.rename_long_vars) && ((String.length s) > OldFlags.long_vars_length) then 
    begin
      try
        LongStringHash.find sym_truenaming_table s
      with Not_found ->
        let s1 = "___z"^(string_of_int renaming_counter#next)^"z___" in
        Hashtbl.replace sym_renaming_table s1 s;
        LongStringHash.replace sym_truenaming_table s s1;
        s1
    end
  else
    s

let internal_name_to_original_name name =
  Hashtbl.find sym_renaming_table name 

let original_name_to_internal_name name =
  LongStringHash.find sym_truenaming_table name

let resolve_var_name n =
  try
    Hashtbl.find sym_renaming_table n
  with Not_found -> n

(* shared bindings *)
(* variable information, referenced by id number *)
(* node, name, type, variable class *)
let varinfo = 
  (Hashtbl.create 100:(int,node_id_t*string*lustre_type*varclass)Hashtbl.t)

let update_varinfo id (node,var,t,c) =
  let var' = rename_sym (resolve_var_name var) in
  Hashtbl.replace varinfo id (node,var',t,c)

let varid_to_info id = safe_find varinfo id "varid_to_info" 

let get_varinfo () = varinfo

let is_input_var id =
  let (_,_,_,c) = safe_find varinfo id ("is_input_var "^(string_of_int id)) in
  c = INPUT

let is_local_var id =
  let (_,_,_,c) = safe_find varinfo id ("is_local_var "^(string_of_int id)) in
  c = LOCAL || c = ABSTRACT

let is_output_var id =
  let (_,_,_,c) = safe_find varinfo id ("is_output_var "^(string_of_int id)) in
  c = OUTPUT

let string_of_varinfo id =
   let (n,v,t,c) = 
     safe_find varinfo id ("string_of_varinfo "^(string_of_int id)) 
   in
   (string_of_int id)^":("^v^")"

(*let get_name_id id =
  let (n,v,t,c) = 
    safe_find varinfo id ("string_of_varinfo "^(string_of_int id)) 
  in
    v
*)
let safe_find_varinfo x label = safe_find varinfo x label

let get_varinfo_name x = 
  let (_,v,_,_) = safe_find varinfo x "get_varinfo_name" in
  v

let get_varinfo_type x = 
  let (_,_,t,_) = safe_find varinfo x "get_varinfo_type" in
  t


let varid_to_orginal_name id = 
  let internal_name = get_varinfo_name id  in
    try
    Hashtbl.find sym_renaming_table internal_name 
  with Not_found -> failwith ("cannot find the name for id:" ^ (string_of_int id))


let varid_lookup_interval name =
  try
    Hashtbl.find reverse_varinfo name
  with Not_found -> -1



(* keeps track of which variables are actually used and at what position(s) *)
(* also keeps a il_expression reference *)
let used_vars = (Hashtbl.create 100:(idtype,used_vars_type option)Hashtbl.t)
let get_used_vars () = used_vars
let find_used_var = Hashtbl.find used_vars
(* when we encounter a "used" var, update at what position it is referenced *)
let update_used_vars id depth e = 
assert (depth >= 0);
  try
    let entry = Hashtbl.find used_vars id in
    if depth > 0 then
      match entry with
         None -> Hashtbl.replace used_vars id (Some {ex=e;depths=[depth]})
       | Some r -> if not (List.mem depth r.depths) then
                      r.depths <- depth::r.depths
  with Not_found ->
    if depth = 0 then
      Hashtbl.replace used_vars id None
    else
      Hashtbl.replace used_vars id (Some {ex=e;depths=[depth]})

let var_is_stateful id =
  try
    match find_used_var id with
        Some _ -> true
      | None -> false
  with Not_found -> false

(* test if a var is actually used in *)
let var_is_used id =
  try
    match find_used_var id with
        Some _ -> true
      | None -> true
  with Not_found -> false


let get_state_vars () = 
  Hashtbl.fold 
    (fun x y z ->
      match y with 
	  Some _ -> x::z 
	| _ -> z
    ) used_vars []


(* keep track of the shortcut functions actually used *)
(* used to determine which cvc3 functions to define *)
let shortcuts_used = (Hashtbl.create 10: (string,bool)Hashtbl.t)
let set_shortcut_used x = Hashtbl.replace shortcuts_used x true
let get_shortcut_used x = Hashtbl.mem shortcuts_used x


(* substitutions *)
(* keeps track of number of rhs occurrances of vars, for inlining complexity *)
let var_count_table = (Hashtbl.create 10:(idtype,int)Hashtbl.t)
let add_var_count id num =
  try
    let n = Hashtbl.find var_count_table id in
    Hashtbl.replace var_count_table id (n+num)
  with Not_found ->
    Hashtbl.add var_count_table id num
let get_var_count id =
  try
    (Hashtbl.find var_count_table id)-1
  with Not_found -> 0
(* this is in a table because properties are not tied to other definitions,
even though they may be in non-main nodes.  If this is the case, we may
have a property variable that does not actually show up anywhere else in the
formula. *)
(* if a variable is not in the table, it does not need to be substituted *)
(* inputs replace parameters, and results replace outputs *)
let number_variables_inlined = ref 0
let get_number_variables_inlined () = !number_variables_inlined
let substitution_table = (Hashtbl.create 10:(idtype,idtype)Hashtbl.t)
let rec resolve_substitution x =
  try
    resolve_substitution (Hashtbl.find substitution_table x)
  with Not_found -> x
let add_substitution x y =
  incr number_variables_inlined;
  add_var_count y ((get_var_count x) - 1);
  Hashtbl.replace substitution_table (resolve_substitution x)
    (resolve_substitution y)

(* node definitions, referenced by node name *)
let node_inputs = (Hashtbl.create 10:(node_id_t,(idtype*lustre_type) list)Hashtbl.t)

let get_node_inputs nid = safe_find node_inputs nid "get_node_inputs"
let add_node_inputs = Hashtbl.replace node_inputs

let node_outputs = (Hashtbl.create 10:(node_id_t,(idtype*lustre_type) list)Hashtbl.t)

let get_node_outputs nid = safe_find node_outputs nid "get_node_outputs"
let add_node_outputs = Hashtbl.replace node_outputs

let node_locals = (Hashtbl.create 10:(node_id_t,(idtype*lustre_type) list)Hashtbl.t)

let get_node_locals = Hashtbl.find node_locals
let add_node_locals = Hashtbl.replace node_locals

(* list of other nodes called: (node name, line, col) *)
let node_defs = (Hashtbl.create 10:(node_id_t,typed_stream list)Hashtbl.t)

let get_node_defs nid = safe_find node_defs nid "get_node_defs"
let add_node_defs = Hashtbl.replace node_defs

(* from node id to node name *)
let nodenamehash = (Hashtbl.create 100: (int,string)Hashtbl.t)

let get_nodename_table () = nodenamehash
let get_nodename nid = safe_find nodenamehash nid "get_nodename"


(*let add_nodename = Hashtbl.replace nodenamehash*)
let add_nodename id name = 
(* for implication only, since the adding of invariants cannot cross 
   the bounds of nodes. Yeting *)
  if (Hashtbl.length nodenamehash) >= 2 then
    failwith (
      "More than one node found. " ^
	"Please translate the Lustre file into a single node one by using lus2ec"; 
    );
  Hashtbl.replace nodenamehash id name

let nodeid_to_original_name node_id = 
  resolve_var_name (get_nodename node_id) 

(*   A simple form for the following function  *)
(*   Hashtbl.fold (fun x y list -> (x,y)::list ) hash_table []   *)
let fold_table_item x y list = (x,y)::list 
let fold_hash_table table = Hashtbl.fold fold_table_item table [] 

let fold_reverse_varinfo () =  fold_hash_table reverse_varinfo 

let fold_sym_renaming_table () = fold_hash_table sym_renaming_table 

let fold_sym_truenaming_table () = 
  LongStringHash.fold fold_table_item  sym_truenaming_table []

let fold_used_vars () = fold_hash_table used_vars

let fold_shortcuts_used () =  fold_hash_table shortcuts_used 
      
let fold_var_count_table () = fold_hash_table var_count_table

let fold_substitution_table () = fold_hash_table substitution_table

let fold_node_inputs () = fold_hash_table node_inputs

let fold_node_outputs () = fold_hash_table node_outputs

let fold_node_locals () = fold_hash_table node_locals

let fold_node_defs () = fold_hash_table node_defs
 
let fold_nodenamehash () = fold_hash_table nodenamehash

let fold_varinfo () = fold_hash_table varinfo 

let print_varinfo () =
  let var_list = fold_hash_table varinfo  in
    List.iter 
      (fun (id,(a,b,c,d)) -> 
	print_int id; 
	print_newline();
	print_int a;
 	print_newline();
	print_string b;
	print_newline();
      ) var_list

let fold_all_tables () = 
  let t1 = "reverse_varinfo" , fold_hash_table reverse_varinfo 
  and 
      t2 = "sym_renaming_table", fold_hash_table sym_renaming_table 
  and 
      t3 = "sym_truenaming_table",  
  LongStringHash.fold fold_table_item  sym_truenaming_table []
  and 
      t4 = "used_vars", fold_hash_table used_vars
  and 	
      t5 = "shortcuts_used", fold_hash_table shortcuts_used 
  and 
      t6 ="var_count_table", fold_hash_table var_count_table
  and 
      t7 ="substitution_table", fold_hash_table substitution_table
  and 
      t8 ="fold_node_inputs", fold_hash_table node_inputs
  and 
      t9 = "fold_node_outputs", fold_hash_table node_outputs
  and 
      t10 = "fold_node_locals", fold_hash_table node_locals
  and 
      t11 = "fold_node_defs", fold_hash_table node_defs
  and 
      t12 = "fold_nodenamehash", fold_hash_table nodenamehash 
  and 
      t13 = "fold_varinfo", fold_hash_table varinfo in

    t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13

