(*
This file is part of the Kind verifier

* Copyright (c) 2007-2010 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of sourc@e code must retain the above copyright
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


let pstr = print_string
let pr = print_string 
let pint = print_int 
let pbool b = pstr (if b then "TRUE" else "FALSE") 
let p_str_list l = List.iter (fun x -> pstr x; pstr " ") l 
let p_int_list l = List.iter (fun x -> pint x; pstr " ") l 

let pause_or_break hint quit_command = 
  print_string hint;
  let user_input = String.uppercase (read_line () ) in
  let quit_cmd  = String.uppercase quit_command in
    if (user_input = quit_cmd ) 
    then failwith "User break.\n"
    else ()


let rec unique_sorted l  =
  match l with 
      [] -> []
    | hd::[] -> l
    | hd::tl ->
	let rest = unique_sorted tl in
	let cp_result = compare hd (List.hd rest) in
	if (0 = cp_result) then rest
	else if ( cp_result < 0 ) then hd::rest
	else failwith "list is not sorted in unique list" 


let unique_list l =
  let l_sorted = List.sort compare l in
  unique_sorted l_sorted 


(*filter elments belong to forbidden_list *) 
(*
let rec filter_forbidden forbidden_list candidate_list cmp_func =
  if [] = forbidden_list then candidate_list
  else if [] = candidate_list then []
  else let fbd_hd = List.hd forbidden_list and
      cdt_hd = List.hd candidate_list and
      fbd_tl = List.tl forbidden_list and
      cdt_tl = List.tl candidate_list in
  let cmp_res = cmp_func fbd_hd cdt_hd in
    if 0 = cmp_res then filter_forbidden fbd_tl cdt_tl cmp_func 
    else if cmp_res <= 0 then filter_forbidden fbd_tl candidate_list cmp_func
    else cdt_hd::(filter_forbidden forbidden_list cdt_tl cmp_func)
*)

let rec filter_forbidden forbidden_list candidate_list  =
  if [] = forbidden_list then candidate_list
  else if [] = candidate_list then []
  else let fbd_hd = List.hd forbidden_list and
      cdt_hd = List.hd candidate_list and
      fbd_tl = List.tl forbidden_list and
      cdt_tl = List.tl candidate_list in
  let cmp_res = compare fbd_hd cdt_hd in
    if 0 = cmp_res then filter_forbidden fbd_tl cdt_tl 
    else if cmp_res <= 0 then filter_forbidden fbd_tl candidate_list 
    else cdt_hd::(filter_forbidden forbidden_list cdt_tl)


 let print_solver_out out1 = 
  let newout1 = 
    List.fold_right 
      (fun x y -> x^"\n"^y) 
      (Str.split (Str.regexp "[\n]+") out1)
      "" in
    print_string "current out is:\n ";
    print_string newout1

let rec n_to_m n m =
  if  n > m then failwith "one_to_n"
  else if n = m then [m]
  else n::(n_to_m (n+1) m)

let rec n_to_m_inc n m =
  if n = m then [m]
  else n::(n_to_m_inc (n+1) m)

let list_minus l_list r_list =
  let l = unique_list l_list in
  let r = unique_list r_list in
  let rec minus l r =
    match l, r with 
      hd1::tl1, hd2::tl2 -> 
	let cp_res = compare hd1 hd2 in
	  if 0 == cp_res 
	  then minus tl1 tl2 
	  else if 1 = cp_res 
	  then minus l tl2
	  else hd1::(minus tl1 r)
      | [], hd2::tl2 -> []
      |  hdl::tl1, [] -> l 
      | [], [] -> [] in
    minus l r ;;


let rec interval_list n m =
  if  n > m then failwith "Interval list failed"
  else if n = m then [m]
  else n::(n_to_m (n+1) m)
    



