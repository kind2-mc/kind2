(*
This file is part of the Kind verifier

* Copyright (c) 2007-2010 by the Board of Trustees of the University of Iowa, 
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

module Int_set = 
  Set.Make (
    struct
      type t = int
      let compare = compare
    end)
    
open Types
open Util

exception No_more_node
exception Loc of int

type cmp_result = EQU | NON_CMP | LESS | GREAT ;;

let flatten_arr arr = List.flatten (DynArray.to_list arr) 

let fold_list_with_op  = Expr_util.fold_list_with_op 
      
let nvr_def x = New_vars.nvr_to_nvr_def x

let mk_eq_pos x y pos  = F_EQ (REL (EQ, PRED(x,[pos]), PRED(y, [pos])), ONE ,L_BOOL) 

let mk_eq_positions l r positions = 
  List.map (fun x -> mk_eq_pos l r x)  positions 

let mk_eq_pos_oneclass equiv_class positions = 
  List.flatten(
    fold_list_with_op  
      (fun x y -> mk_eq_positions x y positions) 
      equiv_class 
  )

let mk_less_pos x y pos = F_EQ (REL (LTE, PRED(x,[pos]), PRED(y,[pos])), ONE, L_BOOL) 

let mk_less_positions l r positions = 
    List.map (fun x -> mk_less_pos l r x)  positions 

let mk_less_pos_onechain chain positions =
  List.flatten(
    fold_list_with_op 
      (fun x y -> mk_less_positions x y positions) 
      chain 
  )


let mk_eq x y  = F_EQ (REL (EQ, PRED(x,[]), PRED(y, [])), ONE ,L_BOOL) 

let mk_eq_oneclass equiv_class  = 
  fold_list_with_op  
    (fun x y -> mk_eq x y ) 
    equiv_class 

let mk_less x y  = F_EQ (REL (LTE, PRED(x,[]), PRED(y,[])), ONE, L_BOOL) 

let strip_less e =
  match e with F_EQ (REL (LTE, PRED(x,[]), PRED(y,[])), ONE, L_BOOL) 
      -> x, y
    | _ -> failwith "strip less"


let mk_less_onechain chain =
  fold_list_with_op  mk_less  chain 

(* compare two int lists *)
let compare_int_node node_l node_r = 
  assert ((List.length node_l ) = (List.length node_r));
  let rec comp_help_func node_l node_r expected_result =
    if ([] = node_l && [] = node_r  )
    then expected_result
    else 
      let l_hd = List.hd node_l and r_hd = List.hd node_r in
      let l_tl = List.tl node_l and r_tl = List.tl node_r in 
	match expected_result with
	  EQU -> 
	    if l_hd = r_hd 
	    then comp_help_func l_tl r_tl EQU
	    else if l_hd > r_hd 
	    then comp_help_func l_tl r_tl GREAT
	    else comp_help_func l_tl r_tl LESS
	| LESS -> 
	    if l_hd <= r_hd 
	    then comp_help_func l_tl r_tl LESS
	    else NON_CMP 
	| GREAT -> 
	    if l_hd >= r_hd 
	    then comp_help_func l_tl r_tl GREAT
	    else NON_CMP 
	| _  -> failwith "Error in compare two nodes" 
  in
    comp_help_func node_l node_r EQU ;;

(* The graph to sort a partial order *)
(* The items in a partial order are stored in chains *)
(* For chain [l1;l2;....ln], we have l1<=l2, l2<=l3, ... , ln_1<=ln *)
(* For a node i, d_outs[i] means an edge from i to d_outs[i] *)
(* Given a set of serted items and a new item t,
   1. Scan all chains to see if t can be inserted into a chain. 
      The t can be inseted into the beginning, end and middle of a chain.
      If t cannot be inserted into an chain, make a new chain that contains t      only. 

   2. If t cannot be inserted into a chain, but t is comparable to an item
   in that chain, record an edge for this case.

   Redudant edges:
   Suppose we have two chains 
   1;2
   3;4 
   and we also have an edge 3-->2
   Now, a new node 5 is inserted and the result is as follows
   1;5;2
   3;5;4 
   Now the edge 3--2 is redudant. 
   A naive algorithm to removed these edges:
   Get nodes reachable from the new node 5, make them a set R.
   Get nodes that lead to the new node 5, make them a set L.
   Remove and edges from a node in L to a node in R.
   In the above case, R is {2,4} and L is {1,3}
*)

class partial_order_graph comp_func = 
object (self)
  val d_nodes = DynArray.create() 
  method changed () = not (DynArray.empty d_nodes)
  val d_node_extra = DynArray.create()
  method private ith_node i = 
    DynArray.get d_nodes i 
  method private iter_nodes func  = 
    DynArray.iteri func d_nodes
  val d_chains = DynArray.create()
  method private ith_chain i = 
    DynArray.get d_chains i 
  method private iter_chains func =
    DynArray.iteri  func d_chains
  method private print_chain chain =
      DynArray.iter (fun x -> 
	pstr "["; p_int_list (self#ith_node x); pstr "]")
	chain
  method private print_chain_id chain_id =
    let chain = self#ith_chain chain_id in
      self#print_chain chain
  method private insert_chain_loc chain_id loc node_id =
    DynArray.insert (self#ith_chain chain_id) loc node_id 
  val d_ins = DynArray.create()
  val d_outs = DynArray.create()
  method id_to_nv id = 
    List.hd (DynArray.get d_node_extra id) 
  method doc_of_stepn_asserts positions =   
    let id_to_nvr_def id = 
      nvr_def (self#id_to_nv id) in 
    let map_node_extra_func node_extra  = 
      let equiv_class = List.map (fun x -> nvr_def x) node_extra in
	(mk_eq_pos_oneclass equiv_class positions)  
    in
    let eq_ops = flatten_arr (DynArray.map map_node_extra_func d_node_extra )
    in
    let map_chain_func chain = 
      let items = List.map id_to_nvr_def (DynArray.to_list chain) in
	mk_less_pos_onechain items positions
    in
    let less_chain_ops = flatten_arr (DynArray.map map_chain_func d_chains) 
    in
    let map_outs_func id outs =
      let out_list = List.map id_to_nvr_def (Int_set.elements outs) in
      let id_nvr_def = id_to_nvr_def id in
	List.flatten (
         List.map (fun x -> mk_less_positions id_nvr_def x positions) out_list )
    in
    let less_out_ops =  flatten_arr (DynArray.mapi map_outs_func d_outs) 
    in 
      (eq_ops@less_out_ops)@less_chain_ops        
  method insert_edge l r =
(*    pstr "insert edge:" ; pint l ; pstr "  " ; pint r ; pstr "\n";*)
    let new_outs = Int_set.add r (DynArray.get d_outs l ) in
      DynArray.set d_outs l new_outs ;
    let new_ins = Int_set.add l (DynArray.get d_ins r ) in
      DynArray.set d_ins r new_ins;
  method equiv_classes () = DynArray.to_list d_node_extra 
  method eq_imp () = 
    let arr_to_nvr x = List.map self#id_to_nv (DynArray.to_list x) in
    let map_chain_func chain =
      let chain_list = arr_to_nvr chain in
	mk_less_onechain chain_list 
    in  
    let less_chain_ops =  flatten_arr (DynArray.map map_chain_func d_chains)
    in
    let map_outs_func id outs = 
      let map_list_func l = List.map self#id_to_nv (Int_set.elements l)  in
      let outs_list = map_list_func outs in
      let id_nvr = self#id_to_nv id in
	List.map (fun x -> mk_less id_nvr x ) outs_list
    in
    let less_out_ops = flatten_arr (DynArray.mapi map_outs_func d_outs) 
    in 
    let map_node_extra_func node_extra =
      mk_eq_oneclass node_extra
    in
    let eq_ops = 
      flatten_arr (DynArray.map map_node_extra_func d_node_extra)  in
      eq_ops, (less_out_ops@less_chain_ops  )
  method doc () = 
    let eqs,imps = self#eq_imp () in
      eqs@imps

  method print () =
    pstr "================ partial order graph ==============\n";
    let iter_chain_func chain_id chain =
      pstr "Chain: "; pint chain_id ; pstr "\n";
      self#print_chain_id chain_id ;
      pstr "\n" 
    in
    let iter_other_edges node_id node =
      pstr "Out edges of Node: ["; p_int_list node ; pstr "] ";
      let extra = DynArray.get d_node_extra node_id in 
	pstr "[{";
	p_str_list extra; 
	pstr "}]\n" ; 
      Int_set.iter 
	(fun x -> 
	  let item = self#ith_node x in 
	    pstr "[";
	    p_int_list item; 
	    pstr "]" ; 
	) 
	(DynArray.get d_outs node_id);
      pstr "\n";
    in 
      self#iter_chains iter_chain_func ;
      self#iter_nodes iter_other_edges  
  method add_node  (node:int list) (extra_info:string list) = 
    let collect_node_info chain = 
      let chain_len = DynArray.length chain 
      in
      let ith i = DynArray.get chain i 
      in
      let cmp i = comp_func node (self#ith_node (ith i)) 
      in 
      let rec binary_find_less l_bound u_bound =
(*	pstr "debug 1: "; pint l_bound; pstr " " ; pint u_bound; pstr "\n";*)
	match  (cmp l_bound) with 
	    LESS -> l_bound
	  | EQU -> failwith "found equal node"
	  | _ -> 
	      if l_bound = u_bound 
	      then -1 (* not found *) 
	      else if (l_bound < u_bound) 
	      then 
		let mid = (l_bound + 1 + u_bound )/2 in
		  if LESS = cmp mid 
		  then  binary_find_less (l_bound + 1) mid 
		  else  binary_find_less  (mid ) u_bound
	      else failwith "L_BOUND > U_BOUND" 
      in
      let rec binary_find_great l_bound u_bound =
(*	pstr "debug 2\n";*)
	match  (cmp u_bound) with 
	    GREAT -> u_bound + 1
	  | EQU -> failwith "found equal node"
	  | _ -> 
	      if l_bound = u_bound 
	      then -1 (* not found *) 
	      else if (l_bound < u_bound) 
	      then 
		let mid = (l_bound  + u_bound -1)/2 in
		  if GREAT = cmp mid 
		  then  binary_find_great mid  (u_bound - 1)
		  else  binary_find_great  l_bound mid
	      else failwith "L_BOUND > U_BOUND" 
      in
      let less_loc = binary_find_less 0 (chain_len - 1) in
      let great_loc = binary_find_great 0 (chain_len - 1) in
	less_loc, great_loc 
    in (* end of collect_node_info *)
    let node_id = DynArray.length d_nodes in 
      DynArray.add d_nodes node;
      DynArray.add d_node_extra extra_info;
      DynArray.add d_outs Int_set.empty ;
      DynArray.add d_ins Int_set.empty;
    let node_info_array = DynArray.map collect_node_info d_chains in
    let node_placed = ref false in 
    let iter_chain_func chain_id (less_loc,great_loc) =
      let chain_len = DynArray.length (self#ith_chain chain_id) in 
      if (-1 = less_loc && -1 = great_loc)
      then ()
      else if (less_loc  = great_loc) 
      then 
	begin
	  node_placed := true;
          self#insert_chain_loc chain_id less_loc node_id;
	end
      else if ( 0  = less_loc) 
      then 
	begin 
	  assert ( -1 = great_loc);
	  node_placed := true;
	  self#insert_chain_loc chain_id less_loc node_id;
	end 
      else if chain_len = great_loc
      then
	begin
	  assert ( -1 = less_loc);
	  node_placed := true;
	  self#insert_chain_loc chain_id great_loc node_id;
	end 
      else 
	begin 
	  if (-1 != less_loc)
	  then self#insert_edge node_id (DynArray.get (self#ith_chain chain_id) less_loc);
	  if (-1 != great_loc)
	  then self#insert_edge (DynArray.get (self#ith_chain chain_id) (great_loc - 1)) node_id
	end  
      in
	DynArray.iteri iter_chain_func  node_info_array ;
	if (not (!node_placed) ) 
	then 
	  begin
(*	    pstr "debug 1\n";*)
	    DynArray.add d_chains (DynArray.create());
	    DynArray.add (DynArray.last d_chains) node_id;
	  end ;
        (* filter redudant edges: for a newly place node t:
	   1. collect all nodes reachable from t, make a set set_after
	   2. collect all nodes reverse reachable from t, make a set set_before
	   3. remove any edge from a node in set_before to a node in set_after 
	*)
end 


class partial_order (init_list:string list) =
object (self)
  val mutable d_history = [(init_list,[])]
  val mutable d_sort_graph = new partial_order_graph compare_int_node 
  val mutable d_sort_graph_old = new partial_order_graph compare_int_node 
  initializer 
    if (List.length init_list) >0 
    then d_sort_graph#add_node [1] init_list
    else ()
  method print() =
    pstr "-- Value history --- \n";
    List.iter (fun (x, y) -> pstr "## "; p_str_list x ; pstr " @@ " ; p_int_list y; pstr "\n") d_history
  method private filter counter_model =
    let iter_list_func (equiv_class,values) =
      Equiv_util.filter_int_func_with_history equiv_class counter_model values
    in
    let new_classes = List.map iter_list_func d_history in
      d_history <- List.flatten new_classes;
  method sort counter_model =
    self#filter counter_model ;
    let sort_graph = new partial_order_graph compare_int_node in
    let iter_func (equiv_class,values) = sort_graph#add_node values equiv_class in
      List.iter iter_func d_history;
      d_sort_graph <- sort_graph;
      d_sort_graph#changed ();
  method doc_of_asserts () =
    d_sort_graph#doc () 
    method make_copy () =
      d_sort_graph_old <- d_sort_graph
  method eq_imp () =
(*    d_sort_graph#print ();*)
    d_sort_graph#eq_imp () 
  method doc_of_stepn_asserts positions =
    let fml =  d_sort_graph#doc_of_stepn_asserts positions in 
    let doc =   
      List.map 
	(fun x -> Lus_convert_yc.simple_command_string (ASSERT (x)))
	fml 
    in 
      doc 
  method equiv_classes () =
    d_sort_graph#equiv_classes () 
  method imps () = 
    let _, imps = d_sort_graph#eq_imp() in
      List.map strip_less imps 
end 
