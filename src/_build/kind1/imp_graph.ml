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

open Types
open Util
open Channels


type node_id = int

(* boolean implication graph *)
class ['a] graph =
object (self)
  (* node of false *)
  val mutable d_false_id = 0 
  method set_false_node id = d_false_id <- id 
  (* node of true *)
  val mutable d_true_id = 0
  method set_true_node id = d_true_id <- id 
  method is_true_node id = d_true_id = id 
  method is_false_node id = d_false_id = id 
  method get_false_node () = d_false_id 
  (* the info associated with a node.  *)
  (* A node's id is its index in the array *) 
  val d_nodes_info = DynArray.create()
  (* d_ins[t] stores the in edges of t *)
  val d_ins = DynArray.create()
  val d_outs = DynArray.create() 
  (* an array of edges (l,r).  (l,r) means an edge l ---> r. *)
  (* This is useful when output edges in a grph *)  
  val d_edges = DynArray.create()
  (* Used to check if an edge has been added before *)
  val d_edge_hash = Hashtbl.create 1000 
  method add_node (x:'a):node_id =  
    DynArray.add d_nodes_info x;
    DynArray.add d_ins (DynArray.create ());  
    DynArray.add d_outs (DynArray.create ());  

    assert (DynArray.length d_nodes_info = (DynArray.length d_ins));
    assert (DynArray.length d_nodes_info = (DynArray.length d_outs));

    let length = DynArray.length d_nodes_info in
    let new_id = length - 1 in
      new_id
  method ith_node_info node_id = 
    DynArray.get d_nodes_info node_id
  method private i_ith_ins node_id = 
    DynArray.get d_ins node_id
  method private i_ith_outs node_id = 
    DynArray.get d_outs node_id
  method ith_ins node_id = 
    DynArray.to_list (self#i_ith_ins node_id)
  method ith_outs node_id = 
    DynArray.to_list (self#i_ith_outs node_id)
  method add_edge (l:node_id) (r:node_id) =
    try (Hashtbl.find d_edge_hash (l,r) ; ())
    with Not_found ->(
    Hashtbl.add d_edge_hash (l,r)  true;
    DynArray.add d_edges (l,r);
    DynArray.add (self#i_ith_outs l) r;
    DynArray.add (self#i_ith_ins r) l;
    )
  method iter_node func =
    DynArray.iteri func d_nodes_info 
  method iter_edge func =
    DynArray.iter func d_edges 
  method fold_nodes : 'c. ('a -> 'c -> 'c) -> 'c -> 'c  =
    fun func start -> DynArray.fold_right func d_nodes_info start
  method fold_edges : 'c. ('e -> 'c -> 'c) -> 'c -> 'c  =
    fun func start -> DynArray.fold_right func d_edges start
  method num_nodes () = DynArray.length d_nodes_info
  method num_edges () = DynArray.length d_edges
  method print_graph (pr_node_func:'a->unit) (pr_node_detail:'a->unit)  =
    let iter_edge_func (x,y) = 
      (
	pint x; pstr "-->"; pint y; pstr " : "; 
        pr_node_func (self#ith_node_info x);
	pstr "===>";
	pr_node_func (self#ith_node_info y);
	pstr"\n"
      )
    in
    let iter_node_func id x = 
	(
	  pint id; pstr " : ";
	  pr_node_detail x;
	  pstr " :INS ";
	  DynArray.iter (fun x -> pint x; pstr " ") (self#i_ith_ins id);
	  pstr " :OUT ";
	  DynArray.iter (fun x -> pint x; pstr " ") (self#i_ith_outs id);
	  pstr "\n"
	)
    in 
      pstr "GRAPH : \n";
      self#iter_node iter_node_func ;
      self#iter_edge iter_edge_func 
end  




type equiv_class_type = string list  


class node_info (equiv_class:equiv_class_type) = 
object (self)
  val d_equiv = equiv_class 
    (*
       If the node has both next_true_id and next_false_id, then
       the true_top is [next_true_id], and the true_false is [next_false_id].
       If the node only has one of the next_id, say next_true_id,
       then true_top is [next_true_id], false_top will be the set of ids 
       such that { x | x \in (false_top of y) and (y is a child of the node)}
       In other words, the false_top will be the set of ids that contains all
       the true_top ids in its children. 
    *)
  val mutable d_true_tops = ([]:node_id list)
  val mutable d_false_tops  = ([]:node_id list)
  method true_tops () = d_true_tops
  method false_tops () = d_false_tops
  method update_true_tops id_list = d_true_tops <- id_list  
  method update_false_tops id_list = d_false_tops <- id_list  

  val mutable d_next_true_id = (None:node_id option ) 
  val mutable d_next_false_id =(None:node_id option )
  method next_true_id () = d_next_true_id
  method next_false_id () = d_next_false_id 
  method update_next_true_id id = 
    d_next_true_id <- id 
  method update_next_false_id id = 
    d_next_false_id <- id 
  method equiv = d_equiv 
  method print () = 
    let print_list l = List.iter (fun x -> pstr x; pstr " ") l in 
      print_list d_equiv
  method print_detail () = 
    let print_list l pr_func = List.iter (fun x -> pr_func x; pstr " ") l 
    in 
    let pr_next n =  match n with 
	Some i -> pint i; pstr " "
      | None -> pstr "NO " 
    in
      print_list d_equiv pstr;
      pstr " : " ;
      pr_next d_next_true_id ;
      pr_next d_next_false_id;
      pstr " :T tops ";
      print_list (self#true_tops()) pint;
      pstr " :F tops ";
      print_list (self#false_tops()) pint
end ;;

type imp_graph = node_info graph 

let new_imp_graph () =  new graph

let new_init_imp_graph init_equiv_class = 
  let new_graph = new graph in
  let first_node_id = (new_graph#add_node (new node_info init_equiv_class)) in
    new_graph#set_false_node first_node_id;
    new_graph#set_true_node first_node_id;
    new_graph


let is_true str =
  let up_value = Char.uppercase (String.get str 0)  in
    if 'T' = up_value then true
    else if 'F' = up_value then false
    else failwith ("unknown boolean value: " ^ str)  

let is_false str = not (is_true str)

let filter_bool_func hash_tbl one_class =
  let t_expr, f_expr = 
    List.partition (fun x -> 
(*      pstr "finding: "; pstr x; pstr "\n";*)
      is_true (Hashtbl.find hash_tbl x)) one_class in
   (t_expr,f_expr)

let filter_bool_equiv hash_tbl one_class =
  let new_true,new_false = filter_bool_func hash_tbl one_class in
    new_true,new_false

(* Given an old graph and a counter model hash_tbl, *)
(* return a new graph *)
let get_new_graph hash_tbl (old_graph:imp_graph) =  
  let get_chls_true_tops node_id =
    let chls_id = old_graph#ith_outs node_id in
    let chls = List.map (fun x -> old_graph#ith_node_info x) chls_id in 
    let all_true_tops = List.fold_right (fun x y -> (x#true_tops()) @ y) chls[] in
      Util.unique_list all_true_tops
  in
  let get_chls_false_tops node_id =
    let chls_id = old_graph#ith_outs node_id in
    let chls = List.map (fun x -> old_graph#ith_node_info x) chls_id in 
    let all_false_tops = List.fold_right (fun x y -> x#false_tops() @ y) chls [] in
      Util.unique_list all_false_tops
  in
  let get_grand_chls_true_tops node_id =
    let chls_id = old_graph#ith_outs node_id in
    let grand_chls_true_tops =  
      List.fold_right (fun x y -> (get_chls_true_tops x) @ y ) chls_id [] in
      Util.unique_list grand_chls_true_tops
  in
  let get_grand_chls_false_tops node_id =
    let chls_id = old_graph#ith_outs node_id in
    let grand_chls_false_tops = 
      List.fold_right (fun x y -> (get_chls_false_tops x) @ y) chls_id [] in 
      Util.unique_list grand_chls_false_tops 
  in
    
  let changed = ref false in 
  (* Given an old graph: 
     1. Creat a new graph.  

     2. For each node in old graph, add new nodes (up to two) in the new
     graph based on the values in hash_tbl.

     A node represents a equiv class.  Given a node OLD_N in the old graph
     and the counter model, some terms in the equiv class of OLd_N are
     evaluated to be true and some are false. (It is possible that all
     terms of OLD_N are true, or all terms of OLD_N are false.)  Next, make
     a new equiv class of all terms evaluated to be true and another new
     equiv class for false terms.  Add the two new equiv classes into the
     new graph.  That is, add two nodes into the new graph.  If all terms
     are evaluated to be true, then add only one node into the new graph.
     The same for the case if all terms are false.  Let new_true_id denotes
     the id of the node of true terms in the new graph, and new_false_id
     for the node of false terms.  Assign new_true_id to OLD_N's
	 next_true_id and new_false_id to OLD_N's next_false_id. 

     3. Finally, return the half-baked new graph.  
  *)
  let iter_split_node hash_tbl (old_graph:imp_graph) = 
        (
      let new_graph = new graph in
      let new_node_id equiv =
	if [] = equiv then None 
	else let new_node = new node_info equiv in
	       Some (new_graph#add_node new_node ) in
      let split_node_func node_id node_info =
	let equiv = node_info#equiv in
	let new_true, new_false = filter_bool_equiv hash_tbl equiv in
	let new_true_id = new_node_id new_true in
	let new_false_id = new_node_id new_false in
	  assert (new_true <> [] or new_false <> []);
	  if (new_true <> [] && new_false <> []) then changed := true;
	  if old_graph#is_true_node node_id then
	    begin 
	      match new_true_id with 
		  Some int_id -> (new_graph#set_true_node int_id)
		| _ -> failwith "True node not found"
	    end ;
	  if old_graph#is_false_node node_id then
	    begin 
	      match new_false_id with 
		  Some int_id -> (new_graph#set_false_node int_id)
		| _ -> failwith "False node not found"
	    end ;
	  node_info#update_next_true_id  new_true_id; 
	  node_info#update_next_false_id  new_false_id; 
      in 
	old_graph#iter_node split_node_func ;
	new_graph
    ) 
  in 
    (* For each node OLD_N in the old graph, update its true_tops and
       false_tops 
    *)
    (* Suppose OLD_N's children have been processed.  
       If OLD_N's next_true_id exists, make the true_tops = [next_true_id]

       If OLD_N's next_true_id does not exist, this means that all terms in
       OLD_N are evaluated to be false in the counter model.  We make
       OLD_N's next_true is to be the set {all true_tops of OLD_N's
       children} - {all true_tops of OLD_N's grandchildren}
       
       The same for OLD_N's false_tops
    *)
  let build_tops (old_graph:imp_graph) =
    (
      let num_nodes = old_graph#num_nodes() in
      let done_tbl = Array.make num_nodes false in  
      let doing_tbl = Array.make num_nodes false in
      let rec deal_node node_id  =
	(
	  assert (not (Array.get done_tbl node_id));
	  assert (not (Array.get doing_tbl node_id));
	  Array.set doing_tbl node_id true;
	  let cur_node = old_graph#ith_node_info node_id in
	  let cur_children = old_graph#ith_outs node_id in
	    List.iter 
	      (fun x -> if not (Array.get done_tbl x) then deal_node x)
	      cur_children;
	    ignore (
	      match (cur_node#next_false_id(), cur_node#next_true_id() )
	      with
		  (Some f_id, Some t_id) -> 
		    cur_node#update_false_tops [f_id];
		    cur_node#update_true_tops [t_id]
		| (Some f_id, None) ->
		    cur_node#update_false_tops [f_id];
		    let chls_tops = (get_chls_true_tops node_id) in
		    let grand_chls_tops=(get_grand_chls_true_tops node_id) in
		    let cur_tops=Util.list_minus chls_tops grand_chls_tops in
 		      (*cur_node#update_true_tops chls_tops*)
		      cur_node#update_true_tops cur_tops
		| (None, Some t_id) ->
		    cur_node#update_true_tops [t_id];		
		    let chls_tops = (get_chls_false_tops node_id) in
		    let grand_chls_tops=(get_grand_chls_false_tops node_id)in
		    let cur_tops=Util.list_minus chls_tops grand_chls_tops in
 		      (*cur_node#update_false_tops chls_tops*)
 		      cur_node#update_false_tops cur_tops
		| (_ , _) -> failwith "Should not be here" ;
	    );
	    
	    Array.set  done_tbl node_id true;
	)
      in
	deal_node (old_graph#get_false_node ()  )
    )
  in
    (* Given an old graph and a new graph, 
       For each node in old graph, if both next_true_id and next_false_id
       exists, add an edge from next_false_id to next_true_id in the new
       graph.

       For each edge l-->r in the old graph:
       If l's next_true_id exists, in the new graph add edges from l's
       next_true_id to r's true_tops.  
       If l's next_false_id exists, in the new graph add edges from l's
       next_false_id to r's false_tops.
       If l's next_true_id does not exists and r's next_false_id does not
       exists, the add edges from l's next_false_id to r's true_tops.  

    *)
  let final_new_graph (old_graph:imp_graph) (new_graph:imp_graph) = 
    (
      let add_one_to_many_edges one many =
	List.iter (fun x -> new_graph#add_edge one x) many 
      in
      let iter_old_node_func id node = 
	match node#next_false_id(), node#next_true_id() 
	with 
	    Some f_id, Some t_id -> 
	      assert (!changed);
	      new_graph#add_edge f_id t_id 
	  | _,_ -> ()
      in
      let iter_old_edge_func (l_id, r_id) =
	let l_node = old_graph#ith_node_info l_id in
	let r_node = old_graph#ith_node_info r_id in
	  match l_node#next_false_id(), l_node#next_true_id() 
	  with 
	      Some l_f_id, Some l_t_id -> 
		(
		  assert (!changed);
		  (*	       new_graph#add_edge l_f_id l_t_id ;*)
		 add_one_to_many_edges l_f_id (r_node#false_tops());
		 add_one_to_many_edges l_t_id (r_node#true_tops());
	       )
	   | Some l_f_id, None -> 
	       (
		 add_one_to_many_edges l_f_id (r_node#false_tops()); 
		 match r_node#next_false_id() with
		     None -> (
		       add_one_to_many_edges l_f_id (r_node#true_tops());
		       if (not !changed) 
		       then (
			 if (1 <> (List.length (r_node#false_tops() @ r_node#true_tops()))) 
		 then changed:=true
		       )
		     )
		   | Some _ -> (
		       if (not !changed) 
		       then (
		       if (1 <> (List.length (r_node#false_tops()) ))  
		       then changed:=true;
		       )
		     )
	       )
       	   | None, Some l_t_id -> (
	       add_one_to_many_edges l_t_id (r_node#true_tops() );
	       if (not !changed) 
	       then (
	       if (1 <> (List.length (r_node#true_tops()) ))  
	       then changed:=true;
	       )
	     )
	   | _ , _ -> failwith "should not be here"
     in
       old_graph#iter_node iter_old_node_func;
       old_graph#iter_edge iter_old_edge_func 
   )
  in
 let new_graph = iter_split_node hash_tbl old_graph  in
   build_tops old_graph ;
   final_new_graph old_graph new_graph ;
   if (not !changed) then(
     if (new_graph#num_edges () <>  old_graph#num_edges ())
     then changed := true;
   );
   ((new_graph#num_edges() > 0) || !changed ), new_graph
(*
  !changed, new_graph
*)


let doc_of_equ (impgraph:imp_graph) =
  let fold_func x y = 
    let equiv = x#equiv in 
    (Equiv_util.mk_eqs_one_class equiv L_BOOL)@y in
  let bool_eqs = impgraph#fold_nodes fold_func [] in
    bool_eqs

let strip_imp e =
  match e with  Types.F_IMPL (Types.F_PRED (expr_l,[]), Types.F_PRED(expr_r,[])) -> expr_l, expr_r
    | _ -> failwith "strip implications"

let mk_imp  expr_l expr_r ty  =
  Types.F_IMPL (Types.F_PRED (expr_l,[]), Types.F_PRED(expr_r,[]))

let doc_of_imp (impgraph:imp_graph) =
  let get_rep id = List.hd (impgraph#ith_node_info id)#equiv  in
  let fold_func (l,r) y = 
    let rep_l = get_rep l in
    let rep_r = get_rep r in
      if impgraph#is_false_node l or impgraph#is_true_node r 
      then y
      else (mk_imp rep_l rep_r L_BOOL)::y in
  let bool_impls = impgraph#fold_edges fold_func [] in
    bool_impls 


let internal_eq_imp_graph graph = 
  let eqs = (doc_of_equ graph) in
  let imps = (doc_of_imp graph) in
    eqs,imps

let internal_doc_of_asserts graph = 
  let eqs = (doc_of_equ graph) in
  let imps = (doc_of_imp graph) in
  if !OldFlags.no_imp then eqs
  else eqs@imps

let nvr_to_expr x = New_vars.nvr_to_expr x 
let nvr_to_nvr_def x = New_vars.nvr_to_nvr_def x   
let nvr_to_nvr_def_decl_body x = New_vars.nvr_to_nvr_def_decl_body x

 let eq_org eq = 
  match eq with 
      F_EQ (PRED(l,[]),PRED(r,[]),t) ->
	let l_str = Expr_util.map_org_il_expr (nvr_to_expr l) in
	let r_str =  Expr_util.map_org_il_expr (nvr_to_expr r) in
(*	  "(" ^ l_str ^ " = " ^ r_str ^ ")" ^ "::" ^ l ^ " , " ^ r*)
	  "(" ^ l_str ^ " = " ^ r_str ^ ")" 
    | _ -> failwith "eq_org" 


(*Teme: added for the invariant generation*)

let equ_invariant eq=
 match eq with 
      F_EQ (PRED(l,[]),PRED(r,[]),t) ->
	let l_str = (nvr_to_nvr_def_decl_body l) in
	let r_str = (nvr_to_nvr_def_decl_body r) in 
	  "( = " ^ l_str ^ r_str ^ ")" 
    | _ -> failwith "equ_invariant"


let int_eq_org eq = 
  match eq with 
      F_EQ (REL (EQ, PRED(l,[]), PRED(r, [])), ONE ,L_BOOL) ->
	let l_str = Expr_util.map_org_il_expr (nvr_to_expr l) in
	let r_str = Expr_util.map_org_il_expr (nvr_to_expr r) in
(*	  "(" ^ l_str ^ " = " ^ r_str ^ ")" ^ "::" ^ l ^ " , " ^ r*)
	  "(" ^ l_str ^ " = " ^ r_str ^ ")" 
    | _ -> failwith "eq_org" 

(*Teme: added for the invariant generation*)
let int_eq_invariant eq = 
  match eq with 
      F_EQ (REL (EQ, PRED(l,[]), PRED(r, [])), ONE ,L_BOOL) ->
	let l_str = (nvr_to_nvr_def_decl_body l) in
	let r_str = (nvr_to_nvr_def_decl_body r) in
	  "( = " ^ l_str ^ r_str ^ ")" 
    | _ -> failwith "int_eq_invariant" 


let imp_org imp = 
  match imp with 
      F_IMPL (F_PRED(l,[]),F_PRED(r,[])) ->
	let l_str = Expr_util.map_org_il_expr (nvr_to_expr l) in
	let r_str = Expr_util.map_org_il_expr (nvr_to_expr r) in
(*	  "(" ^ l_str ^ " => " ^ r_str ^ ")" ^ "::" ^ l ^ " , " ^ r*)
	  "(" ^ l_str ^ " => " ^ r_str ^ ")" 
    | _ -> failwith "imp_org" 

(*Teme: added for the invariant generation*)

let imp_invariant imp = 
  match imp with 
      F_IMPL (F_PRED(l,[]),F_PRED(r,[])) ->
	let l_str = (nvr_to_nvr_def_decl_body l) in
	let r_str = (nvr_to_nvr_def_decl_body r) in
	  "( => " ^ l_str ^" "^ r_str ^ ")" 
    | _ -> failwith "imp_invariant" 



let int_imp_org imp = 
  match imp with 
      F_EQ (REL (LTE, PRED(l,[]), PRED(r,[])), ONE, L_BOOL) ->
	let l_str = Expr_util.map_org_il_expr (nvr_to_expr l) in
	let r_str = Expr_util.map_org_il_expr (nvr_to_expr r) in
(*	  "(" ^ l_str ^ " => " ^ r_str ^ ")" ^ "::" ^ l ^ " , " ^ r*)
	  "(" ^ l_str ^ " <=" ^ r_str ^ ")" 
    | _ -> failwith "int_imp_org" 

(*Teme: added for the invariant generation*)

let int_imp_invariant imp = 
  match imp with 
      F_EQ (REL (LTE, PRED(l,[]), PRED(r,[])), ONE, L_BOOL) ->
	let l_str = (nvr_to_nvr_def_decl_body l) in
	let r_str = (nvr_to_nvr_def_decl_body r) in
	  "( <= " ^ l_str ^ " " ^ r_str ^ ")" 
    | _ -> failwith "int_imp_invariant"


open Types

let nvr_def x = New_vars.nvr_to_nvr_def x

let mk_eq_pos x y pos ty = F_EQ (PRED(x,[pos]), PRED(y, [pos]), ty)

let mk_eq_positions l r positions ty = 
  List.map (fun x -> mk_eq_pos l r x ty)  positions 


let mk_eq_pos_oneclass equiv_class positions = 
  let rec mk_eqs l = 
    match l with 
	[] -> []
      | hd::[] -> []
      | hd::((hd2::tl) as tail) ->
          (mk_eq_positions hd hd2 positions L_BOOL)

	  @(mk_eqs tail)  in
  let raw_defs = List.map nvr_def equiv_class in
    mk_eqs raw_defs 
	  
let mk_imp_pos x y pos = F_IMPL (F_PRED (x,[pos]), F_PRED(y,[pos]))
let mk_imp_positions l r positions = 
  List.map (fun x -> mk_imp_pos l r x)  positions 

(*Give a graph and a set of positions, return formulas that represents the
  graph at positions *)
let stepn_asserts (graph:imp_graph) positions = 
 
  let fold_node_func node rest = 
    let equiv_class = node#equiv in
     
      (mk_eq_pos_oneclass equiv_class positions)@rest in
  let eqs = graph#fold_nodes fold_node_func [] in
  let fold_edge_func (l,r) rest = 
    let get_rep id = 
      nvr_def (List.hd (graph#ith_node_info id)#equiv)  in
      if (graph#is_false_node l or graph#is_true_node r )
      then rest
      else 
	let cur_res = mk_imp_positions (get_rep l) (get_rep r) positions in
	  cur_res@rest 
  in
  let imps = graph#fold_edges fold_edge_func []in
    if !OldFlags.no_imp then eqs
    else eqs@imps

let internal_doc_of_stepn_asserts (graph:imp_graph) positions = 
  let fmls = stepn_asserts graph positions in
  let doc =   
    List.map 
      (fun x -> Lus_convert_yc.simple_command_string (ASSERT (x)))
      fmls 
  in 
    doc 


class bool_imp_graph init_equiv_class =
  let new_graph = new graph in
  let first_node_id = (new_graph#add_node (new node_info init_equiv_class)) in
object (self)
  initializer   
    new_graph#set_false_node first_node_id;
    new_graph#set_true_node first_node_id;
  val mutable d_graph = new_graph  
  method doc_of_asserts () = 
    internal_doc_of_asserts  d_graph
  method doc_of_stepn_asserts  positions = 
    internal_doc_of_stepn_asserts d_graph positions
  method set_new_graph hash_tbl =
    let changed,new_graph = get_new_graph hash_tbl d_graph in
      d_graph <- new_graph;
      changed
  method eq_imp_graph () = internal_eq_imp_graph d_graph
(*
  method internal_graph() =
    d_graph
*)
  method equiv_classes () = 
    d_graph#fold_nodes (fun x y -> (x#equiv) ::y) []
  method imps () =
    let imps = doc_of_imp d_graph in
      List.map strip_imp imps
 

end
    
    
