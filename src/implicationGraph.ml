(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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

open Lib
open Printf

type term = Term.t
module TermSet = Term.TermSet
module TermMap = Term.TermMap
type term_set = TermSet.t
let term_compare = Term.compare

let term_to_string t = Term.string_of_term t
let term_set_to_string set = TermSet.elements set
                             |> List.map term_to_string
                             |> String.concat ","
let term_top = Term.mk_true ()
let term_is_top term = term = term_top
let term_bottom = Term.mk_false ()
let term_is_bottom term = term = term_bottom

let check_graph_sanity = false

module rec FrontierUp :
sig

  type t =
    | TrueFalse of Node.t * (Node.t option)
    | FalseTrue of Node.t * Node.t
    | Nothing
  val to_string: t -> string
  val empty: unit -> t
  val update_uplinks: t -> SplitResult.t -> t
  val to_string: t -> string

end =

struct

  type t =
    | TrueFalse of Node.t * (Node.t option)
    | FalseTrue of Node.t * Node.t
    | Nothing

  let empty () = Nothing

  let to_string = function
    | TrueFalse (true_node, Some false_node) ->
       sprintf "TrueFalse(%s,%s)"
               (Node.to_string true_node)
               (Node.to_string false_node)
    | TrueFalse (true_node, None) ->
       sprintf "True(%s)"
               (Node.to_string true_node)
    | FalseTrue (false_node, true_node) ->
       sprintf "FalseTrue(%s,%s)"
               (Node.to_string false_node)
               (Node.to_string true_node)
    | Nothing -> "Nothing"


  (* Updates an up frontier with a split result, creating appropriate
     relations in the process. *)
  let update_uplinks up = function

    | SplitResult.True true_node ->
       ( match up with

         | TrueFalse (up_true, up_false_opt) ->
            (* True implies up true, and does not imply up_false. *)
            Node.relate true_node up_true ;

            TrueFalse (true_node, up_false_opt)

         | FalseTrue (up_false, up_true) ->
            (* True implies up true, and does not imply up_false. *)
            Node.relate true_node up_true ;

            TrueFalse (true_node, Some up_false)

         | Nothing ->
            (* We are actually handling the top node, nothing to
               do. *)
            TrueFalse (true_node, None) )

    | SplitResult.False false_node ->
       ( match up with

         | TrueFalse (up_true, up_false_opt) ->
            (* False implies up true. *)
            Node.relate false_node up_true ;

            ( match up_false_opt with
              | Some up_false ->
                 (* False implies false. Obviously up true does not
                    imply up false so we need to create the
                    relation. *)
                 Node.relate false_node up_false
              | None -> () ) ;

            FalseTrue (false_node, up_true )

         | FalseTrue (up_false, up_true) ->
            (* False implies up false --which already implies up
               true. *)
            Node.relate false_node up_false ;

            FalseTrue (false_node, up_true) 

         | Nothing ->
            (* This cannot happen, the top node cannot only evaluate
               to false. *)
            assert false )

    | SplitResult.Split (true_node, false_node) ->
       ( match up with

         | TrueFalse (up_true, up_false_opt) ->
            (* True implies up true. *)
            Node.relate true_node up_true ;

            ( match up_false_opt with
              | Some up_false ->
                 (* False implies up false. *)
                 Node.relate false_node up_false
              | None -> () ) ;

            (* That's all, true node and false node are already
               related. *)
            FalseTrue (false_node, true_node)

         | FalseTrue (up_false, up_true) ->
            (* True implies up true. *)
            Node.relate true_node up_true ;
            (* False implies up false. *)
            Node.relate false_node up_false ;

            (* That's all, true node and false node are already
               related. *)
            FalseTrue (false_node, true_node)

         | Nothing ->
            (* We are actually handling the top node, nothing to do as
               true node and false node are already related. *)
            FalseTrue (false_node, true_node) )

end

and FrontierDown :
sig

  type t =
    | FalseTrues of Node.t * NodeS.t
    | TrueFalses of Node.t * NodeS.t

  val to_string: t -> string

  type set

  val elements: set -> t list
  val cardinal: set -> int

  val compare: t -> t -> int

  val set_empty: unit -> set

  val set_add: set -> t -> set
  val set_add_list: set -> t list -> set

  val update_downlinks:
    set -> ConditionalRelation.set -> FrontierUp.t -> unit

end =

struct


  type t =
    | FalseTrues of Node.t * NodeS.t
    | TrueFalses of Node.t * NodeS.t

  let to_string = function
    | FalseTrues (false_node, true_nodes) ->
       sprintf "FalseTrues(%s, { %s })"
               (Node.to_string false_node)
               (NodeS.elements true_nodes |> List.map Node.to_string
                |> String.concat ",")
    | TrueFalses (true_node, false_nodes) ->
       sprintf "TrueFalses(%s, { %s })"
               (Node.to_string true_node)
               (NodeS.elements false_nodes |> List.map Node.to_string
                |> String.concat ",")


  let compare down1 down2 =
    let n1, n2 =
      ( (match down1 with
         | FalseTrues (n,_) -> n
         | TrueFalses (n,_) -> n),
        (match down2 with
         | FalseTrues (n,_) -> n
         | TrueFalses (n,_) -> n) )
    in

    Node.compare n1 n2

  type set = FrontierDownS.t

  let elements = FrontierDownS.elements
  let cardinal = FrontierDownS.cardinal

  let set_empty () = FrontierDownS.empty

  let set_add downs down =
    try

      let to_update = FrontierDownS.find down downs in
      let downs' = FrontierDownS.remove down downs in

      let downs'' =
        match to_update, down with

        | FalseTrues (n, set1), FalseTrues (_, set2) ->
           FrontierDownS.add
             (FalseTrues (n, NodeS.union set1 set2))
             downs'

        | TrueFalses (n, set1), TrueFalses (_, set2) ->
           FrontierDownS.add
             (TrueFalses (n, NodeS.union set1 set2))
             downs'

        | _ ->
           (* This cannot happen, the same node cannot evaluate
                   to true and false .*)
           assert false ;
      in

      downs''

    with
      Not_found -> FrontierDownS.add down downs

  (* Adds a list of down frontiers to a set of down frontiers. *)
  let rec set_add_list downs = function
    | down :: tail -> set_add_list (set_add downs down) tail
    | [] -> downs


  let update_downlinks downs c_rels up =

    ( match up with

      | FrontierUp.TrueFalse (true_up, false_up_opt)->
         downs
         |> FrontierDownS.iter
              ( function

                | TrueFalses (true_down, false_downs) ->
                   (* True implies true. *)
                   Node.relate true_down true_up ;
                   ( match false_up_opt with
                     | None -> ()
                     | Some false_up ->
                        (* False implies false. *)
                        false_downs
                        |> NodeS.iter
                             ( fun false_down ->
                               Node.relate false_down false_up) )

                | FalseTrues (false_down, true_downs) ->
                   (* True implies true. *)
                   true_downs
                   |> NodeS.iter
                        ( fun true_down ->
                          Node.relate true_down true_up ) ;
                   (* True downs do not imply false_down. *)
                   Node.relate false_down true_up ;
                   ( match false_up_opt with
                     | None -> ()
                     | Some false_up ->
                        (* False implies false. *)
                        Node.relate false_down false_up ) )

      | FrontierUp.FalseTrue (false_up, true_up) ->
         downs
         |> FrontierDownS.iter
              ( function

                | TrueFalses (true_down, false_downs) ->
                   (* True implies true. *)
                   Node.relate true_down true_up ;
                   (* False implies false. *)
                   false_downs
                   |> NodeS.iter
                        ( fun false_down ->
                          Node.relate false_down false_up)

                | FalseTrues (false_down, true_downs) ->
                   (* True implies true. *)
                   true_downs
                   |> NodeS.iter
                        ( fun true_down ->
                          Node.relate true_down true_up ) ;
                   (* False implies false. *)
                   Node.relate false_down false_up )

      | FrontierUp.Nothing -> () ) ;

    c_rels
    |> ConditionalRelation.iter
         ( function
           | (ConditionalRelation.FalseKidOf (parent, false_kid)) ->
              downs
              |> FrontierDownS.iter
                ( function
                  | TrueFalses (true_node, _) ->
                     Node.update_down_frontier
                       [FalseTrues (false_kid, NodeS.of_list [true_node])]
                       parent
                  | FalseTrues (_, true_nodes) ->
                     Node.update_down_frontier
                       [FalseTrues (false_kid, true_nodes)]
                       parent )

           | (ConditionalRelation.TrueKidOf (parent, true_kid)) ->
              downs
              |> FrontierDownS.iter
                ( function
                  | FalseTrues (false_true, _) ->
                     Node.update_down_frontier
                       [TrueFalses(true_kid, NodeS.of_list [false_true])]
                       parent
                  | TrueFalses (_, false_nodes) ->
                     Node.update_down_frontier
                       [TrueFalses (true_kid, false_nodes)]
                       parent ) ) ;



end

and ConditionalRelation :
sig
  type t =
    (* Parent * false kid. *)
    | FalseKidOf of Node.t * Node.t
    (* Parent * true kid. *)
    | TrueKidOf of Node.t * Node.t
  val to_string: t -> string
  type set
  val set_to_string: set -> string
  val set_empty: unit -> set
  val elements: set -> t list
  val cardinal: set -> int
  val iter: (t -> unit) -> set -> unit
  val set_update: set -> NodeS.t -> SplitResult.t -> set
end =

struct

  type t =
    (* Parent * false kid. *)
    | FalseKidOf of Node.t * Node.t
    (* Parent * true kid. *)
    | TrueKidOf of Node.t * Node.t

  let to_string = function
    | FalseKidOf (parent, false_kid) ->
       sprintf "FalseKidOf(%s <- %s)"
               (Node.to_string parent) (Node.to_string false_kid)
    | TrueKidOf (parent, true_kid) ->
       sprintf "TrueKidOf(%s <- %s)"
               (Node.to_string parent) (Node.to_string true_kid)

  type set = t list

  let set_to_string set =
    set
    |> ConditionalRelation.elements
    |> List.map ConditionalRelation.to_string
    |> String.concat ","

  let set_empty () = []

  let elements s = s
  let cardinal = List.length

  let iter = List.iter

  let rec set_update c_rels parents = function

    | SplitResult.True true_node ->
       let new_c_rels =
         NodeS.fold
           ( fun  parent c_rels' ->
             (TrueKidOf (parent, true_node)) :: c_rels' )
           parents
           (set_empty ())
       in

       c_rels
       |> List.fold_left
            ( fun c_rels' c_rel ->
              ( match c_rel with
                | FalseKidOf (parent, false_kid) ->
                   Node.update_down_frontier
                     [ FrontierDown.FalseTrues
                         ( false_kid,
                           NodeS.of_list [true_node] ) ]
                     parent ;
                   c_rels'
                | _ ->
                   c_rel :: c_rels' ) )
            new_c_rels

    | SplitResult.False false_node when Node.is_bottom false_node ->
       parents
       |> NodeS.iter
            ( Node.update_down_frontier
                [ FrontierDown.FalseTrues
                    ( false_node, NodeS.empty ) ] ) ;

       c_rels
       |> List.iter
            ( function
              | FalseKidOf (parent, false_kid) ->
                 Node.update_down_frontier
                   [ FrontierDown.FalseTrues
                       ( false_kid, NodeS.empty ) ]
                   parent
              | TrueKidOf (parent, true_kid) ->
                 Node.update_down_frontier
                   [ FrontierDown.TrueFalses
                       ( true_kid,
                         NodeS.of_list [false_node] ) ]
                   parent ) ;
       set_empty ()

    | SplitResult.False false_node ->
       let new_c_rels =
         NodeS.fold
           ( fun parent c_rels' ->
             (FalseKidOf (parent, false_node)) :: c_rels' )
           parents
           (set_empty ())
       in

       c_rels
       |> List.fold_left
            ( fun c_rels' c_rel ->
              ( match c_rel with
                | TrueKidOf (parent, true_kid) ->
                   Node.update_down_frontier
                     [ FrontierDown.TrueFalses
                         ( true_kid,
                           NodeS.of_list [false_node] ) ]
                     parent ;
                   c_rels'
                | _ ->
                   c_rel :: c_rels' ) )
            new_c_rels

    | SplitResult.Split (true_node, false_node) ->
       parents
       |> NodeS.iter
            ( Node.update_down_frontier
                [ FrontierDown.TrueFalses
                    ( true_node,
                      NodeS.of_list [false_node] ) ] ) ;

       c_rels
       |> List.iter
            ( function
              | FalseKidOf (parent, false_kid) ->
                 Node.update_down_frontier
                   [ FrontierDown.FalseTrues
                       ( false_kid,
                         NodeS.of_list [true_node] ) ]
                   parent
              | TrueKidOf (parent, true_kid) ->
                 Node.update_down_frontier
                   [ FrontierDown.TrueFalses
                       ( true_kid,
                         NodeS.of_list [false_node] ) ]
                   parent ) ;

       set_empty ()

end

and SplitResult :
sig
  (* Result of splitting a node. *)
  type t =
    (* No split, all members evaluated to true. *)
    | True of Node.t
    (* No split, all members evaluated to false. *)
    | False of Node.t
    (* Split, first the true node and then the false node. *)
    | Split of Node.t * Node.t
end =

struct
  (* Result of splitting a node. *)
  type t =
    (* No split, all members evaluated to true. *)
    | True of Node.t
    (* No split, all members evaluated to false. *)
    | False of Node.t
    (* Split, first the true node and then the false node. *)
    | Split of Node.t * Node.t
end

(* Node module. *)
and Node :
sig

  (* An equivalence class, i.e. a node of the implication graph. *)
  type t

  val representative: t -> term
                             
  val members: t -> term_set
                             
  val kids: t -> NodeS.t

  val to_string: t -> string

  val create_top: TermSet.t -> t

  val is_top: t -> bool

  val is_bottom: t -> bool

  val print: t -> unit

  val check_links: t -> bool


  (* The context passed down during graph rewriting. *)
  type context
  val print_context: context -> unit

  val update_context:
    context -> SplitResult.t -> NodeS.t -> FrontierDown.set -> context

  val top_context: unit -> context

  (* Prints a graph to a file. *)
  val graph_to_dot: string -> t -> unit

  (* Comparison function for nodes. *)
  val compare: t -> t -> int

  (* Updates the down frontier of a node. *)
  val update_down_frontier: FrontierDown.t list -> Node.t -> unit

  (* Creates a birectional kid/parent relation between two nodes. *)
  val relate: t -> t -> unit

  val split:
    (t -> unit) -> int -> (term -> bool) -> t ->
    (bool * NodeS.t * NodeS.t * FrontierDown.set * SplitResult.t)

  (* All the nodes of a graph. *)
  val all_nodes_of: t -> NodeS.t

end =

struct

  (* An equivalence class, i.e. a node of the implication graph. *)
  type t = {

    (* The representative of this class. *)
    representative: term ;
    (* The members of this class, INCLUDING the representative. *)
    members: TermSet.t ;
    (* The value of this node when it was created. *)
    value: bool ;

    (* The kids of this node. *)
    mutable kids: NodeS.t ;
    (* The parents of this node. *)
    mutable parents: NodeS.t ;

    (* Downward information about sub chains already evaluated. *)
    mutable updated_down_frontier: FrontierDown.set ;


    (* Debug and log stuff. *)

    (* The graph iteration at which this node was created. *)
    iteration: int ;
    (* All the values the members of this class have been evaluated
          to. *)
    history: bool list ;
    (* The node iteration at which this node was created. *)
    creation_index: int ;
    (* The representative of the old node this node comes from. *)
    creation_from: term ;

  }




  let all_nodes_of graph =

    let rec collect_nodes nodes to_visit =
      try
        let node = NodeS.choose to_visit in
        if NodeS.mem node nodes then
          collect_nodes
            nodes
            (NodeS.remove node to_visit)
        else
          collect_nodes
            (NodeS.add node nodes)
            (NodeS.remove node to_visit |> NodeS.union node.kids)
      with
        Not_found -> nodes
    in

    collect_nodes NodeS.empty (NodeS.singleton graph)






  let representative { representative } = representative
                                            
  let members { members } = members
                                            
  let kids { kids } = kids

  type set = NodeS.t

  let is_top node = TermSet.exists term_is_top node.members
  let is_bottom node = TermSet.exists term_is_bottom node.members


  (* Creates a set of nodes from a list. *)
  let set_of_list l = NodeS.of_list l

  let isolate ({ kids ; parents ; updated_down_frontier } as node) =
    parents
    |> NodeS.iter
         ( fun parent ->
           parent.kids <- NodeS.remove node parent.kids ) ;
    kids
    |> NodeS.iter
         ( fun kid ->
           kid.parents <- NodeS.remove node kid.parents ) ;
    node.kids <- NodeS.empty ;
    node.parents <- NodeS.empty ;
    node.updated_down_frontier <- FrontierDown.set_empty () ;
    (kids, parents, updated_down_frontier)

  (* Creates a graph with only one node. Should contain the top and
     bottom terms. *)
  let create_top members =
    (* Members should include top term. *)
    assert ( TermSet.exists term_is_top members ) ;
    (* Members should include bottom term. *)
    assert ( TermSet.exists term_is_bottom members ) ;

    (* Creating a node. *)
    { representative = term_top ;
      members = members ;
      value = true ; (* Why not, we don't care anyway. *)

      kids = NodeS.empty ;
      parents = NodeS.empty ;

      updated_down_frontier = FrontierDown.set_empty () ;

      iteration = 0 ;
      history = [] ;
      creation_index = 0 ;
      creation_from = term_top ; }


  (* Compare function for nodes. *)
  let compare node node' =
    (* Making sure we are comparing nodes created at the same
       iteration. *)
    assert (node.iteration = node'.iteration) ;
    term_compare node.representative node'.representative




  (* To string things. *)

  let to_string { representative } =
    term_to_string representative

  let set_to_string set =
    NodeS.elements set |> List.map to_string |> String.concat ","

  let history_to_string h =
    List.rev h
    |> List.map (fun b -> if b then "1" else "0")
    |> String.concat ","

  let to_string_list
        { representative ; members ; value ; kids ; parents ;
          iteration ; history ; creation_index ; creation_from } =
    [ sprintf "Node %s created at %i.%i from %s {"
              (term_to_string representative)
              iteration
              creation_index
              (term_to_string creation_from) ;
      sprintf "  members: %s" (term_set_to_string members) ;
      sprintf "  kids:    %s" (set_to_string kids) ;
      sprintf "  parents: %s" (set_to_string parents) ;
      sprintf "  history: %s" (history_to_string history) ;
      "}" ]



  (* Prints a node. *)
  let print node =
    to_string_list node
    |> List.iter (printf "%s\n")


  let check_implication n1 n2 =
    let rec loop = function
      | b1 :: tail1, b2 :: tail2 ->
         if (not b1) || b2 then loop (tail1,tail2)
         else false
      | [],[] -> true
      | _ -> failwith "Inconsistent history detected."
    in

    loop (n1.history, n2.history)

  let check_links node =

    let bad_kids, bad_parents =
      (node.kids
       |> NodeS.filter
            ( fun kid -> not (check_implication kid node) )),
      (node.parents
       |> NodeS.filter
            ( fun parent -> not (check_implication node parent) ))
    in

    let bad_kids', bad_parents' =
      (node.kids
       |> NodeS.filter
            ( fun kid -> not (NodeS.mem node kid.parents) )),
      (node.parents
       |> NodeS.filter
            ( fun parent -> not (NodeS.mem node parent.kids) ))
    in

    ( if NodeS.is_empty node.parents && (not (is_top node))
      then (
        printf "\n[Error] Node has empty parents but is not top:\n" ;
        print node ;
        printf "\n" ;
        false
      ) else true )

    &&

      ( if NodeS.is_empty node.kids && (not (is_bottom node))
        then (
          printf "\n[Error] Node has empty kids but is not bottom:\n" ;
          print node ;
          printf "\n" ;
          printf "His parents are:\n" ;
          node.parents |> NodeS.iter print ;
          false
        ) else true )

    &&

      ( if not (NodeS.is_empty bad_kids) then (
          printf "\n[Error] Some kids of node\n" ;
          print node ;
          printf "do not entail it. Bad kids are:\n" ;
          bad_kids |> NodeS.iter print ;
          printf "\n" ;
          false
        ) else true )

    &&

      ( if not (NodeS.is_empty bad_parents) then (
          printf "\n[Error] Some parents of node\n" ;
          print node ;
          printf "are not entailed. Bad parents are:\n" ;
          bad_parents |> NodeS.iter print ;
          printf "\n" ;
          false
        ) else true )

    &&

      ( if not (NodeS.is_empty bad_kids') then (
          printf "\n[Error] Some kids of node\n" ;
          print node ;
          printf "do not know it. Bad kids are:\n" ;
          bad_kids |> NodeS.iter print ;
          printf "\n" ;
          false
        ) else true )

    &&

      ( if not (NodeS.is_empty bad_parents') then (
          printf "\n[Error] Some parents of node\n" ;
          print node ;
          printf "do not know it. Bad parents are:\n" ;
          bad_parents |> NodeS.iter print ;
          printf "\n" ;
          false
        ) else true )


  (* Prints a graph to a file. *)
  let graph_to_dot file ({ iteration } as node) =

    (* Used to remember the nodes we already saw. *)
    let mem = ref NodeS.empty in
    (* Adds a node to the memory. *)
    let remember node = mem := NodeS.add node !mem in
    (* Returns true if we have already seen this node. *)
    let already_seen node = NodeS.mem node !mem in

    (* Recursive print function. *)
    let rec print_node
              oc
              ({ representative ; members ;
                 kids ; parents ;
                 iteration ; history ;
                 creation_index ; creation_from } as node) =

      (* Doing nothing if already seen. *)
      if already_seen node then () else (

        fprintf oc
                "  %10i [label=\"%s {%i}\"]\n"
                (* "  %10i [label=\"%s {%i}\\n(%i,%s)\\n%s\\n%s\"]\n" *)
                (Term.tag representative)
                (term_to_string representative)
                (TermSet.cardinal members) ;
                (* creation_index *)
                (* (term_to_string creation_from) *)
                (* (term_set_to_string members) *)
                (* (history_to_string history) ; *)

        remember node ;

        NodeS.iter (print_node oc) kids

      )
    in


    let oc = open_out file in

    fprintf oc "digraph iteration%i {\n\n" iteration ;
    print_node oc node ;
    fprintf oc "\n\n" ;

    !mem
    |> NodeS.iter
         ( fun ({ representative ; parents ; kids }) ->

           fprintf oc "\n// Node %i:\n" (Term.tag representative) ;

           (* Printing parents relations. *)
           fprintf oc "// Parents of %i:\n" (Term.tag representative) ;
           parents
           |> NodeS.iter
                ( fun parent ->
                  fprintf oc
                          "  %10i -> %10i [dir=back, color=\"black\"]\n"
                          (Term.tag parent.representative)
                          (Term.tag representative) ) ;

           (* Printing kids relations. *)
           (* fprintf oc "// Kids of %s:\n" representative ; *)
           (* kids *)
           (* |> NodeS.iter *)
           (*      ( fun kid -> *)
           (*        fprintf oc *)
           (*                "  %10s -> %10s [dir=back, color=\"red\"]\n" *)
           (*                representative kid.representative ) *)
         ) ;

    fprintf oc "\n\n}\n" ;
    close_out oc ;
    
    ()

  let node_eq n n' = compare n n' = 0

  (* Destroys a kid/parent relation between two nodes. *)
  let unrelate kid parent =
    (* Breaking it. *)
    kid.parents <- kid.parents |> NodeS.remove parent ;
    parent.kids <- parent.kids |> NodeS.remove kid

  let break_redundants kid parent =
    (* Removing parent from the kid's kids. *)
    kid.kids
    |> NodeS.iter (fun grand_kid -> unrelate grand_kid parent) ;
    (* Removing the kid from the parent's parents. *)
    parent.parents
    |> NodeS.iter (unrelate kid) ;
    (* Removing true from the kid's parents. *)
    kid.parents
    |> NodeS.iter (fun parent ->
                   if is_top parent then unrelate kid parent) ;
    (* Removing false from the parent's kids. *)
    parent.kids
    |> NodeS.iter (fun kid ->
                   if is_bottom kid then unrelate kid parent)


  let shall_relate kid parent =
    (* Not relating kids already related by one node. *)
    ( not ( parent.kids
            |> NodeS.exists
                 ( fun kid' ->
                   kid'.kids |> NodeS.mem kid ) ) )
    (* Not relating a node to top if it has parents. *)
    && ( not (is_top parent) || (NodeS.is_empty kid.parents) )
    (* Not relating a node to bottom if it has kids. *)
    && ( not (is_bottom kid) || (NodeS.is_empty parent.kids) )                       


  (* Creates a birectional kid/parent relation between two nodes. *)
  let relate kid parent =
    (* if *)
    (*   ( not ( parent.kids *)
    (*           |> NodeS.exists *)
    (*                ( fun kid' -> *)
    (*                  kid'.kids |> NodeS.mem kid ) ) ) *)
    (* then redundant_relation () ; *)
    
    if shall_relate kid parent then (
      break_redundants kid parent ;
      kid.parents <- kid.parents |> NodeS.add parent ;
      parent.kids <- parent.kids |> NodeS.add kid
    )


  (* Updates the down frontier of a node. *)
  let update_down_frontier new_downs node =
    node.updated_down_frontier <-
      FrontierDown.set_add_list node.updated_down_frontier new_downs


  (* Splits a node based on an evaluation function. Links the nodes
     created if necessary. *)
  let split remember_node
            creation_index
            eval
            ({ representative ; members ; value ; history ; iteration }
             as node) =

    (* Making sure there are some members to split. *)
    assert ( not (TermSet.is_empty members) ) ;

    (* printf "Handling:\n" ; *)
    (* print node ; *)

    (* Breaking everything. *)
    let kids, parents, down_frontier_set = isolate node in

    (* Splitting the members in two. *)
    let trues, falses =
      members |> TermSet.partition eval
    in

    match
      ( if TermSet.is_empty trues then None else
          (* Creating true node. *)
          Some {
              (* Trying to keep the same representative. *)
              representative =
                if TermSet.mem representative trues
                then representative
                else TermSet.choose trues ;
              members = trues ;
              value = true ;

              kids = NodeS.empty ;
              parents = NodeS.empty ;

              updated_down_frontier = FrontierDown.set_empty () ;

              iteration = iteration + 1 ;
              history = [] ; (* true :: history ; *)
              creation_index = creation_index ;
              creation_from = representative ;
            } ),

      ( if TermSet.is_empty falses then None else
          (* Creating false node. *)
          Some {
              (* Trying to keep the same representative. *)
              representative =
                if TermSet.mem representative falses
                then representative
                else if TermSet.mem term_bottom falses
                then term_bottom
                else TermSet.choose falses ;
              members = falses ;
              value = false ;

              kids = NodeS.empty ;
              parents = NodeS.empty ;

              updated_down_frontier = FrontierDown.set_empty () ;

              iteration = iteration + 1 ;
              history = [] ; (* false :: history ; *)
              creation_index = creation_index ;
              creation_from = representative ;
            } )
    with

    | Some true_node, Some false_node ->
       remember_node true_node ;
       remember_node false_node ;
       (* printf "Splitting %s to %s <- %s.\n" *)
       (*        (to_string node) (to_string true_node) (to_string false_node) ; *)
       relate false_node true_node ;
       true,
       kids,
       parents,
       down_frontier_set,
       SplitResult.Split (true_node, false_node)

    | Some true_node, None ->
       remember_node true_node ;
       (* printf "Splitting %s to %s (true).\n" *)
       (*        (to_string node) (to_string true_node) ; *)
       not value,
       kids,
       parents,
       down_frontier_set,
       SplitResult.True true_node

    | None, Some false_node ->
       remember_node false_node ;
       (* printf "Splitting %s to %s (false).\n" *)
       (*        (to_string node) (to_string false_node) ; *)
       value,
       kids,
       parents,
       down_frontier_set,
       SplitResult.False false_node

    | None, None ->
       failwith "Node has no members."


  (* The context passed down during graph rewriting. *)
  type context =
      { frontier_up: FrontierUp.t ;
        conditional_parents: ConditionalRelation.set }

  let print_context { frontier_up ; conditional_parents } =
    printf "Context {\n  %s\n  (%s)\n}\n"
            (FrontierUp.to_string frontier_up)
            (ConditionalRelation.set_to_string conditional_parents)

  (* The graph rewriting context for the top node. *)
  let top_context () = {
    frontier_up = (FrontierUp.empty ()) ;
    conditional_parents = (ConditionalRelation.set_empty ())
  }

  let update_context
        { frontier_up ; conditional_parents }
        split_result
        parents frontier_down_set =

    let frontier_up' =
      FrontierUp.update_uplinks
        frontier_up split_result
    in

    let conditional_parents' =
      ConditionalRelation.set_update
        conditional_parents parents split_result
    in

    
    FrontierDown.update_downlinks
      frontier_down_set conditional_parents' frontier_up' ;

    { frontier_up = frontier_up' ;
      conditional_parents = conditional_parents' }

end

and NodeS: Set.S
    with type elt = Node.t =
                      Set.Make(Node)

and FrontierDownS: Set.S
    with type elt = FrontierDown.t =
                      Set.Make(FrontierDown)


type t = {
  graph: Node.t ;
  eq_classes: term_set list ;
  non_trivial_implications: term list ;
  trivial_implications: term list ;
}

let eq_classes { eq_classes } = eq_classes

let non_trivial_implications
      { non_trivial_implications } = non_trivial_implications

let trivial_implications
      { trivial_implications } = trivial_implications

let to_dot file { graph } = Node.graph_to_dot file graph

let create members = {
  graph = Node.create_top members ;
  eq_classes = [members] ;
  non_trivial_implications = [] ;
  trivial_implications = [] ;
}

let build_graph_container all_nodes graph =

  (* let all_nodes = Node.all_nodes_of graph in *)

  (* Checking the links of all the nodes now that the graph has been
       printed. *)
  if check_graph_sanity then
    assert ( List.fold_left
               (fun b n -> b && (Node.check_links n))
               true
               all_nodes ) ;

  let eq_classes, non_trivial_implications, trivial_implications =
    List.fold_left

      ( fun (eq_cls, nt_impls, t_impls) node ->
        
        let nt_impls', t_impls' =
          NodeS.fold
            ( fun kid (nt_list, t_list) ->
              if Node.is_top node || Node.is_bottom kid then
                (nt_list,
                 ((Term.mk_implies
                     [ Node.representative kid ;
                       Node.representative node ]) :: t_list))
              else
                (((Term.mk_implies
                     [ Node.representative kid ;
                       Node.representative node ]) :: nt_list),
                t_list) )
            (Node.kids node)
            (nt_impls, t_impls)
        in
        
        ((Node.members node) :: eq_cls, nt_impls', t_impls') )
      
      ([], [], [])
      
      all_nodes
  in

  { graph ; eq_classes ;
    non_trivial_implications ; trivial_implications }

let create_of_list members =
  create (TermSet.of_list members)

let rewrite_graph eval { graph } =

  (* Making sure this node is the top node. *)
  assert ( Node.is_top graph ) ;

  let creation_index = ref 0 in
  let mem = ref TermSet.empty in

  let shall_skip node =
    TermSet.mem (Node.representative node) !mem
  in

  let remember node =
    mem := TermSet.add (Node.representative node) !mem
  in

  let rec continue f changed = function
    | (context, nodes) :: tail ->
       ( try
           let node = NodeS.choose nodes in
           let nodes' = NodeS.remove node nodes in
           f changed context node ((context, nodes') :: tail)
         with
           Not_found -> continue f changed tail )
    | _ -> changed
  in

  let all_nodes_ref = ref [] in
  let remember_node node = all_nodes_ref := node :: !all_nodes_ref in

  let rec loop changed context node continuation =

    if shall_skip node then

      continue loop changed continuation

    else (

      remember node ;

      creation_index := 1 + !creation_index ;

      let node_changed, node_kids, node_parents,
          down_frontier_set, split_result =
        Node.split remember_node !creation_index eval node
      in

      let new_context =
        Node.update_context
          context
          split_result
          node_parents
          down_frontier_set
      in

      continue loop
               (node_changed || changed)
               ((new_context, node_kids) :: continuation)
    )
           
  in

  (* We begin by splitting the top node. *)
  let top_changed, top_kids, top_parents, _, top_result =
    Node.split remember_node !creation_index eval graph
  in

  (* Top node should have no parents. *)
  assert ( NodeS.is_empty top_parents ) ;

  (* Memorizing the top node so that we can return it afterwards. *)
  let top_node =
    match top_result with
    | SplitResult.True true_node -> true_node
    | SplitResult.Split (true_node, _) -> true_node
    | SplitResult.False _ ->
       (* All elements of the top node cannot be false. *)
       failwith "Top node cannot evaluate to false."
  in

  try

    let first_kid = NodeS.choose top_kids in
    let other_kids = NodeS.remove first_kid top_kids in

    (* Updating the top (empty) context. *)
    let context =
      Node.update_context
        (Node.top_context ())
        top_result
        NodeS.empty
        (FrontierDown.set_empty ())
    in

    let changed =
      loop top_changed context first_kid [ (context, other_kids) ]
    in

    (not changed, build_graph_container !all_nodes_ref top_node )

  with
    Not_found ->
    if (Node.is_bottom graph)
    then (not top_changed, build_graph_container !all_nodes_ref top_node)
    else assert false ;
    
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

