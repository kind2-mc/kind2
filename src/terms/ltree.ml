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

(* Abbreviation for module name *)
module H = Hashcons


(* Set over integers *)
module IntegerSet = Set.Make (struct type t = int let compare = compare end)


(* Input signature for functor *)
module type BaseTypes =
sig

  type symbol 

  type var 

  type sort

  type attr

  val hash_of_symbol : symbol -> int

  val hash_of_var : var -> int

  val hash_of_sort : sort -> int

  val hash_of_attr : attr -> int

  val sort_of_var : var -> sort

  val mk_fresh_var : sort -> var

  val import_symbol : symbol -> symbol

  val import_var : var -> var

  val import_sort : sort -> sort

  val pp_print_symbol : Format.formatter -> symbol -> unit

  val pp_print_var : Format.formatter -> var -> unit

  val pp_print_sort : Format.formatter -> sort -> unit

  val pp_print_attr : Format.formatter -> attr -> unit

end


(* Output signature of functor *)
module type S = 
sig

  type symbol 

  type var 

  type sort

  type attr

  type lambda_node = private L of sort list * t

  and lambda = private (lambda_node, unit) H.hash_consed

  and t_node = private
    | FreeVar of var
    | BoundVar of int
    | Leaf of symbol
    | Node of symbol * t list
    | Let of lambda * t list
    | Exists of lambda
    | Forall of lambda
    | Annot of t * attr

  and t = private (t_node, t_prop) H.hash_consed

  and t_prop = private { bound_vars : int list } 

  and flat = private
    | Var of var
    | Const of symbol
    | App of symbol * t list
    (* | Attr of t * attr *)

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val hash : t -> int

  val tag : t -> int

  val mk_lambda : var list -> t -> lambda

  val eval_lambda : lambda -> t list -> t

  val partial_eval_lambda : lambda -> t list -> lambda

  val mk_term : t_node -> t

  val mk_var : var -> t
  
  val mk_const : symbol -> t

  val mk_app : symbol -> t list -> t

  val mk_let : (var * t) list -> t -> t

  val mk_let_elim : (var * t) list -> t -> t

  val mk_exists : var list -> t -> t

  val mk_forall : var list -> t -> t

  val mk_annot : t -> attr -> t

  val node_of_t : t -> t_node

  val node_of_lambda : lambda -> lambda_node

  val sorts_of_lambda : lambda -> sort list

  val tag_of_t : t -> int
(*
  val eval : (symbol -> 'a list -> 'a) -> t -> 'a
*)
  val eval_t : ?fail_on_quantifiers:bool -> (flat -> 'a list -> 'a) -> t -> 'a

  val map : (int -> t -> t) -> t -> t

  val destruct : t -> flat

  val has_quantifier : t -> bool

  val instantiate : lambda -> t list -> t

  val construct : flat -> t

  val import : t -> t

  val import_lambda : lambda -> lambda

  val pp_print_term : ?db:int -> Format.formatter -> t -> unit
    
  val pp_print_lambda_w :
    (?arity:int -> Format.formatter -> symbol -> unit) ->
    (Format.formatter -> var -> unit) ->
    (Format.formatter -> sort -> unit) ->
    ?db:int -> Format.formatter -> lambda -> unit

  val pp_print_term_w :
    (?arity:int -> Format.formatter -> symbol -> unit) ->
    (Format.formatter -> var -> unit) ->
    (Format.formatter -> sort -> unit) ->
    ?db:int -> Format.formatter -> t -> unit

  val print_term : ?db:int -> t -> unit

  val pp_print_lambda : ?db:int -> Format.formatter -> lambda -> unit
    
  val print_lambda : ?db:int -> lambda -> unit

  val stats : unit -> int * int * int * int * int * int

end    


(* Functor to create a higher-order abstract syntax tree module *)
module Make(T : BaseTypes) : 
  (S with type symbol = T.symbol 
      and type var = T.var 
      and type sort = T.sort
      and type attr = T.attr) =
struct

  (* ********************************************************************* *)
  (* Type definitions                                                      *)
  (* ********************************************************************* *)

  (* Symbol, constrained by the type of the input module *)
  type symbol = T.symbol

  (* Free variable, constrained by the type of the input module *)
  type var = T.var

  (* Sort, constrained by the type of the input module *)
  type sort = T.sort

  (* Attribute, constrained by the type of the input module *)
  type attr = T.attr

  (* Typed lambda abstraction

     We do nameless abstraction with de Bruijn indexes, hence we only have
     the type of the variables bound in the abstraction. 

     We need the variant L to do pattern matching because the type is
     private. *)
  type lambda_node = L of sort list * t

  (* Hashconsed typed lambda abstraction *)
  and lambda = (lambda_node, unit) H.hash_consed

  (* Abstract syntax term with let bindings and quantifiers *)
  and t_node = 

    (* Free variable *)
    | FreeVar of var

    (* Bound variable with its de Bruijn index *)
    | BoundVar of int

    (* Constant, i.e. a nullary symbol *)
    | Leaf of symbol

    (* Function application, the list must not be empty *)
    | Node of symbol * t list

    (* Let binding *)
    | Let of lambda * t list

    (* Existential quantification *)
    | Exists of lambda

    (* Universal quantification *)
    | Forall of lambda

    (* Annotated term *)
    | Annot of t * attr

  (* Property of a term node *)
  and t_prop = { bound_vars : int list } 

  (* Hashconsed abstract syntax term *)
  and t = (t_node, t_prop) H.hash_consed

  (* Flattened term without binders at the top symbol *)
  type flat = 
    | Var of var
    | Const of symbol
    | App of symbol * t list
    (* | Attr of t * attr *)

  (* Return property of term *)
  let hash_of_term { H.hkey = h } = h

  (*
  (* Return property of term *)
  let prop_of_term { H.prop = p } = p
  *)

  (* Hashconsed lambda abstraction *)
  module Lambda_node = 
  struct 

    (* Type of the hashconsed node *)
    type t = lambda_node 

    (* Type of the node property *)
    type prop = unit

    (* Equality: abstracted terms are equal, number of variables and
       their types are equal *)
    let equal l1 l2 = match l1, l2 with
      | L (i1, t1), L (i2, t2) -> 
        (t1 == t2) &&
        (List.length i1 = List.length i2) &&
        (List.for_all2 (==) i1 i2)

    (* Take hash of abstracted term, ignoring the type *)
    let hash (L (_, t)) = hash_of_term t

  end

  (* Hashconsing for lambda abstractions *)
  module Hlambda = H.Make (Lambda_node)

  (* Hashcons table for lambda abstractions *)
  let hl = Hlambda.create 251

  (* Unsafe constructor for hashconsed lambda abstraction *)
  let hl_lambda s t = Hlambda.hashcons hl (L (s, t)) ()

  (* Hashconsed terms *)
  module T_node = 
  struct 

    (* Type of the hashconsed node *)
    type t = t_node

    (* Type of the node property *)
    type prop = t_prop

    (* Equality of two terms *)
    let equal t1 t2 = match t1, t2 with 

      (* Equality on free variables: variables are physically equal *)
      | FreeVar v1, FreeVar v2 -> v1 == v2

      (* Equality on integer de Bruijn indexes *)
      | BoundVar v1, BoundVar v2 -> v1 = v2 

      (* Physical equality on leaves *)
      | Leaf s1, Leaf s2 -> s1 == s2

      (* Equality of nodes: symbols are physically equal, number of
         subterms is equal and respective subterms are physically
         equal *)
      | Node (s1, a1), Node (s2, a2) -> 
        (s1 == s2) &&
        (List.length a1 = List.length a2) &&
        (List.for_all2 (==) a1 a2)

      (* Equality of let bindings: lambda abstractions are physically
         equal, number of terms are equal and respective terms are
         physically equal *)
      | Let (l1, b1), Let (l2, b2) ->
        (l1 == l2) &&
        (List.length b1 = List.length b2) &&
        (List.for_all2 (==) b1 b2)

      (* Equality of quantifiers: lambda abstractions are physically
         equal *)
      | Exists l1, Exists l2
      | Forall l1, Forall l2 -> l1 == l2

      (* Equality of annotated terms: terms are physically equal and
         annotations are physically equal *)
      | Annot (t1, a1), Annot (t2, a2) -> t1 == t2 && a1 == a2

      (* Terms of different kinds are not equal *)
      | FreeVar _, _
      | BoundVar _, _
      | Leaf _, _
      | Node _, _
      | Let _, _
      | Exists _, _
      | Forall _, _
      | Annot _, _ -> false

    (* Hash of a term: interleave hash values of kinds *)
    let hash = function 

      (* Hash of a free variable: delegate *)
      | FreeVar v -> 

        safe_hash_interleave
          (T.hash_of_var v)
          8 0

      (* Hash of bound variable is the de Bruijn index *)
      | BoundVar i -> safe_hash_interleave i 8 1

      (* Hash of symbol: delegate *)
      | Leaf s -> safe_hash_interleave (T.hash_of_symbol s) 8 2

      (* Hash of a node: hash a list of hashes of symbol and arguments *)
      | Node (s, l) -> 

        safe_hash_interleave
          (Hashtbl.hash 
             ((T.hash_of_symbol s) :: 
                (List.map (function { H.hkey = h } -> h) l)))
          8
          3

      (* Hash of a let binding: hash a list of hashes of lambda
         abstraction and bound terms *)
      | Let ({ H.hkey = hl }, l) ->       

        safe_hash_interleave
          (Hashtbl.hash 
             (hl :: (List.map (function { H.hkey = h } -> h) l)))
          8
          4

      (* Hash of quantifiers: hash of lambda abstraction *)
      | Exists { H.hkey = hl } -> safe_hash_interleave hl 8 5 
      | Forall { H.hkey = hl } -> safe_hash_interleave hl 8 6

      (* Hash of attribute: delegate *)
      | Annot ( { H.hkey = ht }, a) -> 

        safe_hash_interleave (Hashtbl.hash [T.hash_of_attr a; ht]) 8 7

  end

  (* Hashconsing for terms *)
  module Ht = H.Make (T_node)

  (* Hashcons table for terms *)
  let ht = Ht.create 251

  let stats () = Ht.stats ht

  (* Ordering of terms based on tags *)
  let compare { H.tag = t1 } { H.tag = t2 } = Stdlib.compare t1 t2

  (* Equality of terms based on tags *)
  let equal { H.tag = t1 } { H.tag = t2 } = t1 = t2

  (* Hashing based on stored hash *)
  let hash { H.hkey = h } = h

  (* Return unique identifier *)
  let tag { H.tag = i } = i

  (* Read bound variables from term properties and add to list without
     duplicates *)
  let bound_vars_of_terms accum t = 

    (* Add lists of bound variables to a set and return elements of set *)
    IntegerSet.elements
      (List.fold_left 
         (fun a { H.prop = { bound_vars } } -> 
            IntegerSet.union a (IntegerSet.of_list bound_vars))
         accum
         t)

  (* Reduce list of variables to those bound outside a lambda
     abstraction of l variables, and adjust their indexes *)
  let bound_vars_outside_lambda l b = 

    (* Return in original order *)
    List.rev

      (List.fold_left

         (fun a i -> 

            (* Is the variable bound outside this lambda abstraction *)
            if i > l then 

              (* Adjust distance to bound term *)
              i - l :: a 

            else 

              (* Discard variable bound by this lambda abstraction *)
              a)

         []

         b)

  (* Read bound variables of properties subterms and return as list *)
  let bound_vars_of_term_node = function

    (* Free variable or constant do not have bound variables *)
    | FreeVar _ 
    | Leaf _  -> []

    (* Bound variable is the only bound variables *)
    | BoundVar i -> [i]

    (* Bound variables in a function application are the bound
       variables in subterms *)
    | Node (_, l) -> bound_vars_of_terms IntegerSet.empty l

    (* Bound variables in let bindings are bound variables in term and
       bound variables in substituted terms *)
    | Let ({ H.node = L (_, { H.prop = { bound_vars } } ) }, l)  -> 

      let bound_vars' =
        bound_vars_outside_lambda (List.length l) bound_vars
      in

      bound_vars_of_terms (IntegerSet.of_list bound_vars') l 


    (* Bound variables in quantifier are variables in quantified term *)
    | Exists { H.node = L (i, { H.prop = { bound_vars } }) } 
    | Forall { H.node = L (i, { H.prop = { bound_vars } }) } -> 

      bound_vars_outside_lambda (List.length i) bound_vars

    (* Bound variables in annotated term are bound variables in term *)
    | Annot ({ H.prop = { bound_vars } }, _) -> bound_vars


  (* Initilize property of term *)
  let prop_of_term_node t = 

    (* Get bound variables from term to construct *)
    let bound_vars = bound_vars_of_term_node t in

    (* Ensure list of bound variables is sorted *)
    let _ = 
      List.fold_left
        (fun p i -> assert (i >= p); i)
        0 
        bound_vars
    in

    (* Return properties of term *)
    { bound_vars } 
   

  (* Unsafe constructor for a term *)
  let ht_term t = Ht.hashcons ht t (prop_of_term_node t)
 
  (* Unsafe constructor for free variable *)
  let ht_free_var v = 
    let n = FreeVar v in 
    Ht.hashcons ht n (prop_of_term_node n)

  (* Unsafe constructor for bound variable *)
  let ht_bound_var i = 
    let n = BoundVar i in
    Ht.hashcons ht n (prop_of_term_node n)

  (* Unsafe constructor for leaf *)
  let ht_leaf s = 
    let n = Leaf s in
    Ht.hashcons ht n (prop_of_term_node n)

  (* Unsafe constructor for node *)
  let ht_node s l = 
    let n = Node (s, l) in
    Ht.hashcons ht n (prop_of_term_node n)

  (* Unsafe constructor for let binding *)
  let ht_let l b = 
    let n = Let (l, b) in
    Ht.hashcons ht n (prop_of_term_node n)

  (* Unsafe constructor for existential quantifier *)
  let ht_exists l = 
    let n = Exists l in
    Ht.hashcons ht n (prop_of_term_node n)

  (* Unsafe constructor for universal quantifier *)
  let ht_forall l = 
    let n = Forall l in
    Ht.hashcons ht n (prop_of_term_node n)

  (* Unsafe constructor for an annotated term *)
  let ht_annot t a = 
    let n = Annot (t, a) in
    Ht.hashcons ht n (prop_of_term_node n)


  (* Convert the flattened representation back into a higher-oder
      abstract syntax term

     Use unsafe constructors here, because this function is used by
     fold. *)
  let construct = function 
    | Var v -> ht_free_var v
    | Const c -> ht_leaf c
    | App (s, l) -> ht_node s l
    (* | Attr (t, a) -> ht_annot t a *)

  (* ********************************************************************* *)
  (* Pretty-printing                                                       *)
  (* ********************************************************************* *)

  (* Print pairs of fresh variable names and types, starting with the
     given de Bruijn index *)
  let rec pp_print_var_seq db ppf = function 

    (* Terminate at end of list *)
    | [] -> ()

    | t :: tl -> 

      (* Increment de Bruijn index *)
      let db' = succ db in 

      (* Print variable for de Bruijn index and its type *)
      Format.fprintf ppf "@[<hv 1>(X%i@ %a)@]" db' T.pp_print_sort t;

      (* Continue if not at the end of the list *)
      if not (tl = []) then 
        (Format.pp_print_space ppf (); 
         pp_print_var_seq db' ppf tl)


  (* Pretty-print a list of typed variables *)
  let rec pp_print_typed_var_list pp_sort db ppf = function 

    (* Print nothing for the empty list *)
    | [] -> ()

    (* Print the first typed variable *)
    | s :: tl -> 

      (* Increment variable index *)
      let db' = succ db in

      (* Print variable as (Xn t) *)
      Format.fprintf ppf "@[<hv 1>(X%i@ %a)@]" db' pp_sort s;

      (* Add space and recurse if more bindings follow *)
      if not (tl = []) then 
        (Format.pp_print_space ppf (); 
         pp_print_typed_var_list pp_sort db' ppf tl)


  (* Pretty-print a lambda abstraction given the de Bruijn index of
     the most recent bound variable *)
  let rec pp_print_lambda' pp_symbol pp_var pp_sort db ppf = function 

    | { H.node = L (l, t) } ->

      (* Print variables bound in abstraction and recurse with an
         incremented de Bruijn index *)
      Format.fprintf ppf
        "@[<hv 1>(lambda@ (%a)@ (%a))@]"
        (pp_print_var_seq db) l
        (pp_print_term' pp_symbol pp_var pp_sort (db + (List.length l))) t


  (* Pretty-print a list of variable term bindings *)
  and pp_print_let_bindings pp_symbol pp_var pp_sort i db ppf = function 

    (* Print nothing for the empty list *)
    | [] -> ()

    (* Print the first binding *)
    | t :: tl -> 

      (* Increment variable index *)
      let db' = succ db in

      (* Print as binding as (Xn t) *)
      Format.fprintf 
        ppf 
        "@[<hv 1>(X%i@ %a)@]" 
        db' 
        (pp_print_term' pp_symbol pp_var pp_sort (db - i)) t;

      (* Add space and recurse if more bindings follow *)
      if not (tl = []) then 
        (Format.pp_print_space ppf (); 
         pp_print_let_bindings pp_symbol pp_var pp_sort (succ i) db' ppf tl)


  (* Pretty-print a higer-order abstract syntax term given the de
     Bruijn index of the most recent bound variable *)
  and pp_print_term' pp_symbol pp_var pp_sort db ppf = function 

    (* Delegate printing of free variables to function in input module *)
    | { H.node = FreeVar v } -> pp_var ppf v

    (* Print bound variable with its de Bruijn index *)
    | { H.node = BoundVar dbv } -> Format.fprintf ppf "X%i" (db - dbv + 1)

    (* Delegate printing of leaf to function in input module *)
    | { H.node = Leaf s } -> pp_symbol ?arity:(Some 0) ppf s

    (* Print a function application as S-expression *)
    | { H.node = Node (s, a) } -> 
        
      (Format.fprintf ppf 
        "@[<hv 1>(%a@ %a)@]" 
        (pp_symbol ?arity:(Some (List.length a))) s 
        (pp_print_term_list pp_symbol pp_var pp_sort db) a)

    (* Print a let binding *)
    | { H.node = Let ({ H.node = L (_, t) }, b) } -> 

      Format.fprintf ppf 
        "@[<hv 1>(let@ @[<hv 1>(%a)@]@ %a)@]" 
        (pp_print_let_bindings pp_symbol pp_var pp_sort 0 db) b
        (pp_print_term' pp_symbol pp_var pp_sort (db + List.length b)) t

    (* Print an existential quantification *)
    | { H.node = Exists { H.node = L (x, t) } } -> 

      Format.fprintf ppf 
        "@[<hv 1>(exists@ @[<hv 1>(%a)@ %a@])@]" 
        (pp_print_typed_var_list pp_sort db) x
        (pp_print_term' pp_symbol pp_var pp_sort (db + List.length x)) t

    (* Print a universal quantification *)
    | { H.node = Forall { H.node = L (x, t) } } -> 

      Format.fprintf ppf 
        "@[<hv 1>(forall@ @[<hv 1>(%a)@ %a@])@]" 
        (pp_print_typed_var_list pp_sort db) x
        (pp_print_term' pp_symbol pp_var pp_sort (db + List.length x)) t

    (* Print an annotated term *)
    | { H.node = Annot (t, a) } ->

      Format.fprintf ppf 
        "@[<hv 1>(!@ @[<hv 1>%a@] @[<hv 1>%a@])@]" 
        (pp_print_term' pp_symbol pp_var pp_sort db) t
        T.pp_print_attr a


  (* Pretty-print a list of higher-order abstract syntax terms given
     the de Bruijn index of the most recent bound variable *)
  and pp_print_term_list pp_symbol pp_var pp_sort db ppf = function

    (* Terminate at end of list *)
    | [] -> ()

    | t :: tl -> 

      (* Print term a head of list *)
      pp_print_term' pp_symbol pp_var pp_sort db ppf t;

      (* Continue if not at the end of the list *)
      if not (tl = []) then
        (Format.pp_print_space ppf ();
         pp_print_term_list pp_symbol pp_var pp_sort db ppf tl)


  (* Top-level pretty-printing function, start with given de Bruijn
     index or default to zero *)
  let pp_print_term_w pp_symbol pp_var pp_sort ?(db = 0) ppf term = 

    (* Pretty-print term into buffer *)
    pp_print_term' pp_symbol pp_var pp_sort db ppf term

 
  (* Top-level pretty-printing function, start with given de Bruijn
     index or default to zero *)
  let pp_print_lambda_w pp_symbol pp_var pp_sort ?(db = 0) ppf term = 

    (* Pretty-print term into buffer *)
    pp_print_lambda' pp_symbol pp_var pp_sort db ppf term

 
  
  let pp_print_term =
    pp_print_term_w (fun ?arity -> T.pp_print_symbol) T.pp_print_var T.pp_print_sort

  let print_term ?db = pp_print_term ?db Format.std_formatter

  let pp_print_lambda =
    pp_print_lambda_w (fun ?arity -> T.pp_print_symbol) T.pp_print_var T.pp_print_sort

  let print_lambda ?db = pp_print_lambda ?db Format.std_formatter

  (*
  (* Pretty-print a flattened term *)
  let pp_print_flat pp_symbol pp_var pp_sort ppf = function 

    | Var v -> Format.fprintf ppf "Var@ %a" pp_var v

    | Const s -> Format.fprintf ppf "Const@ %a" (pp_symbol ?arity:(Some 0)) s

    | App (s, l) -> 

      Format.fprintf 
        ppf 
        "App@ (%a,@ %a)" 
        (pp_symbol ?arity:None) s 
        (pp_print_term_list pp_symbol pp_var pp_sort 0) l

    (* | Attr (t, a) -> 

      Format.fprintf 
        ppf 
        "Attr@ (%a,@ %a)" 
        (pp_print_term ~db:0) t 
        T.pp_print_attr a *)
  *)

  (*
  let pp_print_flat =
    pp_print_flat (fun ?arity -> T.pp_print_symbol) T.pp_print_var
  *)

  (* ********************************************************************* *)
  (* Auxiliary functions                                                   *)
  (* ********************************************************************* *)

  (* [int_seq' l s n] adds a sequence of [n] integers ending with [s]
     to the list [l] *)
  let rec int_seq' a s = function 
    | 0 -> a
    | i -> int_seq' (s :: a)  (pred s) (pred i)

  (* [int_seq s n] returns a sequence of [n] integers starting with
     [s] *)
  let int_seq s n = int_seq' [] (pred (s + n)) n

  (* ********************************************************************* *)
  (* Folding function                                                      *)
  (* ********************************************************************* *)


  (* Elements on the instruction stack *)
  type mapstack =
    | MTree of t
    | MNode of symbol
    | MLet of sort list
    | MExists of sort list
    | MForall of sort list
    | MAnnot of attr

  (* Tail-recursive bottom-up right-to-left map on the term

     Not every subterm is a proper term, since the de Bruijn indexes are
     shifted. Therefore, the function [f] is called with the number of
     let bindings the subterm is under as first argument, so that the
     indexes can be adjusted in the subterm if necessary. 

     We keep a stack and an accumulator when traversing the term: 

     - The stack contains one of five values. A [MTtree t] value maps
     the subterms of [t] and pushes the result onto the accumulator. An
     [MNode s] value takes the list of values of its subterms from the
     result stack and evaluates these for the top symbol [s]. An [MLet
     x] value takes one value from the accumulator and binds it with the
     variables [x] to the next values from the accumulator. Similarly,
     for [MExists x] and [MForall x], one value is taken from the
     accumulator and the variables [x] in the term are quantified.

     - The accumulator is a list of lists of values for the subterms of
     a term. When recursing into the subterms an empty value is added
     and when moving back up, a list of values is popped from the result
     stack. If the instruction stack is empty, the result stack contains
     a singleton list with the final result.

     We could prune assignments to variables that are not occurring as
     subterms, but that would maybe be unexpected. This would be an \eta
     conversion, which is not necessary. *)
  let map f term = 

    (* Add the subterms in reverse order to the instruction stack *)
    let rec push db trees st = match trees with
      | [] -> st
      | h :: t -> push db t ((db, MTree h) :: st)
    in

    (* Recursive map *)
    let rec map f accum = function 

      (* The stack is empty, we are done. The accumulator contains
         exactly one element, which is a singleton list of the result *)
      | [] -> (match accum with [[n]] -> n | _ -> assert false)

      (* Free variable, bound variable or constant *)
      | (db, MTree ({ H.node = FreeVar _ } as n)) :: s
      | (db, MTree ({ H.node = BoundVar _ } as n)) :: s
      | (db, MTree ({ H.node = Leaf _ } as n)) :: s -> 

        (* Apply the function immediately and push result to the
           accumulator *)
        (match accum with 
          | h :: tl -> map f ((f db n :: h) :: tl) s
          | _ -> assert false)

      (* Function application *)
      | (db, MTree { H.node = Node (o, a)}) :: s -> 

        (* Push symbol and subterms in reverse order to the stack *)
        map f ([] :: accum) (push db a ((db, MNode o) :: s))

      (* Annotated term *)
      | (db, MTree { H.node = Annot (t, a)}) :: s -> 

        (* Push annotation and terms to the stack *)
        map f ([] :: accum) ((db, MTree t) :: (db, MAnnot a) :: s)

      (* Let binding *)
      | (db, MTree { H.node = Let ({ H.node = L (x, t)}, b) }) :: s -> 

        (* Push bound subterm with incremented index to the stack,
           followed by the assigned terms and a marker for the let
           binding *)
        map 
          f 
          ([] :: accum) 
          (push db b ((db + (List.length x), MTree t) :: (db, MLet x) :: s)) 

      (* Existential quantifier *)
      | (db, MTree ({ H.node = Exists { H.node = L (x, t) } })) :: s -> 

        (* Push quantified term to the stack followed by a marker for
           the quantifier *)
        map 
          f 
          ([] :: accum) 
          ((db + (List.length x), MTree t) :: (db, MExists x) :: s)

      (* Universal quantifier *)
      | (db, MTree ({ H.node = Forall { H.node = L (x, t) } })) :: s -> 

        (* Push quantified term to the stack followed by a marker for
           the quantifier *)
        map 
          f 
          ([] :: accum) 
          ((db + (List.length x), MTree t) :: (db, MForall x) :: s)

      (* Function application *)
      | (db, MNode op) :: s -> 

        (* Rebuild function application with mapped subterms *)
        (match accum with 
          | h :: h' :: d -> map f ((f db (ht_node op h) :: h') :: d) s
          | _ -> assert false)

      (* Annotation *)
      | (db, MAnnot a) :: s -> 

        (* Rebuild annotated term with mapped terms *)
        (match accum with 
          | [h] :: h' :: d -> map f ((f db (ht_annot h a) :: h') :: d) s
          | _ -> assert false)

      (* Let binding *)
      | (db, MLet x) :: s -> 

        (* Rebuild let binding with mapped subterms *)
        (match accum with 

          | (t :: b) :: h' :: d -> 
            map f ((f db (ht_let (hl_lambda x t) b) :: h') :: d) s

          | _ -> assert false)

      | (db, MExists x) :: s -> 

        (* Rebuild existential quantification with mapped subterm *)
        (match accum with 

          | [t] :: h' :: d -> 
            map f ((f db (ht_exists (hl_lambda x t)) :: h') :: d) s

          | _ -> assert false)

      | (db, MForall x) :: s -> 

        (* Rebuild universal quantification with mapped subterm *)
        (match accum with 

          | [t] :: h' :: d -> 
            map f ((f db (ht_forall (hl_lambda x t)) :: h') :: d) s

          | _ -> assert false)

    in

    (* Call recursive function with initial parameters *)
    map f [[]] [(0, MTree term)]


  (* ********************************************************************* *)
  (* Folding function                                                      *)
  (* ********************************************************************* *)

  (* Variable assignments *)
  type 'a s_or_e = 

    (* Not yet evaluated *)
    | S of int * t 

    (* Cached evaluation *)
    | E of 'a

    (* Skip evaluation *)
    | Skip

  (* ********************************************************************* *)
  (* Folding function keeping the term                                     *)
  (* ********************************************************************* *)


  (* We need a separate type to store the term when moving bottom-up *)
  type 'a fold_tstack = 

    (* Recurse into tree *)
    | FTree of int * t 

    (* Combine evaluated arguments from the result stack *)
    | FNode of 'a * t list

    (* Pop [n] substitutions from the context *)
    | FPop of int 

    (* Add top of the result stack as substitution for variable [n] to
       the context *)
    | FCtx of int


(* Folding function for bottom-up right-to-left evaluation of a term;
   substitutions for variables are evaluated lazily and evaluated
   only once

   We keep three stacks when traversing the term: 

   - The context stack is an association list of variables to either
   terms or cached values. Elements on the context stack are in
   reverse order of the de Bruijn indices. 

   - The instruction stack contains one of four values. An [FTree t]
   value evaluates the subterms of [t] and pushes the result onto the
   result stack. An [FNode s] value takes the list of values of its
   subterms from the result stack and evaluates these for the top
   symbol [s]. An [FCtx i] value takes the top element of the result
   stack, which is the value of the variable [i] and replaces the
   assignment to variable [i] on the context stack with the value. An
   [FPop n] value marks the end of scope of [n] variables, the top [n]
   elements of the context stack are removed.

   - The result stack is a list of lists of values for the subterms of
   a term. When recursing into the subterms an empty value is added
   and when moving back up, a list of values is popped from the result
   stack. When a variable needs to be evaluated, its value is computed
   and taken from the stack. If the instruction stack is empty, the
   result stack contains a singleton list with the final result.

   TODO: implement fold over quantified terms

*)

  (* Variant of the folding function above, where the term that is we
     are looking at is given as an argument to the function *)
  let rec fold fail_quant f subst accum = function 

    (* The stack is empty, we are done *)
    | [] -> 

      (

        (* When we are done the accumulator contains exactly one
           element, which is a singleton list of the result *)
        match accum with 
          | [[(_, res)]] -> res
          | _ -> assert false

      )

    (* The top element of the stack is a constant *)
    | FTree (_, { H.node = Leaf op }) :: tl -> 

      let t = Const op in

      (* Apply function to constant and continue with result *)
      (match accum with 
        | h :: d -> fold fail_quant f subst (((t, f t []) :: h) :: d) tl
        | _ -> assert false)

    (* The top element of the stack is a free variable *)
    | FTree (_, { H.node = FreeVar v }) :: tl -> 

      let t = Var v in 

      (* Apply function to variable and continue with result *)
      (match accum with 
        | h :: d -> fold fail_quant f subst (((t, f t []) :: h) :: d) tl
        | _ -> assert false)

    (* The top element of the stack is a non-nullary function *)
    | FTree (db, { H.node = Node (op, args) }) :: tl -> 

      (* Push the argument terms as FTree on the instruction stack in
         reverse order *)
      let rec push trees st = match trees with
        | [] -> st
        | h :: t -> push t ((FTree (db, h)) :: st)
      in

      (* Add an empty list to the result stack, and the subterms to
         the instruction stack followed by the symbol *)
      fold fail_quant f subst ([] :: accum) (push args (FNode (op, args) :: tl))

    (* The top element of the stack is an annotated term *)
    | FTree (db, { H.node = Annot (t, _) }) :: tl -> 

      (* Remove annotation and continue with unannotated term *)
      fold fail_quant f subst accum ((FTree (db, t)) :: tl)

    (* The top element of the stack is a bound variable *)
    | FTree (dbm, { H.node = BoundVar db }) :: tl -> 

      ( 

        match 

          (* try  *)

            (* Get the assignment to the variable in the context stack *)
            List.assoc (dbm - db + 1) subst 

          (* Every variable must be bound *)
          (* with Not_found -> assert false *)

        with 

          (* Assignment to variable has not been evaluated *)
          | S (dbl, t) -> 

            (* Evaluate term assigned to variable as top term, add
               value to the context stack and evaluate variable
               again *)
            fold
              fail_quant
              f 
              subst 
              ([] :: accum) 
              (FTree (dbl, t) :: 
               FCtx  (dbm - db + 1) :: 
               FTree (dbm, (ht_bound_var db)) :: 
               tl)

          (* Assignment to variable has been evaluated before *)
          | E l -> 

            (

              match accum with 

                (* The result stack contains at least two elements, a
                   variable at the top would be free *)
                | es :: d -> 

                  (* Add evaluation of the variable and add it to the
                     result stack *)
                  fold fail_quant f subst ((l :: es) :: d) tl

                | _ -> assert false

            )

          | Skip -> fold fail_quant f subst accum tl
            
          | exception Not_found -> assert false
                                     

      )

    (* The top element of the stack is a let binding *)
    | FTree (db, { H.node = Let ({ H.node = L (n, l) }, t) }) :: tl -> 

      (* Substitutions to append to the context *)
      let s = 

        try 

          (* Evaluate term substituted for variable lazily *)
          List.map2 
            (fun dbi a -> (dbi, (S (db, a)))) 
            (int_seq (db + 1) (List.length n))
            t

        (* List are of equal length in a well-formed term *)
        with Invalid_argument _ -> assert false

      in

      (* Add substitutions to the context stack *)
      (* let subst' = List.rev_append s subst in *)
      let subst' = s @ subst in

      (* Add term under lambda to instruction stack, followed by a pop
         instruction for the number of scopes added by the binding *)
      fold
        fail_quant
        f
        subst'
        accum
        (FTree (db + (List.length n), l) :: FPop (List.length n) :: tl)

    (* The top element of the stack is a quantifier *)
    | FTree (db, { H.node = (Forall { H.node = L (n, l) } |
                             Exists { H.node = L (n, l) })
                 }) :: tl ->

      if fail_quant then raise (Invalid_argument "Ltree.fold : quantified term");
      
      let vs = int_seq (db + 1) (List.length n) in

      let s = List.map (fun dbi -> (dbi, Skip)) vs in
      
      (* Add to the context stack *)
      let subst' = s @ subst in

      (* Add term under lambda to instruction stack, followed by a pop
         instruction for the number of scopes added by the binding *)
      fold
        fail_quant 
        f
        subst'
        accum
        (FTree (db + (List.length n), l) :: FPop (List.length n) :: tl)

    (* The top element of the instruction stack is a symbol *)
    | FNode (op, args) :: tl -> 

      (

        match accum with 

          (* The result stack contains at least two elements *)
          | es :: es' :: d -> 

            let s, r = List.split es in

            let t = App (op, List.map construct s) in

            (* Evaluate the top element on the result stack with the
               symbol and add it to the result stack *)
            fold fail_quant f subst (((t, f t r) :: es') :: d) tl

          | _ -> assert false

      )

    (* The top element of the stack is an empty end-of-scope marker *)
    | FPop 0 :: tl -> 

      (* Remove marker from the instruction stack *)
      fold fail_quant f subst accum tl

    (* The top element of the stack is a positive end-of-scope marker *)
    | FPop i :: tl when i > 0 -> 

      (

        match subst with 

          (* Pop one scope from the context stack *)
          | _ :: subst' -> fold fail_quant f subst' accum (FPop (pred i) :: tl)
          | [] -> assert false 

      )

    (* The top element of the stack is a negative end-of-scope marker *)
    | FPop _ :: _ -> assert false

    (* The top of the stack is an evaluation of the context *)
    | FCtx i :: itl -> 

      (

        match accum with 

          | [t] :: atl -> 

            let rec aux accum = function 
              | [] -> List.rev accum 
              | (v, _) :: tl when v = i -> List.rev_append ((v, E t) :: accum) tl 
              | h :: tl -> aux (h :: accum) tl
            in
(*
            (* Modify context to store evaluation for variable *)
            let subst' = 
              List.map 
                (function 
                  | (v, _) when v = i -> (v, E t)
                  | e -> e)
                subst
            in
*)
            (* Modify context to store evaluation for variable *)
            let subst' = aux [] subst in 

            (* Continue with modified context *)
            fold fail_quant f subst' atl itl

          (* nothing to evaluate context, skip *)
          | [] :: atl -> fold fail_quant f subst atl itl

          (* Result stack is never empty and has a singleton list as
             first element *)
              
          | x :: _ -> Format.eprintf "%d@." (List.length x); assert false
          | [] -> assert false

      )

  (* Evaluate the term bottom-up and right-to-left. The evaluation
     function is called at each node of the term with the symbol and the
     list of values computed for the subterms. Let bindings are lazily
     unfolded.
  *)
  let eval_t ?(fail_on_quantifiers=true)f t = 
    fold fail_on_quantifiers f [] [[]] [FTree (0, t)]


  let rec import_lambda = function { H.node = L (i, t) } -> 

    let i' = List.map T.import_sort i in
    
    let t' = import t in

    hl_lambda i' t'
    

  (* Import a term into the hashcons table by rebuilding it bottom
      up *)
  and import term = 

    map
      (function _ -> 
        function { H.node = n } -> 
          let n' = 
            match n with 
              | FreeVar v -> FreeVar (T.import_var v)
              | BoundVar i -> n
              | Leaf s -> Leaf (T.import_symbol s)
              | Node (s, l) -> Node (T.import_symbol s, l)
              | Let (l, b) -> Let (import_lambda l, b)
              | Exists l -> Exists (import_lambda l)
              | Forall l -> Forall (import_lambda l)
              | Annot (t, a) -> Annot (import t, a)
          in
          Ht.hashcons ht n' (prop_of_term_node n'))
      term

  (*
  (* Bind free variables in a term and adjust de Bruijn indices *)
  let rec bump_and_bind b k = function 

    (* Free variable *)
    | { H.node = FreeVar v } -> 

      (

        try 

          (* Bind variable and set de Bruijn index if in list *)
          ht_bound_var (List.assoc v b)

        with Not_found -> 

          (* Variable remains free *)
          ht_free_var v

      )

    (* Variable with an index lower than the bound to be bumped *)
    (* | BoundVar db when db < k -> BoundVar db *)

    (* Variable with an index to be bumped *)
    | { H.node = BoundVar db } -> ht_bound_var (db + List.length b)

    (* Let binding *)
    | { H.node = Let ({ H.node = L (n, s) }, t) } -> 

      ht_let 
        (hl_lambda n (bump_and_bind b (k + (List.length n)) s))
        (List.map (bump_and_bind b k) t)

    (* Existential quantifier *)
    | { H.node = Exists { H.node = L (n, s) } } -> 

      ht_exists (hl_lambda n (bump_and_bind b (k + (List.length n)) s))

    (* Universal quantifier *)
    | { H.node = Forall { H.node = L (n, s) } } -> 

      ht_forall (hl_lambda n (bump_and_bind b (k + (List.length n)) s))

    (* Constant *)
    | { H.node = Leaf t } -> ht_leaf t

    (* Function application *)
    | { H.node = Node (s, a) } -> ht_node s (List.map (bump_and_bind b k) a)

    (* Annotated term *)
    | { H.node = Annot (t, a) } -> ht_annot (bump_and_bind b k t) a
  *)
  
  (* Bind a free variable in the term given an association list of
     variables to be bound and their position in a simultaneous
     binding

     We use the map on the term, which gives the number of lambdas the
     sub-term is under in its first argument. To bind a free variable
     we look up its relative position in the simultaneous binding, and
     increment it. *)
  let bind dbm term = 

    map

      (function db -> function 

         (* Free variable may need to be bound *)
         | { H.node = FreeVar v } as t ->

           (try 

              (* Get relative index of variable to be bound *)
              let dbt = List.assq v dbm in

              (* Replace free variable with bound variable *)
              ht_bound_var (succ db + dbt)
                
            (* Variable does not need to be bound *)
            with Not_found -> t)

         (* Only free variables can be bound *)
         | t -> t)

      term


  (* ********************************************************************* *)
  (* Constructors                                                          *)
  (* ********************************************************************* *)

  (* Constructor for a lambda expression *)
  let mk_lambda x t =

    (* Associate each variable with its relative index in the
       binding *)
    let dbm = List.mapi (fun i v -> (v, i)) (List.rev x) in

    (* Bind free variables in term in a new lambda *)
    hl_lambda
      (List.map T.sort_of_var x) 
      (bind dbm t)


  (* Beta-evaluate a lambda expression *)
  let eval_lambda ({ Hashcons.node = L (v, t) } as l) b = 

    if List.length v = List.length b then ht_let l b else 
      
      raise (Invalid_argument "eval_lambda")


      
        
  



  (* Constructor for a term *)
  let mk_term t = ht_term t

  (* Constructor for a free variable *)
  let mk_var v = ht_free_var v

  (* Constructor for a constant *)
  let mk_const s = ht_leaf s

  (* Constructor for a function application *)
  let mk_app s a = 
    match a with
      | [] -> assert false
      | _ -> ht_node s a

  (* Constructor for a let binding: 
     [let x_1 : s_1 = t_1; ...; x_n : s_n = t_n in s] *)
  let mk_let b t = 

    (* Split list of bindings into list of variables and list of the
       terms they are to be bound to *)
    let x, b = List.split b in

    (* Return let binding *)
    ht_let (mk_lambda x t) b

  (* Create a let binding of terms to variables, eliminate bindings to
     variables that do not occur in the term *)
  let trim_let_domain 
      offset
      bvar_types 
      bvar_terms
      ({ H.prop = { bound_vars } } as term) =

    (* Map of bound variable index to bound variable index without
       eliminated variables 

       Simply map the n-th variable in the ordered list of bound
       variables to n *)
    let _, bound_var_map = 
      List.fold_left
        (fun (c, a) i -> 
           if i > List.length bvar_terms then
             (c, a) 
           else
             (succ c, (i, c) :: a))
        (1, [])
        bound_vars
    in

    Debug.ltree
      "@[<hv>trim_let_domain:@ %a@ \
             terms@ @[<hv>%a@]@ \
             bound vars@ @[<hv>%a@]@ \
             map@ @[<hv>%a@]@]"
      (pp_print_term ~db:0) term
      (pp_print_list pp_print_term ",@ ") bvar_terms
      (pp_print_list Format.pp_print_int ",@ ") bound_vars
      (pp_print_list 
         (fun ppf (i, j) -> Format.fprintf ppf "%d:%d" i j)
         ",@ ") 
      bound_var_map;

      (* Return the elements with indexes from the list

       The list of indexes must be sorted, the first element in the
       list has index 1 *)
    let list_extract_indexes indexes list = 

      let rec aux' count accum = function 

        (* Return when all indexes extracted *)
        | [] -> (function _ -> List.rev accum)

        (* Take the first index to extract *)
        | i :: itl as indexes -> (function

            (* Return when list is empty *)
            | [] -> List.rev accum

            (* Index of first element is less than the next index to
               extract *)
            | _ :: ltl when count < i -> 

              (* Drop element, and increment counter *)
              aux' (succ count) accum indexes ltl

            (* Index of first element is next in list of indexes *)
            | h :: ltl -> 

              (* List of indexes is sorted etc. *)
              assert (count = i); 

              (* Add element to accumulator, drop index, increment
                 counter and continue *)
              aux' (succ count) (h :: accum) itl ltl)

      in

      (* Start at first index with empty accumulator *)
      aux' 1 [] indexes list 

    in

    (* Adjust indexes of all variables according to the map *)
    let term_adjust_bound_indexes bound_var_map term =

      map

        (fun o -> function

           (* May need to change the index of a bound variable *)
           | { H.node = BoundVar i } as t -> 

             (try 

                (* Bound variable is bound outside this let binding? *)
                if i > o + List.length bvar_terms then

                  (* Adjust index with number of eliminated
                     variables *)
                  ht_bound_var
                    (i - 
                     (List.length bvar_terms - 
                      List.length bound_var_map))

                (* Bound variable is bound in this let binding? *)
                else if i > o then 

                  (* Replace with new index after eliminating
                     variables *)
                  ht_bound_var
                    ((List.assoc (i - o) bound_var_map) + o)

                (* Keep variables bound inside the term *)
                else t

              (* Every variable in the term the is bound outside has a
                 new index *)
              with Not_found -> 
                Debug.ltree
                  "No mapping for BoundVar %d at offset %d" i o ;
                assert false)

           (* Keep terms other than bound variables unchanged *)
           | t -> t)

        term

    in

    (* Adjust indexes in term to be bound *)
    let term' = term_adjust_bound_indexes bound_var_map term in

    (* Eliminate variables not bound in the term *)
    let bvar_terms' = 
      List.rev
        (list_extract_indexes 
           bound_vars 
           (List.rev bvar_terms))
    in 

    (* Eliminate types of variables not bound in the term *)
    let bvar_types' = 
      List.rev
        (list_extract_indexes 
           bound_vars
           (List.rev bvar_types))
    in 

    (* Is the list of variables to bind empty? *)
    match bvar_terms' with 

      (* Return term unchanged *)
      | [] -> term'

      (* Add non-empty let binding to term *)
      | _ -> 

        (* Create let binding with variables eliminated *)
        ht_let
          (hl_lambda bvar_types' term')
          bvar_terms'


  (* Testing only, this is inefficient *)
  let mk_let_elim b t =

    match mk_let b t with 
      
      | { H.node = Let ({ H.node = L (s, t)}, b) } -> 

        (* Return let binding *)
        trim_let_domain 0 s b t

      | _ -> assert false


  (* Constructor for an existential quantification: 
     [exists x_1 : s_1; ...; x_n : s_n = t_n in s] *)
  let mk_exists x t = ht_exists (mk_lambda x t)

  (* Constructor for a universal quantification: 
     [forall x_1 : s_1; ...; x_n : s_n = t_n in s] *)
  let mk_forall x t = ht_forall (mk_lambda x t)

  (* Constructor for annotated term *)
  let mk_annot t a = ht_annot t a 

  (* Return the node of a hashconsed term *)
  let node_of_t { Hashcons.node = n } = n

  (* Return the sorts of a hashconsed lambda abstraction *)
  let sorts_of_lambda { Hashcons.node = L (v, _) } = v

  (* Return the node of a hashconsed lamda abstraction *)
  let node_of_lambda { Hashcons.node = l } = l

  (* Return the tag of a hashconsed term *)
  let tag_of_t { Hashcons.tag = n } = n


  (* ********************************************************************* *)
  (* Accessing the top node of the term                                    *)
  (* ********************************************************************* *)

  (* Return the top symbol of a term along with its subterms

     If the top symbol of a term is a let binding, the binding is
     distributed over the subterms. 

     destruct' always returns a term with BoundVar, Leaf, FreeVar, 
     Node or Annot at the top *)
  let rec destruct' ofs = function

    (* Bound variable must not occur free at top level, but may occur
       when recursively evaluating a chain of let bindings *)
    | { H.node = BoundVar i } as t -> t

    (* Constant *)
    | { H.node = Leaf s }
    | { H.node = Let ({ H.node = L (_, { H.node = Leaf s }) }, _) } -> 

      ht_leaf s

    (* Free variable *)
    | { H.node = FreeVar v }
    | { H.node = Let ({ H.node = L (_, { H.node = FreeVar v }) }, _) } -> 

      ht_free_var v

    (* Function application *)
    | { H.node = Node (_, _) } as t -> t

    (* Let binding of a function application *)
    | { H.node = Let ({ H.node = L (i, { H.node = Node (s, l) }) }, b) } -> 

      (* Distribute let binding over arguments of function application *)
      ht_node 
        s
        (List.map
           (function r -> trim_let_domain ofs i b r)
           l)

    (* Let binding of a let binding *)
    | { H.node = Let ({ H.node = L (i, ({ H.node = Let _ } as t)) }, b) } ->

      (* Destruct inner let binding to get a not let bound term at
         the top, then destruct this term *)
      destruct' 
        ofs 
        (ht_let (hl_lambda i (destruct' (ofs + (List.length i)) t)) b)
        (* (trim_let_domain ofs i b (destruct' (ofs + (List.length i)) t)) *)

    (* Let binding of a bound variable that is bound outside the let
       binding *)
    | { H.node = Let ({ H.node = L (_, { H.node = BoundVar i }) }, l) } 
      when i > List.length l -> 

      (* Remove let binding, and adjust index of bound variable *)
      ht_bound_var (i - List.length l)

    (* Let binding of a bound variable that is bound to the let binding *)
    | { H.node = Let ({ H.node = L (_, { H.node = BoundVar i }) }, l) } -> 

      (* Return assignment to bound variable *)
      destruct' ofs (List.nth l (List.length l - i))

    (* Let binding of an annotated term *)
    | { H.node = Let ({ H.node = L (i, { H.node = Annot (t, a) }) }, b) } -> 

      (* Move let binding over annotation to term *)
      ht_annot 
        (ht_let (hl_lambda i t) b)
        a

    (* Quantified term *)
    | { H.node = Exists _ }
    | { H.node = Forall _ }
    | { H.node = Let ({ H.node = L (_, { H.node = Exists _ }) }, _ ) }
    | { H.node = Let ({ H.node = L (_, { H.node = Forall _ }) }, _ ) } -> 

      invalid_arg "destruct: quantified term"

    (* Annotated term  *)
    | { H.node = Annot (_, _) } as t -> t

  

  (* *)
  let rec destruct t = match destruct' 0 t with

    (* Constant *)
    | { H.node = Leaf s } ->
       Const s

    (* Free variable *)
    | { H.node = FreeVar v } -> Var v

    (* Function application *)
    | { H.node = Node (s, l) } -> App (s, l)

    (* Bound variable *)
    | { H.node = BoundVar _ } -> 
       invalid_arg "destruct: bound variable"

    (* Skip over annotations *)
    | { H.node = Annot (t, _) } -> destruct t

    (* No other terms returned by destrcut' *)
    | _ -> assert false


  let has_quantifier term =

    (* Add the subterms in reverse order to the instruction stack *)
    let rec push trees st = match trees with
      | [] -> st
      | h :: t -> push t ((MTree h) :: st)
    in

    
    (* Recursive has_quantifier *)
    let rec has_quantifier has n =
      has ||
      match n with

      (* The stack is empty, we are done. *)
      | [] -> has

      (* Free variable, bound variable or constant *)
      | MTree { H.node = (FreeVar _ | BoundVar _ | Leaf _) } :: s -> 
        has_quantifier has s

      (* Function application *)
      | MTree { H.node = Node (o, a)} :: s -> 
        (* Push symbol and subterms in reverse order to the stack *)
        has_quantifier has (push a ((MNode o) :: s))

      (* Annotated term *)
      | MTree { H.node = Annot (t, a)} :: s -> 
        (* Push annotation and terms to the stack *)
        has_quantifier has ((MTree t) :: (MAnnot a) :: s)

      (* Let binding *)
      | MTree { H.node = Let ({ H.node = L (x, t)}, b) } :: s -> 
        has_quantifier has (push b ((MTree t) :: (MLet x) :: s)) 

      (* Existential quantifier *)
      | MTree ({ H.node = Exists _ }) :: _
      | MTree ({ H.node = Forall _ }) :: _ -> true
        
      (* Function application *)
      | MNode _ :: s | MAnnot _ :: s | MLet _ :: s -> has_quantifier has s

      | MExists _ :: _  | MForall _ :: _ -> true
        
    in

    (* Call recursive function with initial parameters *)
    has_quantifier false [MTree term]


    
  let instantiate l b = ht_let l b
    

  (* let list_keep_same_number l1 l2 = *)
  (*   let rec aux acc = function *)
  (*     | e :: r1, _ :: r2 -> aux (e :: acc) (r1, r2) *)
  (*     | r1, [] -> List.rev acc, r1 *)
  (*     | [], _ -> assert false *)
  (*   in *)
  (*   aux [] (l1, l2) *)

  (* let missing_args l1 l2 = *)
  (*   let rec aux = function *)
  (*     | _ :: r1, _ :: r2 -> aux (r1, r2) *)
  (*     | r1, [] -> (\* List.map (fun ty -> Var.mk_fresh_var ty) *\) r1 *)
  (*     | [], _ -> assert false *)
  (*   in *)
  (*   aux (l1, l2) *)

  (* let missing_ints l1 l2 = *)
  (*   let e = List.length l1 in *)
  (*   let d = List.length l2 in *)
  (*   let rec aux acc i = *)
  (*     if i = d - 1 then List.rev acc else aux (i :: acc) (pred i) in *)
  (*   aux [] (pred e) *)
    
    
  (* (\* Beta-evaluate a lambda expression *\) *)
  (* let partial_eval_lambda ({ Hashcons.node = L (v, t) } as l) b =  *)

  (*   if List.length v <= List.length b then        *)
  (*     raise (Invalid_argument "partial_eval_lambda") *)
  (*   else *)
  (*     (\* let t = map *\) *)
  (*     (\*     (function db -> function  *\) *)
  (*     (\*        | { H.node = BoundVar i } -> ht_bound_var (if i = 1 then 2 else 1) *\) *)
  (*     (\*        | t -> t) t in *\) *)
  (*     let v_covered, v_rest = list_keep_same_number v b in *)
  (*     (\* hl_lambda v_rest (ht_let (hl_lambda v_covered t) b (\\* |> eval_t (fun t _ -> construct t) *\\)) *\) *)
  (*     (\* ; *\) *)
  (*     let missing = missing_ints v b |> List.map ht_bound_var in *)
  (*     hl_lambda v_rest (ht_let l (b @ missing) |> eval_t (fun t _ -> )) *)

let partial_eval_lambda _ _ = assert false
  

end

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

