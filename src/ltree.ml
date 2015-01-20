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

open Lib


(* Abbreviation for module name *)
module H = Hashcons


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

  and t_prop = private { mutable to_string : string option } 

  and flat = private
    | Var of var
    | Const of symbol
    | App of symbol * t list
    | Attr of t * attr

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val hash : t -> int

  val tag : t -> int

  val mk_lambda : var list -> t -> lambda

  val eval_lambda : lambda -> t list -> t

  val mk_term : t_node -> t

  val mk_var : var -> t
  
  val mk_const : symbol -> t

  val mk_app : symbol -> t list -> t

  val mk_let : (var * t) list -> t -> t

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
  val eval_t : (flat -> 'a list -> 'a) -> t -> 'a

  val map : (int -> t -> t) -> t -> t

  val destruct : t -> flat

  val instantiate : lambda -> t list -> t

  val construct : flat -> t

  val import : t -> t

  val pp_print_term : ?db:int -> Format.formatter -> t -> unit
    
  val pp_print_term_w : (?arity:int -> Format.formatter -> symbol -> unit) ->
    ?db:int -> Format.formatter -> t -> unit

  val print_term : ?db:int -> t -> unit

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
  and t_prop = { mutable to_string : string option } 

  (* Hashconsed abstract syntax term *)
  and t = (t_node, t_prop) H.hash_consed

  (* Flattened term without binders at the top symbol *)
  type flat = 
    | Var of var
    | Const of symbol
    | App of symbol * t list
    | Attr of t * attr

  (* Return property of term *)
  let hash_of_term { H.hkey = h } = h

  (* Return property of term *)
  let prop_of_term { H.prop = p } = p

  (* Set cached string representation of term *)
  let set_to_string { H.prop = p } s = p.to_string <- Some s

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

  (* Constructor for hashconsed lambda abstraction *)
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
  let compare { H.tag = t1 } { H.tag = t2 } = Pervasives.compare t1 t2

  (* Equality of terms based on tags *)
  let equal { H.tag = t1 } { H.tag = t2 } = t1 = t2

  (* Hashing based on stored hash *)
  let hash { H.hkey = h } = h

  (* Return unique identifier *)
  let tag { H.tag = i } = i

  (* Initial property of term *)
  let prop_of_term_node _ = { to_string = None }

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
  let rec pp_print_typed_var_list db ppf = function 

    (* Print nothing for the empty list *)
    | [] -> ()

    (* Print the first typed variable *)
    | s :: tl -> 

      (* Increment variable index *)
      let db' = succ db in

      (* Print variable as (Xn t) *)
      Format.fprintf ppf "@[<hv 1>(X%i@ %a)@]" db' T.pp_print_sort s;

      (* Add space and recurse if more bindings follow *)
      if not (tl = []) then 
        (Format.pp_print_space ppf (); 
         pp_print_typed_var_list db' ppf tl)


  (* Pretty-print a lambda abstraction given the de Bruijn index of
     the most recent bound variable *)
  let rec pp_print_lambda pp_symbol db ppf = function { H.node = L (l, t) } ->

    (* Print variables bound in abstraction and recurse with an
       incremented de Bruijn index *)
    Format.fprintf ppf
      "@[<hv 0>@[<hv 2>(%a).@]%a@]"
      (pp_print_var_seq db) l
      (pp_print_term' pp_symbol (db + (List.length l))) t


  (* Pretty-print a list of variable term bindings *)
  and pp_print_let_bindings pp_symbol i db ppf = function 

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
        (pp_print_term' pp_symbol (db - i)) t;

      (* Add space and recurse if more bindings follow *)
      if not (tl = []) then 
        (Format.pp_print_space ppf (); 
         pp_print_let_bindings pp_symbol (succ i) db' ppf tl)


  (* Pretty-print a higer-order abstract syntax term given the de
     Bruijn index of the most recent bound variable *)
  and pp_print_term' pp_symbol db ppf = function 

    (* Delegate printing of free variables to function in input module *)
    | { H.node = FreeVar v } -> T.pp_print_var ppf v

    (* Print bound variable with its de Bruijn index *)
    | { H.node = BoundVar db } -> Format.fprintf ppf "X%i" db

    (* Delegate printing of leaf to function in input module *)
    | { H.node = Leaf s } -> pp_symbol ?arity:(Some 0) ppf s

    (* Print a function application as S-expression *)
    | { H.node = Node (s, a) } -> 

      Format.fprintf ppf 
        "@[<hv 1>(%a@ %a)@]" 
        (pp_symbol ?arity:(Some (List.length a))) s 
        (pp_print_term_list pp_symbol db) a

    (* Print a let binding *)
    | { H.node = Let ({ H.node = L (_, t) }, b) } -> 

      Format.fprintf ppf 
        "@[<hv 1>(let@ @[<hv 1>(%a)@]@ %a)@]" 
        (pp_print_let_bindings pp_symbol 0 db) b
        (pp_print_term' pp_symbol (db + List.length b)) t

    (* Print an existential quantification *)
    | { H.node = Exists { H.node = L (x, t) } } -> 

      Format.fprintf ppf 
        "@[<hv 1>(exists@ @[<hv 1>(%a)@ %a@])@]" 
        (pp_print_typed_var_list db) x
        (pp_print_term' pp_symbol (db + List.length x)) t

    (* Print a universal quantification *)
    | { H.node = Forall { H.node = L (x, t) } } -> 

      Format.fprintf ppf 
        "@[<hv 1>(forall@ @[<hv 1>(%a)@ %a@])@]" 
        (pp_print_typed_var_list db) x
        (pp_print_term' pp_symbol (db + List.length x)) t

    (* Print an annotated term *)
    | { H.node = Annot (t, a) } ->

      Format.fprintf ppf 
        "@[<hv 1>(!@ @[<hv 1>%a@] @[<hv 1>%a@])@]" 
        (pp_print_term' pp_symbol db) t
        T.pp_print_attr a


  (* Pretty-print a list of higher-order abstract syntax terms given
     the de Bruijn index of the most recent bound variable *)
  and pp_print_term_list pp_symbol db ppf = function

    (* Terminate at end of list *)
    | [] -> ()

    | t :: tl -> 

      (* Print term a head of list *)
      pp_print_term' pp_symbol db ppf t;

      (* Continue if not at the end of the list *)
      if not (tl = []) then
        (Format.pp_print_space ppf ();
         pp_print_term_list pp_symbol db ppf tl)


  (* Top-level pretty-printing function, start with given de Bruijn
     index or default to zero *)
  let pp_print_term_w pp_symbol ?(db = 0) ppf term = 

    (* This breaks indentation and is going to fail when the meaning
       of indexes is reversed. *)
    (*
    (* String representation of term *)
    let term_string = 

      (* Get cached string *)
      match prop_of_term term with

        (* No cached string of term *)
        | { to_string = None } -> 
          
          (* Create a buffer and formatter to write into buffer *)
          let buf = Buffer.create 80 in 
          let bppf = Format.formatter_of_buffer buf in
          
          (* Pretty-print term into buffer *)
          pp_print_term' db bppf term;
          
          (* Flush formatter *)
          Format.pp_print_flush bppf ();
          
          (* Return string representation of term from buffer *)
          let term_string = Buffer.contents buf in

          (* Write string representaion to cache *)
          set_to_string term term_string;

          (* Return string representation *)
          term_string

        (* Return cached string of term *)
        | { to_string = Some s } -> s

    in
    
    (* Print string representation of term to formatter *)
    Format.fprintf ppf "%s" term_string
*)

    (* Pretty-print term into buffer *)
    pp_print_term' pp_symbol db ppf term


  
  let pp_print_term = pp_print_term_w (fun ?arity -> T.pp_print_symbol)

  let print_term ?db = pp_print_term ?db Format.std_formatter

(*

  let pp_print_term_infix' db ppf = function 

    (* Delegate printing of free variables to function in input module *)
    | { H.node = FreeVar v } -> T.pp_print_var ppf v

    (* Print bound variable with its de Bruijn index *)
    | { H.node = BoundVar db } -> Format.fprintf ppf "X%i" db

    (* Delegate printing of leaf to function in input module *)
    | { H.node = Leaf s } -> T.pp_print_symbol ppf s

    (* Print a function application as S-expression *)
    | { H.node = Node (s, a) } -> 

      Format.fprintf ppf 
        "@[<hv 1>(%a)@]" 
        T.pp_print_node s a 
        (pp_print_term_list db) a

    (* Print a let binding *)
    | { H.node = Let ({ H.node = L (_, t) }, b) } -> 

      Format.fprintf ppf 
        "@[<hv 1>(let@ @[<hv 1>(%a)@]@ %a)@]" 
        (pp_print_let_bindings db) b
        (pp_print_term' (db + List.length b)) t

    (* Print an existential quantification *)
    | { H.node = Exists { H.node = L (x, t) } } -> 

      Format.fprintf ppf 
        "@[<hv 1>(exists@ @[<hv 1>(%a)@ %a@])@]" 
        (pp_print_typed_var_list db) x
        (pp_print_term' (db + List.length x)) t

    (* Print a universal quantification *)
    | { H.node = Forall { H.node = L (x, t) } } -> 

      Format.fprintf ppf 
        "@[<hv 1>(forall@ @[<hv 1>(%a)@ %a@])@]" 
        (pp_print_typed_var_list db) x
        (pp_print_term' (db + List.length x)) t

    (* Print an annotated term *)
    | { H.node = Annot (t, a) } ->

      Format.fprintf ppf 
        "@[<hv 1>(!@ @[<hv 1>%a@] @[<hv 1>%a@])@]" 
        (pp_print_term' db) t
        T.pp_print_attr a

*)


  (* Pretty-print a flattened term *)
  let rec pp_print_flat pp_symbol ppf = function 

    | Var v -> Format.fprintf ppf "Var@ %a" T.pp_print_var v

    | Const s -> Format.fprintf ppf "Const@ %a" (pp_symbol ?arity:(Some 0)) s

    | App (s, l) -> 

      Format.fprintf 
        ppf 
        "App@ (%a,@ %a)" 
        (pp_symbol ?arity:None) s 
        (pp_print_term_list pp_symbol 0) l

    | Attr (t, a) -> 

      Format.fprintf 
        ppf 
        "Attr@ (%a,@ %a)" 
        (pp_print_term ~db:0) t 
        T.pp_print_attr a

  let pp_print_flat = pp_print_flat (fun ?arity -> T.pp_print_symbol)

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
  let rec int_seq s n = int_seq' [] (pred (s + n)) n


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


  (* ********************************************************************* *)
  (* Constructors                                                          *)
  (* ********************************************************************* *)

  (* Constructor for a lambda expression *)
  let mk_lambda x t =

    (* Association list of variable names to de Bruijn indices *)
    let x_and_db = List.mapi (fun i x -> (x, succ i)) x in

    (* Return existential quantification *)
    hl_lambda 
      (List.map T.sort_of_var x) 
      (bump_and_bind x_and_db 1 t)


  (* Beta-evaluate a lambda expression *)
  let eval_lambda l b = ht_let l b

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


  (* Convert the flattened representation back into a higher-oder
      abstract syntax term. *)
  let construct = function 
    | Var v -> mk_var v
    | Const c -> mk_const c
    | App (s, l) -> mk_app s l
    | Attr (t, a) -> mk_annot t a 

  (* Return the top symbol of a term along with its subterms

     If the top symbol of a term is a let binding, the binding is
     distributed over the subterms. 

     destruct' always returns a term with BoundVar, Leaf, FreeVar, 
     Node or Annot at the top *)
  let rec destruct' ofs = function

    (* Bound variable must not occur free *)
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
        (List.map (function r -> (ht_let (hl_lambda i r) b)) l)

    (* Let binding of a let binding *)
    | { H.node = Let ({ H.node = L (i, ({ H.node = Let _ } as t)) }, b) } ->

      destruct' 
        ofs 
        (ht_let (hl_lambda i (destruct' (ofs + (List.length i)) t)) b)

    (* Let binding of a bound variable with a higher index than the
       number of bound variables must not occur *)
    | { H.node = Let ({ H.node = L (j, { H.node = BoundVar i }) }, _) }
      when i > (List.length j) + ofs -> 

      assert false

    (* Let binding of a bound variable *)
    | { H.node = Let ({ H.node = L (_, { H.node = BoundVar i }) }, l) } 
      when i <= ofs -> 

      ht_bound_var i

    (* Let binding of a bound variable *)
    | { H.node = Let ({ H.node = L (_, { H.node = BoundVar i }) }, l) } -> 

      (* Return assignment to bound variable *)
      destruct' ofs (List.nth l (pred i - ofs))

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


  let instantiate l b = ht_let l b
    

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


  (* Elements on the instruction stack *)
  type foldstack = 

    (* Recurse into tree *)
    | FTree of int * t 

    (* Combine evaluated arguments from the result stack *)
    | FNode of symbol 

    (* Pop [n] substitutions from the context *)
    | FPop of int 

    (* Add top of the result stack as substitution for variable [n] to
       the context *)
    | FCtx of int


  (* Variable assignments *)
  type 'a s_or_e = 

    (* Not yet evaluated *)
    | S of int * t 

    (* Cached evaluation *)
    | E of 'a


  (* Folding function for bottom-up right-to-left evaluation of a
     higher-order abstract syntax term; substitutions for variables are
     evaluated lazily and evaluated only once

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
     assignment to variable [i] on the context stack with the value. A
     [FPop n] value marks the end of scope of [n] variables, the top [n]
     elements of the context stack are removed.

     - The result stack is a list of lists of values for the subterms of
     a term. When recursing into the subterms an empty value is added
     and when moving back up, a list of values is popped from the result
     stack. When a variable needs to be evaluated, its value is computed
     and taken from the stack. If the instruction stack is empty, the
     result stack contains a singleton list with the final result.

  *)
  let rec fold f subst accum = function 

    (* The stack is empty, we are done *)
    | [] -> 

      (

        (* When we are done the accumulator contains exactly one
           element, which is a singleton list of the result *)
        match accum with 
          | [[res]] -> res
          | _ -> assert false

      )

    (* The top element of the stack is a constant, a nullary function *)
    | FTree (_, { H.node = Leaf op }) :: tl -> 

      (* Add an empty list to the result stack and the symbol to the
         instruction stack *)
      fold f subst ([] :: accum) (FNode op :: tl)

    (* The top element of the stack is a non-nullary function *)
    | FTree (db, { H.node = Node (op, args) }) :: tl -> 

      (* Push the list of terms as T variants on the instruction stack
         in reverse order *)
      let rec push trees st = match trees with
        | [] -> st
        | h :: t -> push t ((FTree (db, h)) :: st)
      in

      (* Add an empty list to the result stack, and the subterms to
         the instruction stack followed by the symbol *)
      fold f subst ([] :: accum) (push args (FNode op :: tl))

    (* The top element of the stack is an annotated term *)
    | FTree (db, { H.node = Annot (t, _) }) :: tl -> 

      (* Remove annotation and continue with unannotated term *)
      fold f subst accum ((FTree (db, t)) :: tl)

    (* The top element of the stack is a bound variable *)
    | FTree (dbm, { H.node = BoundVar db }) :: tl -> 

      ( 

        match 

          try 

            (* Get the assignment to the variable in the context stack *)
            List.assoc db subst 

          (* Every variable must be bound *)
          with Not_found -> assert false

        with 

          (* Assignment to variable has not been evaluated *)
          | S (dbl, t) -> 

            (* Evaluate term assigned to variable as top term, add
               value to the context stack and evaluate variable
               again *)
            fold 
              f 
              subst 
              ([] :: accum) 
              (FTree (dbl, t) :: 
               FCtx db :: 
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
                  fold f subst ((l :: es) :: d) tl

                | _ -> assert false

            )

      )

    (* The top element of the stack is a free variable *)
    | FTree (_, { H.node = FreeVar _ }) :: tl -> 

      invalid_arg "Free variable in term"

    (* The top element of the stack is a let binding *)
    | FTree (db, { H.node = Let ({ H.node = L (n, l) }, t) }) :: tl -> 

      (* Substitutions to append to the context *)
      let s = 

        try 

          (* Evaluate term substituted for variable lazily *)
          List.map2 
            (fun dbi a -> (dbi, S (db, a))) 
            (int_seq (db + 1) (List.length n))
            t

        (* List are of equal length in a well-formed term *)
        with Invalid_argument _ -> assert false

      in

      (* Add substitutions to the context stack *)
      let subst' = s @ subst in 

      (* Add term under lambda to instruction stack, followed by a pop
         instruction for the number of scopes added by the binding *)
      fold 
        f
        subst'
        accum
        (FTree ((List.length n), l) :: FPop (List.length n) :: tl)

    (* The top element of the instruction stack is a symbol *)
    | FNode op :: tl -> 

      (

        match accum with 

          (* The result stack contains at least two elements *)
          | es :: es' :: d -> 

            (* Evaluate the top element on the result stack with the
               symbol and add it to the result stack *)
            fold f subst ((f op es :: es') :: d) tl

          | _ -> assert false

      )

    (* The top element of the stack is a quantified term *)
    | FTree (_, { H.node = Exists _ }) :: tl
    | FTree (_, { H.node = Forall _ }) :: tl -> invalid_arg "Quantified term"

    (* The top element of the stack is an empty end-of-scope marker *)
    | FPop 0 :: tl -> 

      (* Remove marker from the instruction stack *)
      fold f subst accum tl

    (* The top element of the stack is a positive end-of-scope marker *)
    | FPop i :: tl when i > 0 -> 

      (

        match subst with 

          (* Pop one scope from the context stack *)
          | _ :: subst' -> fold f subst' accum (FPop (pred i) :: tl)
          | [] -> assert false

      )

    (* The top element of the stack is a negative end-of-scope marker *)
    | FPop _ :: _ -> assert false

    (* The top of the stack is an evaluation of the context *)
    | FCtx i :: itl -> 

      (

        match accum with 

          | [t] :: atl -> 

            (* Modify context to store evaluation for variable *)
            let subst' = 
              List.map 
                (function 
                  | (v, _) when v = i -> (v, E t)
                  | e -> e)
                subst
            in

            (* Continue with modified context *)
            fold f subst' atl itl

          (* Result stack is never empty and has a singleton list as
             first element *)
          | _ :: _ 
          | [] -> assert false

      )


  (* Evaluate the term bottom-up and right-to-left. The evaluation
     function is called at each node of the term with the symbol and the
     list of values computed for the subterms. Let bindings are lazily
     unfolded.
  *)
  let eval f t = 
    fold f [] [[]] [FTree (0, t)]


  (* ********************************************************************* *)
  (* Folding function keeping the term                                     *)
  (* ********************************************************************* *)


  (* We need a separate type to store the term when moving bottom-up *)
  type 'a fold_tstack = 

    (* Recurse into tree *)
    | FITree of int * t 

    (* Combine evaluated arguments from the result stack *)
    | FINode of 'a * t list

    (* Pop [n] substitutions from the context *)
    | FIPop of int 

    (* Add top of the result stack as substitution for variable [n] to
       the context *)
    | FICtx of int


  (* Variant of the folding function above, where the term that is we
     are looking at is given as an argument to the function *)
  let rec fold_t f subst accum = function 

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
    | FITree (_, { H.node = Leaf op }) :: tl -> 

      let t = Const op in

      (match accum with 
        | h :: d -> fold_t f subst (((t, f t []) :: h) :: d) tl
        | _ -> assert false)

    (* The top element of the stack is a variable *)
    | FITree (_, { H.node = FreeVar v }) :: tl -> 

      let t = Var v in 

      (match accum with 
        | h :: d -> fold_t f subst (((t, f t []) :: h) :: d) tl
        | _ -> assert false)

    (* The top element of the stack is a non-nullary function *)
    | FITree (db, { H.node = Node (op, args) }) :: tl -> 

      (* Push the list of terms as T variants on the instruction stack
         in reverse order *)
      let rec push trees st = match trees with
        | [] -> st
        | h :: t -> push t ((FITree (db, h)) :: st)
      in

      (* Add an empty list to the result stack, and the subterms to
         the instruction stack followed by the symbol *)
      fold_t f subst ([] :: accum) (push args (FINode (op, args) :: tl))

    (* The top element of the stack is an annotated term *)
    | FITree (db, { H.node = Annot (t, _) }) :: tl -> 

      (* Remove annotation and continue with unannotated term *)
      fold_t f subst accum ((FITree (db, t)) :: tl)

    (* The top element of the stack is a bound variable *)
    | FITree (dbm, { H.node = BoundVar db }) :: tl -> 

      ( 

        match 

          try 

            (* Get the assignment to the variable in the context stack *)
            List.assoc db subst 

          (* Every variable must be bound *)
          with Not_found -> assert false

        with 

          (* Assignment to variable has not been evaluated *)
          | S (dbl, t) -> 

            (* Evaluate term assigned to variable as top term, add
               value to the context stack and evaluate variable
               again *)
            fold_t 
              f 
              subst 
              ([] :: accum) 
              (FITree (dbl, t) :: 
               FICtx db :: 
               FITree (dbm, (ht_bound_var db)) :: 
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
                  fold_t f subst ((l :: es) :: d) tl

                | _ -> assert false

            )

      )

    (* The top element of the stack is a let binding *)
    | FITree (db, { H.node = Let ({ H.node = L (n, l) }, t) }) :: tl -> 

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
      fold_t 
        f
        subst'
        accum
        (FITree (db + (List.length n), l) :: FIPop (List.length n) :: tl)

    (* The top element of the stack is a quantified term *)
    | FITree (_, { H.node = Exists _ }) :: tl
    | FITree (_, { H.node = Forall _ }) :: tl -> invalid_arg "Quantified term"

    (* The top element of the instruction stack is a symbol *)
    | FINode (op, args) :: tl -> 

      (

        match accum with 

          (* The result stack contains at least two elements *)
          | es :: es' :: d -> 

            let s, r = List.split es in

            let t = App (op, List.map construct s) in

            (* Evaluate the top element on the result stack with the
               symbol and add it to the result stack *)
            fold_t f subst (((t, f t r) :: es') :: d) tl

          | _ -> assert false

      )

    (* The top element of the stack is an empty end-of-scope marker *)
    | FIPop 0 :: tl -> 

      (* Remove marker from the instruction stack *)
      fold_t f subst accum tl

    (* The top element of the stack is a positive end-of-scope marker *)
    | FIPop i :: tl when i > 0 -> 

      (

        match subst with 

          (* Pop one scope from the context stack *)
          | _ :: subst' -> fold_t f subst' accum (FIPop (pred i) :: tl)
          | [] -> assert false

      )

    (* The top element of the stack is a negative end-of-scope marker *)
    | FIPop _ :: _ -> assert false

    (* The top of the stack is an evaluation of the context *)
    | FICtx i :: itl -> 

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
            fold_t f subst' atl itl

          (* Result stack is never empty and has a singleton list as
             first element *)
          | _ :: _ 
          | [] -> assert false

      )

  (* Evaluate the term bottom-up and right-to-left. The evaluation
     function is called at each node of the term with the symbol and the
     list of values computed for the subterms. Let bindings are lazily
     unfolded.
  *)
  let eval_t f t = 
    fold_t f [] [[]] [FITree (0, t)]


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

end

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

