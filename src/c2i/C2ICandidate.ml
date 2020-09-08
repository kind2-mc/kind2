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

(*

Implementation of candidates for a generic version of
@incollection{
  year={2014},
  isbn={978-3-319-08866-2},
  booktitle={Computer Aided Verification},
  volume={8559},
  series={Lecture Notes in Computer Science},
  editor={Biere, Armin and Bloem, Roderick},
  doi={10.1007/978-3-319-08867-9_6},
  title={
    From Invariant Checking to Invariant Inference Using Randomized Search
  },
  url={http://dx.doi.org/10.1007/978-3-319-08867-9_6},
  publisher={Springer International Publishing},
  author={Sharma, Rahul and Aiken, Alex},
  pages={88-105},
  language={English}
}

*)

(* |===| TODO:
  - add a module for subranges.
  - consider using constant state vars for rhs for arith sub candidates.
    Requires a different pool for rhs.
*)


open Lib

type sys = TransSys.t
type term = Term.t



(* |===| Helpers. *)


(* Returns a random int between [1] and [ubound], both inclusive.
   [ubound] must be [> 0]. *)
let rand_int ubound =
  assert (ubound > 0) ;
  1 + Random.int ubound

(* Returns a random int between [1] and the length of a list, both
   inclusive. *)
let rand_index l = List.length l |> rand_int

(* Returns a random element of an array different from [nto] (not this one). *)
let rec rand_of_array equal nto a =
  let e = Array.length a |> Random.int |> Array.get a in
  if equal nto e then rand_of_array equal nto a else e

(* Applies [f] to a random element of a list. *)
let rand_do f l =
  (* Getting a random index. *)
  let n = rand_index l in
  let rec loop cpt pref = function
    | e :: tail ->
      if cpt = n then (f e) :: tail |> List.rev_append pref
      else loop (cpt + 1) (e :: pref) tail
    | [] -> failwith "unreachable"
  in
  loop 1 [] l

(* Applies [f] to the [n]th element of a list. *)
let nth_do n f l =
  let rec loop cpt prefix = function
    | head :: tail ->
      if cpt = n then (f head) :: tail |> List.rev_append prefix
      else loop (cpt + 1) (head :: prefix) tail
    | [] ->
      List.length l
      |> Format.sprintf "[nth_do] [n = %d] but [l] has length [%d]" n
      |> failwith
  in
  loop 1 [] l

(* Creates a list of length [n] with default element [e]. *)
let mk_list n e =
  let rec loop cpt pref =
    if cpt >= n then pref else e :: pref |> loop (cpt + 1)
  in
  loop 0 []



(* |===| First class modules for sub candidates.

A sub candidate stores the part of the DNF corresponding to a certain type. So
in practice it stores the part of each cube (sub cube) made of atoms mentioning
variables of some type.

A bool sub cube is a conjunction (list) of bool variables, while an int sub
cube is a conjunction (list) of inequalities (coef list * rhs). A sub candidate
is a disjunction (list) of sub cubes. In a candidate, all sub candidates should
have the same number of disjuncts, but the size of the sub cubes can differ.

This is to treat bool and arith candidates uniformily while under the hood the
structure, the initialization, the random moves, and the sub cube construction
differ.

For subranges and arrays, one just needs to add a new module. The paper cited
above actually kind of accounts for arrays. *)


(** A sub candidate stores the info about the equations for a specific type. *)
module type SubCandidate = sig
  (** Name of the sub candidate module. *)
  val name: string
  (** Indicates whether the sub candidate can be move. *)
  val is_moveable: bool
  (** Type of the "coefficient" of the sub candidate. *)
  type value
  (** The zero for type [value]. *)
  val zero: value
  (** Equality over [value]. *)
  val equal: value -> value -> bool
  (** Stores the info about the sub candidate. *)
  type t
  (** Number of actoms in each sub cube of a sub candidate. *)
  val len: t -> int
  (** Creates a new, default sub candidate.
     [mk disj_count conj_count vars vals] creates a sub candidate for a DNF
     with [disj_count] disjuncts, each having [conj_count] atoms in the
     sub cube corresponding to this sub candidate. Each atom is a an equation
     over [vars] with coefficients and constants taking their values in
     [vals].

     Things might be a bit different depending on the type of the variables.
     For bools for instance, a sub cube is just a conjunction of bool
     variables, and [con_count] is ignored. *)
  val mk: int -> int -> Term.t list -> value list -> t
  (** Resets a candidate. *)
  val reset: t -> t
  (** Moves a candidate. *)
  val move: t -> t
  (** [guided_move sc i j] moves the [j]^th atom of the [i]^th sub cube of a
      sub candidate [sc]. *)
  val guided_move: t -> int -> int -> t
  (** [to_term sub_candidate dnf] adds the atoms of each sub cube of the sub
      candidate to each cube of the input dnf.

      /!\ SUPER IMPORTANT /!\
      For the rating to work, terms must be prepended to each cube.
      For instance, assuming the DNF only has one cube, and if the atoms
      stored in the sub candidate for this cube are [ a1 ; a2 ; a3 ]
      then [to_term t (cube :: [])] returns [( a3 :: a2 :: a1 :: cube) :: []].
      Also, the ordering of the DNF itself should not be changed.

      Note that this is what you're naturally going to get by doing a [map2]
      followed by a [fold2]. See [BoolSC.to_term] for a concrete example, or
      the arithmetic subcandidates.  *)
  val to_term: t -> term list list -> term list list
end

(* Module for boolean sub candidates. *)
module BoolSC : SubCandidate = struct
  let name = "bool"
  let is_moveable = true
  type value = bool option
  let zero = None
  let equal b1 b2 = b1 = b2
  
  type t = {
    (* Variables. *)
    vars: Term.t list ;
    (* Values of the variables in the sub cubes. *)
    vals: (bool option) list list ;
  }

  let len { vals } = match vals with
    | [] -> 0 | head :: _ -> List.length head
  
  let mk disj_count _ vars _ =
    (* All bool variables are false in the default sub cube. *)
    let vals =
      vars |> List.map (fun _ -> zero) |> mk_list disj_count
    in
    { vars ; vals }

  let reset { vars ; vals } = {
    vars ; vals = vals |> List.map (List.map (fun _ -> zero))
  }

  (* Moves one of the values for one of the variables at random. *)
  let move { vars ; vals } =
    let vals = vals |> rand_do (fun cube ->
        (* Choosing a variable in the cube at random and moving it. *)
        cube |> rand_do (function
          | None -> if rand_int 2 = 1 then Some true else Some false
          | Some b -> if rand_int 2 = 1 then Some (not b) else None
        )
      )
    in
    { vars ; vals }

  let guided_move { vars ; vals } i j =
    let vals = vals |> nth_do i (nth_do j
        ( function
          | None -> if rand_int 2 = 1 then Some true else Some false
          | Some b -> if rand_int 2 = 1 then Some (not b) else None )
      )
    in
    { vars ; vals }

  let to_term { vars ; vals } =
    (* Map on the values and the input dnf. *)
    List.map2 (fun cube_vals cube ->
      (* Fold on the variables and the sub cube values. Prepending to original
         cube. *)
      List.fold_left2 (fun nu_cube var -> function
        | None -> Term.t_true :: nu_cube
        | Some true -> var :: nu_cube
        | Some false -> (var |> Term.mk_not) :: nu_cube
      ) cube vars cube_vals
    ) vals
end


(** Sub candidate for modes. A mode sub candidate is not moveable. If the
    system has [n] modes, then [n+1] sub disjuncts are created. One for each
    mode and one empty sub disjunct (covers every mode).

    The caller of [mk] is responsible for the consistence between the variable
    list provided and the [disj_count] dimension. *)
module ModeSC: SubCandidate = struct
  let name = "mode"
  let is_moveable = false
  type value = bool
  let zero = false
  let equal b b' = b = b'
  (* Simply storing the list of terms. No move is allowed anyways. *)
  type t = Term.t list
  (* The length is always one. Either the mode variable or true. *)
  let len _ = 1

  let mk disj_count _ terms _ =
    (* Making sure dimensions make sense. *)
    if disj_count - 1 != List.length terms then
      Format.sprintf "[ModeSC] \
        dimension mismatch: %d disjunct requested but found %d mode terms\
      " disj_count (List.length terms)
      |> failwith ;

    (Term.mk_or terms) :: terms

  let reset = identity
  let move _ = failwith "cannot move mode sub candidate"
  let guided_move _ _ _ = failwith "cannot move mode sub candidate"
  let to_term t = List.map2 (fun req cube -> req :: cube) t
end


(* Factoring int and rat sub candidate under [ToArithSC], a functor taking a
   [ArithSCInfo] as parameter. *)
module type ArithSCInfo = sig
  val name: string
  val is_moveable: bool
  val underlying: Type.t
  type value
  val zero: value
  val equal: value -> value -> bool
  val to_term: value -> term
end


(* Int sub candidate info. *)
module IntSCInfo : ArithSCInfo
(* Exposing type info for [value], it is abstracted otherwise. *)
with type value = Numeral.t = struct
  let name = "int"
  let is_moveable = true
  let underlying = Type.mk_int ()
  type value = Numeral.t
  let zero = Numeral.zero
  let equal = Numeral.equal
  let to_term = Term.mk_num
end

(* Rat sub candidate info. *)
module RatSCInfo : ArithSCInfo
(* Exposing type info for [value], it is abstracted otherwise. *)
with type value = Decimal.t = struct
  let name = "rat"
  let is_moveable = true
  let underlying = Type.mk_real ()
  type value = Decimal.t
  let zero = Decimal.zero
  let equal = Decimal.equal
  let to_term = Term.mk_dec
end


(* Transforms an [ArithSCInfo] into a [SubCandidate]. *)
module ToArithSC (Info : ArithSCInfo)
(* Exposing type info for [value], it is abstracted otherwise. *)
: SubCandidate with type value = Info.value = struct
  let name = Info.name
  let is_moveable = Info.is_moveable
  type value = Info.value
  let zero = Info.zero
  let equal = Info.equal

  type t = {
    (* Variables. *)
    vars: Term.t list ;
    (* Values in the sub candidate. First list level is dnf, second level is
       cube and contains atoms: [coef list * rhs].
       The list of coefficient should have the same length as [vars]. *)
    vals: (value list * value) list list ;
    (* Pool of values. *)
    pool: value array ;
  }

  let len { vals } = match vals with
    | [] -> 0 | head :: _ -> List.length head

  let mk disj_count conj_count vars pool =
    (* All atoms have coefs and rhs [0] by default. *)
    let vals =
      (* Default atom. *)
      ( vars |> List.map (fun _ -> zero), zero )
      |> mk_list conj_count |> mk_list disj_count
    in
    (* Pool of values. *)
    let pool = Array.of_list pool in
    { vars ; vals ; pool }

  let reset { vars ; vals ; pool } = {
    vars ;
    vals = vals |> List.map (List.map (fun (lhs, rhs) ->
      lhs |> List.map (fun _ -> zero),
      zero
    )) ;
    pool
  }

  (* Probability of removing an inquality when making an inequality move is
     [1 / roh]. *)
  let roh = 10000

  (* Implementation of the random move on an arithmetic atom from the paper
     cited at the top of this file. *)
  let move_atom pool = fun (coefs, rhs) ->
    (* Choosing which move to make. *)
    match rand_int 3 with
    | 1 ->
      (* Coefficient move, moving a coefficient at random. *)
      coefs |> rand_do (fun coef -> rand_of_array equal coef pool),
      (* Keeping same rhs. *)
      rhs
    | 2 ->
      (* Constant move, keeping coefficients. *)
      coefs,
      (* Moving rhs. *)
      rand_of_array equal rhs pool
    | 3 -> (
      (* Inequality move. *)
      if rand_int roh < roh then
        (* Moving everything. *)
        coefs |> List.map (fun coef -> rand_of_array equal coef pool),
        rand_of_array equal rhs pool
      else
        (* Removing inequality (setting everything to [zero]. *)
        coefs |> List.map (fun _ -> zero),
        zero
    )
    | _ -> failwith "unreachable"

  (* Implementation of the random move from the paper cited at the top of this
     file. *)
  let move { vars ; vals ; pool } =
    (* Moving a disjunct at random. *)
    let vals = vals |> rand_do (fun subcube ->
        (* Moving a cube at random. *)
        subcube |> rand_do (move_atom pool)
      )
    in
    { vars ; vals ; pool }

  let guided_move { vars ; vals ; pool } i j =
    let vals = vals |> nth_do i ( nth_do j (move_atom pool) ) in
    { vars ; vals ; pool }

  let to_term { vars ; vals } =
    (* Map on the values and the input dnf. *)
    List.map2 (fun sub_cube cube ->
      (* Fold on the sub cube, prepending to original cube. *)
      sub_cube |> List.fold_left (fun nu_cube (coefs, rhs) ->
        (* Building inequality. *)
        Term.mk_leq [
          (* Fold on the coefs and the variables. *)
          List.fold_left2 (fun lhs coef var ->
            Term.mk_times [Info.to_term coef ; var] :: lhs
          ) [] coefs vars
          (* Building sum. *)
          |> Term.mk_plus ;
          (* Rhs. *)
          Info.to_term rhs
        ] :: nu_cube
      ) cube
    ) vals

end

(* Int sub candidate. *)
module IntSC = ToArithSC( IntSCInfo )

(* Rat sub candidate. *)
module RatSC = ToArithSC( RatSCInfo )



(* |===| Candidate building. *)

(* GADT for a list of [SubCandidate * sub] pairs. We need a gadt to constrain
   the type of [sub] to be [SubCandidate.t]. *)
type sc_list =
| Cons: (
    (module SubCandidate with type t = 'a) * 'a * sc_list
  ) -> sc_list
| Nil: sc_list

(* The length of an [sc_list]. *)
let sc_list_len =
  let rec loop cpt = function
    | Cons (_,_,tail) -> loop (cpt + 1) tail
    | Nil -> cpt
  in
  loop 0

(* Reverses an [sc_list]. *)
let sc_list_rev =
  let rec loop sc_list = function
    | Cons (m,s,tail) -> loop ( Cons (m,s,sc_list) ) tail
    | Nil -> sc_list
  in
  loop Nil

(* Reverse append for [sc_list]. *)
let sc_list_rev_app scl1 scl2 =
  let rec loop scl = function
    | Cons (m,s,tail) -> loop ( Cons (m,s,scl) ) tail
    | Nil -> scl
  in
  loop scl2 scl1


(* type 'a sc_pair = Pair of (module SubCandidate with type t = 'a) * 'a *)
(* Fold over an [sc_list]. Does not compile, the problem seems to be that
   the type of [sub] would escape its scope. Not sure what the problem is. *)
(* let sc_list_fold f init =
  let rec loop accum = function
    | Cons (modul3, sub, tail) ->
      loop ( f accum ( Pair (modul3, sub) ) ) tail
    | Nil -> accum
  in
  loop init *)

(* Resets all elements of an [sc_list]. Preserves order. *)
let sc_list_reset =
  let rec loop prefix = function
    | Cons (modul3, sub, tail) ->
      let module SC = (val modul3 : SubCandidate with type t = _) in
      loop ( Cons (modul3, SC.reset sub, prefix ) ) tail
    | Nil -> sc_list_rev prefix
  in
  loop Nil

(* Moves the [n]^th element of an [sc_list]. Preserves order. *)
let sc_list_nth_move n =
  let rec loop prefix cpt = function
    | Cons (modul3, sub, tail) ->
      if cpt = n then (
        let module SC = (val modul3 : SubCandidate with type t = _) in
        Cons (modul3, SC.move sub, tail) |> sc_list_rev_app prefix
      ) else loop (Cons (modul3, sub, prefix)) (cpt + 1) tail
    | Nil -> failwith "illegal move on sc_list"
  in
  loop Nil 1

(* Moves the [j]^th atom of the [j]^th cube in the dnf. Preserves order. *)
let sc_list_guided_move i j =
  let rec loop prefix count = function
    | Cons (modul3, sub, tail) ->
      let module SC = (val modul3 : SubCandidate with type t = _) in
      let count' = count + SC.len sub in
      if count' >= j then (
        let j = j - count in
        Cons (modul3, SC.guided_move sub i j, tail) |> sc_list_rev_app prefix
      ) else loop (Cons (modul3, sub, prefix)) count' tail
    | Nil -> failwith "illegal guided move on sc_list"
  in
  loop Nil 0


(* Builds the dnf [Term.t list list ] corresponding to an [sc_list]. [d_count]
   is the number of disjuncts expected in the dnf. Preserves order _mandatory_
   for the rated cost function. *)
let terms_of_sc_list d_count sc_list =
  let rec loop term_ll = function
    | Cons (modul3, sub, tail) ->
      let module SC = (val modul3 : SubCandidate with type t = _) in
      loop (SC.to_term sub term_ll) tail
    | _ -> term_ll
  in
  loop (mk_list d_count []) sc_list
  |> List.map List.rev


(* Returns the indices of the sub atoms that cannot be moved. *)
let unmoveable_of_sc_list sc_list =
  let rec delta_cons offset delta l =
    if delta > 0 then
      (offset + delta) :: l |> delta_cons offset (delta - 1)
    else l
  in
  let rec loop cpt indices = function
    | Cons (modul3, sub, tail) ->
      let module SC = (val modul3 : SubCandidate with type t = _) in
      let len = SC.len sub in
      let indices =
        if not SC.is_moveable then (delta_cons cpt len indices) else indices
      in
      loop (cpt + len) indices tail
    | _ -> indices
  in
  loop 0 [] sc_list


(* |===| Helpers to add sub candidates to an [sc_list]. *)

(* Prepends a bool sub candidate with [d_count] disjuncts if [vars] is not
   empty. *)
let add_bool_sub d_count vars sc_list = match vars with
  | [] -> sc_list
  | _ ->
    (* Term building and type checking. *)
    let terms =
      vars |> List.map (fun v ->
        if Var.type_of_var v != Type.t_bool then
          Var.type_of_var v
          |> Format.asprintf "\
            expected variable of type bool but %a has type %a\
          " Var.pp_print_var v Type.pp_print_type
          |> failwith
        else
          Term.mk_var v
      )
    in
    Cons (
      (module BoolSC: SubCandidate with type t = BoolSC.t),
      BoolSC.mk d_count 0 terms [],
      sc_list
    )

(* Prepends an int sub candidate with [d_count] disjuncts and [c_count] atoms
   in each subcube if [vars] is not empty. *)
let add_int_sub d_count c_count vars (vals: Numeral.t list) sc_list = match vars with
  | [] -> sc_list
  | _ ->
    (* Term building and type checking. *)
    let terms =
      vars |> List.map (fun v ->
        if Var.type_of_var v != Type.t_int then
          Var.type_of_var v
          |> Format.asprintf "\
            expected variable of type int but %a has type %a\
          " Var.pp_print_var v Type.pp_print_type
          |> failwith
        else
          Term.mk_var v
      )
    in
    Cons (
      (module IntSC: SubCandidate with type t = IntSC.t),
      IntSC.mk d_count c_count terms vals,
      sc_list
    )

(* Prepends a rat sub candidate with [d_count] disjuncts and [c_count] atoms
   in each subcube if [vars] is not empty. *)
let add_rat_sub d_count c_count vars vals sc_list = match vars with
  | [] -> sc_list
  | _ ->
    (* Term building and type checking. *)
    let terms =
      vars |> List.map (fun v ->
        if Var.type_of_var v != Type.t_real then
          Var.type_of_var v
          |> Format.asprintf "\
            expected variable of type real but %a has type %a\
          " Var.pp_print_var v Type.pp_print_type
          |> failwith
        else
          Term.mk_var v
      )
    in
    Cons (
      (module RatSC: SubCandidate with type t = RatSC.t),
      RatSC.mk d_count c_count terms vals,
      sc_list
    )

let add_mode_sub terms sc_list = match terms with
  | [] -> sc_list
  | _ -> Cons (
    (module ModeSC: SubCandidate with type t = ModeSC.t),
    ModeSC.mk ((List.length terms) + 1) 0 terms [],
    sc_list
  )


(* |===| Sets for ints and rats when mining the int and rat constants. *)

(* Set of [Numeral.t]. *)
module IntSet = Set.Make( struct
  type t = Numeral.t
  let compare = Numeral.compare
end )

(* Set of [Decimal.t]. *)
module RatSet = Set.Make( struct
  type t = Decimal.t
  let compare = Decimal.compare
end )

(* Initial int and rat set contain [0] and [1]. *)
let int_init_set, rat_init_set =
  (* [ -3 ; -2 ; -1 ; 0 ; 1 ; 2 ; 3 ] *)
  IntSet.empty |> IntSet.add Numeral.zero |> IntSet.add Numeral.one
  |> IntSet.add Numeral.(one + one) |> IntSet.add Numeral.(one + one + one),
  RatSet.empty |> RatSet.add Decimal.zero |> RatSet.add Decimal.one

(* Mines a term for integer and rational constants. Integers (resp. rationals)
   are added to set [ints] (resp. [rats]). *)
let mine_constants term (ints, rats) =

  let ints, rats = ref ints, ref rats in

  Term.eval_t (fun flat _ -> match flat with
    | (Term.T.Const _) as const ->
      (* Retrieving term. *)
      let const = Term.construct const in

      if Term.is_numeral const then
        (* Updating [ints]. *)
        ints := IntSet.add (Term.numeral_of_term const) !ints
      else if Term.is_decimal const then 
        (* Updating [rats]. *)
        rats := RatSet.add (Term.decimal_of_term const) !rats
      else ()

    | _ -> ()
  ) term ;

  !ints, !rats

(* Mining the constants is not enough, we need to generate difference of
   constants, sum, etc. *)

(* Int operators to populate the set of int values from the constants mined. *)
let unary_int_ops, binary_int_ops =
  [ Numeral.neg ], [ Numeral.add ; Numeral.sub ]

(* Rat operators to populate the set of rat values from the constants mined. *)
let unary_rat_ops, binary_rat_ops =
  [ Decimal.neg ], [ Decimal.add ; Decimal.sub ]

(* Augments [ints] with
   (1) for all [e1] in [ints],
       for all [unary] in [unary_int_ops],
       [unary e1]
   (2) for all [e1], [e2] in [ints], [ints] when [e1 != e2],
       for all [binary] in [binary_int_ops],
       [binary e1 e2].
   Does the same for [rats], respectively. *)
let op_combinate_arith_sets (ints, rats) =

  let rec loop un_ops bin_ops add set = function
    | e1 :: tail ->
      (* (1): applying unary operators. *)
      let set =
        un_ops |> List.fold_left (
          fun set unary -> add (unary e1) set
        ) set
      in
      (* (2): applying binary operators. *)
      let set =
        tail |> List.fold_left (fun set e2 ->
          bin_ops |> List.fold_left (fun set binary ->
            set |> add (binary e1 e2) |> add (binary e2 e1)
          ) set
        ) set
      in
      loop un_ops bin_ops add set tail
    | [] -> set
  in

  IntSet.elements ints |> loop unary_int_ops binary_int_ops IntSet.add ints,
  RatSet.elements rats |> loop unary_rat_ops binary_rat_ops RatSet.add rats

(* A candidate stores some subcandidates. *)
type t = {
  (* System associated to this candidate. *)
  sys: sys ;
  (* Number of disjuncts in the dnf. *)
  d_count: int ;
  (* Sub candidates. *)
  subs: sc_list ;
  (* Number of sub candidates. *)
  subs_len: int ;
}

(* Creates a new candidate. Mines the init and trans predicate, call only once
   and then use reset. *)
let mk sys =
  (* Retrieving DNF and arithmetic sub-candidates sizes. *)
  let d_count, c_int_count, c_rat_count =
    (* DNF size. *)
    ( if Flags.C2I.modes () then
        (* One disjunct per require + 1. *)
        (TransSys.get_mode_requires sys |> snd |> List.length) + 1
      else Flags.C2I.dnf_size () ),
    (* Int cube size. *)
    Flags.C2I.int_cube_size (),
    (* rat cube size. *)
    Flags.C2I.real_cube_size ()
  in

  (* Retrieving relevant variables. *)
  let b_vars, i_vars, r_vars =
    TransSys.vars_of_bounds sys Numeral.zero Numeral.zero
    |> List.fold_left (fun (b,i,r) v ->
      if
        Var.is_const_state_var v || (
          Var.state_var_of_state_var_instance v |> StateVar.for_inv_gen |> not
        )
      then b,i,r else
        match Var.type_of_var v |> Type.node_of_type with
        | Type.Bool -> v :: b, i, r
        | Type.Int  -> b, v :: i, r
        | Type.Real -> b, i, v :: r
        | _ -> b, i, r
    ) ([],[],[])
  in

  Debug.c2i "[mk] %d bool vars, %d int vars, %d rat vars@."
    (List.length b_vars) (List.length i_vars) (List.length r_vars);

  (* Mining init and trans predicates for arith constants. *)
  let int_vals, rat_vals =
    mine_constants
      (TransSys.init_of_bound None sys Numeral.zero)
      (int_init_set, rat_init_set)
    |> mine_constants (TransSys.trans_of_bound None sys Numeral.zero)
    |> op_combinate_arith_sets
    |> fun (i, r) -> IntSet.elements i, RatSet.elements r
  in

  let init_subs =
    match Flags.C2I.modes (), TransSys.get_mode_requires sys with
    | false, _ | true, (None, []) -> Nil
    | true, (Some ass, modes) ->
      (* Extract term for each requirement. *)
      let req_terms = ass :: (modes |> List.map snd) in
      add_mode_sub req_terms Nil
    | true, (None, modes) ->
      (* Extract term for each requirement. *)
      let req_terms = modes |> List.map snd in
      add_mode_sub req_terms Nil
  in

  (* Building sub candidates. *)
  let subs =
    init_subs
    |> add_rat_sub d_count c_rat_count r_vars rat_vals
    |> add_int_sub d_count c_int_count i_vars int_vals
    |> add_bool_sub d_count b_vars
  in
  (* Counting them. *)
  let subs_len = sc_list_len subs in

  (* Building final candidate. *)
  { sys ; d_count ; subs ; subs_len }

(* Resets a candidate. Avoids calling [mk] and mining the init and trans
   predicates again. *)
let reset { sys ; d_count ; subs ; subs_len } = {
  sys ; d_count ; subs = sc_list_reset subs ; subs_len
}

(* The term corresponding to a candidate, as a [Term.t list list]. *)
let terms_of { d_count ; subs } = terms_of_sc_list d_count subs

(* The term corresponding to a canditate, as a [Term.t]. *)
let term_of t = terms_of t |> List.map Term.mk_and |> Term.mk_or

(* Moves a random sub candidate. *)
let move { sys ; d_count ; subs ; subs_len } =
  (* Choosing which subcandidate to move. *)
  let to_move = rand_int subs_len in
  (* Making the move. *)
  let subs = sc_list_nth_move to_move subs in
  (* Returning new candidate. *)
  { sys ; d_count ; subs ; subs_len }


(* |===| Evaluation. *)


(* type rating = int list list *)

let zero_rating_of = List.map ( List.map (fun _ -> 0) )

let int_of_bool = function | false -> 0 | true -> 1

let eval_term sys model term =
  Eval.eval_term (TransSys.uf_defs sys) model term |> Eval.bool_of_value

(* Evaluation function. Evaluates a dnf [Term.t list list] and returns [0] for
   [false], [1] for [true].
   Only here for legacy. *)
let simple_eval sys dnf model =
  let rec eval_conj = function
    | atom :: tail ->
      if eval_term sys model atom then eval_conj tail else false
    | [] -> true
  in
  let rec eval_disj = function
    | conj :: tail ->
      if eval_conj conj then true else eval_disj tail
    | [] -> false
  in
  eval_disj dnf |> int_of_bool

(* Same as [simple_eval], but returns an updated version of [dnf_rating].
   Unchanged if [dnf] evaluates to [true], otherwise the weight of the atoms
   responsible for [dnf] evaluating to [false] has been increased.

   The increase in the weight is the number of times they evaluated to
   [false]. *)
let eval_rate_false sys dnf dnf_rating model =
  let rec eval_conj conj_val rating_prefix_rev = function
    | atom :: a_tail, rating :: r_tail ->
      if eval_term sys model atom then (
        (* Not participating in the dnf being false. *)
        (a_tail, r_tail)
        |> eval_conj conj_val (rating :: rating_prefix_rev)
      ) else (
        (* Participates in the dnf being false. *)
        (a_tail, r_tail)
        |> eval_conj false ((rating + 1) :: rating_prefix_rev)
      )
    | [], [] -> conj_val, List.rev rating_prefix_rev
    | [], _ -> failwith "[eval_rate_false] rating longer than conjunction"
    | _, [] -> failwith "[eval_rate_false] conjunction longer than rating"
  in
  let eval_conj = eval_conj true [] in
  let rec eval_disj rating_prefix_rev = function
    | conj :: c_tail, rating :: r_tail ->
      let conj_val, rating = eval_conj (conj, rating) in
      if conj_val then
        (* Disjunction is true, rating is irrelevant. *)
        true, dnf_rating
      else
        (c_tail, r_tail)
        |> eval_disj (rating :: rating_prefix_rev)
    | [], [] ->
      (* Disjunction is false, rating is relevant. *)
      false, List.rev rating_prefix_rev
    | [], _ -> failwith "[eval_rate_false] rating longer than disjunction"
    | _, [] -> failwith "[eval_rate_false] disjunction longer than rating"
  in
  eval_disj [] (dnf, dnf_rating)


(* Same as [eval_rate_false] but updates the weight of the atoms responsible
   for [dnf] evaluating to [true] if it did. Otherwise, [dnf_rating] is
   unchanged.

   For all conjunctions evaluating to [true], the weight of their atoms is
   augmented by 1. *)
let eval_rate_true sys dnf dnf_rating model =
  let rec eval_conj rating_prefix_rev = function
    | atom :: a_tail, rating :: r_tail ->
      if eval_term sys model atom then (
        (* Participates a priori in the dnf being true. *)
        (a_tail, r_tail)
        |> eval_conj ((rating + 1) :: rating_prefix_rev)
      ) else (
        (* Conjunction is false, rating is irrelevant. *)
        None
      )
    | [], [] ->
      (* Conjunction is true, rating is relevant. *)
      Some (List.rev rating_prefix_rev)
    | [], _ -> failwith "[eval_rate_false] rating longer than conjunction"
    | _, [] -> failwith "[eval_rate_false] conjunction longer than rating"
  in
  let eval_conj = eval_conj [] in
  let rec eval_disj disj_val rating_prefix_rev = function
    | conj :: c_tail, rating :: r_tail -> (
      match eval_conj (conj, rating) with
      | None ->
        (* Conjunction does not participate in dnf being true. *)
        eval_disj disj_val (rating :: rating_prefix_rev) (c_tail, r_tail)
      | Some rating ->
        (* Conjunction participates in dnf being true. *)
        eval_disj true (rating :: rating_prefix_rev) (c_tail, r_tail)
    )
    | [], [] ->
      if disj_val then true, List.rev rating_prefix_rev else false, dnf_rating
    | [], _ -> failwith "[eval_rate_false] rating longer than disjunction"
    | _, [] -> failwith "[eval_rate_false] disjunction longer than rating"
  in
  eval_disj false [] (dnf, dnf_rating)

(* Negation for [0] and [1]. *)
let neg = function
| 0 -> 1 | 1 -> 0 | n ->
  Format.sprintf "illegal bool as int value %d" n |> failwith

(* Type returned by the rated cost function. *)
type rated_t = {
  cost: int ;
  mutable rating: int list list ;
  candidate: t ;
}

let cost_of_rated { cost } = cost

let candidate_of_rated { candidate } = candidate

(* Cost function. *)
let rated_cost_function ({ sys } as candidate) white grey black =

  (* Extracting dnf as [Term.t list list]. *)
  let dnf = terms_of candidate in
  (* Initial rating. *)
  let rating = zero_rating_of dnf in

  (* Evaluating black for c1, computing c3 and updating rating at the same
     time. [black_vals] is actually reversed, but we don't care for c1. *)
  let c3, black_vals, rating =
    black |> List.fold_left (fun (c3, vals, rating) black_model ->
      (* DNF should be false on a black model, thus we rate true. *)
      let v, rating' = eval_rate_true sys dnf rating black_model in
      (* Rating should be unchanged if [v = 0]. *)
      (* assert (v || rating = rating') ; *)
      let v = int_of_bool v in
      c3 + v, v :: vals, rating'
    ) (0, [], rating)
  in

  (* Computing c1 and c2, updating rating. *)
  let c1, c2, rating =
    white |> List.fold_left (fun (c1, c2, rating) white_model ->
      (* DNF should be true on a white model, thus we rate false. *)
      let white_val, rating' = eval_rate_false sys dnf rating white_model in
      (* Rating should be unchanged if [v = 1]. *)
      (* assert (not white_val || rating = rating') ; *)
      let white_val = int_of_bool white_val in

      (* Iterating on [black_vals] for c1. *)
      black_vals |> List.fold_left (fun sum black_val ->
        sum + (neg white_val) * (neg black_val) + white_val * black_val
      ) c1,
      (* c2. *)
      c2 + (neg white_val),
      (* Updated rating. *)
      rating'
    ) (0, 0, rating)
  in

  (* Computing c4, updating rating. *)
  let c4, rating =
    grey |> List.fold_left (fun (c4, rating) (s, s') ->
      (* Here, we want to explain [eval s = true] and [eval s' = false].
         We start by eval-rating [s] for true. *)
      match eval_rate_true sys dnf rating s with
      | false, _ -> (* Evaluates to false, don't care about rating or [s']. *)
        c4, rating
      | true, rating' -> ( (* Evaluates to true, let's check [s']. *)
        match eval_rate_false sys dnf rating' s' with
        | true, _ -> (* Implication holds, [rating'] irrelevant. *)
          c4, rating
        | false, rating' ->
          c4 + 1, rating' (* Implication does not hold, [rating'] relevant. *)
      )
    ) (0, rating)
  in

  { cost = c1 + c2 + c3 + c4 ; rating ; candidate }

(* Transforms a rating of type [int list list] storing the rating for each
   atom of each disjunct into an [(int * (int array)) array].
   Let [n] be the highest atom rating of the input dnf rating. The result
   stores the indices of the disjuncts in which at least an atom has rating
   [n] and the indices of the atoms in this disjunct with rating [n].

   [forbidden] is a list of indices that should be excluded from the max
   rating. They correspond to sub cubes that cannot be moved. *)
let max_of_rating rating forbidden =
  (* Returns the highest rating of a conjunct, and the indices of the atoms
     having the max rating. *)
  let rec max_of_conjunct cpt max_atom_rating max_atoms = function
    | atom_rating :: tail ->
      if List.mem cpt forbidden then
        (* Atom belongs to a forbidden sub cube. Skipping. *)
        max_of_conjunct (cpt + 1) max_atom_rating max_atoms tail
      else if atom_rating < max_atom_rating then
        (* Rating's lower, discarding. *)
        max_of_conjunct (cpt + 1) max_atom_rating max_atoms tail
      else if atom_rating = max_atom_rating then
        (* Rating's the same, updating [max_atoms]. *)
        max_of_conjunct (cpt + 1) max_atom_rating (cpt :: max_atoms) tail
      else
        (* Rating's higher, discarding [max_atoms]. *)
        max_of_conjunct (cpt + 1) atom_rating [cpt] tail
    | [] ->
      (* [max_atoms] is reversed, but that's fine since a random element
         will be chosen. *)
      max_atom_rating, Array.of_list max_atoms
  in
  (* Currified version. *)
  let max_of_conjunct = max_of_conjunct 1 0 [] in

  let rec max_of_dnf cpt max_atom_rating max_conjuncts = function
    | rating_list :: tail ->
      let max_atom_rating', max_atoms = max_of_conjunct rating_list in
      if max_atom_rating' < max_atom_rating then
        (* Rating's lower, discarding. *)
        max_of_dnf (cpt + 1) max_atom_rating max_conjuncts tail
      else if max_atom_rating' = max_atom_rating then
        (* Rating's the same, updating [max_conjuncts]. *)
        max_of_dnf
          (cpt + 1) max_atom_rating ((cpt, max_atoms) :: max_conjuncts) tail
      else
        (* Rating's higher, discarding [max_conjuncts]. *)
        max_of_dnf (cpt + 1) max_atom_rating' [cpt, max_atoms] tail
    | [] ->
      (* [max_conjuncts] is reversed, but that's fine since a random element
         will be chosen. *)
      Array.of_list max_conjuncts
  in

  max_of_dnf 1 0 [] rating

let rating_decrement i j =
  nth_do i (nth_do j (fun v -> max (v-1) 0))

let rated_move ({ rating ; candidate } as rated) =

  (* Retrieving un-moveable indices. *)
  let unmoveable = unmoveable_of_sc_list candidate.subs in

  (* KEvent.log L_info
    "[C2I] | [rated_move] unmoveable: [ %a ]"
    (pp_print_list Format.pp_print_int ", ") unmoveable ; *)

(*   KEvent.log L_info
    "[C2I] |  [rated_move] rating: @[<v>%a@]"
    (pp_print_list
      (fun fmt ->
        Format.fprintf fmt "%a"
          (pp_print_list Format.pp_print_int " "))
      "@ ")
    rating ; *)
  let max_rating = max_of_rating rating unmoveable in

  (* max_rating |> Array.to_list
  |> List.map (fun (idx,a) -> idx, Array.to_list a)
  |> KEvent.log L_info
      "[C2I] |  [rated_move] max rating: @[<v>%a@]"
      (pp_print_list
        (fun fmt (idx, l) ->
          Format.fprintf fmt "%d -> %a"
            idx
            (pp_print_list Format.pp_print_int ",") l)
        "@ ") ; *)

  let disjunct_index, atom_index =
    let d_index, atom_ratings =
      Array.length max_rating |> Random.int |> Array.get max_rating
    in
    d_index,
    Array.length atom_ratings |> Random.int |> Array.get atom_ratings
  in

  (* KEvent.log L_info
    "[C2I] |  [rated_move] moving (%d, %d) of %d possibilities"
    disjunct_index atom_index
    (max_rating |> Array.fold_left (
      fun sum (_,arr) -> sum + Array.length arr
    ) 0) ; *)

  let subs = sc_list_guided_move disjunct_index atom_index candidate.subs in

  rated.rating <- rating_decrement disjunct_index atom_index rating ;

  {
    sys = candidate.sys ;
    d_count = candidate.d_count ;
    subs ;
    subs_len = candidate.subs_len ;
  }




(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
