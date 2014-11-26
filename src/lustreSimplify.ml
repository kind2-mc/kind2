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


(* The main function {!declarations_to_nodes} iterates over the list
   of declarations obtained from parsing Lustre input and returns a
   list of Lustre nodes.

   All alias types are substituted with basic types, global constants
   are propagated to expressions, and nodes are rewritten into a
   normal form, see below.

   {!declarations_to_nodes'} adds to and returns a {!lustre_context}
   that is a record of 

   - [basic_types]: an association list of indexed identifiers to basic
     types of {!Type.t},

   - [indexed_types]: an association list of indexed identifiers to an
     association list of indexes to basic types. The latter maps each
     suffix of a type identifier to a basic type,

   - [free_types]: currently unused, intended to hold a list of types
     that are considered uninterpreted,

   - [type_ctx]: an association list of identifiers to basic types,

   - [index_ctx]: an association list of indexed identifiers to their
     suffixes, implemented as an association list of indexes to units
     for uniformity with [indexed_types],

   - [consts]: an association list of constant identifiers to expressions, and 

   - [nodes]: the list of parsed nodes. 


*)



(* Abbreviations *)
module A = LustreAst
module I = LustreIdent
module E = LustreExpr
module N = LustreNode

module ISet = I.LustreIdentSet
module IMap = I.LustreIdentMap
module IdxMap = I.LustreIndexMap
module ITrie = I.LustreIdentTrie
module IdxTrie = I.LustreIndexTrie



module Event = struct let log _ = Format.printf end

(* Node not found, possible forward reference 

   This is just failing at the moment, we'd need some dependency
   analysis to recognize cycles to fully support forward
   referencing. *)
exception Node_not_found of I.t * A.position


(* Raise parsing exception *)
let fail_at_position pos msg = 

  Event.log
    L_warn
    "Parser error in %a: %s"
    A.pp_print_position pos
    msg;

  raise A.Parser_error
  

(* Raise parsing exception *)
let warn_at_position pos msg = 

  Event.log
    L_warn
    "Parser warning in %a: %s"
    A.pp_print_position pos
    msg


(* ******************************************************************** *)
(* Data structures                                                      *)
(* ******************************************************************** *)

(* Context for typing, flattening of indexed types and constant
   propagation *)
type lustre_context = 

  { 

    (* Type identifiers and their types *)
    type_of_ident : (Type.t * E.t list) ITrie.t; 

    (* Identifiers and the expresssions they are bound to

       Contains a state variable if the identifier denotes a stream,
       and a term if the identifier denotes a constant *)
    expr_of_ident : (E.t * E.t list) ITrie.t;

    (* Nodes *)
    nodes : N.t list;
    
  }


(* Get the greatest integer of an indexed trie *)
let top_int_index_of_idx_trie t = 
  try 

    IdxTrie.max_binding t
    |> fst
    |> (function i -> match I.split_index i with
        | I.IntIndex i :: _ -> i
        | _ -> raise (Invalid_argument "top_int_index_of_idx_trie"))

  with Not_found -> (-1)
    

(* Increment greatest integer of an indexed trie and return an index *)
let next_top_index_of_idx_trie t = 
  top_int_index_of_idx_trie t
  |> succ 
  |> Numeral.of_int
  |> I.mk_int_index
    
  
let pp_print_type_of_ident ppf t = 
  
  Format.fprintf 
    ppf
    "@[<v>%t@]"
    (function ppf -> 
      ITrie.iter 
        (fun i t -> 
           Format.fprintf 
             ppf
             "@[<hv>%a:@ %a@]@,"
             (I.pp_print_ident false) i
             (E.pp_print_lustre_type false) t)
        t)

let print_type_of_ident = pp_print_type_of_ident Format.std_formatter

(* Initial, empty context *)
let init_lustre_context = 
  { type_of_ident = ITrie.empty;
    expr_of_ident = ITrie.empty;
    nodes = [] }


(* Pretty-print a context for type checking *)
let pp_print_lustre_context 
    safe
    ppf 
    { type_of_ident;
      expr_of_ident } =
  
  Format.fprintf ppf
    "@[<v>@[<v>type_of_ident:@,%t@]\
          @[<v>expr_of_ident:@,%t@]\
     @]" 
    (fun ppf -> 
       ITrie.iter
         (fun i (t, b) -> 
            Format.fprintf ppf 
              "%a %a: %a@," 
              (I.pp_print_ident safe) i 
              (pp_print_list 
                (function ppf ->
                  Format.fprintf ppf 
                    "[0..%a]"
                    (E.pp_print_lustre_expr false))
                "")
              b
              Type.pp_print_type t)
         type_of_ident)
    (fun ppf -> 
       ITrie.iter
         (fun i (e, b) -> 
            Format.fprintf ppf 
              "%a %a: %a@," 
              (I.pp_print_ident safe) i 
              (pp_print_list 
                (function ppf ->
                  Format.fprintf ppf 
                    "[0..%a]"
                    (E.pp_print_lustre_expr false))
                "")
              b
              (E.pp_print_lustre_expr safe) e)
         expr_of_ident)
    

(* Environment when simplifying an expression *)
type abstraction_context = 

  { 

    (* Scope for new identifiers *)
    scope : I.index;

    (* Create a new identifier for a variable *)
    mk_fresh_state_var : bool -> Type.t -> StateVar.t;

    (* Define an expression with a state variable or re-use previous
       definition *)
    mk_state_var_for_expr : bool -> (StateVar.t * E.t) list -> E.t -> E.t list -> StateVar.t * (StateVar.t * E.t) list;

    (* Create a new oracle input to guard pre operation on state
       variable *)
    mk_oracle_for_state_var : StateVar.t -> StateVar.t;

    (* Create a new oracle input *)
    mk_new_oracle : Type.t -> StateVar.t;

    (* Create a new identifier for an observer output *)
    mk_new_observer : Type.t -> StateVar.t;

    (* Definitions of new variables to add *)
    new_vars : (StateVar.t * E.t) list;

    (* Definitions of node calls to add *)
    new_calls : N.node_call list;

    (* Oracle inputs to add to the inputs of the node *)
    new_oracles : StateVar.t list;

    (* Observer oututs to add to the ouptuts of the node *)
    new_observers : StateVar.t list;

  }


(* Environment without abstrations allowed *)
let void_abstraction_context pos = 
  
  let msg = "Expression must be constant" in

  { scope = I.empty_index;
    mk_fresh_state_var = (fun _ -> fail_at_position pos msg); 
    mk_state_var_for_expr = (fun _ -> fail_at_position pos msg); 
    mk_oracle_for_state_var = (fun _ -> fail_at_position pos msg);
    mk_new_oracle = (fun _ -> fail_at_position pos msg);
    mk_new_observer = (fun _ -> fail_at_position pos msg);
    new_vars = []; 
    new_calls = [];
    new_oracles = [];
    new_observers = [] } 


(* Pretty-print an environment *)
let pp_print_abstraction_context 
    ppf
    { scope; new_vars; new_calls; new_oracles; new_observers } =

  Format.fprintf 
    ppf 
    "@[<v>Abstraction context for scope %a@,@[<hv>new_vars:@ @[<hv>%a@]@]@,@[<hv>new_calls:@ @[<hv>%a@]@]@,@[<hv>new_oracles:@ @[<hv>%a@]@]@,@[<hv>new_observers:@ @[<hv>%a@]@]@]"
    (I.pp_print_index false) scope
    (pp_print_list
       (fun ppf (sv, def) -> 
          Format.fprintf ppf "@[<hv>%a =@ %a@]"
            StateVar.pp_print_state_var sv
            (E.pp_print_lustre_expr false) def)
       ",@,")
    new_vars
    (pp_print_list
       (fun ppf -> function 
          | { N.call_returns = ret;
              N.call_observers = obs;
              N.call_clock = clk;
              N.call_node_name = node;
              N.call_inputs = inp;
              N.call_defaults = init } when E.equal_expr clk E.t_true -> 
            Format.fprintf ppf "@[<hv>%a =@ %a(%a)@]"
              (pp_print_list StateVar.pp_print_state_var ",@,") 
              (IdxTrie.values ret @ obs)
              (I.pp_print_ident false) node
              (pp_print_list (E.pp_print_lustre_var false) ",@,") 
              (IdxTrie.values inp)
          | { N.call_returns = ret;
              N.call_observers = obs;
              N.call_clock = clk;
              N.call_node_name = node;
              N.call_inputs = inp;
              N.call_defaults = init } -> 
            Format.fprintf ppf "@[<hv>%a =@ condact(%a,%a(%a),%a)@]"
              (pp_print_list StateVar.pp_print_state_var ",@,") 
              (IdxTrie.values ret @ obs)
              (E.pp_print_lustre_expr false) clk
              (I.pp_print_ident false) node
              (pp_print_list (E.pp_print_lustre_var false) ",@,") 
              (IdxTrie.values inp)
              (pp_print_list (E.pp_print_lustre_expr false) ",@,") 
              (IdxTrie.values init @ (List.map (fun _ -> E.t_true) obs)))
       ",@,")
    new_calls
    (pp_print_list StateVar.pp_print_state_var ",@,") 
    new_oracles
    (pp_print_list StateVar.pp_print_state_var ",@,") 
    new_observers
    
    



(* ******************************************************************** *)
(* Evaluation of expressions                                            *)
(* ******************************************************************** *)

(* Given an expression parsed into the AST, evaluate to a list of
   LustreExpr.t paired with an index, sorted by indexes. Unfold and
   abstract from the context, also return a list of created variables
   and node calls.

   The functions [mk_new_state_var] and [mk_new_oracle_var] return a
   fresh state variable and fresh input constant, respectively. A
   typing context is given to type check expressions, it is not
   modified, the created variables for abstracted expressions,
   variables capturing the output of node calls and oracle inputs are
   added to the abstraction context.

   There are several mutually recursive functions, [eval_ast_expr] is
   the main entry point.

   [eval_ast_expr] processes a list of AST expressions and produces a
   list of indexed Lustre expression reverse ordered by indexes.

   TODO: 

   - fail if tuples, record or array values are greater than the 
     defined type
   - multi-dimensional arrays
   - array slicing and concatenation, 
   - arrays and records with modification, 
   - current(e when c) expressions,
   - dynamically indexed arrays, 
   - parametric nodes
   - recursive nodes

*)
let rec eval_ast_expr     
    ({ scope;
       mk_fresh_state_var; 
       mk_state_var_for_expr; 
       mk_oracle_for_state_var; 
       mk_new_oracle; 
       mk_new_observer; 
       new_vars;
       new_calls;
       new_oracles;
       new_observers } as abstractions)
    ({ type_of_ident;
       expr_of_ident;
       nodes } as context) =

  (* Return the trie for the identifier *)
  let eval_ident pos ident = 

    (try 

       (* Get map of suffixes of identifier to expressions *)
       let res = 
         ITrie.find_prefix ident expr_of_ident
       in

       (* Return expresssion and no new abstractions *)
       (res, abstractions)

     with Not_found -> 

       fail_at_position
         pos
         (Format.asprintf 
            "Undeclared identifier %a"
            (I.pp_print_ident false) ident))

  in

  (* Return the constant inserted into an empty trie *)
  let eval_nullary_ast_expr pos expr = 

    (* Add expression to trie with empty index *)
    let res = IdxTrie.add I.empty_index expr IdxTrie.empty in

    (* Return trie and no new abstractions *)
    (res, abstractions)

  in


  (* Evaluate the argument of a unary expression and construct a unary
     expression of the result with the given constructor *)
  let eval_unary_ast_expr pos mk expr = 

    (* Evaluate expression *)
    let expr', abstractions' = 
      eval_ast_expr abstractions context expr 
    in
 
    (* Apply given constructor to each expression and keep bounds *)
    (IdxTrie.map (fun (e, b) -> (mk e, b)) expr', 
     abstractions')
    
  in


  (* Evaluate the argument of a unary expression and construct a unary
     expression of the result with the given constructor *)
  let eval_binary_ast_expr pos mk expr1 expr2 = 

    (* Evaluate first expression *)
    let expr1', abstractions' = 
      eval_ast_expr abstractions context expr1 
    in

    (* Evaluate second expression *)
    let expr2', abstractions'' = 
      eval_ast_expr abstractions' context expr2 
    in

    (* Apply operator pointwise to expressions *)
    let res = 

      try 

        (* Fold simultanously over indexes in expressions

           If tries contain the same indexes, the association list
           returned by bindings contain the same keys in the same
           order. *)
        IdxTrie.map2 


          (* Apply operator to arguments *)
          (fun _ (b1, e1) (b2, e2) -> 

             (* Bounds for array variables must be identical *)
             if b1 = b2 then

               (* Apply given constructor to expression pair and keep
                  bounds of first, which are identical to bounds of
                  second *)
               (mk e1 e2, b1) 

             else 

               raise E.Type_mismatch)

          expr1'
          expr2'

      with 
        | Invalid_argument _ ->

          fail_at_position
            pos
            "Index mismatch for expressions %a and %a" 

        | E.Type_mismatch ->

          fail_at_position
            pos
            (Format.asprintf
               "Type mismatch for expressions %a and %a" 
               A.pp_print_expr expr1
               A.pp_print_expr expr2)

    in

    (res, abstractions'')

  in

  (* Return the trie starting at the given index *)
  let eval_ast_projection pos expr index = 

    (* Evaluate record expression *)
    let expr', abstractions' = 
      eval_ast_expr 
        abstractions
        context
        expr
    in

    (try 

       (* Get value for index of projected field *)
       let res = IdxTrie.find_prefix index expr' in

       (* Return expresssion and new abstractions *)
       (res, abstractions')

     with Not_found ->

       fail_at_position 
         pos
         (Format.asprintf 
            "Expression %a does not have index %a" 
            A.pp_print_expr expr
            (I.pp_print_index false) index))

  in

  (* *)
  let eval_node_call abstractions pos ident cond args defaults = 

    (* Type check expressions for node inputs and return sorted list
       of expressions for node inputs *)
    let node_inputs_of_exprs abstractions node_inputs pos expr_list =

      try

        (* Check types and index *)
        IdxTrie.fold2
          (fun 
            i
            state_var
            ({ E.expr_type } as expr, expr_bounds)
            (accum, ({ mk_state_var_for_expr } as abstractions)) ->

            if 

              (* Expression must be of a subtype of input type *)
              Type.check_type 
                expr_type
                (StateVar.type_of_state_var state_var) &&

              (* Number of indexes must match *)
              (List.length expr_bounds = 
               List.length (StateVar.indexes_of_state_var state_var))

            then 

              (* New variable for abstraction, is constant if input is *)
              let state_var', new_vars' = 
                mk_state_var_for_expr
                  (StateVar.is_const state_var) 
                  abstractions.new_vars
                  expr 
                  expr_bounds
              in

              E.set_state_var_instance state_var' pos ident state_var;

              (* Add definition of variable *)
              let abstractions' =
                { abstractions with new_vars = new_vars' } 
              in

              (* Add expression as input *)
              (IdxTrie.add i state_var' accum, abstractions')

            else
              raise E.Type_mismatch)

          node_inputs
          expr_list
          (IdxTrie.empty, abstractions)

      (* Type checking error or one expression has more indexes *)
      with Invalid_argument _ | E.Type_mismatch -> 

        fail_at_position pos "Type mismatch for expressions"

    in

    let

      (* Extract values from record *)
      { N.inputs = node_inputs; 
        N.oracles = node_oracles;
        N.outputs = node_outputs; 
        N.observers = node_observers;
        N.props = node_props } = 

      try 

        (* Get node by identifier *)
        N.node_of_name ident nodes

      with Not_found -> 

        (* Node may be forward referenced *)
        raise (Node_not_found (ident, pos))

    in

    if

      (* Node call has activation condition  *)
      not (E.equal_expr cond E.t_true)

    then 

      (

        (* Number of defaults must match number of outputs *)
        if (IdxTrie.cardinal node_outputs <> IdxTrie.cardinal defaults) then 

          fail_at_position 
            pos
            "Number of default arguments does not match number of outputs"

        else

          IdxTrie.iter2 
            (fun i sv { E.expr_type = t } -> 

               if 

                 (* Type of default must match type of respective
                    output *)
                 not (Type.check_type t (StateVar.type_of_state_var sv)) 

               then

                 fail_at_position 
                   pos
                   "Type mismatch between default arguments and outputs")

            node_outputs
            defaults

      );

    (* Evaluate inputs as list of expressions *)
    let expr_list', abstractions' = 
      eval_ast_expr
        abstractions
        context 
        (A.ExprList (pos, args))
    in


    (* Fresh state variables for oracle inputs of called node *)
    let oracle_state_vars = 
      List.map 
        (fun node_sv ->
           let sv = mk_new_oracle (StateVar.type_of_state_var node_sv) in
           E.set_state_var_instance sv pos ident node_sv;
           sv)
        node_oracles 
    in

    (* Fresh state variables for observer outputs of called node *)
    let observer_state_vars = 
      List.map 
        (fun node_sv -> 
           let sv = 
             mk_new_observer (StateVar.type_of_state_var node_sv) 
           in
           E.set_state_var_instance sv pos ident node_sv;
           sv)
        node_observers

    in

    (* Type check and flatten indexed expressions for input into list
           without indexes *)
    let call_inputs, abstractions' =
      node_inputs_of_exprs abstractions' node_inputs pos expr_list'
    in

    (* Get the highest index of the inputs *)
    let call_inputs_max_index = top_int_index_of_idx_trie call_inputs in

    (* Add oracles to inputs *)
    let call_inputs', _ = 
      List.fold_left
        (fun (t, i) sv -> 
           ((IdxTrie.add 
               (I.mk_int_index (Numeral.(succ i)))  
               sv
               t),
            Numeral.(succ i)))
        (call_inputs, Numeral.of_int call_inputs_max_index)
        oracle_state_vars 
    in

    (* Create fresh state variable for each output *)
    let call_returns = 
      IdxTrie.map
        (fun node_sv -> 
           let sv = 
             mk_fresh_state_var false (StateVar.type_of_state_var node_sv)
           in
           E.set_state_var_instance sv pos ident node_sv;
           sv)
        node_outputs
    in

    (* Remove index if node has only one output *)
    let call_returns' =
      match IdxTrie.bindings call_returns with
        | [(i, e)] when i = I.mk_int_index Numeral.zero -> 
          IdxTrie.add I.empty_index e IdxTrie.empty
        | _ -> call_returns
    in

    (* Return tuple of state variables capturing outputs *)
    let res = 
      IdxTrie.map
        (fun sv -> E.mk_var sv E.base_clock)
        call_returns'
    in

    (* Add expression to result *)
    (res,
     { abstractions' 
       with new_calls = { N.call_returns = call_returns;
                          N.call_observers = observer_state_vars;
                          N.call_clock = cond;
                          N.call_node_name = ident;
                          N.call_pos = pos;
                          N.call_inputs = call_inputs';
                          N.call_defaults = defaults } 
                        :: abstractions'.new_calls;
            new_oracles = abstractions'.new_oracles @ oracle_state_vars;
            new_observers = abstractions'.new_observers @ observer_state_vars })

  in

  function

    (* Identifier *)
    | A.Ident (pos, ident) -> eval_ident pos ident

    (* Projection to a record field [expr.field] *)
    | A.RecordProject (pos, expr, field) -> eval_ast_projection pos expr field

    (* Projection to a tuple or array field [expr[field_expr]] *)
    | A.TupleProject (pos, expr, field_expr) -> 

      (* Evaluate expression to an integer constant *)
      let field = 
        I.mk_int_one_index (int_const_of_ast_expr context pos field_expr) 
      in

      eval_ast_projection pos expr field

    (* Boolean constant true [true] *)
    | A.True pos -> eval_nullary_ast_expr pos E.t_true

    (* Boolean constant false [false] *)
    | A.False pos ->  eval_nullary_ast_expr pos E.t_false

    (* Integer constant [d] *)
    | A.Num (pos, d) -> 

      eval_nullary_ast_expr pos (E.mk_int (Numeral.of_string d) )

    (* Real constant [f] *)
    | A.Dec (pos, f) -> 

      eval_nullary_ast_expr pos (E.mk_real (Decimal.of_string f))

    (* Conversion to an integer number [int expr] *)
    | A.ToInt (pos, expr) -> eval_unary_ast_expr pos E.mk_to_int expr 

    (* Conversion to a real number [real expr] *)
    | A.ToReal (pos, expr) -> eval_unary_ast_expr pos E.mk_to_real expr

    (* Boolean negation [not expr] *)
    | A.Not (pos, expr) -> eval_unary_ast_expr pos E.mk_not expr 

    (* Boolean conjunction [expr1 and expr2] *)
    | A.And (pos, expr1, expr2) ->

      eval_binary_ast_expr pos E.mk_and expr1 expr2

    (* Boolean disjunction [expr1 or expr2] *)
    | A.Or (pos, expr1, expr2) -> 

      eval_binary_ast_expr pos E.mk_or expr1 expr2 

    (* Boolean exclusive disjunction [expr1 xor expr2] *)
    | A.Xor (pos, expr1, expr2) -> 

      eval_binary_ast_expr pos E.mk_xor expr1 expr2 

    (* Boolean implication [expr1 => expr2] *)
    | A.Impl (pos, expr1, expr2) -> 

      eval_binary_ast_expr pos E.mk_impl expr1 expr2 

    (* Unary minus [- expr] *)
    | A.Uminus (pos, expr) -> 

      eval_unary_ast_expr pos E.mk_uminus expr 

    (* Integer modulus [expr1 mod expr2] *)
    | A.Mod (pos, expr1, expr2) -> 

      eval_binary_ast_expr pos E.mk_mod expr1 expr2 

    (* Subtraction [expr1 - expr2] *)
    | A.Minus (pos, expr1, expr2) -> 

      eval_binary_ast_expr pos E.mk_minus expr1 expr2

    (* Addition [expr1 + expr2] *)
    | A.Plus (pos, expr1, expr2) -> 

      eval_binary_ast_expr pos E.mk_plus expr1 expr2

    (* Real division [expr1 / expr2] *)
    | A.Div (pos, expr1, expr2) -> 

      eval_binary_ast_expr pos E.mk_div expr1 expr2 

    (* Multiplication [expr1 * expr2] ]*)
    | A.Times (pos, expr1, expr2) -> 

      eval_binary_ast_expr pos E.mk_times expr1 expr2 

    (* Integer division [expr1 div expr2] *)
    | A.IntDiv (pos, expr1, expr2) -> 

      eval_binary_ast_expr pos E.mk_intdiv expr1 expr2 

    (* If-then-else [if expr1 then expr2 else expr3 ]*)
    | A.Ite (pos, expr1, expr2, expr3) -> 

      (* Evaluate expression for condition *)
      let expr1', abstractions' = 
        bool_expr_of_ast_expr
          abstractions
          context
          pos
          expr1 
      in

      eval_binary_ast_expr pos (E.mk_ite expr1') expr2 expr3

    (* Equality [expr1 = expr2] *)
    | A.Eq (pos, expr1, expr2) -> 

      (* Apply equality pointwise *)
      let expr, abstractions' = 
        eval_binary_ast_expr pos E.mk_eq expr1 expr2 
      in

      (* Conjunction of equations *)
      let res = 
        IdxTrie.fold
          (fun _ e a -> E.mk_and e a)
          expr
          E.t_true
      in

      (IdxTrie.add I.empty_index res IdxTrie.empty, abstractions')

    (* Disequality [expr1 <> expr2] *)
    | A.Neq (pos, expr1, expr2) -> 

      (* Translate to negated equation *)
      eval_ast_expr
        abstractions
        context
        (A.Not (A.dummy_pos, A.Eq (pos, expr1, expr2)))

    (* Less than or equal [expr1 <= expr2] *)
    | A.Lte (pos, expr1, expr2) -> 

      eval_binary_ast_expr pos E.mk_lte expr1 expr2 

    (* Less than [expr1 < expr2] *)
    | A.Lt (pos, expr1, expr2) -> 

      eval_binary_ast_expr pos E.mk_lt expr1 expr2 

    (* Greater than or equal [expr1 >= expr2] *)
    | A.Gte (pos, expr1, expr2) -> 

      eval_binary_ast_expr pos E.mk_gte expr1 expr2 

    (* Greater than [expr1 > expr2] *)
    | A.Gt (pos, expr1, expr2) -> 

      eval_binary_ast_expr pos E.mk_gt expr1 expr2 

    (* Temporal operator pre [pre expr] *)
    | A.Pre (pos, expr) -> 

      (* Evaluate expression *)
      let expr', abstractions' = 
        eval_ast_expr 
          abstractions
          context 
          expr 
      in

      (* Apply pre operator to expression, may change context with new
         variable *)
      let res, abstractions'' = 

        IdxTrie.fold

          (fun index expr (accum, ({ new_vars } as abstractions)) -> 

             (* Apply pre operator to expression, abstract
                non-variable term and re-use previous variables *)
             let expr', new_vars' = 
               E.mk_pre (mk_state_var_for_expr false) new_vars expr 
             in

             (IdxTrie.add index expr' accum,
              { abstractions with new_vars = new_vars' }))

          expr'
          (IdxTrie.empty, abstractions')

      in

      (res, abstractions'')

    (* Arrow temporal operator [expr1 -> expr2] *)
    | A.Arrow (pos, expr1, expr2) -> 

      eval_binary_ast_expr pos E.mk_arrow expr1 expr2 

    (* An expression list, flatten nested lists and add an index to
       each elements [(expr1, expr2)] *)
    | A.ExprList (pos, expr_list) -> 

      (* Flatten nested lists *)
      let rec flatten_expr_list accum = function 

        | [] -> List.rev accum

        | A.ExprList (pos, expr_list) :: tl -> 
          flatten_expr_list accum (expr_list @ tl)

        | expr :: tl -> flatten_expr_list (expr :: accum) tl

      in

      (* Turn ((a,b),c) into (a,b,c) *)
      let expr_list' = flatten_expr_list [] expr_list in

      (* Treat as tuple *)
      eval_ast_expr 
        abstractions
        context
        (A.TupleExpr (pos, expr_list'))

    (* Tuple constructor [[expr1, expr2]] *)
    | A.TupleExpr (pos, expr_list) -> 

      let _, abstractions', res = 

        (* Iterate over list of expressions *)
        List.fold_left

          (fun (i, abstractions, accum) expr -> 

             (* Evaluate expression *)
             let expr', abstractions' = 
               eval_ast_expr
                 abstractions
                 context 
                 expr
             in

             (* Increment counter *)
             (Numeral.(succ i),

              (* Continue with added definitions *)
              abstractions',

              (* Push current index to indexes in expression and add
                 to accumulator trie *)
              IdxTrie.fold
                (fun j e a -> 
                   IdxTrie.add (I.push_int_index_to_index i j) e a)
                expr'
                accum))

          (* Start counting index at zero, with given abstractions and
             add to the empty trie *)
          (Numeral.zero, abstractions, IdxTrie.empty)

          expr_list

      in

      (res, abstractions')

    (* Array constructor [expr^size_expr] 

       TODO: translate this to a recursive array construction to use
       quantified definitions. [A = expr^size_expr] then becomes 
       [A[i] = expr]. *)
    | A.ArrayConstr (pos, expr, size_expr) -> 

      (* Evaluate expression to an integer constant *)
      let array_size = int_const_of_ast_expr context pos size_expr in

      (* Size of array must be non-zero and positive *)
      if Numeral.(array_size <= zero) then 

        fail_at_position 
          pos
          (Format.asprintf 
             "Expression %a cannot be used as the size of an array" 
             A.pp_print_expr size_expr);

      (* Evaluate expression for array elements *)
      let expr', abstractions' = 
        eval_ast_expr 
          abstractions
          context 
          expr 
      in 

      (* Add expression paired with each index to the result *)
      let res = 

        let rec aux accum = function 

          (* All elements of array enuerated

             Started with size of array, lowest index is zero *)
          | i when Numeral.(i >= array_size) -> accum

          (* Array element *)
          | i -> 


            (* Append current index to each index of evaluated
               expression and recurse to next lower array element *)
            aux 

              (* Push current index to indexes in expression and add
                 to accumulator trie *)
              (IdxTrie.fold
                 (fun j e t -> 
                    IdxTrie.add (I.push_int_index_to_index i j) e t)
                 expr'
                 accum)

              Numeral.(succ i)

        in

        (* Add all array elements *)
        aux IdxTrie.empty Numeral.zero

      in

      (res, abstractions')

    (* Record constructor [record_type {field1 = expr1; field2 = expr2}] *)
    | A.RecordConstruct (pos, record_type, expr_list) -> 

      (* Extract list of fields of record *)
      let record_indexes = 

        try 

          ITrie.find_prefix
            record_type
            expr_of_ident

        with Not_found -> 

          fail_at_position
            pos
            (Format.asprintf 
               "Record type %a not defined" 
               (I.pp_print_ident false) record_type)

      in

      (* Get indexed expressions in record definition *)
      let res, abstractions' =

        List.fold_left 
          (fun (accum, abstraction) (i, expr) -> 

             (* Evaluate expression *)
             let expr', abstractions' = 
               eval_ast_expr 
                 abstractions
                 context 
                 expr
             in

             (* Push field index to indexes in expression and add to
                 accumulator trie *)
             (IdxTrie.fold
                (fun j e t -> 
                   IdxTrie.add (I.push_ident_index_to_index i j) e t)
                expr'
                accum), 
             abstractions')
          (IdxTrie.empty, abstractions)
          expr_list

      in

      (* Keys in type and keys in expression must be identical *)
      if IdxTrie.keys res = IdxTrie.keys record_indexes then

        (res, abstractions')

      else

        fail_at_position
          pos
          (Format.asprintf 
             "Type mismatch in record of type %a" 
             (I.pp_print_ident false) record_type)


    (* Condact, a node with an activation condition *)
    | A.Condact (pos, cond, ident, args, defaults) -> 

      (* Evaluate initial values as list of expressions *)
      let defaults', abstractions' = 
        eval_ast_expr
          abstractions
          context 
          (A.ExprList (pos, defaults))
      in

      (* Evaluate activation condition *)
      let cond', abstractions' = 

        bool_expr_of_ast_expr
          abstractions' 
          context 
          pos
          cond

      in

      let cond'', abstractions'' = 

        if 

          (* Input must not contain variable at previous state *)
          E.has_pre_var cond'

        then

          (* New variable for abstraction, not a constant *)
          let state_var, new_vars' = 
            mk_state_var_for_expr
              false
              new_vars
              cond'
          in

          E.set_state_var_source state_var E.Abstract;

          (* Add definition of variable *)
          let abstractions'' =
            { abstractions' with
                new_vars = new_vars' }
          in

          (* Use abstracted variable as input parameter *)
          (E.mk_var state_var E.base_clock, 
           abstractions'')

        else

          (* Add expression as input *)
          (cond', abstractions')

      in

      (* pos ident cond args defaults *)

      eval_node_call
        abstractions''
        pos
        ident
        cond''
        args
        defaults'

    (* Node call *)
    | A.Call (pos, ident, args) -> 

      eval_node_call 
        abstractions
        pos
        ident
        E.t_true
        args
        IdxTrie.empty

    (* Boolean at-most-one constaint  *)
    | A.OneHot (pos, _) -> 

      fail_at_position pos "One-hot expression not supported"

    (* Array slice [A[i..j,k..l]] *)
    | A.ArraySlice (pos, _, _) -> 

      fail_at_position
        pos
        "Array slices not implemented"

    (* Concatenation of arrays [A|B] *)
    | A.ArrayConcat (pos, _, _) -> 

      fail_at_position pos "Array concatenation not implemented"


    (* With operator for recursive node calls *)
    | A.With (pos, _, _, _) -> 

      fail_at_position pos "Recursive nodes not supported"


    (* Followed by operator *)
    | A.Fby (pos, _, _, _) -> 

      fail_at_position pos "Fby operator not implemented" 


    (* Interpolation to base clock *)
    | A.Current (pos, A.When (_, _, _)) -> 

      fail_at_position pos "Current expression not supported"


    (* Projection on clock *)
    | A.When (pos, _, _) -> 

      fail_at_position 
        pos
        "When expression must be the argument of a current operator"


    (* Interpolation to base clock *)
    | A.Current (pos, _) -> 

      fail_at_position 
        pos
        "Current operator must have a when expression as argument"


    (* Node call to a parametric node *)
    | A.CallParam (pos, _, _, _) -> 

      fail_at_position pos "Parametric nodes not supported" 

(* Evaluate expression to an integer constant *)
and int_const_of_ast_expr context pos expr = 

  match

    (* Evaluate expression to trie *)
    eval_ast_expr 
      (void_abstraction_context pos)
      context
      expr
    |> fst 
    |> IdxTrie.bindings

  with

    (* Expression must evaluate to a singleton list of an integer
       expression without index and without new definitions *)
    | [ index, { E.expr_init = ei; 
                 E.expr_step = es } ]
      when 
        index = I.empty_index && 
        let ei' = (ei :> Term.t) in let es' = (es :> Term.t) in 
        Term.equal ei' es' -> 

      (* Get term for initial value of expression, is equal to step *)
      let ti = E.base_term_of_expr E.base_offset ei in

      (if Term.is_numeral ti then

         Term.numeral_of_term ti

       else

         fail_at_position pos "Expression must be an integer")

    (* Expression is not a constant integer *)
    | _ ->       

      fail_at_position pos "Expression must be constant"


(* Evaluate expression to an integer constant *)
and bool_expr_of_ast_expr
    abstractions
    context 
    pos
    ast_expr = 

  (* Evaluate expression *)
  let expr', abstractions' = 

    (* Evaluate expression to trie *)
    eval_ast_expr 
      abstractions
      context 
      ast_expr 

  in

  (* Check evaluated expression *)
  (match IdxTrie.bindings expr' with 

    (* Boolean expression without indexes *)
    | [ index, 
        ({ E.expr_init; 
           E.expr_step; 
           E.expr_type = t } as expr) ] when 
        index = I.empty_index && Type.equal_types t Type.t_bool -> 

      expr, abstractions'

    (* Expression is not Boolean or is indexed *)
    | _ -> 

      fail_at_position pos "Expression is not of Boolean type") 
  

(* Replace unguarded pres in expression with oracle constants and
   return extened abstraction 

   Keep arguments [expr] and [abstrations] in a pair so that we can
   apply this function directly to the result of [bool_expr_of_ast_expr].
*)
let close_ast_expr pos (expr, abstractions) = 
  
  (* Replace unguarded pres in expression with oracle constants *)
  let expr', oracles' =
    E.oracles_for_unguarded_pres
      pos
      abstractions.mk_oracle_for_state_var
      warn_at_position
      abstractions.new_oracles
      expr
  in
  
  (* Add oracle constants to abstraction *)
  let abstractions' = 
    { abstractions with new_oracles = oracles' } 
  in
  
  (* Return expression and modified abstraction *)
  (expr', abstractions') 
   

(* Keep arguments [expr] and [abstrations] in a pair so that we can
   apply this function directly to the result of
   [bool_expr_of_ast_expr]. *)
let close_indexed_ast_expr pos (expr, abstractions) = 
      
  (* Replace unguarded pres with oracle constants *)
  let expr', abstractions' = 
    IdxTrie.fold 

      (fun index expr (accum, abstractions) -> 

         let expr', abstractions' = 
           close_ast_expr pos (expr, abstractions)
         in

         (* Return expression and modified abstraction *)
         (IdxTrie.add index expr' accum, abstractions'))

      expr
      (IdxTrie.empty, abstractions)
  in
 
  (expr', abstractions')


(* ******************************************************************** *)
(* Arrays helpers                                                       *)
(* ******************************************************************** *)


(* Return a list of index variables for any list *)
let index_vars_of_list l = 

  let rec index_vars' accum = function 
    | [] -> List.rev accum
    | h :: tl -> 
      index_vars' 
        ((E.mk_state_var_of_ident
            false
            true
            I.empty_index
            (I.push_int_index
               (Numeral.of_int (List.length accum))
               I.index_ident)
            Type.t_int) :: accum)
        tl
  in

  index_vars' [] l



(* Take a tuple expression [a, b, c] and convert it to 
   if v=0 then a else if v=1 then b else c *)
let array_of_tuple pos index_vars expr =  

  (* Create map of conditions to expresssions per remaining index *)
  let expr' = 
    IdxTrie.fold
      (fun index expr accum -> 

         let rec aux a vl il = match vl, il with

           (* Condition for all index variables created *)
           | [], _ -> 

             (* Lookup previous expressions for remaining index *)
             let m = 
               try
                 IdxTrie.find (I.index_of_one_index_list il) accum
               with Not_found -> [] 
             in

             (* Add condition and value *)
             IdxTrie.add
               (I.index_of_one_index_list il)
               ((List.fold_left E.mk_and E.t_true a, expr) :: m)
               accum

           (* First index variable and first index of expression *)
           | index_var :: vtl, I.IntIndex i :: itl -> 

             (* Add equality between variable and index to condition *)
             aux
               ((E.mk_eq 
                   (E.mk_var index_var E.base_clock) 
                   (E.mk_int Numeral.(of_int i)))
                :: a)
               vtl 
               itl

           | _ -> 

             fail_at_position 
               pos
               (Format.asprintf 
                  "Invalid expression for array")

         in

         (* Associate condition on indexes with value *)
         aux [] index_vars (I.split_index index))

      expr
      IdxTrie.empty
  in

  (* Convert maps of conditions to expression to if-then-else
     expression *)
  IdxTrie.map
    (fun t -> 
       let rec aux = function
         | [] -> assert false

         (* Last or only condition *)
         | (c, e) :: [] -> e

         (* If condition, then expression, recurse for else *)
         | (c, e) :: tl -> E.mk_ite c e (aux tl)
       in
       aux t)
    expr'


(* ******************************************************************** *)
(* Type declarations                                                    *)
(* ******************************************************************** *)
    
(* Evalute a parsed type expression to a trie of types of indexes *)
let rec eval_ast_type ({ type_of_ident } as context) array_bounds = function

  (* Basic type bool, add to empty trie with empty index *)
  | A.Bool pos -> 

    IdxTrie.add I.empty_index (Type.t_bool, array_bounds) IdxTrie.empty 


  (* Basic type integer, add to empty trie with empty index *)
  | A.Int pos -> 

    IdxTrie.add I.empty_index (Type.t_int, array_bounds) IdxTrie.empty 


  (* Basic type real, add to empty trie with empty index *)
  | A.Real pos -> 

    IdxTrie.add I.empty_index (Type.t_real, array_bounds) IdxTrie.empty 


  (* Integer range type, constructed from evaluated expressions for
     bounds, and add to empty trie with empty index needs

     TODO: should allow constant node arguments as bounds, but then
     we'd have to check if in each node call the lower bound is less
     than or equal to the upper bound. *)
  | A.IntRange (pos, lbound, ubound) -> 

    (* Evaluate expressions for bounds to constants *)
    let const_lbound, const_ubound = 
      (int_const_of_ast_expr context pos lbound, 
       int_const_of_ast_expr context pos ubound) 
    in

    (* Add to empty trie with empty index *)
    IdxTrie.add 
      I.empty_index
      (Type.mk_int_range const_lbound const_ubound, array_bounds)
      IdxTrie.empty 


  (* Enum type needs to be constructed *)
  | A.EnumType (pos, enum_elements) -> 

    fail_at_position pos "Enum types not supported" 


  (* User-defined type, look up type in defined types, return subtrie
     of starting with possibly indexed identifier *)
  | A.UserType (pos, ident) -> 

    (try 

       (* Find subtrie of types starting with identifier *)
       ITrie.find_prefix ident type_of_ident 

     with Not_found -> 

       fail_at_position 
         pos
         (Format.asprintf 
            "Type %a is not declared" 
            (I.pp_print_ident false) ident))


  (* Record type, return trie of indexes in record *)
  | A.RecordType (pos, record_fields) -> 

    (* Take all record fields *)
    List.fold_left

      (* Each index has a separate type *)
      (fun a (i, t) -> 

         (* Take all indexes and their defined types *)
         IdxTrie.fold

           (fun j t a -> 

              (* Add index of record field to index of type and add to
                 trie *)
              IdxTrie.add
                (I.push_index_to_index (I.index_of_ident i) j)
                t 
                a)

           (* Evaluate type expression for field to a trie *)
           (eval_ast_type context array_bounds t)

           (* Add to trie in accumulator *)
           a)

      (* Start with empty trie *)
      IdxTrie.empty

      record_fields

  (* Tuple type, return trie of indexes in tuple fields *)
  | A.TupleType (pos, tuple_fields) -> 

    snd

      (* Take all tuple fields in order *)
      (List.fold_left

         (* Count up index of field, each field has a separate type *)
         (fun (i, a) t -> 

            (* Increment counter for field index *)
            (Numeral.succ i,

             (* Take all indexes and their defined types *)
             IdxTrie.fold 

               (fun j t a -> 

                  (* Add index of tuple field to index of type and add
                     to trie *)
                  IdxTrie.add
                    (I.push_index_to_index (I.mk_int_index i) j)
                    t 
                    a)

               (* Evaluate type expression for field to a map of index
                  to type *)
               (eval_ast_type context array_bounds t)

               (* Add to trie in accumulator *)
               a))

         (* Start with field index zero and empty trie *)
         (Numeral.zero, IdxTrie.empty)

         tuple_fields)


  (* Array type, return trie of indexes in tuple fields *)
  | A.ArrayType (pos, (type_expr, size_expr)) -> 

    (* Evaluate size of array *)
    let array_size = 

      try 

        (* Expression must evaluate without indexes *)
        IdxTrie.find
          I.empty_index
          (fst 
             (eval_ast_expr
                (void_abstraction_context pos)
                context
                size_expr))

      with Not_found -> 

        fail_at_position 
          pos
          (Format.asprintf 
             "Invalid expression for array size")

    in

    (* Evaluate type expression for elements*)
    let element_type = eval_ast_type context array_bounds type_expr in

    (* Add array bounds to type *)
    IdxTrie.map
      (fun (t, b) -> (t, array_size :: b))
      element_type
    



(* Return true if type [t] has been declared in the context *)
let type_in_context { type_of_ident } t = 

  (* Check if [t] is declared *)
  (ITrie.mem t type_of_ident) 


(* Return true if identifier [i] has been declared, raise an
   exception if the identifier is reserved. *)
let ident_in_context { expr_of_ident } i = 

  if 

    (* Identifier must not be reserved *)
    I.ident_is_reserved i

  then
    
    raise 
      (Invalid_argument 
         (Format.asprintf 
            "Identifier %a is reserved internal use" 
            (I.pp_print_ident false) i))

  else

    (* In type context or a nested identifier *)
    (ITrie.mem i expr_of_ident) 



(* Add type declaration for an alias type to a context *)
let add_alias_type_decl 
    ({ type_of_ident } as context) 
    pos
    ident
    ident_type =

  (* Add all indexes of type to identifier and add to trie *)
  let type_of_ident' = 
    IdxTrie.fold
      (fun i t a -> ITrie.add (I.push_index i ident) t a)
      (eval_ast_type context [] ident_type)
      type_of_ident
  in

  (* Add association of type identifier with indexes to types *)
  { context with type_of_ident = type_of_ident' }


(* ******************************************************************** *)
(* Constant declarations                                                *)
(* ******************************************************************** *)


(* Add a typed or untyped constant declaration to the context *)
let add_typed_const_decl
    ident 
    ({ type_of_ident; expr_of_ident } as context) 
    pos
    expr 
    type_expr =

  try 

    (* Evaluate expression, must not generate new abstractions from
       node calls *)
    let expr_val, abstractions = 
      eval_ast_expr 
        (void_abstraction_context pos)
        context 
        expr 
    in

    (match type_expr with 

      (* No type given *)
      | None -> ()

      (* Check if type of expression matches given type *)
      | Some t -> 

        (* Evaluate type expression *)
        let type_expr' = eval_ast_type context [] t in 

        (* Check if type of expression is a subtype of the defined
           type at each index *)
        IdxTrie.iter2
          (fun _ (_, def_type) { E.expr_type } ->
             if not (Type.check_type expr_type def_type) then
               raise E.Type_mismatch)
          type_expr'
          expr_val);

    (* Add expressions for indexes of identifier to trie *)
    let expr_of_ident' = 
      IdxTrie.fold2
        (fun i (b, _) e a -> 
           ITrie.add 
             (I.push_index i ident) 
             (array_of_tuple pos (index_vars_of_list b)  e 
             a))
        expr_val
        expr_of_ident
    in

    { context with expr_of_ident = expr_of_ident' }


  (* Type mismatch if sets indexes are not equal *)
  with Invalid_argument _ | E.Type_mismatch ->

    fail_at_position pos "Type mismatch for expressions"


(* Add declaration of constant to context *)
let add_const_decl context = function 

  (* Free constant *)
  | A.FreeConst (pos, ident, _) -> 

    fail_at_position pos "Free constants not supported"


  (* Constant without type *)
  | A.UntypedConst (pos, ident, expr) -> 
    add_typed_const_decl ident context pos expr None

  (* Constant with given type *)
  | A.TypedConst (pos, ident, expr, type_expr) -> 
    add_typed_const_decl ident context pos expr (Some type_expr)
  

(* ******************************************************************** *)
(* Node declarations                                                    *)
(* ******************************************************************** *)


(* Add declaration of an identifier to trie and to context *)
let add_node_decl_to_trie
    ({ expr_of_ident } as context)
    state_var_trie
    state_var_source
    scope
    ident
    is_const
    is_input
    ident_types =

  (* Get next index at root of trie *)
  let next_top_idx = next_top_index_of_idx_trie state_var_trie in

  (* Create state variable, add as expression with index to map of
     identifiers and as state variable to node inputs *)
  let expr_of_ident', state_var_trie' = 

    IdxTrie.fold

      (fun index t (expr_of_ident, state_var_trie) ->
         
         (* Add index to identifier *)
         let ident' = I.push_back_index index ident in

         (* Add index to highest index of inputs *)
         let index' = 
           I.push_back_index_to_index
             index
             next_top_idx
         in

         (* Create state variable as input and contant *)
         let state_var = 
           E.mk_state_var_of_ident
             is_input
             is_const
             scope
             ident' 
             t
         in

         (* State variable is an input *)
         E.set_state_var_source state_var state_var_source;

         (* Add expression to trie of identifier *)
         (ITrie.add ident' (E.mk_var state_var E.base_clock) expr_of_ident,

          (* Add state variable to trie of inputs *)
          IdxTrie.add index' state_var state_var_trie))
      
      ident_types
      (expr_of_ident, state_var_trie)

  in
  
  ({ context with expr_of_ident = expr_of_ident' }, 
   state_var_trie')
     

(* Add declaration of an identifier to list and to context *)
let add_node_decl_to_list
    ({ expr_of_ident } as context)
    state_var_list
    state_var_source
    scope
    ident
    is_const
    is_input
    ident_types =

  (* Create state variable, add as expression with index to map of
     identifiers and as state variable to node inputs *)
  let expr_of_ident', state_var_list' = 

    IdxTrie.fold

      (fun index t (expr_of_ident, state_var_list) ->
         
         (* Add index to identifier *)
         let ident' = I.push_back_index index ident in

         (* Create state variable as input and contant *)
         let state_var = 
           E.mk_state_var_of_ident
             is_input
             is_const
             scope
             ident' 
             t
         in

         (* State variable is an input *)
         E.set_state_var_source state_var state_var_source;

         (* Add expression to trie of identifier *)
         (ITrie.add ident' (E.mk_var state_var E.base_clock) expr_of_ident,

          (* Add state variable to list *)
          state_var :: state_var_list))
      
      ident_types
      (expr_of_ident, state_var_list)

  in
  
  ({ context with expr_of_ident = expr_of_ident' }, 
   state_var_list')
     

(* Add declaration of a node input to contexts *)
let add_node_input_decl
    context
    ({ N.inputs = node_inputs; N.name = node_ident } as node)
    pos
    ident
    is_const
    ident_types =

  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Add declaration of input to trie and context *)
  let context', node_inputs' = 
    add_node_decl_to_trie
      context
      node_inputs
      E.Input
      scope
      ident
      is_const
      true
      ident_types
  in

  (* Return context and node with declaration *)
  (context', { node with N.inputs = node_inputs' })
     

(* Add declaration of a node input to contexts *)
let add_node_output_decl
    context
    ({ N.outputs = node_outputs; N.name = node_ident } as node)
    pos
    ident
    ident_types =

  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Add declaration of output to trie and context *)
  let context', node_outputs' = 
    add_node_decl_to_trie
      context
      node_outputs
      E.Output
      scope
      ident
      false
      false
      ident_types
  in

  (* Return context and node with declaration *)
  (context', { node with N.outputs = node_outputs' })


(* Add declaration of a node local variable to contexts *)
let add_node_var_decl
    context
    ({ N.name = node_ident; N.locals = node_locals } as node)
    pos
    ident
    ident_types =
     
  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Add declaration of local variable to list and context *)
  let context', node_locals' = 
    add_node_decl_to_list
      context
      node_locals
      (if A.is_dummy_pos pos then E.Abstract else E.Local)
      scope
      ident
      false
      false
      ident_types
  in

  (* Return context and node with declaration *)
  (context', { node with N.locals = node_locals' })

    
(* Add declaration of an oracle input to contexts *)
let add_node_oracle_decl
    context
    ({ N.name = node_ident; N.oracles = node_oracles } as node)
    pos
    ident
    ident_types =
     
  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Add declaration of oracle to list and context *)
  let context', node_oracles' = 
    add_node_decl_to_list
      context
      node_oracles
      E.Oracle
      scope
      ident
      true
      true
      ident_types
  in

  (* Return context and node with declaration *)
  (context', { node with N.oracles = node_oracles' })


(* Add declaration of an observer output to contexts *)
let add_node_observer_decl
    ({ expr_of_ident } as context)
    ({ N.observers = node_observers; 
       N.name = node_ident } as node)
    ident
    state_var =

  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Type of observer *)
  let state_var_type = StateVar.type_of_state_var state_var in

  (* Create state variable as constant and input *)
  let state_var' =
    E.mk_state_var_of_ident
      false
      false
      scope
      ident
      state_var_type
  in
  
  (* State variable is an oracle input variable *)
  E.set_state_var_source state_var E.Observer;

  (* Add expression to trie of identifier *)
  let expr_of_ident' = 
    ITrie.add ident (E.mk_var state_var E.base_clock) expr_of_ident 
  in

  (* Add state variable to observers *)
  let node_observers' = state_var' :: node_observers in

  ({ context with expr_of_ident = expr_of_ident' }, 
   { node with N.observers = node_observers' })


(* Add all node inputs to contexts *)
let rec parse_node_inputs context node = function

  (* All inputs parsed, return in original order *)
  | [] -> (context, node)

  (* Identifier must not be declared *)
  | (pos, ident, _, _, _) :: _ when 

      (try 
         ident_in_context context ident 
       with Invalid_argument e -> 
         fail_at_position pos e) -> 

    fail_at_position 
      pos
      (Format.asprintf 
         "Node input %a already declared" 
         (I.pp_print_ident false) ident)

  (* Input on the base clock *)
  | (pos, ident, ast_type, A.ClockTrue, is_const) :: tl -> 

    (* Evaluate type expression *)
    let ident_types = eval_ast_type context ast_type in
  
    (* Add declaration of possibly indexed type to contexts *)
    let context', node' = 
      add_node_input_decl
        context
        node
        pos
        ident
        is_const
        ident_types
    in

    (* Continue with following inputs *)
    parse_node_inputs context' node' tl

  | (pos, _, _, _, _) :: _ -> 

    fail_at_position pos "Clocked node inputs not supported"


(* Add all node outputs to contexts *)
let rec parse_node_outputs context node = function

  (* All outputs parsed, return in original order *)
  | [] -> (context, node)

  (* Identifier must not be declared *)
  | (pos, ident, _, _) :: _ when       
      
      (try 
         ident_in_context context ident 
       with Invalid_argument e -> 
         fail_at_position pos e) -> 
    
    fail_at_position 
      pos
      (Format.asprintf 
         "Node output %a already declared" 
         (I.pp_print_ident false) ident)

  (* Output on the base clock *)
  | (pos, ident, ast_type, A.ClockTrue) :: tl -> 

    (* Evaluate type expression *)
    let ident_types = eval_ast_type context ast_type in

    (* Add declaration of possibly indexed type to contexts *)
    let context', node' = 
      add_node_output_decl
        context
        node
        pos
        ident
        ident_types
    in

    (* Continue with following outputs *)
    parse_node_outputs context' node' tl

  | (pos, _, _, _) :: _ -> 

    fail_at_position pos "Clocked node outputs not supported" 


(* Add all node local declarations to contexts *)
let rec parse_node_locals context node = function

  (* All local declarations parsed, order does not matter *)
  | [] -> (context, node)


  (* Identifier must not be declared *)
  | A.NodeVarDecl (pos, (_, ident, _, _)) :: _ 
  | A.NodeConstDecl (pos, A.FreeConst (_, ident, _)) :: _
  | A.NodeConstDecl (pos, A.UntypedConst (_, ident, _)) :: _
  | A.NodeConstDecl (pos, A.TypedConst (_, ident, _, _)) :: _ when 

      (try 
         ident_in_context context ident 
       with Invalid_argument e -> 
         fail_at_position pos e) -> 
    
    fail_at_position 
      pos
      (Format.asprintf 
         "Node local variable or constant %a already declared" 
         (I.pp_print_ident false) ident)


  (* Local variable on the base clock *)
  | A.NodeVarDecl (pos, (_, ident, var_type, A.ClockTrue)) :: tl -> 

    (* Evaluate type expression *)
    let ident_types = eval_ast_type context var_type in

    (* Add declaration of possibly indexed type to contexts *)
    let context', node' = 
      add_node_var_decl
        context
        node
        pos
        ident
        ident_types
    in
    
    (* Continue with following outputs *)
    parse_node_locals 
      context'
      node'
      tl

  (* Local variable not on the base clock *)
  |  A.NodeVarDecl (pos, (_, ident, _, _)) :: _ -> 

    fail_at_position 
      pos 
      (Format.asprintf 
         "Clocked node local variables not supported for %a" 
         (I.pp_print_ident false) ident)


  (* Local constant *)
  | A.NodeConstDecl (pos, const_decl) :: tl -> 

    (* Add declaration of constant to context *)
    let context' = add_const_decl context const_decl in

    (* Continue with following outputs *)
    parse_node_locals context' node tl


(* Add an expression as a property *)
let rec property_to_node 
    ({ mk_state_var_for_expr; new_vars } as abstractions)
    context
    node
    pos
    expr =

  (* State variable for property and changed environment *)
  let abstractions', state_var =

    if 

      (* Property is a state variable at current offset? *)
      E.is_var expr

    then 

      (* State variable of expression *)
      let state_var = E.state_var_of_expr expr in

      (* No abstraction necessary *)
      (abstractions, state_var)

    else

      (* State variable of abstraction variable *)
      let state_var, new_vars' = 
        mk_state_var_for_expr false new_vars expr 
      in
      
      (* State variable is a locally abstracted variable *)
      E.set_state_var_source state_var E.Abstract;

      (* Property is new state variable *)
      ({ abstractions with new_vars = new_vars' }, state_var)
      
  in

  (* Add declatation of variable to observers *)
  let node_observers' = node.N.observers @ [state_var] in

  (* Remove declaration of variable from locals *)
  let node_locals' = 
    List.filter
      (fun sv -> not (StateVar.equal_state_vars sv state_var))
      node.N.locals
  in

  (* Remove declaration of variable from outputs *)
  let node_outputs' = 
    IdxTrie.filter
      (fun _ sv -> not (StateVar.equal_state_vars sv state_var))
      node.N.outputs
  in

  (* Add property to node *)
  (abstractions',
   context, 
   { node with 
       N.props = (state_var :: node.N.props); 
       N.observers = node_observers';
       N.locals = node_locals';
       N.outputs = node_outputs' }
   )


(* Add an expression as an assertion *)
and assertion_to_node abstractions context node pos expr = 

  let node' = { node with N.asserts = expr :: node.N.asserts } in

  (abstractions, context, node')


(* Add an expression as a contact clause *)
and assumption_to_node abstractions context node pos ident expr =

  let node' = 
    { node with N.assumptions = (ident, expr) :: node.N.assumptions } 
  in

  (abstractions, context, node')


(* Add an expression as a contact clause *)
and guarantee_to_node abstractions context node pos ident expr =

  let node' = 
    { node with N.guarantees = (ident, expr) :: node.N.guarantees } 
  in

  (abstractions, context, node')


(* Add equational definition of a variable *)
and equation_to_node 
    abstractions
    context 
    node 
    pos
    state_var
    indexes
    ({ E.expr_type } as expr) = 

  (* Replace unguarded pre with oracle constants *)
  let expr', oracles' = 
    E.oracles_for_unguarded_pres
      pos
      abstractions.mk_oracle_for_state_var
      warn_at_position
      abstractions.new_oracles
      expr
  in

  (* Type of state variable defined by expression *)
  let state_var_type = StateVar.type_of_state_var state_var in 

  (* Node with property added if subtyping cannot be inferred *)
  let abstractions', context', node' =

    if 

      (* Type must be a subtype of declared type *)
      Type.check_type expr_type state_var_type 

    then

      (* Nothing to add *)
      abstractions, context, node

    else

      (* Type of expression may not be subtype of declared type *)
      (match state_var_type, expr_type with 

        (* Declared type is integer range, expression is of type
           integer *)
        | t, s 
          when Type.is_int_range t && (Type.is_int s || Type.is_int_range s) -> 

          let (lbound, ubound) = Type.bounds_of_int_range t in

          (* Value of expression is in range of declared type: 
             lbound <= expr and expr <= ubound *)
          let range_expr = 
            (E.mk_and 
               (E.mk_lte (E.mk_int lbound) expr) 
               (E.mk_lte expr (E.mk_int ubound)))
          in

          warn_at_position
            pos
            "Cannot determine correctness of subrange type, \
             adding constraint as property.";

          (* Add property to node *)
          property_to_node 
            abstractions 
            context 
            node
            A.dummy_pos 
            range_expr

        | t, s -> 

          fail_at_position
            pos
            (Format.asprintf 
               "Type mismatch between variable of type %a and expression of type %a"
               (E.pp_print_lustre_type false) state_var_type
               (E.pp_print_lustre_type false) expr_type))

  in

  (* Add oracle constants to abstraction *)
  let abstractions' = 
    { abstractions' with new_oracles = oracles' } 
  in

  (* Add equation and abstractions *)
  (abstractions',
   context', 
   { node' with 
       N.equations = (state_var, (indexes, expr')) :: node'.N.equations })


(* Parse a statement (equation, assert or annotation) in a node *)
let rec parse_node_equations 
    ({ mk_fresh_state_var } as abstractions)
    ({ expr_of_ident } as context) 
    ({ N.name = node_ident;
       N.outputs = node_outputs;
       N.locals = node_locals } as node ) = 

  function

    (* No more statements *)
    | [] -> abstractions, context, node 

    (* Assertion *)
    | A.Assert (pos, ast_expr) :: tl -> 

      (* Evaluate Boolean expression and guard all pre operators *)
      let expr', abstractions = 
        close_ast_expr
          pos
          (bool_expr_of_ast_expr 
             abstractions
             context 
             pos
             ast_expr)
      in

      (* Add assertion to node *)
      let abstractions', context', node' = 
        assertion_to_node abstractions context node pos expr'
      in

      (* Continue with next node statements, and restart with previous
         empty abstractions *)
      parse_node_equations 
        abstractions'
        context'
        node' 
        tl

    (* Property annotation *)
    | A.AnnotProperty (pos, ast_expr) :: tl -> 

      (* Evaluate Boolean expression and guard all pre operators *)
      let expr', abstractions = 
        close_ast_expr
          pos
          (bool_expr_of_ast_expr 
             abstractions
             context 
             pos
             ast_expr)
      in

      (* Add assertion to node *)
      let abstractions', context', node' = 
        property_to_node abstractions context node pos expr'
      in

      (* Continue with next node statements, and restart with previous
         empty abstractions *)
      parse_node_equations 
        abstractions'
        context'
        node' 
        tl


    (* Equations with possibly more than one variable on the left-hand side

       The expression is without node calls, those have been
       abstracted *)
    | A.Equation (pos, lhs, ast_expr) :: tl -> 

(*
      debug lustreSimplify
          "parse_node_equation %a"
          A.pp_print_node_equation (A.Equation (pos, lhs, ast_expr))
      in
*)

      (* State variables and types of their assigned expressions *)
      let eq_lhs, indexes, context' = match lhs with 

        | A.StructDef (pos, struct_items) -> 

          let eq_lhs = 

            List.fold_left
              (function eq_lhs -> function 

                 (* Left-hand side is a single identifier *)
                 | A.SingleIdent (pos, ident) -> 

                   (* Trie of expressions for indexes of identifier *)
                   let ident_exprs = 

                     try 

                       (* Get expressions for each index of identifier *)
                       ITrie.find_prefix
                         ident
                         expr_of_ident

                     with Not_found -> 

                       fail_at_position 
                         pos 
                         "Undefined variable in assignment" 

                   in

                   (* Get next top index of accumulator, use empty
                      index if left-hand side contains only one
                      variable *)
                   let top_index =
                     match struct_items with 
                       | [] -> assert false
                       | [_] -> I.empty_index
                       | _ -> next_top_index_of_idx_trie eq_lhs
                   in

                   (* Add types of indexes to accumulator *)
                   let eq_lhs' = 
                     IdxTrie.fold
                       (fun i e a -> 

                          (* Expression must be a variable *)
                          if not (E.is_var e) then 

                            fail_at_position 
                              pos 
                              "Not assigning to variable";

                          (* Get state variable from expression *)
                          let state_var = 
                            E.state_var_of_expr e
                          in

                          if 

                            (* State variable must be an output *)
                            IdxTrie.exists 
                              (fun _ sv -> 
                                 StateVar.equal_state_vars sv state_var)
                              node_outputs

                            || 

                            (* Or state variable must be a local variable *)
                            List.exists 
                              (fun sv -> 
                                 StateVar.equal_state_vars sv state_var)
                              node_locals

                          then


                            (* Add type of state variable to accumulator *)
                            IdxTrie.add
                              (I.push_back_index_to_index top_index i)
                              state_var
                              a

                          else

                            fail_at_position 
                              pos 
                              "Assignment to neither output nor \
                               local variable")
                       ident_exprs
                       eq_lhs
                   in

                   (* Return state variables on left-hand side *)
                   eq_lhs'

                 (* TODO: Structural assignments *)
                 | _ -> 
                   fail_at_position
                     pos
                     "Structural assignments not supported")
              IdxTrie.empty
              struct_items

          in

          (eq_lhs, [], context)

        | A.ArrayDef (pos, ident, indexes) -> 

          let indexes', context' = 
            List.fold_left 
              (fun (indexes', context') index_ident -> 

                 (* Fresh state variable for index *)
                 let state_var = 
                   mk_fresh_state_var 
                     false 
                     Type.t_int
                 in

                 (* Associate index identifier with state variable *)
                 let expr_of_ident' = 
                   ITrie.add
                     ident
                     (E.mk_var state_var E.base_clock)
                     expr_of_ident
                 in

                 (* Get array size from trie *)
                 let array_size = 

                   try 

                     top_int_index_of_idx_trie

                       (try 

                          ITrie.find_prefix 
                            index_ident 
                            expr_of_ident

                        with Not_found ->

                          fail_at_position
                            pos
                            "Undefined variable in assignment")

                   with _ -> 

                     fail_at_position
                       pos
                       "Variable is not an array in assignment"

                 in

                 (indexes))

                 indexes
          in

          eq_lhs, indexes', context'

      in

      (* Evaluate expression and guard all pre operators *)
      let eq_rhs, abstractions = 
        close_indexed_ast_expr
          pos
          (eval_ast_expr 
             abstractions
             context' 
             ast_expr)

      in

(*
          debug lustreSimplify
              "@[<v>abstractions:@,%a@]"
              pp_print_abstraction_context abstractions
          in
*)


      (* Add all equations to node *)
      let abstractions', context', node' = 

        try 

          IdxTrie.fold2
            (fun _ state_var expr (abstractions, context, node) -> 

               (* Add equation to node *)
               equation_to_node 
                 abstractions

                 (* Use previous with indexes removed *)
                 context 

                 node
                 pos
                 state_var
                 indexes
                 expr)

            eq_lhs
            eq_rhs

            (abstractions, context, node)

        with Invalid_argument _ -> 

          fail_at_position 
            pos
            "Type mismatch in equation"

      in

      (* Continue, and restart with previous empty abstractions *)
      parse_node_equations 
        abstractions'
        context'
        node'
        tl


    (* Annotation for main node *)
    | A.AnnotMain :: tl -> 

      parse_node_equations 
        abstractions
        context 
        { node with N.is_main = true }
        tl

    (* Assumption *)
    | A.Assume (pos, ident, expr) :: tl -> 

      (* Evaluate Boolean expression and guard all pre operators *)
      let expr', abstractions = 
        close_ast_expr
          pos
          (bool_expr_of_ast_expr 
             abstractions
             context 
             pos
             expr)
      in

      (* Add assertion to node *)
      let abstractions', context', node' = 
        assumption_to_node abstractions context node pos ident expr'
      in

      (* Continue with next contract clauses, and restart with
         previous empty abstractions *)
      parse_node_equations
        abstractions'
        context' 
        node'
        tl


    (* Guarantee *)
    | A.Guarantee (pos, ident, expr) :: tl -> 

      (* Evaluate Boolean expression and guard all pre operators *)
      let expr', abstractions = 
        close_ast_expr
          pos
          (bool_expr_of_ast_expr 
             abstractions
             context 
             pos
             expr)
      in

      (* Add assertion to node *)
      let abstractions', context', node' = 
        guarantee_to_node abstractions context node pos ident expr'
      in

      (* Continue with next contract clauses, and restart with
         previous empty abstractions *)
      parse_node_equations
        abstractions'
        context' 
        node'
        tl


(* Add abstracted variables and node calls to context *)
let abstractions_to_context_and_node 
    ({ new_vars } as abstractions)
    context 
    node =

  (* Add declaration of variables to context

     Must add variables first, this may generate new abstractions from
     unguarded pres. *)
  let ({ new_oracles } as abstractions'), context', node' = 

    List.fold_left 
      (fun (abstractions, context, node) (state_var, expr) -> 

         (* Split scope from name of variable *)
         let ident, scope = 
           E.ident_of_state_var state_var
         in

         (* Add variable declaration to context *)
         let context', node' =
           add_node_var_decl
             context
             node
             A.dummy_pos
             ident
             (IdxTrie.add
                I.empty_index
                (StateVar.type_of_state_var state_var)
                IdxTrie.empty)
         in

         (* Add equation to node *)
         let abstractions', context', node' = 
           equation_to_node 
             abstractions context'
             node'
             A.dummy_pos 
             state_var 
             []
             expr 
         in

         (abstractions', context', node'))

      (abstractions, context, node)
      new_vars

  in

  (* Add declaration of oracle inputs to context *)
  let ({ new_calls } as abstractions'),  context', node' = 

    List.fold_left 
      (fun (abstractions, context, node) (state_var) -> 

         (* Split scope from name of variable *)
         let (ident, scope) = 
           E.ident_of_state_var state_var
         in

         (* Add oracle declaration to context *)
         let context', node' = 
           add_node_oracle_decl
             context
             node
             A.dummy_pos
             ident
             (IdxTrie.add
                I.empty_index
                (StateVar.type_of_state_var state_var)
                IdxTrie.empty)
         in
         
         (abstractions, context', node'))

      (abstractions', context', node')
      new_oracles

  in

  (* Add declaration of return variables of calls to context

     No need to iterate over observers, they will become observers of
     the calling node *)
  let ({ new_observers } as abstractions'), context', node' = 

    List.fold_left
      (fun 
        accum
        ({ N.call_returns = outputs;
           N.call_observers = observers;
           N.call_node_name = node_call_ident } as call) ->

         let abstractions', context', node' = 
           IdxTrie.fold
             (fun _ state_var (abstractions, context, node) -> 
                
                (* Split scope from name of variable *)
                let (ident, scope) = 
                  E.ident_of_state_var state_var
                in
                
                (* Add variable declaration to context *)
                let context', node' = 

                  if 

                    (* Variable is already declared as output or
                       local? *)
                    (IdxTrie.exists 
                       (fun _ sv -> 
                          StateVar.equal_state_vars sv state_var)
                       node.N.outputs)

                    || (List.exists 
                          (fun sv -> 
                             StateVar.equal_state_vars sv state_var)
                          node.N.locals)

                  then

                    (* Return context and node unchanged *)
                    (context, node)

                  else

                    (* Add new local variable to node *)
                    add_node_var_decl
                      context
                      node
                      A.dummy_pos
                      ident
                      (IdxTrie.add
                         I.empty_index
                         (StateVar.type_of_state_var state_var)
                         IdxTrie.empty)

                in

                abstractions, context', node')
             outputs
             accum
         in 
 
         (abstractions',
          context', 
          { node' with N.calls = call :: node'.N.calls }))

      (abstractions', context', node')
      new_calls

  in

  (* Add declaration of observer outputs to context *)
  let abstractions', context', node' = 

    List.fold_left 
      (fun (abstractions, context, node) (state_var) -> 

         (* Split scope from name of variable *)
         let (ident, scope) = 
           E.ident_of_state_var state_var
         in

         (* Add variable declaration to context and oracle input to node *)
         let context', node' = 
           add_node_observer_decl
             context
             node
             ident
             state_var
         in

         (abstractions, context', node'))

      (abstractions', context', node')
      new_observers

  in

  abstractions', context', node'


(* Return a LustreNode.t from a node LustreAst.node_decl *)
let parse_node  
    node_ident
    global_context
    inputs 
    outputs 
    locals 
    equations =

  (* Node name is scope for naming of variables *)
  let scope = I.index_of_ident node_ident in 

  (* Empty node *)
  let node = N.empty_node node_ident in

  (* Create a new state variable for abstractions *)
  let mk_fresh_state_var is_const state_var_type = 
    E.mk_fresh_state_var
      false
      is_const
      scope
      I.abs_ident
      state_var_type
      node.N.fresh_state_var_index
  in

  (* Create a new state variable for abstractions *)
  let mk_state_var_for_expr is_const new_vars ({ E.expr_type } as expr) = 

    try 

      (* Find previous definition of expression *)
      let state_var =
        E.ExprHashtbl.find
          node.N.expr_state_var_map
          expr
      in

      (* Return state variable and no new defintiion *)
      (state_var, new_vars)

    with Not_found ->

      (* Create a fresh state variable for definition *)
      let state_var =
        E.mk_fresh_state_var
          false
          is_const
          scope
          I.abs_ident
          expr_type
          node.N.fresh_state_var_index
      in

      (* Record definition of expression by state variable *)
      E.ExprHashtbl.add
        node.N.expr_state_var_map
        expr
        state_var;

      (* Return variable and add definition *)
      (state_var, ((state_var, expr) :: new_vars))

  in

  (* Create a new constant to guard pre operator on state variable *)
  let mk_oracle_for_state_var state_var = 

    try 

      (* Return oracle previously created *)
      StateVar.StateVarHashtbl.find  
        node.N.state_var_oracle_map
        state_var

    (* No oracle for state variable *)
    with Not_found -> 

      (* Create a fresh oracle *)
      let oracle = 
        E.mk_fresh_state_var
          true
          true
          scope
          I.oracle_ident
          (StateVar.type_of_state_var state_var)
          node.N.fresh_oracle_index
      in

      (* Map state variable to oracle *)
      StateVar.StateVarHashtbl.add
        node.N.state_var_oracle_map
        state_var
        oracle;

      (* Return fresh oracle *)
      oracle

  in

  (* Create a new oracle of type *)
  let mk_new_oracle oracle_type = 
    E.mk_fresh_state_var
      true
      true
      scope
      I.oracle_ident
      oracle_type
      node.N.fresh_oracle_index
  in

  (* Create a new variable observing a property of subnode *)
  let mk_new_observer = 
    let r = ref Numeral.(- one) in
    fun observer_type ->
      Numeral.incr r;
      E.mk_state_var_of_ident
        false
        false
        scope
        (I.push_int_index !r I.observer_ident)
        observer_type
  in

  (* Initial, empty abstraction context *)
  let empty_abstractions = 
    { scope;
      mk_fresh_state_var = mk_fresh_state_var;
      mk_state_var_for_expr = mk_state_var_for_expr;
      mk_oracle_for_state_var = mk_oracle_for_state_var;
      mk_new_oracle = mk_new_oracle;
      mk_new_observer = mk_new_observer;
      new_vars = [];
      new_calls = [];
      new_oracles = [];
      new_observers = [] }
  in

  (* Parse inputs, add to global context and node context *)
  let context', node' = 
    parse_node_inputs global_context node inputs
  in

  (* Parse outputs, add to local context and node context *)
  let context', node' = 
    parse_node_outputs
      context' 
      node' 
      outputs
  in

  (* Parse local declarations, add to local context and node context *)
  let context', node' = 
    parse_node_locals context' node' locals
  in

  (* Parse equations and assertions, add to node context, local
     context is not modified *)
  let abstractions', context', node' = 
    parse_node_equations 
      empty_abstractions
      context' 
      node' 
      equations
  in

  (* Add abstractions to context and node *)
  let _, _, node' =
    abstractions_to_context_and_node 
      abstractions' 
      context' 
      node' 
  in

  (* Simplify by substituting variables that are aliases *)
  N.solve_eqs_node_calls node'


(* ******************************************************************** *)
(* Main                                                                 *)
(* ******************************************************************** *)

(* Iterate over a list of declarations and return a context *)
let rec declarations_to_nodes'
    ({ type_of_ident; expr_of_ident; nodes } as global_context) = 

  function

    (* All declarations processed, return result *)
    | [] -> global_context


    (* Declaration of a type as alias or free *)
    | (A.TypeDecl (pos, (A.AliasType (_, ident, _) as type_decl))) :: decls
    | (A.TypeDecl (pos, (A.FreeType (_, ident) as type_decl))) :: decls -> 

      if       

        (* Type t must not be declared *)
        type_in_context global_context ident

      then

        fail_at_position 
          pos
          (Format.asprintf 
             "Type %a is redeclared" 
             (I.pp_print_ident false) ident);

      (* Change context with alias type declaration *)
      let global_context' = match type_decl with 

        (* Identifier is an alias for a type *)
        | A.AliasType (_, ident, type_expr) -> 

          (* Add alias type declarations for the possibly indexed
             type expression *)
          let global_context' = 
            add_alias_type_decl
              global_context
              pos
              ident
              type_expr
          in

          (* Return changed context and unchanged declarations *)
          global_context'

        (* Identifier is a free type *)
        | A.FreeType (_, ident) -> 

          fail_at_position pos "Free types not supported"

      in

      (* Recurse for next declarations *)
      declarations_to_nodes' global_context' decls


    (* Declaration of a typed, untyped or free constant *)
    | (A.ConstDecl (pos, (A.FreeConst (_, ident, _) as const_decl))) :: decls 
    | (A.ConstDecl (pos, (A.UntypedConst (_, ident, _) as const_decl))) :: decls 
    | (A.ConstDecl (pos, (A.TypedConst (_, ident, _, _) as const_decl))) :: decls ->

      if

        (try 

           (* Identifier must not be declared *)
           ident_in_context global_context ident 

         (* Fail if reserved identifier used *)
         with Invalid_argument e -> fail_at_position pos e)

      then

        (* Fail if identifier already declared *)
        fail_at_position 
          pos 
          (Format.asprintf 
             "Identifier %a is redeclared as constant" 
             (I.pp_print_ident false) ident);

      (* Change context with constant declaration *)
      let global_context' = 
        add_const_decl global_context const_decl 
      in

      (* Recurse for next declarations *)
      declarations_to_nodes' global_context' decls


    (* Node declaration without parameters *)
    | (A.NodeDecl 
         (pos, 
          (node_ident, 
           [], 
           inputs, 
           outputs, 
           locals, 
           equations))) :: decls ->

      (try 

        (* Add node declaration to global context *)
        let node_context = 
          parse_node
            node_ident
            global_context 
            inputs 
            outputs
            locals
            equations 
        in
        
        (* Recurse for next declarations *)
        declarations_to_nodes' 
          { global_context with 
              nodes = node_context :: nodes }
          decls

       (* Node may be forward referenced *)
       with Node_not_found (ident, pos) -> 

        if 

          (* Is the referenced node declared later? *)
          List.exists 
            (function 
              | A.NodeDecl (_, (i, _, _, _, _, _)) when i = ident -> true 
              | _ -> false)
            decls

        then

          fail_at_position 
            pos 
            (Format.asprintf 
               "Node %a is forward referenced" 
               (I.pp_print_ident false) ident)
      
        else
          
          fail_at_position
            pos
            (Format.asprintf 
               "Node %a is not defined" 
               (I.pp_print_ident false) ident))


    (* Node declaration without parameters *)
    | (A.FuncDecl (pos, _)) :: _ ->

      fail_at_position pos "Functions not supported"


    (* Node declaration without parameters *)
    | (A.NodeParamInst (pos, _)) :: _
    | (A.NodeDecl (pos, _)) :: _ ->

      fail_at_position pos "Parametric nodes not supported" 


(* Iterate over the declarations and return the nodes *)
let declarations_to_nodes decls = 

  (* Extract nodes from produced global context *)
  let { nodes } as global_context = 
    declarations_to_nodes' init_lustre_context decls 
  in

  (* Return nodes *)
  nodes


(* Standalone Lustre simplifier for testing *)
let main () = 

  Debug.initialize ();
  Debug.enable "lustreSimplify" Format.std_formatter;

  (* Create lexing buffer *)
  let lexbuf = Lexing.from_function LustreLexer.read_from_lexbuf_stack in

  (* Read from file or standard input *)
  let in_ch, curdir = 
    if Array.length Sys.argv > 1 then 
      (let fname = Sys.argv.(1) in 

       let zero_pos = 
         { Lexing.pos_fname = fname;
           Lexing.pos_lnum = 1;
           Lexing.pos_bol = 0;
           Lexing.pos_cnum = 0 } 
       in
       lexbuf.Lexing.lex_curr_p <- zero_pos; 

       let curdir = 
         Filename.dirname fname
       in

       open_in fname, curdir) 
    else
      (stdin, Sys.getcwd ())
  in

  (* Initialize lexing buffer with channel *)
  LustreLexer.lexbuf_init in_ch curdir;

  (* Lustre file is a list of declarations *)
  let declarations = 

    try 

      (* Parse file to list of declarations *)
      LustreParser.main LustreLexer.token lexbuf 

    with 
      | LustreParser.Error ->

        let 
          { Lexing.pos_fname; 
            Lexing.pos_lnum; 
            Lexing.pos_bol; 
            Lexing.pos_cnum } = 
          Lexing.lexeme_start_p lexbuf 
        in

        Format.printf 
          "Syntax error in line %d at column %d in %s: %s@." 
          pos_lnum
          (pos_cnum - pos_bol)
          pos_fname
          (Lexing.lexeme lexbuf);

        exit 1

  in

  (* Simplify declarations to a list of nodes *)
  let nodes = declarations_to_nodes declarations in

  Format.printf 
    "@[<v>Before slicing@,%a@]@."
    (pp_print_list (LustreNode.pp_print_node false) "@,") 
    nodes

;;

main ()



(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
  
