open Dolmen

module KindTerm = Term

(* Instantiate a module for parsing logic languages *)
module Loc = Std.Loc
module Id = Std.Id
module Term = Std.Term
module Statement = Std.Statement

type loc = Loc.t
type id = Id.t
type term = Term.t
type statement = Statement.t

exception UnsupportedZ3Symbol of string


(* Removes optional quantifier for lists. None is replaces with empty list *)
let opt_list_to_list l =
  match l with
    | Some l -> l
    | None -> []

(* Returns a string representation of a Dolmen id *)
let dolmen_id_to_string id =
  let name = Std.Id.name id in
  match name with
  | Std.Name.Simple n -> n
  | _ -> "<TODO ADD SUPPORT FOR NON_SIMPLE DOLMEN NAMES>"

let dolmen_id_to_hstring id = 
  (HString.mk_hstring (dolmen_id_to_string id))

(* Returns a string representation of a Dolmen id if it exists, returns a generic string otherwise *)
let dolmen_opt_id_to_string id =
  match id with 
  | Some id -> dolmen_id_to_string id
  | None -> "<ID: None>"

(* Return the kind2 Type of a Dolmen builtin *)
(* Currently missing support for arrays *)
let type_of_dolmen_builtin = function 
  | Term.Int -> Type.t_int
  | Term.Real -> Type.t_real
  | Term.Bool -> Type.t_bool 
  (* TODO Add support for arrays*)
  | other -> 
    raise
      (Invalid_argument 
         (Format.asprintf 
            "Sort %a not supported" 
            Term.print_builtin other))

(* This only returns types of 'id's that are actually types *)
let type_of_dolmen_id id = match dolmen_id_to_string id with
  | "Int" -> Type.t_int
  | "Real" -> Type.t_real
  | "Bool" -> Type.t_bool 
  (* TODO Add support for arrays*)
  | other -> 
    raise
      (Invalid_argument 
          (Format.asprintf 
            "Sort %s not supported" 
             other))

let type_of_dolmen_term = function
  | Term.{ term = Builtin b ; _ } -> 
    type_of_dolmen_builtin b
  | Term.{ term = Symbol i ; _ } -> 
    type_of_dolmen_id i
  | other -> 
    raise
      (Invalid_argument 
          (Format.asprintf 
            "Type detection for dolmen term %a not yet supported" 
            Term.print other))

(* We are using an id mapping for dolmen. Kind2s functions want an hstring mapping. 
   To allow reuse of some kind2 functions we convert between the two. *)
let dolmen_bound_vars_to_kind bound_vars =
  List.map (fun (id, var) -> (dolmen_id_to_hstring id, var)) bound_vars

(* Extracts an ID from a dolmen term. This assumes that the term is a Dolmen Symbol
   and will error if not *)
let dolmen_symbol_term_to_id (symbol_term: term) = match symbol_term with
  | { term = Symbol name; _ } -> name
  | _ -> raise
    (Invalid_argument 
      (Format.asprintf 
          "Term %a is not a symbol" 
          Term.print symbol_term))
        
(* Given a dolmen term representing a CMC variable declaration 
   return a tuple of the variable's id and kind2 type *)
let dolmen_term_to_id_type (var_def: term) = match var_def with
  | { term = Colon ({ term = Symbol name; _ }, ty); _ } -> (name, type_of_dolmen_term ty)

  | _ -> raise
      (Invalid_argument 
        (Format.asprintf 
            "Term %a is not a variable declaration" 
            Term.print var_def))

(* Given a Dolmen ID, return the primed representation of it *)
let prime id = match (Id.name id) with
  | Simple name ->
    Id.create (Id.ns id) (Dolmen_std.Name.simple (name ^ "'") )
  | _ -> raise
    (Invalid_argument 
      (Format.asprintf 
          "Dolmen id %a is not a simple id and cannot be primed" 
          Id.print id))

let kind_symbol_from_dolmen s = 
  let smtlib_reserved_word_list = ["par"; "!"; "as" ] in
  try 
    (* Map hashconsed string to symbol *)
    (* TODO May want to convert to map instead of using assoc list (like what is done for sexps) *)
    List.assoc s GenericSMTLIBDriver.smtlib_string_symbol_list
  (* String is not one of our symbols *)
  with Not_found -> 
    (* Check if string is a reserved word *)
    if List.memq s smtlib_reserved_word_list then 
      (* Cannot parse S-expression *)
      raise 
        (Invalid_argument 
            (Format.sprintf 
              "Unsupported reserved word '%s' in S-expression"
              s))
    else
      (* String is not a symbol *)
      raise Not_found 

(* Convert a list of typed variables *)
let rec gen_bound_vars_of_dolmen dtte bound_vars accum vars = 
  match (vars : term list) with 

    (* All bindings consumed: return accumulator in original order *)
    | [] -> List.rev accum

    (* Take first binding *)
    (* Assuming Colon binding for now, bindings may be saved differently *)
    (* Assuming typed vars are bound to a builtin *)
    | { term = Colon ({ term = Symbol name; _ },  ty ); _ } :: other_bindings -> 

      (* Get the type of the expression *)
      let var_type = type_of_dolmen_term ty in

      (* Create a variable of the identifier and the type of the expression *)
      let tvar = Var.mk_free_var (dolmen_id_to_hstring name) var_type in

      (* Add bound expresssion to accumulator *)
      gen_bound_vars_of_dolmen dtte bound_vars ((name, tvar) :: accum) other_bindings

    (* Expression must be a pair *)
    | e :: _ -> 
      raise
      (Failure 
          (Format.asprintf 
          "Invalid expression in let binding: %a"
            Term.print e))

(* Convert a list of bindings *)
let rec gen_bindings_of_dolmen dtte bound_vars accum vars = 
  match (vars : term list) with 

    (* All bindings consumed: return accumulator in original order *)
    | [] -> List.rev accum

    (* Take first binding *)
    (* Assuming Colon binding for now, bindings may be saved differently*)
    | { term = Colon ({ term = Symbol name; _ }, expr ); _ } as e:: other_bindings -> 
      
      (* Convert to an expression *)
      let expr = dtte bound_vars expr in

      (* Get the type of the expression *)
      let expr_type = KindTerm.type_of_term expr in

      (* Create a variable of the identifier and the type of
         the expression *)
      let tvar = Var.mk_free_var (dolmen_id_to_hstring name) expr_type in

      (* Add bound expresssion to accumulator *)
      gen_bindings_of_dolmen dtte bound_vars ((name, (tvar, expr)) :: accum) other_bindings


    (* Expression must be a pair *)
    | e :: _ -> 
      raise
      (Failure 
         (Format.asprintf 
          "Invalid expression in let binding: %a"
            Term.print e))

(* Convert a string S-expression to an expression 
   This function is generic, and also used from {!YicesDriver} *)
let dolmen_term_to_expr' dtte bound_vars term = match (term : term) with 
  (* A let binding *) 
  | { term = Binder (binder, vars, term); _ } when binder == Term.Let_par || binder == Term.Let_seq ->
    (* Convert bindings and obtain a list of bound variables *)
    let named_bindings = gen_bindings_of_dolmen dtte bound_vars [] vars in
    let bindings = List.map snd named_bindings in

    (* Convert bindings to an association list from strings to
      variables *)
    let bound_vars' = 
      List.map 
        (function (id, (var, _)) -> (id, var))
        named_bindings 
    in

    (* Parse the subterm, giving an association list of bound
      variables and return a let bound term *)
    KindTerm.mk_let 
      bindings
      (dtte (bound_vars @ bound_vars') term)
          
  (* A universal or existential quantifier *)
  | { term = Binder (binder, vars, term); _ } 
    when binder == Term.All || binder == Term.Ex -> 

    (* Association list from ids to kind variables *)
    let bound_vars' = 
      gen_bound_vars_of_dolmen dtte bound_vars [] vars 
    in

    (* Get list of variables bound by the quantifier *)
    let quantified_vars = 
      List.map snd bound_vars'
    in

    (* Parse the subterm, giving an association list of bound variables
      and return a universally or existenially quantified term *)
    (if binder == Term.All then KindTerm.mk_forall 
    else if  binder == Term.Ex then KindTerm.mk_exists
    else assert false)
      quantified_vars
      (dtte (bound_vars @ bound_vars') term)
      

(* 
  (* Parse (/ n d) as rational constant *)
  | HStringSExpr.List
      [HStringSExpr.Atom s; HStringSExpr.Atom n; HStringSExpr.Atom d] 
    when s == s_div && 
        (try
            let _ =
              Numeral.of_string (HString.string_of_hstring n) 
            in
            true
          with _ -> false) &&
        (try
            let _ =
              Numeral.of_string (HString.string_of_hstring d) 
            in
            true
          with _ -> false) ->

    Term.mk_dec
      Decimal.
        ((HString.string_of_hstring n |> of_string) /
        (HString.string_of_hstring d |> of_string))
 *)
(* 
  (* Parse (/ (- n) d) as rational constant *)
  | HStringSExpr.List
      [HStringSExpr.Atom s2;
      HStringSExpr.List [HStringSExpr.Atom s1; HStringSExpr.Atom n]; 
      HStringSExpr.Atom d] 
    when s1 == s_minus && 
        s2 == s_div && 
        (try
            let _ =
              Numeral.of_string (HString.string_of_hstring n) 
            in
            true
          with _ -> false) &&
        (try
            let _ =
              Numeral.of_string (HString.string_of_hstring d) 
            in
            true
          with _ -> false) ->

    Term.mk_dec
      Decimal.
        (- 
        (HString.string_of_hstring n |> of_string) /
        (HString.string_of_hstring d |> of_string))
 *)

  (* Atom *)
  | { term = Symbol a ; _ } ->
    let s = dolmen_id_to_hstring a in
    (* Leaf in the symbol tree *)
    (GenericSMTLIBDriver.const_of_smtlib_atom (dolmen_bound_vars_to_kind bound_vars) s)

(* 
  (* Prime symbol if it exists *)
  | HStringSExpr.List [HStringSExpr.Atom s; e]
    when (match prime_symbol with
        | None -> false
        | Some s' -> s == s') -> 

    expr_of_string_sexpr conv bound_vars e |> Term.bump_state Numeral.one *)

  (*  A list with more than one element *)
  (* | HStringSExpr.List ((HStringSExpr.Atom h) :: tl) ->  *)
  | { term = App ( { term = Symbol funct ; _ } , params) ; _ }  -> 

    (
      let funct_string = dolmen_id_to_string funct in

      (* Symbol from string *)
      let s = 

        if ((funct_string = "bvudiv_i") || 
            (funct_string = "bvsdiv_i") ||
            (funct_string = "bvurem_i") || 
            (funct_string = "bvsrem_i")) then
          (raise (UnsupportedZ3Symbol funct_string))
        else
          try 

            (* Map the string to an interpreted function symbol *)
            kind_symbol_from_dolmen funct_string 

          with 

            (* Function symbol is uninterpreted *)
            | Not_found -> 

              (* Uninterpreted symbol from string *)
              let u = 

                try 

                  UfSymbol.uf_symbol_of_string funct_string

                with Not_found -> 

                  (* Cannot convert to an expression *)
                  failwith 
                    (Format.sprintf 
                      "Undeclared uninterpreted function symbol %s in \
                        S-expression"
                      funct_string)
              in

              (* Get the uninterpreted symbol of the string *)
              Symbol.mk_symbol (`UF u)


        in

        (* parse arguments *)
        let args = List.map (dtte bound_vars) params in

        (* Add correct type to select *)
        let s = match Symbol.node_of_symbol s, args with
          | `SELECT _, [a; _] ->
            Symbol.mk_symbol (`SELECT (KindTerm.type_of_term a))
          | _ -> s
        in
      
        (* Create an application of the function symbol to the subterms *)
        let t = KindTerm.mk_app s args in

        (* Convert (= 0 (mod t n)) to (t divisible n) *)
        KindTerm.mod_to_divisible t
        (* |> Term.reinterpret_select *)

    )
(* 
  (* Parse ((_ int2bv n) x) *)
  | HStringSExpr.List
      (HStringSExpr.List [HStringSExpr.Atom s1; HStringSExpr.Atom s2;
                          HStringSExpr.Atom n;] :: tl)
    when s1 == s_index && s2 = s_int2bv ->

      (* parse arguments *)
      let args = List.map (expr_of_string_sexpr conv bound_vars) tl in

      (match (int_of_string (HString.string_of_hstring n)) with
      | 8 -> Term.mk_app Symbol.s_to_uint8 args
      | 16 -> Term.mk_app Symbol.s_to_uint16 args
      | 32 -> Term.mk_app Symbol.s_to_uint32 args
      | 64 -> Term.mk_app Symbol.s_to_uint64 args
      | _ -> failwith "Invalid S-expression") *)
(* 
  (* Parse ((_ extract i j) x) *)
  | HStringSExpr.List
      (HStringSExpr.List [HStringSExpr.Atom s1; HStringSExpr.Atom s2;
                          HStringSExpr.Atom i; HStringSExpr.Atom j;] :: tl)
    when s1 == s_index && s2 = s_extract ->

      (* parse indices *)
      let i_n = Numeral.of_string (HString.string_of_hstring i) in
      let j_n = Numeral.of_string (HString.string_of_hstring j) in
      
      (* parse arguments *)
      let args = List.map (expr_of_string_sexpr conv bound_vars) tl in

      Term.mk_app (Symbol.s_extract i_n j_n) args *)

  (* A list with a list as first element *)
  | _ -> 

    (* Cannot convert to an expression *)
    failwith "Invalid S-expression"


(* Call function with an empty list of bound variables and no prime symbol *)
let rec dolmen_term_to_expr bound_vars (term : term) =
  dolmen_term_to_expr' dolmen_term_to_expr bound_vars term 

(* Term must represent a predicate, as None term will be interpreted as True*)
let rec opt_dolmen_term_to_expr bound_vars (term : term option) =
  match term with
    | Some term -> dolmen_term_to_expr' dolmen_term_to_expr bound_vars term 
    | None -> KindTerm.mk_true ()