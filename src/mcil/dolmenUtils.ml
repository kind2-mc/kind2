open Dolmen

exception DolmenParseError

(* Instantiate a module for parsing logic languages *)
module Logic = Class.Logic.Make(Std.Loc)(Std.Id)(Std.Term)(Std.Statement)

(* instantiate the modules for typechecking *)
(* module State = Dolmen_loop.State *)
module State = struct
  include Dolmen_loop.State
  let error ?file ?loc st error payload =
    (* do some things, such as logging, and/or storing some things in the state *)
    let st = flush st () in
    let loc = Dolmen.Std.Misc.opt_map loc Dolmen.Std.Loc.full_loc in 
    let aux _ = Dolmen_loop.Code.exit (Dolmen_loop.Report.Error.code error) in
    match get report_style st with
    | Minimal ->
      failwith (Format.asprintf 
        "E:%s@." (Dolmen_loop.Report.Error.mnemonic error))
    | Regular | Contextual ->
      Format.kfprintf aux Format.err_formatter
        ("@[<v>%a%a @[<hov>%a@]%a@]@.")
        (pp_loc ?file st) loc
        Fmt.(styled `Bold @@ styled (`Fg (`Hi `Red)) string) "Error"
        Dolmen_loop.Report.Error.print (error, payload)
        Dolmen_loop.Report.Error.print_hints (error, payload)
  (* let warn ?file ?loc st warn payload =
    (* do some things... *)
    st *)
end
module Typer_aux = Dolmen_loop.Typer.Typer(State)
module Typer = Dolmen_loop.Typer.Make(Std.Expr)(Std.Expr.Print)(State)(Typer_aux)
(*module Parser = Dolmen_loop.Parser.Make(State)*)

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

type enum = {
  name: id;
  get_type: Type.t;
  to_int: (id * Numeral.t) list;
  to_str: (Numeral.t * id) list;
}

let print_enum ppf enum = 
  Format.fprintf ppf "(%a: %a)" Id.print enum.name (Lib.pp_print_list (Lib.pp_print_pair Id.print Numeral.pp_print_numeral ":") ", ") (enum.to_int)

let print_enums ppf enums = 
  Format.fprintf ppf "%a" ( Lib.pp_print_list print_enum "\n" ) enums
  
let empty_enum name enum_type = {
  name = name;
  get_type = enum_type;
  to_int = [];
  to_str = [];
}

let gen_enum_conversion_map enums =
  enums |> List.fold_left (fun to_int_maps {to_int} -> 
    (* Ensure each string is in only one enum *)
    let checked_enum_values = List.map (fun (id, int_rep) -> 
        if List.mem_assoc id to_int_maps then failwith (Format.asprintf "Enum value `%a` is defined twice." Id.print id)
        else (id, (Numeral.string_of_numeral int_rep))
      ) to_int in
    checked_enum_values @ to_int_maps
  ) []

let enum_name_to_type enums enum_name =
  let enum = List.find (fun (enum) -> Id.equal enum.name enum_name) enums in
  enum.get_type

let is_enum_type_str enums enum_name = 
  let enum = List.find_opt (fun (enum) -> Id.equal enum.name enum_name) enums in
  match enum with 
  | Some _ -> true
  | _ -> false

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
let type_of_dolmen_id enums id = match dolmen_id_to_string id with
  | "Int" -> Type.t_int
  | "Real" -> Type.t_real
  | "Bool" -> Type.t_bool 
  (* TODO Add support for arrays*)
  | other -> 
    if is_enum_type_str enums id then
      enum_name_to_type enums id 
    else 
      raise
        (Invalid_argument 
            (Format.asprintf 
              "Sort %s not supported" 
              other))

let type_of_dolmen_term enums = function
  | Term.{ term = Builtin b ; _ } -> 
    type_of_dolmen_builtin b
  | Term.{ term = Symbol i ; _ } -> 
    type_of_dolmen_id enums i
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

let dolmen_binding_to_types enums (var_def: term) = match var_def with
| { term = Binder (binder, param_terms, return_term); _ } -> 
  (match binder with 
    | Arrow -> 
      let param_types = List.map (type_of_dolmen_term enums) param_terms in
      let return_type = type_of_dolmen_term enums return_term in
      param_types, return_type
    | _ -> raise
      (Invalid_argument 
        (Format.asprintf 
            "Term %a is not bound with Arrow" 
            Term.print var_def))
  )
| _ -> raise
      (Invalid_argument 
        (Format.asprintf 
            "Term %a is not a list of types" 
            Term.print var_def))
        
(* Given a dolmen term representing a MCIL variable declaration 
   return a tuple of the variable's id and kind2 type *)
let dolmen_term_to_id_type enums (var_def: term) = match var_def with
  | { term = Colon ({ term = Symbol name; _ }, ty); _ } -> (name, type_of_dolmen_term enums ty)

  | _ -> raise
      (Invalid_argument 
        (Format.asprintf 
            "Term %a is not a variable declaration" 
            Term.print var_def))

let mk_id ns name = Id.create ns (Dolmen_std.Name.simple (name) )

(** make a new id with two other ids *)

(** Return a new ID with the given string prepended to the name *)
let prepend_to_id start id = match (Id.name id) with
| Simple name ->
  mk_id (Id.ns id) (start ^ name)
| _ -> raise
  (Invalid_argument 
    (Format.asprintf 
        "Dolmen id %a is not a simple id and cannot be prepended" 
        Id.print id))

(** Return a new ID with the given string appended to the name *)
let append_to_id id ending = match (Id.name id) with
| Simple name ->
  mk_id (Id.ns id) (name ^ ending)
| _ -> raise
  (Invalid_argument 
    (Format.asprintf 
        "Dolmen id %a is not a simple id and cannot be appended" 
        Id.print id))

let join_ids first second = match (Id.name first) with
  | Simple name ->
    prepend_to_id (name^"_") second
  | _ -> raise
    (Invalid_argument 
      (Format.asprintf 
          "Dolmen id %a is not a simple id and cannot be joined" 
          Id.print first))

(* Given a Dolmen ID, return the primed representation of it *)
let prime id = append_to_id id "'"

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
let rec gen_bound_vars_of_dolmen enums dtte bound_vars accum vars = 
  match (vars : term list) with 

    (* All bindings consumed: return accumulator in original order *)
    | [] -> List.rev accum

    (* Take first binding *)
    (* Assuming Colon binding for now, bindings may be saved differently *)
    (* Assuming typed vars are bound to a builtin *)
    | { term = Colon ({ term = Symbol name; _ },  ty ); _ } :: other_bindings -> 

      (* Get the type of the expression *)
      let var_type = type_of_dolmen_term enums ty in

      (* Create a variable of the identifier and the type of the expression *)
      let tvar = Var.mk_free_var (dolmen_id_to_hstring name) var_type in

      (* Add bound expresssion to accumulator *)
      gen_bound_vars_of_dolmen enums dtte bound_vars ((name, tvar) :: accum) other_bindings

    (* Expression must be a pair *)
    | e :: _ -> 
      raise
      (Failure 
          (Format.asprintf 
          "Invalid expression in let binding: %a"
            Term.print e))

(* Convert a list of bindings *)
let rec gen_bindings_of_dolmen dtte enums bound_vars accum vars = 
  match (vars : term list) with 

    (* All bindings consumed: return accumulator in original order *)
    | [] -> List.rev accum

    (* Take first binding *)
    (* Assuming Colon binding for now, bindings may be saved differently*)
    | { term = Colon ({ term = Symbol name; _ }, expr ); _ } :: other_bindings -> 
      
      (* Convert to an expression *)
      let expr = dtte enums bound_vars expr in

      (* Get the type of the expression *)
      let expr_type = KindTerm.type_of_term expr in

      (* Create a variable of the identifier and the type of
         the expression *)
      let tvar = Var.mk_free_var (dolmen_id_to_hstring name) expr_type in

      (* Add bound expresssion to accumulator *)
      gen_bindings_of_dolmen dtte enums bound_vars ((name, (tvar, expr)) :: accum) other_bindings

    (* Expression must be a pair *)
    | e :: _ -> 
      raise
      (Failure 
         (Format.asprintf 
          "Invalid expression in let binding: %a"
            Term.print e))

let dolmen_app_info = function
| { Term.term = App ( { term = Symbol funct ; _ } , params) ; _ }  ->
  Some (funct, params)
| _ -> None

(* Convert a string S-expression to an expression 
   This function is generic, and also used from {!YicesDriver} *)
let dolmen_term_to_expr' dtte enums bound_vars term = match (term : term) with 
  (* A let binding *) 
  | { term = Binder (binder, vars, term); _ } when binder == Term.Let_par || binder == Term.Let_seq ->
    (* Convert bindings and obtain a list of bound variables *)
    let named_bindings = gen_bindings_of_dolmen dtte enums bound_vars [] vars in
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
      (dtte enums (bound_vars @ bound_vars') term)
          
  (* A universal or existential quantifier *)
  | { term = Binder (binder, vars, term); _ } 
    when binder == Term.All || binder == Term.Ex -> 

    (* Association list from ids to kind variables *)
    let bound_vars' = 
      gen_bound_vars_of_dolmen enums dtte bound_vars [] vars 
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
      (dtte enums (bound_vars @ bound_vars') term)
      

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
    (* TODO Move enum map generation higher up so we don't do it so often. *)
    (* COULD cause a lot of delay here *)
    let enum_map = gen_enum_conversion_map enums in
    
    let s = match List.assoc_opt a enum_map with
    | Some enum -> HString.mk_hstring enum
    | None ->  dolmen_id_to_hstring a in

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
        let args = List.map (dtte enums bound_vars) params in

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
let rec dolmen_term_to_expr enum_map bound_vars (term : term) =
  dolmen_term_to_expr' dolmen_term_to_expr enum_map bound_vars term 

(* Term must represent a predicate, as None term will be interpreted as True*)
let opt_dolmen_term_to_expr enum_map bound_vars (term : term option) =
  match term with
    | Some term -> dolmen_term_to_expr' dolmen_term_to_expr enum_map bound_vars term 
    | None -> KindTerm.mk_true ()
  
  let process file =
    (* *** Parsing ********************************************************** *)
    (* note the "file" here, which refers to the file location metadata *)
    let format, loc_file, lazy_l = Logic.parse_file_lazy file in

    let parsed_statements =
      try Lazy.force lazy_l with 
        Dolmen.Std.Loc.Syntax_error(loc, msg) ->
          let loc : Dolmen.Std.Loc.loc = Dolmen.Std.Loc.loc loc_file loc in
          (* we can now print the loc if we want, or do whatever we want *)
          Format.eprintf "error at %a\n" Dolmen.Std.Loc.fmt loc ;
          match msg with
            | `Regular msg ->
              failwith (Format.asprintf "%t" msg)
            | `Advanced (error_ref, prod, lexed, expected) -> 
              let p_ref fmt = Format.fprintf fmt "(%s)@ " error_ref in
              failwith (Format.asprintf
                "@[<v>@[<hv>%twhile parsing %t,@ read %t,@]@ @[<hov>but expected %t.@]@]"
                p_ref prod lexed expected)
    in
    
    (* You can match on the detected format of the input *)
    let () =
      match format with
      | Logic.Dimacs | Logic.ICNF -> ()
      | Logic.Alt_ergo | Logic.Smtlib2 _ | Logic.Tptp _ | Logic.Zf -> ()
    in

    
  
    (* *** Typing *********************************************************** *)
    (* create the logic file corresponding to our input *)
    let lang : Dolmen_loop.Logic.language = Smtlib2 `MCIL in
    let logic_file = State.mk_file ~lang ~loc:loc_file "./" (`File file) in
    let response_file = State.mk_file "" (`File "this is unused") in
    
    (* let's create the initial state *)
    let state =
      State.empty
      |> State.init
         ~debug:false ~report_style:Contextual ~max_warn:max_int
         ~reports:(Dolmen_loop.Report.Conf.mk ~default:Enabled)
         ~response_file
         (* these limits are ignored in this example; to actually enforce
            the limits, one has to use the `run` function from `Dolmen_loop.Pipeline` *)
         ~time_limit:0. ~size_limit:0.
      |> State.set State.logic_file logic_file
      |> Typer_aux.init
      |> Typer.init ~type_check:true
    in
  
    (* We can loop over the parsed statements to generated the typed statements *)
    try
      let _final_state, _rev_typed_stmts =
        List.fold_left (fun (state, acc) parsed_stmt -> 
          let state, typed_stmt = Typer.check state parsed_stmt in
          (* let a = State.get State. state in *)
          (* let b =  a.warnings in *)
          (* Format.printf "%a@\n@." Typer.print typed_stmt ; *)
          (state, typed_stmt :: acc)
        ) (state, []) parsed_statements
      in
      let _typed_stmts = List.rev _rev_typed_stmts in
      
    
      (* let's print the typed statements *)
      (* List.iter (fun typed_stmt ->
        Format.printf "%a@\n@." Typer.print typed_stmt
      ) typed_stmts ; *)
      
      parsed_statements

    with Failure _ -> raise DolmenParseError

let dolmen_id_to_kind_term enums bound_vars id = 
  let enum_map = gen_enum_conversion_map enums in
    
  let s = match List.assoc_opt id enum_map with
  | Some enum -> HString.mk_hstring enum
  | None ->  dolmen_id_to_hstring id in

  (* Leaf in the symbol tree *)
  (GenericSMTLIBDriver.const_of_smtlib_atom (dolmen_bound_vars_to_kind bound_vars) s)
    