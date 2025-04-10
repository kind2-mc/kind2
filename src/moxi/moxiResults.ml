(* 
  Questions
  1) Top-level function takes a trans_sys argument. How do we know we're passing the correct one? 
     Is it just the top-level transition system? 
*)

let pp_print_prop_trace _ prop = 
  let prop_name = prop.Property.prop_name in
  match Property.get_prop_status prop with
  | PropFalse _ -> 
    Format.printf "@[<hv 2>:trace@ (@[<v>%s :prefix %s@])@]@,"
      (prop_name ^ "_trace")
      (prop_name ^ "_prefix")
  | PropInvariant _
  | PropKTrue _ 
  | PropUnknown -> () 

let has_model trans_sys svar_path = 
  (*!! List.map will not change the length of the list... so what are we doing? (see mcil branch code) *)
  List.exists (fun svar -> List.mem_assoc svar svar_path)
    (TransSys.global_const_state_vars trans_sys)

let pp_print_const_decl _ppf (svar, svar_value_path) =
  let svar_type = StateVar.type_of_state_var svar in
  (* These should be constant; assume that all values are the same *)
  let const_value = List.hd svar_value_path in

  match List.find_all (fun value -> 
    not (Model.equal_value value const_value)
  ) (List.tl svar_value_path) with
  | [] -> 
    Format.printf "(define-fun %s () %a %a)" 
      (StateVar.name_of_state_var svar) 
      Type.pp_print_type svar_type 
      (Model.pp_print_value ?as_type:(Some svar_type)) const_value
  
  | _ -> 
    failwith (Format.asprintf 
      "Recieved unexpected model value. Unable to construct counterexample.\n
       Variable %a should be constant but was assigned multiple values. %a"
      StateVar.pp_print_state_var svar 
      (Lib.pp_print_list Model.pp_print_value ", ") svar_value_path) 

let pp_print_const_decls: TransSys.t -> Format.formatter -> (StateVar.t * Model.value list) list -> unit 
= fun trans_sys _ppf svar_path -> 
  let const_svars = List.map (fun svar -> 
    svar, List.assoc svar svar_path
  ) (TransSys.global_const_state_vars trans_sys) in
  Format.printf "%a" (Lib.pp_print_list pp_print_const_decl "@,") const_svars

let pp_print_model trans_sys prop_name _ppf path =
  if has_model trans_sys path then 
    Format.printf "%s@,%a@," (prop_name ^ "_model") (pp_print_const_decls trans_sys) path
  else 
    Format.printf "%s ()" (prop_name ^ "_model")

let pp_print_prop_model: TransSys.t -> Format.formatter -> Property.t -> unit 
= fun trans_sys _ppf prop ->
  let prop_name = prop.Property.prop_name in
  match Property.get_prop_status prop with
  | PropFalse cex -> 
    Format.printf "@[<hv 2>:model@ (@[<v>%a@]@])@,"
      (pp_print_model trans_sys prop_name) cex
  | PropInvariant _
  | PropKTrue _ 
  | PropUnknown -> ()

let pp_print_prop_trail _ _ _ _ = ()

let pp_print_prop_cert _ prop = 
  let prop_name = prop.Property.prop_name in
  match Property.get_prop_status prop with
  | PropFalse _ -> () 
  | PropInvariant (k, inv) -> 
    Format.printf "@[<hv 2>:certificate@ (@[<v>%s :inv %a :k %i@])@]@,"
      (prop_name ^ "_cert")
      (LustreExpr.pp_print_term_as_expr false)
      inv
      k
  | PropKTrue k -> 
    Format.printf "@[<hv 2>:certificate@ (@[<v>%s :inv None :k %i@])@]@,"
      (prop_name ^ "_cert")
      k
  | PropUnknown -> ()

let prop_result_info prop_name prop_result = match prop_result with 
| Property.PropFalse _ -> Format.sprintf ":model %s_model :trace %s_trace" prop_name prop_name
| PropInvariant _
| PropKTrue _ -> Format.sprintf ":certificate %s_cert" prop_name
| PropUnknown -> ""

let pp_print_prop_result _ prop =
  let prop_name = prop.Property.prop_name in
  let prop_result = Property.get_prop_status prop in
  let result = match prop_result with
  | PropFalse _ -> "sat"
  | PropInvariant _
  | PropKTrue _ -> "unsat"
  | PropUnknown -> "unknown"
  in
  Format.printf "@[<hv 2>:query@ @[<v>@[<hv 1>(%s@ %s %s)@]@]@]@,"
    prop_name result 
    (prop_result_info prop_name prop_result)

let pp_print_results: TransSys.t -> _ InputSystem.t -> Property.t list -> unit 
= fun trans_sys _in_sys props -> 
  Format.printf
  "@[<v 1>(check-system-response @,\
   @[<hv 2>:verbosity@ %s@]@,\
    %a\
    %a\
    %a\
    %a\
    %a\
    )@]@.@."
  (if false then "condensed" else "full") (*!! TODO: Get flag for ITE condition *)
  (Lib.pp_print_list pp_print_prop_result "") props
  (Lib.pp_print_list pp_print_prop_trace "") (props)
  (Lib.pp_print_list (pp_print_prop_model trans_sys) "") (props)
  (Lib.pp_print_list (pp_print_prop_trail () ()) "") (props)
  (Lib.pp_print_list pp_print_prop_cert  "") (props)