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

module S = SMTSolver
module Strats = TestgenStrategies
module N = LustreNode

module Unused_for_now = TestgenSolver
module Unused_for_now_too = TestgenTree
module Unused_for_now_either = TestgenDF

(* Reference to the solver instance. *)
let solver_ref = ref None

(* Turns an actlit uf in a term. *)
let term_of = Actlit.term_of_actlit


let mk_dir dir =
  try Unix.mkdir dir 0o740 with Unix.Unix_error(Unix.EEXIST, _, _) -> ()

let oracle_dir = "oracle"
let oracle_name sys =
  Format.asprintf "%a_oracle" (LustreIdent.pp_print_ident false) sys.N.name
let oracle_path dir sys =
  match TransSys.get_source sys with
  | TransSys.Native -> assert false
  | TransSys.Lustre nodes ->
    nodes
    |> List.rev
    |> List.hd
    |> oracle_name
    |> Format.sprintf "%s/%s" oracle_dir

module Xml = struct

  let pp_header fmt =
    Format.fprintf fmt "<?xml version=\"1.0\"?>@."

  let pp_necker fmt sys =
    Format.fprintf fmt "<data system=\"%s\">@.@.  @[<v>" sys

  let pp_oracle fmt oracle_path outputs =
    Format.fprintf
      fmt
      "@[<v><oracle path=\"%s\">@,  @[<v>%a@]@,</oracle>@]@,@,"
      oracle_path
      (pp_print_list
        (fun fmt (is_global, output) ->
          Format.fprintf
            fmt "<output global=\"%b\">%s</output>" is_global output)
        "@,")
      outputs

  let pp_tests fmt =
    Format.fprintf
      fmt
      "@[<v>%a@]@."
      (pp_print_list
        (fun fmt f -> Format.fprintf fmt "<tests>%s</tests>" f)
        "@,")

  let pp_footer_flush fmt = Format.fprintf fmt "@]@.</data>@.@.@?"

  module Strat = struct
    let pp_necker fmt sys name =
      Format.fprintf fmt "<data system=\"%s\" name=\"%s\">@.@.  @[<v>" sys name

    let pp_testcase fmt path name format lines =
      Format.fprintf
        fmt
        "@[<v>\
         <testcase@,  @[<v>\
         path=\"%s\"@,\
         name=\"%s\"@,\
         format=\"%s\"\
         @]>@,    @[<v>\
         %a\
         @]@,</testcase>@]@,@,"
        path name format
        (pp_print_list Format.pp_print_string "@,") lines
  end

end


(* |===| Functions for the context of the strategy. *)

(* Declares a UF. *)
let declare solver = S.declare_fun solver

(* Builds actlit implications and asserts them. *)
let actlit_implications solver ?(eq = false) = function
  | [] -> ()
  | impls -> impls |> List.map (
      fun (uf, term) ->
        ( if eq then Term.mk_eq
          else Term.mk_implies ) [ term_of uf ; term ]
    ) |> List.iter (S.assert_term solver)

(* Checksats and returns [Some] of the values of [terms] if sat, [None]
   otherwise. *)
let checksat_getvalues solver actlits terms =
  S.check_sat_assuming
    solver
    ( fun () -> Some (S.get_term_values solver terms) )
    ( fun () -> None )
    ( actlits |> List.map ( fun uf -> term_of uf ) )

(* Checksats and returns [Some] of the model if sat, [None] otherwise. *)
let checksat_getmodel solver actlits =
  S.check_sat_assuming
    solver
    ( fun () -> Some (S.get_model solver) )
    ( fun () -> None )
    ( actlits |> List.map ( fun uf -> term_of uf ) )

(* Prints a comment in the solver trace. *)
let comment solver = S.trace_comment solver

(* Deletes the solver and unsets the reference. *)
let delete_solver () =
  try match !solver_ref with
  | None -> ()
  | Some solver ->
    Format.printf "Deleting solver, resetting reference.@." ;
    SMTSolver.delete_instance solver |> ignore ;
    solver_ref := None
  with
  | e ->
    KEvent.log
      L_debug
      "TestGen @[<v>Error while deleting solver:@ %s@]"
      (Printexc.to_string e)


(* Runs a strategy until it says it's done. *)
let run_strategy out_dir sys strategy =

  (* Retrieving the strategy module. *)
  let module Strat = (val strategy : TestgenStrategies.Sig) in
(* 
  let req_svars = match TransSys.mode_req_svars sys with
    | None -> assert false
    | Some svars -> svars
  in *)

  (* Format.printf
    "Mode req svars: @[<v>%a@]@.@."
    (pp_print_list StateVar.pp_print_state_var "@,") req_svars ; *)

  Format.printf
    "Starting run for strategy %s.@."
    Strat.name ;

  (* Failing if there is already a solver referenced. *)
  assert (!solver_ref = None) ;

  (* Creating a new solver for this run. *)
  let solver =
    S.create_instance
      ~produce_assignments:true
      (TransSys.get_scope sys)
      (TransSys.get_logic sys)
      (TransSys.get_abstraction sys)
      (Flags.Smt.solver ())
  in

  (* Memorizing solver for clean exit. *)
  solver_ref := Some solver ;

  (* Initializing solver. *)
  TransSys.init_solver
    sys
    (comment solver)
    (S.define_fun solver)
    (S.declare_fun solver)
    (S.assert_term solver)
    Numeral.zero Numeral.zero ;

  (* Asserting initial constraint. *)
  TransSys.init_of_bound sys Numeral.zero
  |> SMTSolver.assert_term solver
  |> ignore ;

  (* Creating a context for the strategy. *)
  let context =
    Strat.mk_context
      sys
      (declare solver)
      (actlit_implications solver)
      (checksat_getvalues solver)
      (comment solver)
  in

  (* Runs the strategy at [k], and loops after unrolling the system
     if the strategy is not done. *)
  let rec loop_strategy k =

    (* Format.printf
      "At iteration %a on strategy %s.@."
      Numeral.pp_print_numeral k
      Strat.name ; *)

    (* Letting strategy work at [k]. *)
    let is_done = Strat.work context k in

    (* Looping if not done. *)
    if not is_done then (

      Format.printf "  unrollings: %a@." Numeral.pp_print_numeral k ;

      (* Increment [k]. *)
      let k = Numeral.succ k in

      (* Declare variables at [k]. *)
      TransSys.declare_vars_of_bounds
        sys
        (SMTSolver.declare_fun solver)
        (SMTSolver.assert_term solver)
        k k ;

      (* Unroll at k. *)
      TransSys.trans_of_bound sys k |> SMTSolver.assert_term solver ;

      loop_strategy k
    )

    (* Returning the [k] otherwise. *)
    else k

  in

  (* Going to loop, starting at zero. *)
  let final_k = loop_strategy Numeral.zero in

  Format.printf
    "Strategy %s is done at %a.@.@."
    Strat.name
    Numeral.pp_print_numeral final_k ;

  let xml_short_file_name = Strat.out_dir ^ "-tests.xml" in
  let xml_file_name = out_dir ^ "/" ^ xml_short_file_name in
  Format.printf "Creating xml file@." ;
  Format.printf "  %s@." xml_file_name ;
  let xml_file =
    Unix.openfile
      xml_file_name [ Unix.O_TRUNC ; Unix.O_WRONLY ; Unix.O_CREAT ] 0o640
  in
  let xml_fmt =
    Unix.out_channel_of_descr xml_file |> Format.formatter_of_out_channel
  in

  (* Printing xml header. *)
  Xml.pp_header xml_fmt ;
  Xml.Strat.pp_necker xml_fmt (TransSys.get_name sys) Strat.name ;


  (* Creating strategy directory. *)
  let out_dir = out_dir ^ "/" ^ Strat.out_dir in
  mk_dir out_dir ;

  (* Generating testcases. *)
  Format.printf "Generating testcases.@." ;
  let pp_testcase out_file =
    Format.printf "  %s@." out_file ;
    Xml.Strat.pp_testcase xml_fmt out_file
  in
  checksat_getmodel solver
  |> Strat.testcase_gen out_dir pp_testcase context ;

  (* Printing xml footer and flushing. *)
  Xml.pp_footer_flush xml_fmt ;
  (* Closing xml file. *)
  Unix.close xml_file ;

  (* Deleting solver, resetting solver reference. *)
  delete_solver () ;

  xml_short_file_name


(* Generates the oracle for a list of lustre nodes in topological order. *)
let oracle_of_nodes out_dir nodes =
  let rec last_rev_tail acc = function
  | [ h ] -> (h, acc)
  | h :: t -> last_rev_tail (h :: acc) t
  | [] -> assert false
  in

  let (top, subs) = last_rev_tail [] nodes in

  Format.printf "@[<v>top: %a@,subs:@,  @[<v>%a@]@]@.@."
    (LustreIdent.pp_print_ident false) top.N.name
    (pp_print_list (fun ppf n ->
      Format.fprintf
        ppf "%a" (LustreIdent.pp_print_ident false) n.N.name
    ) "@,") subs ;

  let mk_and = function
    | [] -> LustreExpr.t_true
    | [ e ] -> e
    | e :: tail ->
      let rec loop e = function
        | e' :: tail -> loop (LustreExpr.mk_and e e') tail
        | [] -> e
      in
      loop e tail
  in
  let mk_impl = LustreExpr.mk_impl in
  let mk_out_ident id =
    LustreIdent.mk_string_ident
      ("output_" ^ ( (LustreIdent.string_of_ident false) id ))
  in
  let mk_out_ident_req id =
    LustreIdent.mk_string_ident
      ("output_" ^ ( (LustreIdent.string_of_ident false) id ) ^ "_req")
  in

  let contracts = match top.N.contract_spec with
    | None ->
      assert false
    | Some (_, _, globl, modes, _) ->
      modes
      |> List.fold_left
        ( fun l (m: N.contract) -> (
            m,
            mk_out_ident m.N.name,
            mk_impl (mk_and m.N.reqs) (mk_and m.N.enss)
          ) :: (
            m,
            mk_out_ident_req m.N.name,
            mk_and m.N.reqs
          ) :: l )
        []
      |> List.rev
      |> (fun l -> match globl with
        | None -> l
        | Some c ->
          (c, mk_out_ident_req c.N.name, mk_and c.N.reqs) ::
          (c, mk_out_ident c.N.name, mk_and c.N.enss) :: l
      )
  in

  (* Format.printf
    "contract outputs: @[<v>%a@]@.@."
    (pp_print_list
      (fun ppf (_,id,expr) ->
        Format.fprintf ppf "%a: %a"
          (LustreIdent.pp_print_ident false) id
          (LustreExpr.pp_print_lustre_expr false) expr)
      "@,")
    contracts ; *)

  let oracle_ident =
    oracle_name top |> LustreIdent.mk_string_ident
  in

  (* Format.printf
    "Generating new node.@.> name: %a@."
    (LustreIdent.pp_print_ident false) oracle_ident ; *)

  let oracle_inputs = top.N.inputs @ top.N.outputs in

  (* Format.printf
    "> inputs: @[<v>%a@]@."
    (pp_print_list
      (fun ppf (sv,id) ->
        Format.fprintf ppf
          "%a" (* (LustreIdent.pp_print_index false) id) *)
          StateVar.pp_print_state_var sv)
      "@,")
    oracle_inputs ; *)

  let oracle_outputs, oracle_out_equations =
    contracts
    |> List.fold_left
        ( fun (out,eqs) (_,id,expr) ->
            let sv =
              LustreExpr.mk_state_var_of_ident
                (LustreIdent.index_of_ident id)
                id
                (Type.mk_type Type.Bool)
            in
            (sv, LustreIdent.index_of_ident id) :: out,
            (sv, expr) :: eqs )
        ([],[])
    |> fun (out,eqs) -> List.rev out, List.rev eqs
  in

  let oracle_out_svs = List.map (fun (sv,_) -> sv) oracle_outputs in

  let filtered_top_eqs =
    top.N.equations
    |> List.filter (fun (sv,_) ->
      oracle_inputs
      |> List.exists (fun (sv',_) -> StateVar.equal_state_vars sv sv')
      |> not
    )
  in

  (* Format.printf
    "> outputs: @[<v>%a@]@."
    (pp_print_list
      (fun ppf (sv,id) ->
        Format.fprintf ppf
          "%a" (* (LustreIdent.pp_print_index false) id) *)
          StateVar.pp_print_state_var sv)
      "@,")
    oracle_outputs ; *)

  let oracle: N.t = {
    N.name = oracle_ident ;
    N.inputs = oracle_inputs ;
    N.oracles = top.N.oracles ;
    N.outputs = oracle_outputs ;
    N.observers = [] ; (*top.N.observers ;*)
    N.locals = top.N.locals ;
    N.equations = oracle_out_equations @ filtered_top_eqs ;
    N.calls = top.N.calls ;
    N.asserts = [] ;
    N.props = [] ;
    N.contract_spec = None ;
    N.is_main = true ;
    N.output_input_dep = [] ;
    N.fresh_state_var_index = top.N.fresh_state_var_index ;
    N.fresh_oracle_index = top.N.fresh_oracle_index ;
    N.state_var_oracle_map = top.N.state_var_oracle_map ;
    N.expr_state_var_map = top.N.expr_state_var_map ;
  } in

  (* Format.printf "@.%a@.@." (N.pp_print_node false) oracle ;

  Format.printf "slicing@.@." ; *)

  let sliced =
    N.reduce_to_coi (oracle :: subs) oracle_ident oracle_out_svs
  in

  (* ( match List.rev sliced with
    | oracle :: subs ->
      Format.printf "%a@.subs:@." (N.pp_print_node false) oracle ;
      subs
      |> List.iter
          (fun (n: N.t) ->
            Format.printf "  %a" (LustreIdent.pp_print_ident false) n.N.name)
    | _ -> assert false ) ; *)

  let out_file = Format.asprintf
    "%s/%a.lus" out_dir (LustreIdent.pp_print_ident false) oracle_ident
  in

  Format.printf "Writing oracle to %s@." out_file ;

  let file = Unix.openfile
    out_file [ Unix.O_TRUNC ; Unix.O_WRONLY ; Unix.O_CREAT ] 0o640
  in

  let out_fmt =
    Unix.out_channel_of_descr file |> Format.formatter_of_out_channel
  in

  Format.fprintf
    out_fmt "%a@?"
    (pp_print_list
      (N.pp_print_node ~no_subrange:true true)
      "@.@.")
    sliced ;

  Unix.close file ;
(* 
  ( match Flags.Testgenlustrec () with
    | None -> Format.printf "Skipping oracle compilation.@."
    | Some lustrec ->
      Format.printf "Compiling oracle.@." ;

      let lustrec_out_file = out_file ^ ".lustrec.out" in
      let cmd =
        Format.asprintf
          "%s -d %s -node %a -local -quiet_io %s &> %s"
          lustrec
          out_dir
          (LustreIdent.pp_print_ident false) oracle_ident
          out_file
          lustrec_out_file
      in
      Format.printf "> %s@." cmd ;
      ( match Unix.system cmd with
        | Unix.WEXITED 0 ->
          Format.printf "> done.@."
        | Unix.WEXITED n ->
          Format.printf "> error (%d), see \"%s\".@." n lustrec_out_file
        | Unix.WSIGNALED n ->
          Format.printf "> /!\\ killed by signal %d.@." n
        | Unix.WSTOPPED n ->
          Format.printf "> /!\\ stopped by signal %d.@." n ) ;

      Format.printf "Compiling C code.@." ;
      let cmd =
        (* (String.length out_file) - 3
        |> String.sub out_file 0 (String.length out_dir) *)
        Format.asprintf "\
          cd %s ; \
          make -f %a.makefile &> /dev/null ; \
          mv %a_%a %a"
          out_dir
          (LustreIdent.pp_print_ident false) oracle_ident
          (LustreIdent.pp_print_ident false) oracle_ident
          (LustreIdent.pp_print_ident false) oracle_ident
          (LustreIdent.pp_print_ident false) oracle_ident
      in
      Format.printf "> %s@." cmd ;
      ( match Unix.system cmd with
        | Unix.WEXITED 0 ->
          Format.printf "> done.@."
        | Unix.WEXITED n ->
          Format.printf "> error (%d).@." n
        | Unix.WSIGNALED n ->
          Format.printf "> /!\\ killed by signal %d.@." n
        | Unix.WSTOPPED n ->
          Format.printf "> /!\\ stopped by signal %d.@." n ) ) ; *)

  Format.printf "@." ;

  ()


let generate_oracle out_dir sys =
  Format.printf "generating oracle@.@." ;
  match TransSys.get_source sys with
  | TransSys.Lustre nodes ->
    let out_dir = out_dir ^ "/" ^ oracle_dir in
    mk_dir out_dir ;
    oracle_of_nodes out_dir nodes
  | TransSys.Native ->
    Format.asprintf
      "Cannot generate oracle for %a: native input is unsupported."
      TransSys.pp_print_trans_sys_name sys
    |> failwith

let main sys =

  let out_dir =
    Format.asprintf
      "%s/%a"
      (Flags.testgen_out_dir ())
      TransSys.pp_print_trans_sys_name sys
  in

  (* Creating output directory. *)
  mk_dir out_dir ;

  (* Generating the oracle. *)
  generate_oracle out_dir sys ;

  (* The strategies to run. *)
  let strategies = [ Strats.unit_mode_switch ] in

  (* Running the strategies, retrieving the name of the xml files. *)
  let subfiles = try
    strategies |> List.map (run_strategy out_dir sys)
  with e ->
    delete_solver () ;
    raise e
  in

  Format.printf "@." ;

  (* Generating the xml file aggregating all tests. *)
  let xml_file = out_dir ^ "/tests.xml" in
  Format.printf "Generating global xml file@." ;
  Format.printf "  %s@." xml_file ;
  let xml_file =
    Unix.openfile
      xml_file [ Unix.O_TRUNC ; Unix.O_WRONLY ; Unix.O_CREAT ] 0o640
  in
  let xml_fmt =
    Unix.out_channel_of_descr xml_file |> Format.formatter_of_out_channel
  in

  Xml.pp_header xml_fmt ;
  TransSys.get_name sys
  |> Xml.pp_necker xml_fmt ;
  (* Oracle things. *)
  TransSys.get_contracts sys
  |> List.map (
    fun (_, _, name) ->
      match TransSys.contract_is_global sys name with
      | Some b -> b, name
      | None -> assert false
  )
  |> Xml.pp_oracle xml_fmt (oracle_path out_dir sys) ;
  (* Tests xml files. *)
  Xml.pp_tests xml_fmt subfiles ;
  (* Footer. *)
  Xml.pp_footer_flush xml_fmt ;

  (* Close file. *)
  Unix.close xml_file ;



  Format.printf "@."


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)