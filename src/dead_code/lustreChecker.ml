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
assert false

let pp_print_position ppf 
    { Lexing.pos_fname;
      Lexing.pos_lnum;
      Lexing.pos_bol;
      Lexing.pos_cnum } =

  Format.fprintf ppf 
    "@[<hv 2>{ pos_fname : %s;@ \
     pos_lnum : %d;@ \
     pos_bol : %d;@ \
     pos_cnum : %d; }@]"
    pos_fname
    pos_lnum
    pos_bol
    pos_cnum

let main () = 

  Debug.initialize ();
  Debug.enable "smt" Format.std_formatter;
  Debug.enable "extract" Format.std_formatter;
  Debug.enable "simplify" Format.std_formatter;

  try 

    Sys.catch_break true;

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
    let nodes = LustreSimplify.declarations_to_nodes declarations in

    (* Find main node by annotation *)
    let main_node = LustreNode.find_main nodes in

    Format.printf 
      "@[<v>Before slicing@,%a@]@."
      (pp_print_list (LustreNode.pp_print_node false) "@,") nodes;

    (* Consider only nodes called by main node *)
    let nodes_coi = 
      List.map
        (LustreNode.equations_order_by_dep nodes)
        (LustreNode.reduce_to_property_coi nodes main_node) 
    in

    Format.printf 
      "@[<v>After slicing@,%a@]@."
      (pp_print_list (LustreNode.pp_print_node false) "@,") nodes_coi;

    (* Create transition system of Lustre nodes *)
    let fun_defs, state_vars, init, trans = 
      LustreTransSys.trans_sys_of_nodes nodes_coi
    in

    (* Create Kind transition system *)
    let trans_sys = 
      TransSys.mk_trans_sys 
        fun_defs
        state_vars
        init
        trans
        []
    in

    Format.printf "%a@." TransSys.pp_print_trans_sys trans_sys;

    (* Create solver instance *)
    let solver = 
      SMTSolver.new_solver
        ~produce_assignments:true 
        `QF_UFLIA
        (Flags.smtsolver ())
    in

    List.iter
      (SMTSolver.declare_fun solver)
      (TransSys.uf_symbols_of_trans_sys trans_sys);

    List.iter 
      (fun (u, (v, t)) -> SMTSolver.define_fun solver u v t)
      fun_defs;

    SMTSolver.assert_term solver init;

    SMTSolver.assert_term solver trans;

    (if SMTSolver.check_sat solver then 
       
       let val_0 = 
         SMTSolver.get_model
           solver
           (List.map
              (fun sv -> Var.mk_state_var_instance sv Numeral.zero)
              state_vars)
       in

       let val_1 = 
         SMTSolver.get_model
           solver
           (List.map
              (fun sv -> Var.mk_state_var_instance sv Numeral.one)
              state_vars)
       in

       Format.printf
         "@[<v>Model:@,%a@]@."
         (pp_print_list 
           (fun ppf (v, a) -> 
             Format.fprintf ppf
               "%a: %a"
               Var.pp_print_var v
               Term.pp_print_term a)
           "@,")
         (val_0 @ val_1);

       let trans_extract = 
         Extract.extract 
           fun_defs
           (val_1 @ val_0)
           trans
       in

       Format.printf 
         "@[<v>Extract@,%a@,%a@]@."
         Term.pp_print_term (fst trans_extract)
         Term.pp_print_term (snd trans_extract) 

     else

       Format.printf "Transition system is unsatisfiable@.")


  with Sys.Break -> exit 0

;;

main ()

(* 
   Local Variables:
   compile-command: "make -C .. lustre-checker"
   indent-tabs-mode: nil
   End: 
*)
  
