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

(** Kind-1 parser 

    Parse a Lustre file with the Kind-1 parser into a transition
    system.

    @author Christoph Sticksel
*)


(** Convert a Kind-1 IL expression to a term *)
val il_expression_to_term : bool -> Kind1.Types.lustre_type option * Kind1.Types.il_expression -> Term.t

(** Convert a Kind-1 IL formula to a term *)
val il_formula_to_term : bool -> Kind1.Types.il_formula -> Term.t

(** Parse from the channel *)
val of_channel : in_channel -> TransSys.t

(** Parse from the file *)
val of_file : string -> TransSys.t


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
