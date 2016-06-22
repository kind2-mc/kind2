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

let dflags = Flags.debug ()

let certif =     List.mem "all" dflags || List.mem "certif" dflags
let event =      List.mem "all" dflags || List.mem "event" dflags
let extract =    List.mem "all" dflags || List.mem "extract" dflags
let fec =        List.mem "all" dflags || List.mem "fec" dflags
let invgencand = List.mem "all" dflags || List.mem "invgencand" dflags
let kind2 =      List.mem "all" dflags || List.mem "kind2" dflags
let ltree =      List.mem "all" dflags || List.mem "ltree" dflags
let messaging =  List.mem "all" dflags || List.mem "messaging" dflags
let parse =      List.mem "all" dflags || List.mem "parse" dflags
let qe =         List.mem "all" dflags || List.mem "qe" dflags
let qedetailed = List.mem "all" dflags || List.mem "qedetailed" dflags
let simplify =   List.mem "all" dflags || List.mem "simplify" dflags
let smt =        List.mem "all" dflags || List.mem "smt" dflags
let smtexpr =    List.mem "all" dflags || List.mem "smtexpr" dflags
let transsys =   List.mem "all" dflags || List.mem "transsys" dflags
let c2i =        List.mem "all" dflags || List.mem "c2i" dflags
let ic3 =        List.mem "all" dflags || List.mem "ic3" dflags
let compress =   List.mem "all" dflags || List.mem "compress" dflags
let native =     List.mem "all" dflags || List.mem "native" dflags


let enabled_time = Unix.gettimeofday ()

let ppf = ref Format.std_formatter

let set_formatter f = ppf := f


(* Types of debug functions *)
type 'a t = ('a, Format.formatter, unit) format -> 'a


(* Output a message for an debug section *)
let printf cond section fmt = 
  let fprintf = if cond then Format.fprintf else Format.ifprintf in
  fprintf !ppf
    ("@[<hv %i>@{<b>[@}@{<cyan_b>%s@}, @{<cyan>%.3f@}@{<b>]@}@ @[<hv>" ^^fmt^^ "@]@]@.")
    ((String.length section) + 3)
    section
    (Unix.gettimeofday () -. enabled_time)


(* Instantiated debug functions *)
let certif fmt = printf certif "certif" fmt
let event fmt = printf event "event" fmt
let extract fmt = printf extract "extract" fmt
let fec fmt = printf fec "fec" fmt
let invgencand fmt = printf invgencand "invgencand" fmt
let kind2 fmt = printf kind2 "kind2" fmt
let ltree fmt = printf ltree "ltree" fmt
let messaging fmt = printf messaging "messaging" fmt
let parse fmt = printf parse "parse" fmt
let qe fmt = printf qe "qe" fmt
let qedetailed fmt = printf qedetailed "qedetailed" fmt
let simplify fmt = printf simplify "simplify" fmt
let smt fmt = printf smt "smt" fmt
let smtexpr fmt = printf smtexpr "smtexpr" fmt
let transsys fmt = printf transsys "transsys" fmt
let c2i fmt = printf c2i "c2i" fmt
let ic3 fmt = printf ic3 "ic3" fmt
let compress fmt = printf compress "compress" fmt
let native fmt = printf native "native" fmt


        
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
