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

(** Debug ouput, support for Camlp4 module

    Debug output is handled with the [Camlp4DebugParser] from the
    Camlp4 standard preprocessing libraries.

    [Camlp4DebugParser] introduces a new keyword [debug] in two
    variants: 

    [(debug {section} {format} {arg1} ... {argN} end);] 

    [debug {section} {format} {arg1} ... {argN} in] 

    Every debug message is tagged with a section, each section can be
    dynamically enabled or disabled at runtime or statically removed
    at compile-time. The section must be a lowercase keyword, not a
    quoted string.

    The first variant can be used anywhere, but must be put in
    parentheses. If compiled out, it becomes a unit value. The second
    variant can be used like a [let ... in] operator, but it may need
    to be wrapped in parentheses. If compiled out, the second variant
    disappears completely, therefore it is the preferred variant.

    The first variant is expanded to 

    [if Debug.mode {section}
    then Debug.printf {section} {format} {arg1} ... {argN} 
    else ();]

    wheras the second variant is expanded to 

    [let () = 
    if Debug.mode {section}
    then Debug.printf {section} {format} {arg1} ... {argN} 
    else () 
    in].

    The format string must not flush the formatter, this is done by
    {!printf} itself and would interfere with the indentation. For the
    same reason, line breaks with the conversion [@\\n] should not be
    used.

    The [Camlp4DebugParser] reads the environment variable
    [STATIC_CAMLP4_DEBUG], which is a colon separated list of enabled
    debug sections or an asterisk indicating that all sections are
    enabled.

    In order to enable a debug section at runtime, a call to {!enable}
    is required for each section and a [Format.formatter] must be
    given. Each debug section outputs into its associated formatter.

    @author Christoph Sticksel *)


(** Types of debug functions *)
(* type t = (unit, Format.formatter, unit, unit, unit, unit) format6 -> unit *)
type 'a t = ('a, Format.formatter, unit) format -> 'a

val set_formatter : Format.formatter -> unit

val certif : 'a t
val event : 'a t
val extract : 'a t
val fec : 'a t
val invgencand : 'a t
val kind2 : 'a t
val ltree : 'a t
val messaging : 'a t
val parse : 'a t
val qe : 'a t
val qedetailed : 'a t
val simplify : 'a t
val smt : 'a t
val smtexpr : 'a t
val transsys : 'a t
val c2i : 'a t
val ic3 : 'a t
val compress : 'a t
val native : 'a t

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

