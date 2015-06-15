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


(** [enable s f] enables the debug tag [c] and prints the messages
    to the formatter [f] 

    An [Invalid_argument] exception is raised if the debug section
    has been enabled before. *)
val enable : string -> Format.formatter -> unit

(** [enable_all s f] enables all debug sections and prints their
    messages to the formatter [f]

    An [Invalid_argument] exception is raised if a debug section
    has been enabled individually before. *)
val enable_all : Format.formatter -> unit

(** [disable c] disables the debug tag [c] *)
val disable : string -> unit

(** [disable_all ()] disables all debug sections *)
val disable_all : unit -> unit

(** Remove default output of all debug sections if there was no previous call to {!enable} or {!enable_all} *)
val initialize : unit -> unit 

(** [mode c] returns true if debugging is enabled for the tag [c] *)
val mode : string -> bool

(** [printf c f v] logs a debug message for tag [c], formatted with
    the parameterized string [f] and the values [v] *)
val printf : string -> ('a, Format.formatter, unit) format -> 'a

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

