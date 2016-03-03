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

(* Entry for a debug section *)
type debug_section = 
  { formatter : Format.formatter;
    mutable seq : int;
    enabled_time : float; }

(* Formatters for enabled debug sections

   Start with defaults to enable debug output before flags have been
   parsed *)
let section_formatters = ref [("*", 
                               { formatter = Format.std_formatter; 
                                 enabled_time = Unix.gettimeofday ();
                                 seq = 1 })]

(* Set to true after the first call to enable a debug section *)
let initialized = ref false


(* Initialize debug output by removing the default output *)
let initialize () = 

  (* Remove default debug section *)
  if not !initialized then (initialized := true; section_formatters := [])
  

(* Check if debug section is enabled *)
let mode section = 

  (* A section is enabled if a formatter has been associated with it
     or there is a global formatter *)
  (List.mem_assoc section !section_formatters) || 
    (List.mem_assoc "*" !section_formatters)


(* Return the formatter for a debug section 

   The debug section must be enabled or all sections must be enabled
   globally, otherwise the exception {!Not_found} is raised. *)
let formatter_of_section section = 

  try 

    (* Get the individual formatter for the section *)
    (List.assoc section !section_formatters).formatter

  with Not_found -> 

    (* Get the global formatter for all sections *)
    (List.assoc "*" !section_formatters).formatter


(* Return the timestamp for a debug section 

   The debug section must be enabled or all sections must be enabled
   globally, otherwise the exception {!Not_found} is raised. *)
let timestamp_of_section section = 

  let enabled_time = 

    try 
      
      (* Get the individual formatter for the section *)
      (List.assoc section !section_formatters).enabled_time
        
    with Not_found -> 
      
      (* Get the global formatter for all sections *)
      (List.assoc "*" !section_formatters).enabled_time 

  in

  (Unix.gettimeofday ()) -. enabled_time


(* Return the sequence number for a debug section 

   The debug section must be enabled or all sections must be enabled
   globally, otherwise the exception {!Not_found} is raised. *)
let seq_of_section section = 

  let entry = 

    try 
    
      (* Get the individual formatter for the section *)
      List.assoc section !section_formatters
        
    with Not_found -> 
      
      (* Get the global formatter for all sections *)
      List.assoc "*" !section_formatters

  in

  let res = entry.seq in

  entry.seq <- succ entry.seq;

  res



(* Enable a debug section *)
let enable section fmt = 

  (* Initialize debug sections to empty if this is the first call *)
  initialize ();

  (* Check if debug section has had a formatter associated *)
  if mode section then 

    (* Do not enable twice, this would shadow previous formatter,
       which would become visible again after disabling the section *)
    invalid_arg 
      (Format.sprintf "Debug section %s is already enabled" section)
      
  else
    
    (* Add association of section with its formattter to head of list *)
    section_formatters := 
      (section, 
       { formatter = fmt; 
         enabled_time = Unix.gettimeofday ();
         seq = 1 }) :: 
        !section_formatters


(* Enable a debug section *)
let enable_all ppf = 

  (* Initialize debug sections to empty if this is the first call *)
  initialize ();

  (* Check if debug sections are enabled *)
  match !section_formatters with 

    (* No debug sections are enabled, add global formatter *)
    | [] -> 

      section_formatters := 
        [("*", 
          { formatter = ppf; 
            enabled_time = Unix.gettimeofday ();
            seq = 1 })]

    | _ -> 

      (* Do not add global formatter if there is a section with an
         individual formatter *)
      invalid_arg "Individual debug section already enabled"

        
(* Disable a debug section *)
let disable section = 

  (* Initialize debug sections to empty if this is the first call *)
  initialize ();

  (* Remove association of section with a formattter from list *)
  section_formatters := List.remove_assoc section !section_formatters


(* Disable a debug section *)
let disable_all () = 
  
  (* Remove all associations of sections with a formattter *)
  section_formatters := []


(* Output a message for an debug section *)
let printf section fmt = 

  (* We know that the section is enabled, {!List.assoc} will not fail *)
  Format.fprintf
    (formatter_of_section section)
    ("@[<hv %i>@{<b>[@}@{<cyan>%s@}, %.3f/%d@{<b>]@}@ @[<hv>" ^^fmt^^ "@]@]@.")
    ((String.length section) + 3)
    section
    (timestamp_of_section section)
    (seq_of_section section)
    
        
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
