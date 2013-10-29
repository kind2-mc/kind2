(*
This file is part of the Kind verifier

* Copyright (c) 2007-2013 by the Board of Trustees of the University of Iowa, 
* here after designated as the Copyright Holder.
* All rights reserved.
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
*     * Redistributions of source code must retain the above copyright
*       notice, this list of conditions and the following disclaimer.
*     * Redistributions in binary form must reproduce the above copyright
*       notice, this list of conditions and the following disclaimer in the
*       documentation and/or other materials provided with the distribution.
*     * Neither the name of the University of Iowa, nor the
*       names of its contributors may be used to endorse or promote products
*       derived from this software without specific prior written permission.
*
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
* WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
* DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
* (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
* LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
* ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
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
    ("@[<hv %i>[%s, %.3f/%d] " ^^ fmt ^^ "@]@.")
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
