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

(** Lexer for Lustre input 

    This lexer supports nested include files by maintaining a stack of
    lexing buffers, with the one for the currently processed file at
    the top. If an [include] directive is encountered, open the
    referenced file, create a new lexing buffer and push it to the
    stack. Catch end of file exceptions, pop the now empty buffer of
    the stack, and continue with the buffer below.

    Call {!lexbuf_init} with the first channel to parse, and the
    directory to search for include files. Then create the lexing
    buffer with [Lexing.from_function
    LustreLexer.read_from_lexbuf_stack].

    {1 Lexical conventions} 
    
    The character sequence [include "FILE"], where [FILE] is a
    relative or absolute path, is replaced with the contents of
    [FILE]. The [include] directive may appear at any position in the
    input. Recursive includes are allowed. Positions are labeled by
    line, column and file name.

    The token [--] is a comment, everything following the token until
    the end of the line is discarded, unless the comment is a special
    comment, see below. Multi-line comments can be enclosed in [/*]
    and [*/], or [(*] and [*)].

    The following special comments are parsed:

    - [--%MAIN] marks the node containing the annotation as the top
      node. Only one annotation is allowed in the whole input. The
      rest of the line is ignored, in particular it does not matter
      whether the comment is terminated by a [;] or not.

    - [--%PROPERTY] or [--\@property] must be followed by a Lustre
      expression and a [;], it marks a proof obligation for the node
      that contains the comment.

    - [--\@var], [--\@const], [--\@import], [--\@import_mode],
      [--\@contract], [--\@require] and [--\@ensure] are annotations for
      contracts

    - [--!<key> : <value>;] are the following aliases 

      - [--!main : true;] is [--%MAIN]
      - [--!property : EXPR;] is [--%PROPERTY EXPR;]
      - [--!var : DEF;] is [--\@var DEF]
      - [--!const : DEF;] is [--\@const DEF;]
      - [--!import : ID;] is [--\@import ID;]
      - [--!import_mode : ID;] is [--\@import-mode ID]
      - [--!contract : ID;] is [--\@contract ID]
      - [--!require : EXPR;] is [--\@require EXPR;]
      - [--!ensure : EXPR;] is [--\@ensure EXPR;]

    Unrecognized [--%] and [--\@] comments result in a failure, but any
    [--!] comments are accepted with a warning.

    @author Christoph Sticksel *)

(** Initialize the lexing function *)
val lexbuf_init : in_channel -> string -> unit

(** Create a lexer reading from a stack of nested include files *)
val read_from_lexbuf_stack : bytes -> int -> int

(** Entry point for the lexer *)
val token : Lexing.lexbuf -> LustreParser.token
