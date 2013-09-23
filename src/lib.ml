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

(* ********************************************************************** *)
(* Arithmetic functions                                                   *)
(* ********************************************************************** *)

(* Compute [m * h + i] and make sure that the result does not overflow
   to a negtive number *)
let safe_hash_interleave h m i = abs(i + (m * h) mod max_int)

(* ********************************************************************** *)
(* List functions                                                         *)
(* ********************************************************************** *)

(* Return the first n elements of a list *)
let rec list_first_n' a l n =
  if n = 0 then a else 
    list_first_n' 
      ((try List.nth l (pred n) with 
        | Failure _ -> invalid_arg "Lib.list_first_n") :: a) 
      l
      (pred n) 


(* Return the first n elements of a list *)
let list_first_n l n = list_first_n' [] l n 

let rec list_from_n l n = 
  if n = 0 then l else
    list_from_n 
      (try List.tl l with Failure _ -> invalid_arg "Lib.list_first_n")
      (pred n)


(* [chain_list \[e1; e2; ...\]] is \[\[e1; e2\]; \[e2; e3\]; ... \]]*)
let chain_list = function 

  | [] 
  | _ :: [] -> invalid_arg "chain_list"

  | h :: tl -> 
    
    let rec chain_list (accum, last) curr = ([last; curr] :: accum, curr) in
    List.rev (fst (List.fold_left chain_list ([], h) tl))



(* Return a list containing all values in the first list that are not
    in the second list *)
let list_subtract l1 l2 = 
  List.filter
    (function e -> not (List.mem e l2))
    l1


(* From a sorted list return a list with physical duplicates removed *)
let list_uniq l = 
  let rec list_uniq accum = function 
    | [] -> List.rev accum
    | h1 :: tl -> 
      match accum with 
        | [] -> list_uniq [h1] tl
        | h2 :: _ -> 
          if h1 == h2 then list_uniq accum tl else list_uniq (h1 :: accum) tl
  in

  list_uniq [] l


(* Merge two sorted lists without physical duplicates to a sorted list without
   physical duplicates *)
let list_merge_uniq cmp l1 l2 = 
  
  let rec list_merge_uniq cmp accum l1 l2 = match l1, l2 with

    (* One of the lists is empty: reverse accumulator, append
       other list and return *)
    | [], l 
    | l, [] -> List.rev_append accum l

    (* First and second head elements are physically equal: remove
       head element from second list *)
    | h1 :: _, h2 :: tl when h1 == h2 -> list_merge_uniq cmp accum l1 tl

    (* First head element is smaller than second: add first head
       element to accumulator *)
    | h1 :: tl, h2 :: _ when cmp h1 h2 < 0 -> 
      list_merge_uniq cmp (h1 :: accum) tl l2

    (* First head element is greater than second: add second head
       element to accumulator *)
    | h1 :: _, h2 :: tl when cmp h1 h2 > 0 -> 
      list_merge_uniq cmp (h2 :: accum) l1 tl

    (* Head elements are structurally but not physically equal: keep
       both in original order *)
    | h1 :: tl1, h2 :: tl2 -> 
      list_merge_uniq cmp (h2 :: h1 :: accum) tl1 tl2
  in

  list_merge_uniq cmp [] l1 l2


(* From two sorted lists without physical duplicates return a sorted
   list without physical duplicates containing elements in both lists *)
let list_inter_uniq cmp l1 l2 = 

  let rec list_inter_uniq cmp accum l1 l2 = match l1, l2 with 

    (* One of the lists is empty: reverse accumulator and return *)
    | [], l
    | l, [] -> List.rev accum

    (* First and second head elements are physically equal: add first
       head element to accumulator *)
    | h1 :: tl1, h2 :: tl2 when h1 == h2 -> 
      list_inter_uniq cmp (h1 :: accum) tl1 tl2

    (* First head element is smaller than second: remove first head
       element from list *)
    | h1 :: tl, h2 :: _ when cmp h1 h2 < 0 -> 
      list_inter_uniq cmp accum tl l2

    (* First head element is greater than or structurally but not
       physically equal to second: remove second head element from
       list *)
    | h1 :: _, h2 :: tl ->
      list_inter_uniq cmp accum l1 tl
  in

  list_inter_uniq cmp [] l1 l2


(* From two sorted lists without physical duplicates return a sorted
   list without physical duplicates containing elements in the first
   but not in the second list *)
let list_diff_uniq cmp l1 l2 = 

  let rec list_diff_uniq cmp accum l1 l2 = match l1, l2 with 

    (* First list is empty: reverse accumulator and return *)
    | [], l -> List.rev accum

    (* Second list is empty: reverse accumulator, append first list
       and return *)
    | l, [] -> List.rev_append accum l

    (* First and second head elements are physically equal: remove
       both head elements *)
    | h1 :: tl1, h2 :: tl2 when h1 == h2 -> 
      list_diff_uniq cmp accum tl1 tl2

    (* First head element is smaller than second: add first head
       element to accumulator *)
    | h1 :: tl, h2 :: _ when cmp h1 h2 < 0 -> 
      list_diff_uniq cmp (h1 :: accum) tl l2

    (* First head element is greater than second: remove first head
       element from list *)
    | h1 :: _, h2 :: tl ->
      list_diff_uniq cmp accum l1 tl
  in

  list_diff_uniq cmp [] l1 l2


(* For two sorted lists without physical duplicates return true if the
   first list contains a physically equal element for each element in
   the second list *)
let rec list_subset_uniq cmp l1 l2 = match l1, l2 with 

  (* Both lists are empty: return true *)
  | [], [] -> true

  (* First list is empty, but second list not: return true *)
  | [], _ -> true

  (* Second list is empty, but first list not: return false *)
  | _, [] -> false

  (* First and second head elements are physically equal: remove
     both head elements *)
  | h1 :: tl1, h2 :: tl2 when h1 == h2 -> list_subset_uniq cmp tl1 tl2

  (* First head element is smaller than second: return false *)
  | h1 :: tl, h2 :: _ when cmp h1 h2 < 0 -> false

  (* First head element is greater than the second or structurally
     but not physically equal: remove first head element *)
  | h1 :: _, h2 :: tl -> list_subset_uniq cmp l1 tl


(* Lexicographic comparison of lists *)
let rec compare_lists f l1 l2 = 

    match l1, l2 with 

      (* Two empty lists are equal *)
      | [], [] -> 0

      (* An empty list is smaller than a non-empty list *)
      | [], _ -> -1 

      (* An non-empty list is greater than an empty list *)
      | _, [] -> 1

      (* Compare two non-empty lists *)
      | h1 :: tl1, h2 :: tl2 -> 

        (* Compare head elements of lists *)
        let c = f h1 h2 in

        (* If head elements are equal, compare tails of lists,
           otherwise return comparison of head elements *)
        if c = 0 then compare_lists f tl1 tl2 else c


(* ********************************************************************** *)
(* Genric pretty-printing                                                 *)
(* ********************************************************************** *)


(* Pretty-print a list *)
let rec pp_print_list pp sep ppf = function 

  (* Output nothing for the empty list *) 
  | [] -> ()

  (* Output a single element in the list  *) 
  | e :: [] -> 
    pp ppf e

  (* Output a single element and a space *) 
  | e :: tl -> 

    (* Output one element *)
    pp_print_list pp sep ppf [e]; 

    (* Output separator *)
    Format.fprintf ppf sep; 

    (* Output the rest of the list *)
    pp_print_list pp sep ppf tl


(* Pretty-print a list wrapped in parentheses *)
let pp_print_paren_list ppf list = 
      
  (* Begin expression with opening parenthesis *)
  Format.pp_print_string ppf "(";
  
  (* Output elements of list *)
  pp_print_list Format.pp_print_string " " ppf list;

  (* End expression with closing parenthesis *)
  Format.pp_print_string ppf ")"


(* Pretty-print an option type *)
let pp_print_option pp ppf = function 
  | None -> Format.fprintf ppf "None"
  | Some s -> Format.fprintf ppf "@[<hv>Some@ %a@]" pp s


(* Pretty-print into a string *)
let string_of_t pp t = 

  (* Create a buffer *)
  let buf = Buffer.create 80 in
  
  (* Create a formatter printing into the buffer *)
  let ppf = Format.formatter_of_buffer buf in

  (* Output into buffer *)
  pp ppf t;
  
  (* Flush the formatter *)
  Format.pp_print_flush ppf ();
  
  (* Return the buffer contents *)
  Buffer.contents buf


(* Return the strings as a parenthesized and space separated list *)
let paren_string_of_string_list list =
  string_of_t pp_print_paren_list list


(* ********************************************************************** *)
(* Numerals, decimals and bitvectors                                      *)
(* ********************************************************************** *)


(* Infinite-precision integer numeral *)
type numeral = HString.t


(* Infinite-precision real decimal *)
type decimal = HString.t


(* Constant bitvector *)
type bitvector = bool list


let (+%) a b = 
  HString.mk_hstring 
    (string_of_int 
       (int_of_string (HString.string_of_hstring a) + 
          int_of_string (HString.string_of_hstring b)))

let (+/) a b = 
  HString.mk_hstring 
    (string_of_float 
       (float_of_string (HString.string_of_hstring a) +. 
          float_of_string (HString.string_of_hstring b)))


(* Pretty-print an infinite-precision integer numeral *)
let pp_print_numeral = HString.pp_print_hstring 


(* Pretty-print an infinite-precision real decimal *)
let pp_print_decimal = HString.pp_print_hstring 


(* Pretty-print a bitvector in binary format without #b prefix *)
let rec pp_print_bitvector_b' ppf = function 
  | [] -> ()
  | true :: tl -> Format.pp_print_int ppf 1; pp_print_bitvector_b' ppf tl
  | false :: tl -> Format.pp_print_int ppf 0; pp_print_bitvector_b' ppf tl


(* Pretty-print a bitvector in binary format *)
let pp_print_bitvector_b ppf b = 
  Format.fprintf ppf "#b%a" pp_print_bitvector_b' b


(* Pretty-print a bitvector in binary format without #b prefix *)
let rec pp_print_bitvector_b' ppf = function 
  | [] -> ()
  | true :: tl -> Format.pp_print_int ppf 1; pp_print_bitvector_b' ppf tl
  | false :: tl -> Format.pp_print_int ppf 0; pp_print_bitvector_b' ppf tl


(* Association list of bitvectors to hexadecimal digits *)
let bv_hex_table = 
  [([false; false; false; false], "0");
   ([false; false; false; true],  "1");
   ([false; false; true; false],  "2");
   ([false; false; true; true],   "3");
   ([false; true; false; false],  "4");
   ([false; true; false; true],   "5");
   ([false; true; true; false],   "6");
   ([false; true; true; true],    "7");
   ([true; false; false; false],  "8");
   ([true; false; false; true],   "9");
   ([true; false; true; false],   "A");
   ([true; false; true; true],    "B");
   ([true; true; false; false],   "C");
   ([true; true; false; true],    "D");
   ([true; true; true; false],    "E");
   ([true; true; true; true]),    "F"]

(* Association list of hexadecimal digits to bitvectors *)
let hex_bv_table = 
  [("0", [false; false; false; false]);
   ("1", [false; false; false; true]);
   ("2", [false; false; true; false]);
   ("3", [false; false; true; true]);
   ("4", [false; true; false; false]);
   ("5", [false; true; false; true]);
   ("6", [false; true; true; false]);
   ("7", [false; true; true; true]);
   ("8", [true; false; false; false]);
   ("9", [true; false; false; true]);
   ("A", [true; false; true; false]);
   ("B", [true; false; true; true]);
   ("C", [true; true; false; false]);
   ("D", [true; true; false; true]);
   ("E", [true; true; true; false]);
   ("F", [true; true; true; true]);
   ("a", [true; false; true; false]);
   ("b", [true; false; true; true]);
   ("c", [true; true; false; false]);
   ("d", [true; true; false; true]);
   ("e", [true; true; true; false]);
   ("f", [true; true; true; true])] 


(* Pretty-print a bitvector in hexadecimal format *)
let rec pp_print_bitvector_x' ppf = function

  (* Print nothing for the empty bitvector *)
  | [] -> ()

  (* Pad with a false bit if less than four bits *)
  | d :: ([] as tl)
  | d :: ([_] as tl) 
  | d :: ([_; _] as tl) ->
    pp_print_bitvector_x' ppf (false :: d :: tl)

  (* Print a hexadecimal digit for the first four bits *)
  | d1 :: d2 :: d3 :: d4 :: tl -> 
    Format.pp_print_string 
      ppf 
      (List.assoc ([d1; d2; d3; d4]) bv_hex_table);
    pp_print_bitvector_x' ppf tl
    
      
(* Pretty-print a bitvector in hexadecimal format *)
let pp_print_bitvector_x ppf b = 
  
  Format.pp_print_string ppf "#X";
  
  match (List.length b) mod 4 with 
    | 0 -> pp_print_bitvector_x' ppf b
    | i -> 
      pp_print_bitvector_x' ppf (list_first_n b i);
      pp_print_bitvector_x' ppf (list_from_n b i)


(* Convert an OCaml integer to an infinite-precision integer numeral *)
let numeral_of_int i = HString.mk_hstring (Printf.sprintf "%i%!" i)


(* Convert an OCaml float to an infinite-precision real decimal *)
let decimal_of_float f = 

  if floor f = ceil f then 
    HString.mk_hstring (Printf.sprintf "%F0%!" f)
  else
    HString.mk_hstring (Printf.sprintf "%F%!" f)
      

(* Convert an infinite-precision integer numeral to an OCaml integer *)
let int_of_numeral n = int_of_string (HString.string_of_hstring n)


(* Convert an OCaml float to an infinite-precision real decimal *)
let float_of_decimal d = float_of_string (HString.string_of_hstring d)


(* Increment a numeral by one *)
let incr_numeral n = n +% (numeral_of_int 1)


(* Convert a bitvector to an integer *)
let int_of_bitvector b = 
  List.fold_left (fun a b -> a lsl 1 + (if b then 1 else 0)) 0 b


(* Convert a bitvector to an integer *)
let length_of_bitvector b = numeral_of_int (List.length b)


(* A sequence of digits without leading zero *)
let numeral_of_string s = 

  try

    (* Scan string as a signed integer and discard*)
    Scanf.sscanf s "%_d%!" ();

    (* Return as string *)
    HString.mk_hstring s

  with 

    (* Raise exception if scanning fails *)
    | Scanf.Scan_failure _
    | End_of_file
    | Failure _ -> raise (Invalid_argument "smtlib_numeral_of_string")


(* A numeral followed by a decimal point followed by a sequence of digits *)
let decimal_of_string s = 
  
  try 
    
    (* Ensure that string consists of exactly a signed decimal, a
       decimal point and an unsigned decimal *)
    Scanf.sscanf s "%_d.%_u%!" ();

    (* Scan string as a floating point number and discard *)
    Scanf.sscanf s "%_f" ();

    (* Return as string *)
    HString.mk_hstring s

  with 

    (* Raise exception if scanning fails *)
    | Scanf.Scan_failure _
    | End_of_file
    | Failure _ -> raise (Invalid_argument "smtlib_decimal_of_string")


(* Convert a sequence of binary digits to a constant bitvector *)
let rec bitvector_of_string_b a i s = 

  if i <= 1 then a else
    
    match String.sub s i 1 with 

      | "0" -> bitvector_of_string_b (false :: a) (pred i) s
      | "1" -> bitvector_of_string_b (true :: a) (pred i) s
      | _ -> raise (Invalid_argument "bitvector_of_string")


(* Convert a sequence of hexadecimal digits to a constant bitvector *)
let rec bitvector_of_string_x a i s = 
  
  if i <= 1 then a else
    
    try 

      bitvector_of_string_x
        ((List.assoc (String.sub s i 1) hex_bv_table ) @ a)
        (pred i)
        s

    with Not_found -> 

      raise (Invalid_argument "bitvector_of_string")


(* Convert a string to a constant bitvector *)
let bitvector_of_string s = 

  match 
    
    (* First two characters must be #b or #x *)
    (try 
       String.sub s 0 2 
     with
         Invalid_argument _ -> 
           raise (Invalid_argument "bitvector_of_string"))
      
  with 
      
    (* Convert from a binary string *)
    | "#b" -> bitvector_of_string_b [] ((String.length s) - 1) s

    (* Convert from a hexadecimal string *)
    | "#x" -> bitvector_of_string_x [] ((String.length s) - 1) s
      
    (* Invalid prefix *)
    | _ -> raise (Invalid_argument "bitvector_of_string")


(* Cache for conversions of strings to numerals *)
let hstring_numeral_cache = HString.HStringHashtbl.create 7

(* Convert a hashconsed string to a numeral using the cache *)
let numeral_of_hstring s =

  (* Return cached value if available *)
  try HString.HStringHashtbl.find hstring_numeral_cache s with 

    | Not_found -> 
      
      (* Convert string to a numeral *)
      let n = numeral_of_string (HString.string_of_hstring s) in
      
      (* Add to cache *)
      HString.HStringHashtbl.add hstring_numeral_cache s n;

      (* Return numeral *)
      n

(* Cache for conversions of strings to decimals *)
let hstring_decimal_cache = HString.HStringHashtbl.create 7

(* Convert a hashconsed string to a decimal using the cache *)
let decimal_of_hstring s =

  (* Return cached value if available *)
  try HString.HStringHashtbl.find hstring_decimal_cache s with 

    | Not_found -> 
      
      (* Convert string to a decimal *)
      let n = decimal_of_string (HString.string_of_hstring s) in
      
      (* Add to cache *)
      HString.HStringHashtbl.add hstring_decimal_cache s n;

      (* Return decimal *)
      n


(* Cache for conversions of strings to bitvectors *)
let hstring_bitvector_cache = HString.HStringHashtbl.create 7

(* Convert a hashconsed string to a bitvector using the cache *)
let bitvector_of_hstring s =

  (* Return cached value if available *)
  try HString.HStringHashtbl.find hstring_bitvector_cache s with 

    | Not_found -> 
      
      (* Convert string to a bitvector *)
      let n = bitvector_of_string (HString.string_of_hstring s) in
      
      (* Add to cache *)
      HString.HStringHashtbl.add hstring_bitvector_cache s n;

      (* Return bitvector *)
      n


(* Convert an infinite-precision integer numeral to a string *)
let string_of_numeral s = HString.string_of_hstring s 


(* Convert an infinite-precision real decimal to a string *)
let string_of_decimal s = HString.string_of_hstring s 


(* Convert a hashconsed string to a Boolean value *)
let bool_of_hstring s = bool_of_string (HString.string_of_hstring s) 

(* ********************************************************************** *)
(* System functions                                                       *)
(* ********************************************************************** *)

(* Kind modules *)
type kind_module = [ `PDR | `BMC | `IND | `INVGEN | `INVMAN | `Interpreter ]


(* Pretty-print the type of the process *)
let pp_print_kind_module ppf = function
  | `PDR -> Format.fprintf ppf "PDR"
  | `BMC -> Format.fprintf ppf "BMC"
  | `IND -> Format.fprintf ppf "inductive step"
  | `INVGEN -> Format.fprintf ppf "invariant generator"
  | `INVMAN -> Format.fprintf ppf "invariant manager"
  | `Interpreter -> Format.fprintf ppf "interpreter"


(* String representation of a process type *)
let string_of_kind_module = string_of_t pp_print_kind_module 


(* Process type of a string *)
let kind_module_of_string = function 
  | "PDR" -> `PDR
  | "BMC" -> `BMC
  | "IND" -> `IND
  | "INVGEN" -> `INVGEN
  | "INVMAN" -> `INVMAN
  | _ -> raise (Invalid_argument "kind_module_of_string")

(* Timeouts *)
exception TimeoutWall
exception TimeoutVirtual

(* System signal caught *)
exception Signal of int

(* String representation of signal *)
let string_of_signal = function 
  | s when s = Sys.sigabrt -> "SIGABRT"
  | s when s = Sys.sigalrm -> "SIGALRM"
  | s when s = Sys.sigfpe -> "SIGFPE"
  | s when s = Sys.sighup -> "SIGHUP"
  | s when s = Sys.sigill -> "SIGILL"
  | s when s = Sys.sigint -> "SIGINT"
  | s when s = Sys.sigkill -> "SIGKILL"
  | s when s = Sys.sigpipe -> "SIGPIPE"
  | s when s = Sys.sigquit -> "SIGQUIT"
  | s when s = Sys.sigsegv -> "SIGSEGV"
  | s when s = Sys.sigterm -> "SIGTERM"
  | s when s = Sys.sigusr1 -> "SIGUSR1"
  | s when s = Sys.sigusr2 -> "SIGUSR2"
  | s when s = Sys.sigchld -> "SIGCHLD"
  | s when s = Sys.sigcont -> "SIGCONT"
  | s when s = Sys.sigstop -> "SIGSTOP"
  | s when s = Sys.sigtstp -> "SIGTSTP"
  | s when s = Sys.sigttin -> "SIGTTIN"
  | s when s = Sys.sigttou -> "SIGTTOU"
  | s when s = Sys.sigvtalrm -> "SIGVTALRM"
  | s when s = Sys.sigprof -> "SIGPROF"
  | s -> string_of_int s

let pp_print_signal ppf s = Format.fprintf ppf "%s" (string_of_signal s)

(* Pretty-print the termination status of a process *)
let pp_print_process_status ppf = function 
  | Unix.WEXITED s -> Format.fprintf ppf "exited with return code %d" s

  | Unix.WSIGNALED s -> 
    Format.fprintf ppf "killed by signal %a" pp_print_signal s

  | Unix.WSTOPPED s -> 
    Format.fprintf ppf "stopped by signal %a" pp_print_signal s


(* Raise exception on signal *)
let exception_on_signal signal = 
  Format.printf "Signal %a caught" pp_print_signal signal;
  raise (Signal signal)


(* Sleep for seconds, resolution is in ms *)
let minisleep sec =

  try 

    (* Sleep for the given seconds, yield to other threads *)
    Thread.delay sec 

  with 

    (* Signal caught while in kernel *)
    | Unix.Unix_error(Unix.EINTR, _, _) -> 

      (* Cannot find out signal number *)
      raise (Signal 0)



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
