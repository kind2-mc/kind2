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

(* ********************************************************************** *)
(* Helper functions                                                       *)
(* ********************************************************************** *)

(* Identity function. *)
let identity anything = anything

(* Returns true when given unit. *)
let true_of_unit () = true

(* Returns false when given unit. *)
let false_of_unit () = false

(* ********************************************************************** *)
(* Arithmetic functions                                                   *)
(* ********************************************************************** *)

(* Compute [m * h + i] and make sure that the result does not overflow
   to a negtive number *)
let safe_hash_interleave h m i = abs(i + (m * h) mod max_int)

(* ********************************************************************** *)
(* List functions                                                         *)
(* ********************************************************************** *)

(* Creates a size-n list equal to [f 0; f 1; ... ; f (n-1)] *)
let list_init f n =
  if n = 0 then [] else
    let rec init_aux i =
      if i = n-1 then
        [f i]
      else
        (f i) :: (init_aux (i+1))
    in
    init_aux 0

(* Returns the maximum element of a non-empty list *)
let list_max l =
  assert (List.length l > 0);
  let rec list_max_aux l acc =
    match l with
    | [] ->
       acc
    | hd :: tl ->
       list_max_aux tl (max hd acc)
  in
  list_max_aux l (List.hd l)
             
(* Return the index of the first element that satisfies the predicate [p] *)
let list_index p = 
  let rec list_index p i = function
    | [] -> raise Not_found
    | x :: l -> if p x then i else list_index p (succ i) l
  in
  list_index p 0 


(* [list_indexes l1 l2] returns the indexes in list [l2] of elements in
   list [l1] *)
let rec list_indexes' accum pos l = function 

  | [] -> List.rev accum

  | h :: tl -> 

    if List.mem h l then 
      list_indexes' (pos :: accum) (succ pos) l tl
    else
      list_indexes' accum (succ pos) l tl


let list_indexes l1 l2 = list_indexes' [] 0 l1 l2

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


(* [list_filter_nth l [p1; p2; ...]] returns the elements [l] at positions [p1], [p2] etc. *)
let rec list_filter_nth' current_pos accum = 

  function 

    | [] -> (function _ -> List.rev accum)

    | h :: list_tl -> 

      (function 
        | next_pos :: positions_tl when current_pos = next_pos -> 


          (match positions_tl with

            | next_pos' :: _ when next_pos >= next_pos' -> 
              
              raise 
                (Invalid_argument
                   "list_filter_nth: list of position is not sorted")
                
            | _ -> 
              
              list_filter_nth' 
                (succ current_pos) 
                (h :: accum) 
                list_tl 
                positions_tl)
      
        | positions -> 
          
          list_filter_nth' (succ current_pos) accum list_tl positions)


let list_filter_nth l p = list_filter_nth' 0 [] l p


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


(* Lexicographic comparison of pairs *)
let compare_pairs cmp_a cmp_b (a1, b1) (a2, b2) =
  let c_a = cmp_a a1 a2 in if c_a = 0 then cmp_b b1 b2 else c_a


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


(* Given two ordered association lists with identical keys, push the
   values of each element of the first association list to the list of
   elements of the second association list. 

   The returned association list is in the order of the input lists,
   the function [equal] is used to compare keys. *)
let list_join equal l1 l2 = 

  let rec list_join' equal accum l1 l2 = match l1, l2 with
    
    (* Both lists consumed, return in original order *)
    | [], [] -> List.rev accum 
                  
    (* Keys of head elements in both lists equal *)
    | (((k1, v1) :: tl1), ((k2, v2) :: tl2)) when equal k1 k2 -> 
      
      (* Add to accumulator and continue *)
      list_join' equal ((k1, (v1 :: v2)) :: accum) tl1 tl2
        
    (* Keys of head elements different, or one of the lists is empty *)
    | _ -> failwith "list_join"
             
  in

  (* Call recursive function with initial accumulator *)
  list_join' equal [] l1 l2

(* ********************************************************************** *)
(* Array functions                                                        *)
(* ********************************************************************** *)

(* Returns the maximum element of a non-empty array *)
let array_max a =
  assert (Array.length a > 0);
  let max_val = ref a.(0) in
  Array.iter (fun x -> if x > !max_val then max_val := x else ()) a;
  !max_val

(* ********************************************************************** *)
(* Genric pretty-printing                                                 *)
(* ********************************************************************** *)

(* Pretty-print an array *)
let pp_print_arrayi pp sep ppf array  =
  let n = Array.length array in
  let print_element i =
    if i = n-1 then
      pp ppf i array.(i)
    else
      (pp ppf i array.(i);
       Format.fprintf ppf sep)
  in
  let indices = list_init (fun i -> i) n in  
  List.iter print_element indices
  
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
  pp_print_list Format.pp_print_string "@ " ppf list;

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


(* Output a horizonal dasehd line *)
let pp_print_hline ppf () = 
  
  let width = Format.pp_get_margin ppf () in 

  let hline = String.make width '-' in

  Format.fprintf 
    ppf 
    "%s"
    hline


(* ********************************************************************** *)
(* Option types                                                           *)
(* ********************************************************************** *)

(* Return the value of an option type, raise [Invalid_argument "get"]
   if the option value is [None] *)
let get = function None -> raise (Invalid_argument "get") | Some x -> x


(* ********************************************************************** *)
(* String                                                                 *)
(* ********************************************************************** *)



(* Return true if the first characters of [s1] up to the length of
   [s2] are ientical to [s2]. Return false if [s2] is longer than
   [s1]. *)
let string_starts_with s1 s2 = 

  (* First string is shorter than second? *)
  if String.length s1 < String.length s2 then false else

    (* Create string of length of [s2] *)
    let s1' = String.create (String.length s2) in

    (* Copy characters from [s1] *)
    String.blit s1 0 s1' 0 (String.length s2);

    (* Return true if strings are identical *)
    s1' = s2



(* ********************************************************************** *)
(* Numerals, decimals and bitvectors                                      *)
(* ********************************************************************** *)



(* Constant bitvector *)
type bitvector = bool list


(* Pretty-print a bitvector in binary format without #b prefix *)
let rec pp_print_bitvector_b' ppf = function 
  | [] -> ()
  | true :: tl -> Format.pp_print_int ppf 1; pp_print_bitvector_b' ppf tl
  | false :: tl -> Format.pp_print_int ppf 0; pp_print_bitvector_b' ppf tl


(* Pretty-print a bitvector in SMTLIB binary format *)
let pp_smtlib_print_bitvector_b ppf b = 
  Format.fprintf ppf "#b%a" pp_print_bitvector_b' b


(* Pretty-print a bitvector in Yices' binary format *)
let pp_yices_print_bitvector_b ppf b = 
  Format.fprintf ppf "0b%a" pp_print_bitvector_b' b


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

(* Constant zero *)
let num_zero = numeral_of_int 0

(* Constant one *)
let num_one = numeral_of_int 1

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



(* Convert a bitvector to an integer *)
let int_of_bitvector b = 
  List.fold_left (fun a b -> a lsl 1 + (if b then 1 else 0)) 0 b


(* Convert a bitvector to an integer *)
let length_of_bitvector b = List.length b


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
    | "#b" | "0b" -> bitvector_of_string_b [] ((String.length s) - 1) s

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
(* Log levels                                                             *)
(* ********************************************************************** *)


(* Levels of log messages *)
type log_level =
  | L_off
  | L_fatal
  | L_error
  | L_warn
  | L_info
  | L_debug
  | L_trace


(* Associate an integer with each level to induce a total ordering *)
let int_of_log_level = function 
  | L_off -> -1 
  | L_fatal -> 0
  | L_error -> 1
  | L_warn -> 2
  | L_info -> 3
  | L_debug -> 4
  | L_trace -> 5

let log_level_of_int = function 
  | -1 -> L_off 
  | 0 -> L_fatal
  | 1 -> L_error
  | 2 -> L_warn
  | 3 -> L_info
  | 4 -> L_debug
  | 5 -> L_trace
  | _ -> raise (Invalid_argument "log_level_of_int")

(* Compare two levels *)
let compare_levels l1 l2 = 
  Pervasives.compare (int_of_log_level l1) (int_of_log_level l2)


(* Current log level *)
let log_level = ref L_warn


(* Set log level *)
let set_log_level l = log_level := l


(* Level is of higher or equal priority than current log level? *)
let output_on_level level = compare_levels level !log_level <= 0


(* Return Format.fprintf if level is is of higher or equal priority
   than current log level, otherwise return Format.ifprintf *)
let ignore_or_fprintf level = 
  if output_on_level level then Format.fprintf else Format.ifprintf


(* ********************************************************************** *)
(* Output target                                                          *)  
(* ********************************************************************** *)


(* Current formatter for output *)
let log_ppf = ref Format.std_formatter


(* Set file to write log messages to *)
let log_to_file f = 

  (* Open channel to logfile *)
  let oc = 
    try open_out f with
      | Sys_error _ -> failwith "Could not open logfile"
  in 
  
  (* Create and store formatter for logfile *)
  log_ppf := Format.formatter_of_out_channel oc


(* Write messages to standard output *)
let log_to_stdout () = log_ppf := Format.std_formatter


(* ********************************************************************** *)
(* System functions                                                       *)
(* ********************************************************************** *)

let pp_print_banner ppf () =
    Format.fprintf ppf "%s %s" Kind2Config.package_name Version.version

let pp_print_version ppf = pp_print_banner ppf ()
  

(* Kind modules *)
type kind_module = 
  [ `PDR 
  | `BMC 
  | `IND
  | `INVGEN
  | `INVGENOS
  | `INVMAN
  | `Interpreter
  | `Parser ]


(* Pretty-print the type of the process *)
let pp_print_kind_module ppf = function
  | `PDR -> Format.fprintf ppf "property directed reachability"
  | `BMC -> Format.fprintf ppf "bounded model checking"
  | `IND -> Format.fprintf ppf "inductive step"
  | `INVGEN -> Format.fprintf ppf "two state invariant generator"
  | `INVGENOS -> Format.fprintf ppf "one state invariant generator"
  | `INVMAN -> Format.fprintf ppf "invariant manager"
  | `Interpreter -> Format.fprintf ppf "interpreter"
  | `Parser -> Format.fprintf ppf "parser"


(* String representation of a process type *)
let string_of_kind_module = string_of_t pp_print_kind_module 


(* Return a short representation of kind module *)
let suffix_of_kind_module = function
 | `PDR -> "pdr"
 | `BMC -> "bmc"
 | `IND -> "ind"
 | `INVGEN -> "inv"
 | `INVGENOS -> "invos"
 | `INVMAN -> "man"
 | `Interpreter -> "interp"
 | `Parser -> "parse"
                

(* Process type of a string *)
let kind_module_of_string = function 
  | "PDR" -> `PDR
  | "BMC" -> `BMC
  | "IND" -> `IND
  | "INVGEN" -> `INVGEN
  | "INVGENOS" -> `INVGENOS
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
  (* Format.printf "Signal %a caught" pp_print_signal signal; *)
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


(* Return full path to executable, search PATH environment variable
   and current working directory *)
let find_on_path exec = 

  let rec find_on_path' exec path = 

    (* Terminate on empty path *)
    if path = "" then raise Not_found;

    (* Split path at first colon *)
    let path_hd, path_tl = 

      try 

        (* Position of colon in string *)
        let colon_index = String.index path ':' in

        (* Length of string *)
        let path_len = String.length path in

        (* Return string up to colon *)
        (String.sub path 0 colon_index, 
         
         (* Return string after colon *)
         String.sub path (colon_index + 1) (path_len - colon_index - 1))

      (* Colon not found, return whole string and empty string *)
      with Not_found -> path, ""

    in
    
    (* Combine path and filename *)
    let exec_path = Filename.concat path_hd exec in
    
    if 

      (* Check if file exists on path *)
      Sys.file_exists exec_path 

    then 

      (* Return full path to file 

         TODO: Check if file is executable here? *)
      exec_path 

    else 

      (* Continue on remaining path entries *)
      find_on_path' exec path_tl

  in

  try 

    if Filename.is_relative exec then 

      (* Return filename on path, fail with Not_found if path is empty
         or [exec] not found on path *)
      find_on_path' exec (Unix.getenv "PATH")
        
    else if 
      
      (* Check if file exists on path *)
      Sys.file_exists exec
        
    then 
      
      (* Return full path to file 
         
         TODO: Check if file is executable here? *)
      exec

    else 

      raise Not_found

  with Not_found -> 

    (* Check current directory as last resort *)
    let exec_path = Filename.concat (Sys.getcwd ()) exec in 

    (* Return full path if file exists, fail otherwise *)
    if Sys.file_exists exec_path then exec_path else raise Not_found

(* ********************************************************************** *)
(* Parser and lexer functions                                             *)
(* ********************************************************************** *)


(* A position in a file

   The column is the actual colum number, not an offset from the
   beginning of the file as in Lexing.position *)
type position =
  { pos_fname : string; pos_lnum: int; pos_cnum: int }


(* Comparision on positions *)
let compare_pos 
    { pos_fname = p1; pos_lnum = l1; pos_cnum = c1 }  
    { pos_fname = p2; pos_lnum = l2; pos_cnum = c2 } =

  compare_pairs 
    String.compare
    (compare_pairs Pervasives.compare Pervasives.compare)
    (p1, (l1, c1)) 
    (p2, (l2, c2)) 


(* A dummy position, different from any valid position *)
let dummy_pos = { pos_fname = ""; pos_lnum = 0; pos_cnum = -1 }


(* A dummy position in the specified file *)
let dummy_pos_in_file fname = 
  { pos_fname = fname; pos_lnum = 0; pos_cnum = -1 }


(* Pretty-print a position *)
let pp_print_position 
    ppf 
    ({ pos_fname; pos_lnum; pos_cnum } as pos) =

  if pos = dummy_pos then 

    Format.fprintf ppf "(unknown)"

  else if pos_lnum = 0 && pos_cnum = -1 then

    Format.fprintf ppf "%s" pos_fname

  else

    Format.fprintf 
      ppf
      "@[<hv>%tline %d@ col. %d@]"
      (function ppf -> 
        if pos_fname = "" then () else Format.fprintf ppf "%s@ " pos_fname)
      pos_lnum
      pos_cnum


(* Convert a position from Lexing to a position *)
let position_of_lexing 
    { Lexing.pos_fname;
      Lexing.pos_lnum;
      Lexing.pos_bol;
      Lexing.pos_cnum } = 

  (* Colum number is relative to the beginning of the file *)
  { pos_fname = pos_fname; 
    pos_lnum = pos_lnum; 
    pos_cnum = pos_cnum - pos_bol } 


(* Return true if position is a dummy position *)
let is_dummy_pos = function 
  | { pos_cnum = -1 } -> true 
  | _ -> false


(* Return the file, line and column of a position; fail if the
   position is a dummy position *)
let file_row_col_of_pos = function 

  (* Fail if position is a dummy position *)
  | p when is_dummy_pos p -> raise (Invalid_argument "file_row_col_of_pos")

  (* Return tuple of filename, line and column *)
  | { pos_fname; pos_lnum; pos_cnum } -> (pos_fname, pos_lnum, pos_cnum)



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
