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

open Format

exception Unsupported of string

(** function thunk for unimplimented features*)
let todo = fun s -> raise (Unsupported s)
                  
(* ********************************************************************** *)
(* Helper functions                                                       *)
(* ********************************************************************** *)

(* Identity function. *)
let identity anything = anything

(* Prints the first argument and returns the second. *)
let print_pass s whatever =
  printf "%s@." s ;
  whatever

(* Returns true when given unit. *)
let true_of_unit () = true

(* Returns false when given unit. *)
let false_of_unit () = false

(* Returns None when given unit. *)
let none_of_unit () = None

(* Returns true *)
let true_of_any _ = true

(* Returns false s*)
let false_of_any _ = false

(* Creates a directory if it does not already exist. *)
let mk_dir dir =
  try Unix.mkdir dir 0o740 with Unix.Unix_error(Unix.EEXIST, _, _) -> ()

(* Flips the expected argument of the function *)
let flip f = fun b a -> f a b 

(* ********************************************************************** *)
(* Arithmetic functions                                                   *)
(* ********************************************************************** *)

(* Compute [m * h + i] and make sure that the result does not overflow
   to a negtive number *)
let safe_hash_interleave h m i = abs(i + (m * h) mod max_int)
  
(* ********************************************************************** *)
(* List functions                                                         *)
(* ********************************************************************** *)

(* Add element to the head of the list if the option value is not [None] *)
let ( @:: ) = 
    function
    | None -> (function l -> l)
    | Some e -> (function l -> e :: l)


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


let list_extract_nth l i =
  let rec aux acc l i = match i, l with
    | 0, x :: r -> x, List.rev_append acc r
    | i, x :: r when i > 0 -> aux (x :: acc) r (i - 1) 
    | _ -> raise (Invalid_argument "list_extract_nth")
  in
  aux [] l i


(* [chain_list \[e1; e2; ...\]] is \[\[e1; e2\]; \[e2; e3\]; ... \]]*)
let chain_list = function 

  | [] 
  | _ :: [] -> invalid_arg "chain_list"

  | h :: tl -> 
    
    let chain_list (accum, last) curr = ([last; curr] :: accum, curr) in
    List.rev (fst (List.fold_left chain_list ([], h) tl))


(* [chain_list_p \[e1; e2; ...\]] is [\[(e1, e2); (e2, e3); ... \]] *)
let chain_list_p = function

  | []
  | _ :: [] -> invalid_arg "chain_list_p"

  | h :: tl ->

    let chain_list' (accum, last) curr = ((last, curr) :: accum, curr) in
    List.rev (fst (List.fold_left chain_list' ([], h) tl))

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

  (* Second list is empty? *)
  match l2 with 

    (* Initialize with singleton elements from first list *)
    | [] -> List.map (fun (k, v) -> (k, [v])) l1

    (* Call recursive function with initial accumulator *)
    | _ -> list_join' equal [] l1 l2

let rec list_apply: ('a -> 'b) list -> 'a -> 'b list = fun fs arg ->
  match fs with
  | [] -> []
  | f :: rest -> f arg :: (list_apply rest arg)  

let rec drop_last: 'a list -> 'a list
  = function
  | [] -> failwith "drop_last"
  | [e] -> []
  | e :: r -> e :: drop_last r

               

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
(* Set functions                                                          *)
(* ********************************************************************** *)

(* Set of integers *)
module IntegerSet = 
  Set.Make
  (struct
    type t = int
    let compare = Stdlib.compare
    let equal = (=)
   end)
  
  
(* Hashtable of integers *)
module IntegerHashtbl =
  Hashtbl.Make
    (struct
      type t = int
      let hash i = i
      let equal = (=)
     end)

    
(* ********************************************************************** *)
(* Generic pretty-printing                                                 *)
(* ********************************************************************** *)
  
(* Pretty-print an array *)
let pp_print_arrayi pp sep ppf array  =
  let n = Array.length array in
  let print_element i =
    if i = n-1 then
      pp ppf i array.(i)
    else
      (pp ppf i array.(i);
       fprintf ppf sep)
  in
  let indices = list_init (fun i -> i) n in  
  List.iter print_element indices

let pp_print_pair pp1 pp2 sep ppf (left, right) =
  pp1 ppf left; fprintf ppf sep; pp2 ppf right 
  
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
    fprintf ppf sep; 

    (* Output the rest of the list *)
    pp_print_list pp sep ppf tl


  
(* Pretty-print a list with a counter of its elements *)
let rec pp_print_listi' pp sep ppf = function 

  (* Output nothing for the empty list *) 
  | (_, []) -> ()

  (* Output a single element in the list  *) 
  | (i, e :: []) -> pp ppf i e

  (* Output a single element and a space *) 
  | (i, e :: tl) -> 

    (* Output one element *)
    pp ppf i e;

    (* Output separator *)
    fprintf ppf sep; 

    (* Output the rest of the list *)
    pp_print_listi' pp sep ppf (succ i, tl)


(* Pretty-print a list with a counter of its elements *)
let pp_print_listi pp sep ppf l = pp_print_listi' pp sep ppf (0, l)



let rec pp_print_list2i' pp sep ppf = function 
  | _, [], [] -> ()
  | i, [e1], [e2] -> pp ppf i e1 e2
  | i, e1 :: tl1, e2 :: tl2 -> 
    pp ppf i e1 e2;
    (* Output separator *)
    fprintf ppf sep; 
    (* Output the rest of the two lists *)
    pp_print_list2i' pp sep ppf (succ i, tl1, tl2)
  | _ -> invalid_arg "pp_print_list2i"

(* Pretty-print two lists of the same length with a counter of their
   elements *)
let pp_print_list2i pp sep ppf l1 l2 = pp_print_list2i' pp sep ppf (0, l1, l2)


(* Pretty-print a list wrapped in parentheses *)
let pp_print_paren_list ppf list = 
      
  (* Begin expression with opening parenthesis *)
  pp_print_string ppf "(";
  
  (* Output elements of list *)
  pp_print_list pp_print_string "@ " ppf list;

  (* End expression with closing parenthesis *)
  pp_print_string ppf ")"


(* Pretty-print an option type *)
let pp_print_option pp ppf = function 
  | None -> fprintf ppf "None"
  | Some s -> fprintf ppf "@[<hv>Some@ %a@]" pp s


(* Print if list is not empty *)
let pp_print_if_not_empty s ppf = function 
  | [] -> ()
  | _ -> fprintf ppf s

(* Pretty-print into a string *)
let string_of_t pp t = 

  (* Create a buffer *)
  let buf = Buffer.create 80 in
  
  (* Create a formatter printing into the buffer *)
  let ppf = formatter_of_buffer buf in

  (* Output into buffer *)
  pp ppf t;
  
  (* Flush the formatter *)
  pp_print_flush ppf ();
  
  (* Return the buffer contents *)
  Buffer.contents buf

(* Return the strings as a parenthesized and space separated list *)
let paren_string_of_string_list list =
  string_of_t pp_print_paren_list list

(* Return the width of the string, meaning the wisth of it's longest line *)
let width_of_string s =
  let lines = Str.split (Str.regexp "\n") s in
  List.fold_left (fun max_width s ->
      max max_width (String.length s)
    ) 0 lines

let escape_json_string s =
  let backslash = Str.regexp "\\" in
  let double_quotes = Str.regexp "\"" in
  let newline = Str.regexp "\n" in
  s |> Str.global_replace backslash "\\\\"
    |> Str.global_replace double_quotes "\'"
    |> Str.global_replace newline "\\n"

let escape_xml_string s =
  let ltr = Str.regexp "<" in
  let gtr = Str.regexp ">" in
  let ampr = Str.regexp "&" in
  s |> Str.global_replace ltr "&lt;"
    |> Str.global_replace gtr "&gt;"
    |> Str.global_replace ampr "&amp;"


(* ********************************************************************** *)
(* Option types                                                           *)
(* ********************************************************************** *)

(* Return the value of an option type, raise [Invalid_argument "get"]
   if the option value is [None] *)
let get = function None -> raise (Invalid_argument "get") | Some x -> x

let min_option f1 f2 = match f1, f2 with
  | None, None -> None
  | Some f, None | None, Some f -> Some f
  | Some f1, Some f2 -> if f1 < f2 then Some f1 else Some f2

(* ********************************************************************** *)
(* String                                                                 *)
(* ********************************************************************** *)



(* Return true if the first characters of [s1] up to the length of
   [s2] are ientical to [s2]. Return false if [s2] is longer than
   [s1]. *)
let string_starts_with s1 s2 = 
  (String.length s1 >= String.length s2) &&
  (String.sub s1 0 (String.length s2) = s2)



(* ********************************************************************** *)
(* Log levels                                                             *)
(* ********************************************************************** *)


(* Levels of log messages *)
type log_level =
  | L_off
  | L_fatal
  | L_error
  | L_warn
  | L_note
  | L_info
  | L_debug
  | L_trace

(* Default log level. *)
let default_log_level = L_note

(* Associate an integer with each level to induce a total ordering *)
let int_of_log_level = function 
  | L_off -> -1 
  | L_fatal -> 0
  | L_error -> 1
  | L_warn -> 2
  | L_note -> 3
  | L_info -> 4
  | L_debug -> 5
  | L_trace -> 6


let log_level_of_int = function 
  | -1 -> L_off 
  | 0 -> L_fatal
  | 1 -> L_error
  | 2 -> L_warn
  | 3 -> L_note
  | 4 -> L_info
  | 5 -> L_debug
  | 6 -> L_trace
  | _ -> raise (Invalid_argument "log_level_of_int")

let string_of_log_level = function
  | L_off -> "off"
  | L_fatal -> "fatal"
  | L_error -> "error"
  | L_warn -> "warn"
  | L_note -> "note"
  | L_info -> "info"
  | L_debug -> "debug"
  | L_trace -> "trace"



(* Compare two levels *)
let compare_levels l1 l2 = 
  Stdlib.compare (int_of_log_level l1) (int_of_log_level l2)


(* Current log level *)
let log_level = ref L_warn


(* Set log level *)
let set_log_level l = log_level := l
(* Log level *)
let get_log_level () = !log_level


(* Level is of higher or equal priority than current log level? *)
let output_on_level level = compare_levels level !log_level <= 0


(* Return fprintf if level is is of higher or equal priority
   than current log level, otherwise return ifprintf *)
let ignore_or_fprintf level = 
  if output_on_level level then fprintf else ifprintf


(* ********************************************************************** *)
(* Output target                                                          *)  
(* ********************************************************************** *)


(* Current formatter for output *)
let log_ppf = ref std_formatter


(* Set file to write log messages to *)
let log_to_file f = 

  (* Open channel to logfile *)
  let oc = 
    try open_out f with
      | Sys_error _ -> failwith "Could not open logfile"
  in 
  
  (* Create and store formatter for logfile *)
  log_ppf := formatter_of_out_channel oc


(* Write messages to standard output *)
let log_to_stdout () = log_ppf := std_formatter


(* ********************************************************************** *)
(* System functions                                                       *)
(* ********************************************************************** *)

let pp_print_banner ppf () =
    fprintf ppf "%s %s" Version.package_name Version.version

let pp_print_version ppf = pp_print_banner ppf ()
  

(* Kind modules *)
type kind_module = 
  [ `IC3 
  | `BMC
  | `IND
  | `IND2
  | `INVGEN
  | `INVGENOS
  | `INVGENINT
  | `INVGENINTOS
  | `INVGENMACH
  | `INVGENMACHOS
  | `INVGENINT8
  | `INVGENINT8OS
  | `INVGENINT16
  | `INVGENINT16OS
  | `INVGENINT32
  | `INVGENINT32OS
  | `INVGENINT64
  | `INVGENINT64OS
  | `INVGENUINT8
  | `INVGENUINT8OS
  | `INVGENUINT16
  | `INVGENUINT16OS
  | `INVGENUINT32
  | `INVGENUINT32OS
  | `INVGENUINT64
  | `INVGENUINT64OS
  | `INVGENREAL
  | `INVGENREALOS
  | `C2I
  | `Interpreter
  | `Supervisor
  | `Parser
  | `Certif
  | `MCS
  | `CONTRACTCK ]


(* Pretty-print the type of the process *)
let pp_print_kind_module ppf = function
  | `IC3 -> fprintf ppf "property directed reachability"
  | `BMC -> fprintf ppf "bounded model checking"
  | `IND -> fprintf ppf "inductive step"
  | `IND2 -> fprintf ppf "2-induction"
  | `INVGEN -> fprintf ppf "two state invariant generator (bool)"
  | `INVGENOS -> fprintf ppf "one state invariant generator (bool)"
  | `INVGENINT -> fprintf ppf "two state invariant generator (int)"
  | `INVGENINTOS -> fprintf ppf "one state invariant generator (int)"
  | `INVGENMACH -> fprintf ppf "two state invariant generator (mach int)"
  | `INVGENMACHOS -> fprintf ppf "one state invariant generator (mach int)"
  | `INVGENINT8 -> fprintf ppf "two state invariant generator (int8)"
  | `INVGENINT8OS -> fprintf ppf "one state invariant generator (int8)"
  | `INVGENINT16 -> fprintf ppf "two state invariant generator (int16)"
  | `INVGENINT16OS -> fprintf ppf "one state invariant generator (int16)"
  | `INVGENINT32 -> fprintf ppf "two state invariant generator (int32)"
  | `INVGENINT32OS -> fprintf ppf "one state invariant generator (int32)"
  | `INVGENINT64 -> fprintf ppf "two state invariant generator (int64)"
  | `INVGENINT64OS -> fprintf ppf "one state invariant generator (int64)"
  | `INVGENUINT8 -> fprintf ppf "two state invariant generator (uint8)"
  | `INVGENUINT8OS -> fprintf ppf "one state invariant generator (uint8)"
  | `INVGENUINT16 -> fprintf ppf "two state invariant generator (uint16)"
  | `INVGENUINT16OS -> fprintf ppf "one state invariant generator (uint16)"
  | `INVGENUINT32 -> fprintf ppf "two state invariant generator (uint32)"
  | `INVGENUINT32OS -> fprintf ppf "one state invariant generator (uint32)"
  | `INVGENUINT64 -> fprintf ppf "two state invariant generator (uint64)"
  | `INVGENUINT64OS -> fprintf ppf "one state invariant generator (uint64)"
  | `INVGENREAL -> fprintf ppf "two state invariant generator (real)"
  | `INVGENREALOS -> fprintf ppf "one state invariant generator (real)"
  | `C2I -> fprintf ppf "c2i"
  | `Interpreter -> fprintf ppf "interpreter"
  | `Supervisor -> fprintf ppf "invariant manager"
  | `Parser -> fprintf ppf "parser"
  | `Certif -> Format.fprintf ppf "certificate"
  | `MCS -> Format.fprintf ppf "minimal cut set"
  | `CONTRACTCK -> Format.fprintf ppf "contract checker"

(* String representation of a process type *)
let string_of_kind_module = string_of_t pp_print_kind_module


(* Return a short representation of kind module *)
let short_name_of_kind_module = function
 | `IC3 -> "ic3"
 | `BMC -> "bmc"
 | `IND -> "ind"
 | `IND2 -> "ind2"
 | `INVGEN -> "invgents"
 | `INVGENOS -> "invgenos"
 | `INVGENINT -> "invgenintts"
 | `INVGENINTOS -> "invgenintos"
 | `INVGENMACH -> "invgenmachts"
 | `INVGENMACHOS -> "invgenmachos"
 | `INVGENINT8 -> "invgenint8ts"
 | `INVGENINT8OS -> "invgenint8os"
 | `INVGENINT16 -> "invgenint16ts"
 | `INVGENINT16OS -> "invgenint16os"
 | `INVGENINT32 -> "invgenint32ts"
 | `INVGENINT32OS -> "invgenint32os"
 | `INVGENINT64 -> "invgenuint64ts"
 | `INVGENINT64OS -> "invgenuint64os"
 | `INVGENUINT8 -> "invgenuint8ts"
 | `INVGENUINT8OS -> "invgenuint8os"
 | `INVGENUINT16 -> "invgenuint16ts"
 | `INVGENUINT16OS -> "invgenuint16os"
 | `INVGENUINT32 -> "invgenuint32ts"
 | `INVGENUINT32OS -> "invgenuint32os"
 | `INVGENUINT64 -> "invgenuint64ts"
 | `INVGENUINT64OS -> "invgenuint64os"
 | `INVGENREAL -> "invgenintts"
 | `INVGENREALOS -> "invgenintos"
 | `C2I -> "c2i"
 | `Interpreter -> "interp"
 | `Supervisor -> "super"
 | `Parser -> "parse"
 | `Certif -> "certif"
 | `MCS -> "mcs"
 | `CONTRACTCK -> "contractck"
                

(* Process type of a string *)
let kind_module_of_string = function 
  | "IC3" -> `IC3
  | "BMC" -> `BMC
  | "IND" -> `IND
  | "IND2" -> `IND2
  | "INVGEN" -> `INVGEN
  | "INVGENOS" -> `INVGENOS
  | "INVGENINT" -> `INVGENINT
  | "INVGENINTOS" -> `INVGENINTOS
  | "INVGENMACH" -> `INVGENMACH
  | "INVGENMACHOS" -> `INVGENMACHOS
  | "INVGENINT8" -> `INVGENINT8
  | "INVGENINT8OS" -> `INVGENINT8OS
  | "INVGENINT16" -> `INVGENINT16
  | "INVGENINT16OS" -> `INVGENINT16OS
  | "INVGENINT32" -> `INVGENINT32
  | "INVGENINT32OS" -> `INVGENINT32OS
  | "INVGENINT64" -> `INVGENINT64
  | "INVGENINT64OS" -> `INVGENINT64OS
  | "INVGENUINT8" -> `INVGENUINT8
  | "INVGENUINT8OS" -> `INVGENUINT8OS
  | "INVGENUINT16" -> `INVGENUINT16
  | "INVGENUINT16OS" -> `INVGENUINT16OS
  | "INVGENUINT32" -> `INVGENUINT32
  | "INVGENUINT32OS" -> `INVGENUINT32OS
  | "INVGENUINT64" -> `INVGENUINT64
  | "INVGENUINT64OS" -> `INVGENUINT64OS
  | "INVGENREAL" -> `INVGENREAL
  | "INVGENREALOS" -> `INVGENREALOS
  | "C2I" -> `C2I
  | _ -> raise (Invalid_argument "kind_module_of_string")


let int_of_kind_module = function
  | `CONTRACTCK -> -6
  | `MCS -> -5
  | `Certif -> -4
  | `Parser -> -3
  | `Interpreter -> -2
  | `Supervisor -> -1
  | `BMC -> 1
  | `IND -> 2
  | `IND2 -> 3
  | `IC3 -> 4
  | `INVGEN -> 5
  | `INVGENOS -> 6
  | `INVGENINT -> 7
  | `INVGENINTOS -> 8
  | `INVGENREAL -> 9
  | `INVGENREALOS -> 10
  | `C2I -> 11
  | `INVGENINT8 -> 12
  | `INVGENINT8OS -> 13
  | `INVGENINT16 -> 14
  | `INVGENINT16OS -> 15
  | `INVGENINT32 -> 16
  | `INVGENINT32OS -> 17
  | `INVGENINT64 -> 18
  | `INVGENINT64OS -> 19
  | `INVGENUINT8 -> 20
  | `INVGENUINT8OS -> 21
  | `INVGENUINT16 -> 22
  | `INVGENUINT16OS -> 23
  | `INVGENUINT32 -> 24
  | `INVGENUINT32OS -> 25
  | `INVGENUINT64 -> 26
  | `INVGENUINT64OS -> 27
  | `INVGENMACH -> 28
  | `INVGENMACHOS -> 29


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

let pp_print_signal ppf s = fprintf ppf "%s" (string_of_signal s)

(* Pretty-print the termination status of a process *)
let pp_print_process_status ppf = function 
  | Unix.WEXITED s -> fprintf ppf "exited with return code %d" s

  | Unix.WSIGNALED s -> 
    fprintf ppf "killed by signal %a" pp_print_signal s

  | Unix.WSTOPPED s -> 
    fprintf ppf "stopped by signal %a" pp_print_signal s


(* Raise exception on signal *)
let exception_on_signal signal = 
  (* printf "Signal %a caught" pp_print_signal signal; *)
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


let rec find_file filename = function
  | [] -> None
  | dir :: include_dirs ->
    let path = Filename.concat dir filename in
    if Sys.file_exists path then Some path
    else find_file filename include_dirs
    

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
    (compare_pairs Stdlib.compare Stdlib.compare)
    (p1, (l1, c1)) 
    (p2, (l2, c2)) 


(* A dummy position, different from any valid position *)
let dummy_pos = { pos_fname = ""; pos_lnum = 0; pos_cnum = -1 }


(* A dummy position in the specified file *)
let dummy_pos_in_file fname = 
  { pos_fname = fname; pos_lnum = 0; pos_cnum = -1 }


(* Pretty-print a position *)
let pp_print_position ppf (
  { pos_fname; pos_lnum; pos_cnum } as pos
) =

  if pos = dummy_pos then 

    fprintf ppf "(unknown)"

  else if pos_lnum = 0 && pos_cnum = -1 then

    fprintf ppf "%s" pos_fname

  else if pos_fname <> "" then

    fprintf ppf "%s:%d:%d" pos_fname pos_lnum pos_cnum

  else

    fprintf 
      ppf
      "@[<hv>line %d@ col. %d@]"
      pos_lnum
      pos_cnum


(* Pretty-print a position *)
let pp_print_pos ppf (
  { pos_fname; pos_lnum; pos_cnum } as pos
) =

  if pos = dummy_pos then 

    fprintf ppf "[unknown]"

  else if pos_lnum = 0 && pos_cnum = -1 then

    fprintf ppf "%s" pos_fname

  else

    fprintf 
      ppf
      "[%tl%dc%d]"
      (function ppf -> 
        if pos_fname = "" then () else fprintf ppf "%s|" pos_fname)
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
                                       

let print_backtrace fmt bt =
  match Printexc.backtrace_slots bt with
  | None -> ()
  | Some slots ->
    let n = Array.length slots in
    Array.iteri (fun i s ->
        match Printexc.Slot.format i s with
        | None -> ()
        | Some s ->
          pp_print_string fmt s;
          if i < n - 1 then pp_force_newline fmt ()
      ) slots


let pos_of_file_row_col (pos_fname, pos_lnum, pos_cnum) =
  { pos_fname; pos_lnum; pos_cnum }


(* Split a string at its first dot. Raises {Not_found} if there are not dots *)
let split_dot s =
  let open String in
  let n = (index s '.') in
  sub s 0 n, sub s (n+1) (length s - n - 1)


(* Extract scope from a concatenated name *)
let extract_scope_name name =

  let rec loop s scope =
    try
      let next_scope, s' = split_dot s in
      loop s' (next_scope :: scope)
    with Not_found -> s, List.rev scope
  in
  loop name []



(* Create a directory if it does not already exists. *)
let create_dir dir =
  try if not (Sys.is_directory dir) then failwith (dir^" is not a directory")
  with Sys_error _ -> Unix.mkdir dir 0o755


(* Copy file.

   Implementation adapted from "Unix system programming in OCaml" by Xavier
   Leroy and Didier Remy*)


let copy_fds fd_in fd_out =
  let open Unix in
  let buffer_size = 8192 in
  let buffer = Bytes.create buffer_size in
  let rec copy_loop () = match read fd_in buffer 0 buffer_size with
    | 0 -> ()
    | r -> ignore (write fd_out buffer 0 r); copy_loop ()
  in
  copy_loop ()
  

let file_copy input_name output_name =
  let open Unix in
  let fd_in = openfile input_name [O_RDONLY] 0 in
  let fd_out = openfile output_name [O_WRONLY; O_CREAT; O_TRUNC] 0o666 in
  copy_fds fd_in fd_out;
  close fd_in;
  close fd_out


let files_cat_open ?(add_prefix=fun _ -> ()) files output_name =
  let open Unix in
  let fd_out = openfile output_name [O_WRONLY; O_CREAT; O_TRUNC] 0o666 in
  add_prefix (out_channel_of_descr fd_out |> Format.formatter_of_out_channel);
  let _, fd_out =
    List.fold_left (fun (first, fd_out) input_name ->
        let fd_in = openfile input_name [O_RDONLY] 0 in
        copy_fds fd_in fd_out;
        let fd_out =
          if first then begin
            close fd_out;
            openfile output_name [O_WRONLY; O_CREAT; O_APPEND] 0o666
          end
          else fd_out in
        false, fd_out
      )
      (true, fd_out)
      files
  in
  fd_out


(* Captures the output and exit status of a unix command : aux func *)
let syscall cmd =
  let so, si, se = Unix.open_process_full cmd (Unix.environment ()) in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf so 1
     done
   with End_of_file -> ());
  ignore(Unix.close_process_full (so, si, se));
  Buffer.contents buf



let reset_gc_params =
  let gc_c = Gc.get() in
  fun () -> Gc.set gc_c
  

let set_liberal_gc () =
  Gc.full_major ();
  let gc_c =
    { (Gc.get ()) with
      (* Gc.verbose = 0x3FF; *)
      Gc.minor_heap_size = 64000000; (* default 32000*)
      major_heap_increment = 3200000;    (* default 124000*)
      space_overhead = 100; (* default 80% des donnes vivantes *)
    }
  in
  Gc.set gc_c


(* ********************************************************************** *)
(* Paths techniques write to                                              *)
(* ********************************************************************** *)

module Paths = struct
  let testgen = "tests"
  let oracle = "oracle"
  let implem = "implem"
end

(* ********************************************************************** *)
(* Reserved identifiers                                                   *)
(* ********************************************************************** *)

module ReservedIds = struct

  let abs_ident_string = "abs"
  let oracle_ident_string = "nondet"
  let instance_ident_string = "instance"
  let init_flag_ident_string = "init_flag"
  let all_req_ident_string = "all_req"
  let all_ens_ident_string = "all_ens"
  let inst_ident_string = "inst"
  let init_uf_string = "__node_init"
  let trans_uf_string = "__node_trans"
  let index_ident_string = "__index"
  let function_of_inputs = "__function_of_inputs"

  let state_string = "state"
  let restart_string = "restart"
  let state_selected_string = "state.selected"
  let restart_selected_string = "restart.selected"
  let state_selected_next_string = "state.selected.next"
  let restart_selected_next_string = "restart.selected.next"
  let handler_string = "handler"
  let unless_string = "unless"
  
  (* Init flag string. *)
  let init_flag_string = "__init_flag"
  (* Abstraction depth input string. *)
  let depth_input_string = "__depth_input"
  (* Abstraction depth input string. *)
  let max_depth_input_string = "__max_depth_input"

  let reserved_strings = [
    init_flag_string ;
    depth_input_string ;
    max_depth_input_string ;
    function_of_inputs ;

    abs_ident_string ;
    oracle_ident_string ;
    instance_ident_string ;
    init_flag_ident_string ;
    all_req_ident_string ;
    all_ens_ident_string ;
    inst_ident_string ;
    init_uf_string ;
    trans_uf_string ;
    index_ident_string ;
  ]

end


(* |===| Exit codes. *)

(** Exit codes. *)
module ExitCodes = struct
  let unknown = 0
  let unsafe = 10
  let safe = 20
  let error = 2
  let kid_status = 128
end


(* |===| File names. *)

(** File names. *)
module Names = struct
  (** Contract generation file. *)
  let contract_gen_file = "kind2_contract.lus"

  (** Contract name for contract generation. *)
  let contract_name =
    Format.asprintf "%a_spec" (pp_print_list Format.pp_print_string "_")

  (** Invariant logging file. *)
  let inv_log_file = "kind2_strengthening.lus"
  
  (** Contract name for invariant logging. *)
  let inv_log_contract_name =
    Format.asprintf "%a_str_spec" (pp_print_list Format.pp_print_string "_")
end


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
