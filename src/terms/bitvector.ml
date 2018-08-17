open Format
open Lib

(* Constant bitvector *)
type t = bool list

exception NonBinaryDigit

(* Function that converts a single binary integer digit to Boolean *)
let bin_to_bool (i : int) : bool =
  match i with 
  | 0 -> false
  | 1 -> true
  | _ -> raise NonBinaryDigit

(* Function that returns fixed-width int version of an int *)
let int_to_bv (b : int) (i : int) : t =
  let m = 1 lsl b in
  let n =
    if (i < 0) then (m + (i mod m)) mod m
    else i mod m
  in
  let rec convert acc l n =
    if n>0 then
      convert (((n mod 2) = 1) :: acc) (l+1) (n / 2)
    else (acc, l)
  in
  let bv, l = convert [] 0 n in
  let rec pad bv l =
    if l>0 then pad (false :: bv) (l-1) else bv
  in
  pad bv (b - l)

let int_to_bv8 = int_to_bv 8 
   

(* Return the first n elements of a list *)
let rec list_first_n' a l n =
  if n = 0 then a else 
    list_first_n' 
      ((try List.nth l (pred n) with 
        | Failure _ -> invalid_arg "list_first_n") :: a) 
      l
      (pred n) 


(* Return the first n elements of a list *)
let list_first_n l n = list_first_n' [] l n 


let rec list_from_n l n = 
  if n = 0 then l else
    list_from_n 
      (try List.tl l with Failure _ -> invalid_arg "list_from_n")
      (pred n)


(* Pretty-print a bitvector in binary format without #b prefix *)
let rec pp_print_bitvector_b' ppf = function 
  | [] -> ()
  | true :: tl -> pp_print_int ppf 1; pp_print_bitvector_b' ppf tl
  | false :: tl -> pp_print_int ppf 0; pp_print_bitvector_b' ppf tl


(* Pretty-print a bitvector in SMTLIB binary format *)
let pp_smtlib_print_bitvector_b ppf b = 
  fprintf ppf "#b%a" pp_print_bitvector_b' b


(* Pretty-print a bitvector in Yices' binary format *)
let pp_yices_print_bitvector_b ppf b = 
  fprintf ppf "0b%a" pp_print_bitvector_b' b


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
    pp_print_string 
      ppf 
      (List.assoc ([d1; d2; d3; d4]) bv_hex_table);
    pp_print_bitvector_x' ppf tl
    
      
(* Pretty-print a bitvector in hexadecimal format *)
let pp_print_bitvector_x ppf b = 
  
  pp_print_string ppf "#X";
  
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
