open Format
open Lib

(* Constant bitvector *)
type t = bool list

exception NonBinaryDigit
exception ComparingUnequalBVs
exception NonStandardBVSize

(* Function that converts a single binary integer digit to Boolean *)
(*let bin_to_bool (digit : int) : bool =
  match digit with 
  | 0 -> false
  | 1 -> true
  | _ -> raise NonBinaryDigit*)

(* Function that inputs bit b, integer n, and repeats b n times *)
let rec repeat_bit (b : bool) (n : int) : t =
 match n with
 | 0 -> []
 | n -> b :: repeat_bit b (n - 1)

(* Function that returns the first bit of bitvector b *)
let first_bit (b : t) : bool =
  match b with
  | h :: t -> h
  | _ -> raise NonStandardBVSize

(* Function that extracts m down to n from the input bitvector *)
let rec bvextract (m : int) (n : int) (b : t) : t =
  let b_rev = (List.rev b) in
    if (m < n) then 
      raise NonStandardBVSize
    else if (n != 0) then
      raise NonStandardBVSize
    else
      match m with
      | 0 -> [List.hd b_rev]
      | m' -> (List.nth b_rev m') :: (bvextract (m' - 1) n b)

(* Function that sign extends the input bitvector by m bits *)
let rec bvsignext (m : int) (b : t) : t =
  let sign = List.hd b in
    let rec repeat (m : int) (b : bool) : t =
      match m with
      | 0 -> []
      | m' -> b :: repeat (m' - 1) b 
    in List.append (repeat m sign) b

(* Function that concatenates the input bitvectors *)
let rec bvconcat (b1 : t) (b2 : t) : t =
  List.append b1 b2


(* ********************************************************************** *)
(* Numeral -> Unsigned BV                                                 *)
(* ********************************************************************** *)

(* The mod operator in OCaml implements remainder 
with respect to numeral division. Since numeral division
in OCaml rounds toward 0, we design modulo which considers 
division that rounds toward negative infinity. 
For example, -1 mod 8 is -1 (with quotient 0) in OCaml, 
we want it to be 7 (with quotient -1).
While considering a mod b, the OCaml mod operator will do what 
we want when a and b are positive. The following function will 
additionally do what we want when a is negative; it wont do what 
we want when b is negative, but that's okay since 
we don't consider cases of 
modulo-n arithmetic where n is negative. *)
let modulo (x : Numeral.t) (y : Numeral.t) : Numeral.t =
  let result = (Numeral.rem x y) in
    if (Numeral.geq result Numeral.zero) then result
  else (Numeral.add result y)

(* Function that calculates the nth power of two *)
let rec pow2 (n : Numeral.t) : Numeral.t =
  if (Numeral.equal n Numeral.zero) then
    Numeral.one
  else
    Numeral.mult (Numeral.succ (Numeral.one)) 
                 (pow2 (Numeral.sub n Numeral.one))

(* Function that returns unsigned fixed-width int or bitvector version of a numeral *)
let num_to_ubv (size : Numeral.t) (i : Numeral.t) : t =
  (* x = 2^N for ubvN, where we need to 
  do n modulo x on the input n *)
  let m = pow2 size in
  let n = modulo i m in
  (* Tail-recursive function that converts n to type t,
  which is a list of bools *)
  let rec convert acc (l : Numeral.t) (n : Numeral.t) =
    if (Numeral.gt n Numeral.zero) then
      convert ((Numeral.equal (Numeral.rem n (Numeral.of_int 2)) Numeral.one) :: acc) 
              (Numeral.add l Numeral.one) (Numeral.div n (Numeral.of_int 2))
    else (acc, l)
  in
  let bv, l = convert [] Numeral.zero n in
  (* For n-bit BV, pad upto n bits with 0s *)
  let rec pad (bv : t) (l :Numeral.t) =
    if (Numeral.gt l Numeral.zero) then 
      pad (false :: bv) (Numeral.sub l Numeral.one) 
    else 
      bv
  in
  pad bv (Numeral.sub size l)

  let num_to_ubv8 = num_to_ubv (Numeral.of_int 8)

  let num_to_ubv16 = num_to_ubv (Numeral.of_int 16)

  let num_to_ubv32 = num_to_ubv (Numeral.of_int 32)

  let num_to_ubv64 = num_to_ubv (Numeral.of_int 64)


(* ********************************************************************** *)
(* Unsigned BV -> Numeral                                                 *)
(* ********************************************************************** *)

(* Function that converts a Boolean to a single binary numeral *)
let bool_to_bin (b : bool) : Numeral.t =
  match b with 
  | false -> Numeral.zero
  | true -> Numeral.one
  
(*Function that returns the numeral corresponding to a bitvector *)
let rec ubv_to_num (size : Numeral.t) (b : t) : Numeral.t =
  match b with
  | h :: t -> 
      let prod = Numeral.mult (bool_to_bin h) 
                              (pow2 (Numeral.sub size Numeral.one)) 
      in
        Numeral.add prod (ubv_to_num (Numeral.sub size Numeral.one) t)
  | [] -> Numeral.zero

let ubv8_to_num = ubv_to_num (Numeral.of_int 8)

let ubv16_to_num = ubv_to_num (Numeral.of_int 16)

let ubv32_to_num = ubv_to_num (Numeral.of_int 32)

let ubv64_to_num = ubv_to_num (Numeral.of_int 64)


(* ********************************************************************** *)
(* Numeral -> Signed BV                                                   *)
(* ********************************************************************** *)

(* Input any numeral n, input the size of the BV range, output the 
numeral fit into the range.For example, for 4-bit signed integers, 
input -9, 16 (2^4), and output 7 *)
let signed_modulo (n : Numeral.t) (range_size : Numeral.t) : Numeral.t = 
  let neg_lim = Numeral.neg (Numeral.div range_size (Numeral.of_int 2)) in
  let pos_lim = Numeral.sub (Numeral.div range_size (Numeral.of_int 2)) Numeral.one in 
    if (Numeral.lt n neg_lim) then
      let diff = (Numeral.sub neg_lim n) in
      let diff_mod = (Numeral.rem diff range_size) in
        if (Numeral.equal diff_mod Numeral.zero) then 
          neg_lim 
        else 
          (Numeral.sub pos_lim (Numeral.sub diff_mod Numeral.one))
    else if (Numeral.gt n pos_lim) then
      let diff = Numeral.sub n pos_lim in
      let diff_mod = (Numeral.rem diff range_size) in
        if(Numeral.equal diff_mod Numeral.zero) then 
          pos_lim
        else 
          Numeral.add neg_lim (Numeral.sub diff_mod Numeral.one)
    else n

(*1's complement of binary number - 
flip all bits *)
let rec ones_comp (n : t) : t =
  match n with 
  | [] -> []
  | h :: t -> match h with 
	      | true -> false :: (ones_comp t)
	      | false -> true :: (ones_comp t)

(* Return a binary version of "size"-bit 1 *)
let rec bin_one (size : int) : t =
  if (size > 1) then
    false :: (bin_one (size - 1))
  else [true]

(* Input : bit1, bit2, carryIn; Output : sum, carryOut *)
let add_bits (x : bool) (y : bool) (carry : bool) : (bool * bool) = 
  match x, y, carry with 
  | false, false, false -> (false, false) 
  | false, false, true  -> (true, false)
  | false, true, false  -> (true, false) 
  | false, true, true   -> (false, true)
  | true, false, false  -> (true, false)
  | true, false, true   -> (false, true)
  | true, true, false   -> (false, true)
  | true, true, true    -> (true, true)

(* Binary additon - LSB is the left-most bit 
because binary numbers have been reversed. 
Ignore bit carried out of MSB (2's complement). *)
let rec bitwise_add (l1 : t) (l2 : t) (carry : bool) : t =
match l1, l2 with
  | [], [] -> []
  | h1 :: t1, h2 :: t2 -> 
    (match (add_bits h1 h2 carry) with
    | (sum_bit, carry_bit) -> sum_bit :: (bitwise_add t1 t2 carry_bit)) 
  | _ -> raise ComparingUnequalBVs

(* Input an n-size number and add an 
n-size 1 to it, ignoring if the last bit 
carry's out (for 2's complement)*)
let plus_one (n : t) (one : t) : t =
  let r_n = List.rev n in
  let r_one = List.rev one in 
  List.rev (bitwise_add r_n r_one false)

let num_to_bv (size : Numeral.t) (i : Numeral.t) : t =
  (* x =2^n for ubvN, where we need to do 
     n modulo x on the input n *)
  let m = pow2 size in
  let n = signed_modulo i m in
    if (Numeral.geq n Numeral.zero) then
      (num_to_ubv size n)
    else 
      let pos = (num_to_ubv size (Numeral.neg n)) in
      let onescomp = ones_comp pos in
      plus_one onescomp (bin_one (Numeral.to_int size))

let num_to_bv8 = num_to_bv (Numeral.of_int 8) 

let num_to_bv16 = num_to_bv (Numeral.of_int 16)

let num_to_bv32 = num_to_bv (Numeral.of_int 32)

let num_to_bv64 = num_to_bv (Numeral.of_int 64)


(* ********************************************************************** *)
(* Signed BV -> Num                                                       *)
(* ********************************************************************** *)

let bv_to_num (size : Numeral.t) (b : t) : Numeral.t =
  if((List.nth b 0) = false) then
    ubv_to_num size b
  else
    (Numeral.neg (ubv_to_num size
                             (plus_one (ones_comp b) 
                                       (bin_one (Numeral.to_int size)))))
  
let bv8_to_num = bv_to_num (Numeral.of_int 8)

let bv16_to_num = bv_to_num (Numeral.of_int 16)

let bv32_to_num = bv_to_num (Numeral.of_int 32)

let bv64_to_num = bv_to_num (Numeral.of_int 64)


(* Using functions involving numerals rather than ints 
(* ********************************************************************** *)
(* Int -> Unsigned BV                                                     *)
(* ********************************************************************** *)

(* The mod operator in OCaml implements remainder 
with respect to integer division. Since integer division
in OCaml rounds toward 0, we design modulo which considers 
division that rounds toward negative infinity. 
For example, -1 mod 8 is -1 (with quotient 0) in OCaml, 
we want it to be 7 (with quotient -1).
While considering a mod b, the OCaml mod operator will do what 
we want when a and b are positive. The following function will 
additionally do what we want when a is negative; it wont do what 
we want when b is negative, but that's okay since 
we don't consider cases of 
modulo-n arithmetic where n is negative. *)
let modulo_int x y =
  let result = x mod y in
  if result >= 0 then result
  else result + y

(* Function that returns unsigned fixed-width int or bitvector version of an int *)
let int_to_ubv (size : int) (i : int) : t =
  (* 
  For converting n to UBV8, n modulo 256.
  In general, for converting n to UBVm, 
  n modulo 2^m, or n modulo r where
  r = 1 << m since (<< m) <=> ( * 2^m).
  *)
  let m = 1 lsl size in
  let n = modulo_int i m in
  (* Tail-recursive function that converts n to type t,
  which is a list of bools *)
  let rec convert acc l n =
    if n>0 then
      convert (((n mod 2) = 1) :: acc) (l+1) (n / 2)
    else (acc, l)
  in
  let bv, l = convert [] 0 n in
  (* For n-bit BV, pad upto n bits with 0s *)
  let rec pad bv l =
    if l>0 then pad (false :: bv) (l-1) else bv
  in
  pad bv (size - l)

let int_to_ubv8 = int_to_ubv 8 

let int_to_ubv16 = int_to_ubv 16

let int_to_ubv32 = int_to_ubv 32

let int_to_ubv64 = int_to_ubv 64


let ubvM_to_ubvm (m2 : int) (m : int) (n : int) : t =
  if (m2 <= m) then
    (int_to_ubv m n)
  else
    let range = 1 lsl m2 in
    let i = modulo n range in
    int_to_ubv m i

(* Using functions involving numerals rather than ints *)
(* ********************************************************************** *)
(* Unsigned BV -> Int                                                     *)
(* ********************************************************************** *)

(* Function that converts a Boolean to a single binary integer digit *)
let bool_to_bin_int (b : bool) : int =
  match b with 
  | false -> 0
  | true -> 1

(* Function that calculates the nth power of two *)
let rec pow2_int (n : int) : int =
  match n with
  | 0 -> 1
  | n' -> 2 * pow2_int (n' - 1)

(* Function that returns the integer corresponding to a bitvector *)
let rec ubv_to_int (size : int)  (b: t) : int =
  match b with
  | h :: t ->  (bool_to_bin_int h) * (pow2_int (size - 1)) + ubv_to_int (size - 1) t
  | [] -> 0

let ubv8_to_int = ubv_to_int 8

let ubv16_to_int = ubv_to_int 16

let ubv32_to_int = ubv_to_int 32

let ubv64_to_int = ubv_to_int 64


(* Using functions involving numerals rather than ints *)
(* ********************************************************************** *)
(* Int -> Signed BV                                                       *)
(* ********************************************************************** *)

(* Input any number n, input the size of the 
BV range, output the number fit into the range.
For example, for 4-bit signed integers, input 
-9, 16 (2^4), and output 7 *)
let signed_modulo_int (n : int) (range_size : int) : int = 
  let neg_lim = -(range_size/2) in
  let pos_lim = (range_size/2) - 1 in
    if (n < neg_lim) then
      let diff = (neg_lim - n) in 
      let diff_mod = (diff mod range_size) in
        if (diff_mod = 0) then neg_lim else (pos_lim - (diff_mod - 1))
    else if (n > pos_lim) then
      let diff = (n - pos_lim) in
	    let diff_mod = (diff mod range_size) in
	      if (diff_mod = 0) then pos_lim else (neg_lim + (diff_mod - 1))
    else n

let int_to_bv (size : int) (i : int) : t =
  let m = 1 lsl size in 
  let n = signed_modulo_int i m in
  if (n >= 0) then 
    (int_to_ubv size i)
  else 
    let pos = (int_to_ubv size (-(n))) in
    let onescomp = ones_comp pos in 
    plus_one onescomp (bin_one size)

let int_to_bv8 = int_to_bv 8 

let int_to_bv16 = int_to_bv 16

let int_to_bv32 = int_to_bv 32

let int_to_bv64 = int_to_bv 64


(* Using functions involving numerals rather than ints *)
(* ********************************************************************** *)
(* Signed BV -> Int                                                       *)
(* ********************************************************************** *)

let bv_to_int (size : int) (b : t) :  int =
  if ((List.nth b 0) = false) then
    ubv_to_int size b
  else 
    (-(ubv_to_int size 
                  (plus_one (ones_comp b) 
                            (bin_one size))))

let bv8_to_int = bv_to_int 8

let bv16_to_int = bv_to_int 16

let bv32_to_int = bv_to_int 32

let bv64_to_int = bv_to_int 64
*)


(* ********************************************************************** *)
(* Arithmetic Operations                                                  *)
(* ********************************************************************** *)

(* Addition *)
let sbv_add (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else
    let num1 = bv_to_num (Numeral.of_int (List.length bv1)) bv1 in
    let num2 = bv_to_num (Numeral.of_int (List.length bv2)) bv2 in
    let sum = Numeral.add num1 num2 in
    num_to_bv (Numeral.of_int (List.length bv1)) sum

let ubv_add (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else
    let num1 = ubv_to_num (Numeral.of_int (List.length bv1)) bv1 in
    let num2 = ubv_to_num (Numeral.of_int (List.length bv2)) bv2 in
    let sum = Numeral.add num1 num2 in
    num_to_ubv (Numeral.of_int (List.length bv1)) sum


(* Multiplication *)
let sbv_mult (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else
    let num1 = bv_to_num (Numeral.of_int (List.length bv1)) bv1 in
    let num2 = bv_to_num (Numeral.of_int (List.length bv2)) bv2 in
    let prod = Numeral.mult num1 num2 in
    num_to_bv (Numeral.of_int (List.length bv1)) prod

let ubv_mult (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else
    let num1 = ubv_to_num (Numeral.of_int (List.length bv1)) bv1 in
    let num2 = ubv_to_num (Numeral.of_int (List.length bv2)) bv2 in
    let prod = Numeral.mult num1 num2 in
    num_to_ubv (Numeral.of_int (List.length bv1)) prod


(* Division *)
let sbv_div (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else
    let num1 = bv_to_num (Numeral.of_int (List.length bv1)) bv1 in
    let num2 = bv_to_num (Numeral.of_int (List.length bv2)) bv2 in
    let q = 
      (match num1, num2 with
      | n1, n2 when ((Numeral.geq n1 Numeral.zero) && 
                     (Numeral.geq n2 Numeral.zero))
        -> Numeral.div n1 n2
      | n1, n2 when ((Numeral.lt n1 Numeral.zero) &&
                     (Numeral.geq n2 Numeral.zero))
        -> let neg_n1 = (Numeral.neg n1) in
           let q_aux = Numeral.div neg_n1 n2 in
           Numeral.neg q_aux
      | n1, n2 when ((Numeral.geq n1 Numeral.zero) &&
                     (Numeral.lt n2 Numeral.zero))
        -> let neg_n2 = (Numeral.neg n2) in
           let q_aux = Numeral.div n1 neg_n2 in
           Numeral.neg q_aux
      | n1, n2 when ((Numeral.lt n1 Numeral.zero) &&
                     (Numeral.lt n2 Numeral.zero))
        -> let neg_n1 = (Numeral.neg n1) in
           let neg_n2 = (Numeral.neg n2) in
           Numeral.div neg_n1 neg_n2
      | _ -> assert false) in
    num_to_bv (Numeral.of_int (List.length bv1)) q

let ubv_div (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else
    let num1 = ubv_to_num (Numeral.of_int (List.length bv1)) bv1 in
    let num2 = ubv_to_num (Numeral.of_int (List.length bv2)) bv2 in
    let q = Numeral.div num1 num2 in
    num_to_ubv (Numeral.of_int (List.length bv1)) q


(* Subtraction *)
let sbv_sub (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else
    let num1 = bv_to_num (Numeral.of_int (List.length bv1)) bv1 in
    let num2 = bv_to_num (Numeral.of_int (List.length bv2)) bv2 in
    let diff = Numeral.sub num1 num2 in
    num_to_bv (Numeral.of_int (List.length bv1)) diff


(* ********************************************************************** *)
(* Logical Operations                                                     *)
(* ********************************************************************** *)

(* Conjunciton *)
let rec bv_and_aux (bv1 : t) (bv2 : t) (acc : t) : t =
  match bv1, bv2 with
  | [], [] -> acc
  | h1 :: t1, h2 :: t2 -> bv_and_aux t1 t2 (List.append acc [h1 && h2])
  | _ -> assert false

let bv_and (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else
    bv_and_aux bv1 bv2 []


(* Disjunction *)
let rec bv_or_aux (bv1 : t) (bv2 : t) (acc : t) : t =
  match bv1, bv2 with
  | [], [] -> acc
  | h1 :: t1, h2 :: t2 -> bv_or_aux t1 t2 (List.append acc [h1 || h2])
  | _ -> assert false

let bv_or (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else
    bv_or_aux bv1 bv2 []


(* Negation *)
let rec bv_not_aux (bv : t) (acc : t) : t =
  match bv with
  | [] -> acc
  | h :: t -> bv_not_aux t (List.append acc [not h])

let bv_not (bv : t) : t =
  bv_not_aux bv []


(* ********************************************************************** *)
(* Unused - Might be Useful in the Future                                 *)
(* ********************************************************************** *)

(* Function that inputs a list of bitvectors and returns Some n
   if all bitvectors have size n, where n = 8,16,32,64, and None otherwise 
   Special case: it returns None for the input of an empty list of BVs*)
let check_bv_uniform bvl = 
  if List.length bvl = 0 then
    None
  else
    let l_lens = List.map List.length bvl in
      let el1 = List.hd l_lens in
        if ((el1 != 8) && (el1 != 16) && (el1 != 32) && (el1 != 64)) then
          None
        else
          if List.for_all (fun (i : int) -> i = el1) l_lens then
            Some el1
          else
            None


(* ********************************************************************** *)
(* Auxiliary Functions                                                    *)
(* ********************************************************************** *)

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


(* ********************************************************************** *)
(* Pretty-printing                                                        *)
(* ********************************************************************** *)

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

(* Pretty-print a bitvector in Yices' binary format given the decimal value and size *)
let pp_yices_print_bitvector_d ppf i s = 
  let size = (Numeral.to_int s) in
  let b = (match size with
    | 8 -> num_to_ubv8 i
    | 16 -> num_to_ubv16 i
    | 32 -> num_to_ubv32 i
    | 64 -> num_to_ubv64 i
    | _ -> raise NonStandardBVSize) 
  in
    fprintf ppf "0b%a" pp_print_bitvector_b' b

(* Pretty-print a bitvector in SMTLIB extended decimal format *)
let pp_smtlib_print_bitvector_d ppf n size = 
  fprintf ppf "(_ bv%s %s)" (Numeral.string_of_numeral n) (Numeral.string_of_numeral size)

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
    
      
(* ********************************************************************** *)
(* Conversions                                                            *)
(* ********************************************************************** *)

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
let rec bitvector_of_string_b (a : t) (i : int) (s : string) : t = 

  if i <= 1 then a else
    
    match String.sub s i 1 with 

      | "0" -> bitvector_of_string_b (false :: a) (pred i) s
      | "1" -> bitvector_of_string_b (true :: a) (pred i) s
      | _ -> raise (Invalid_argument "bitvector_of_string")

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

    (* Convert from a decimal string *)
    | "_ " -> 
      let f n s = (n, s) in
        let (n, s) =
          (try 
            Scanf.sscanf s "(_ bv%d %d)" f (*use %Ld and %u here to account for 64 bit ints*)
           with
           Scanf.Scan_failure _ -> 
            raise (Invalid_argument "bitvector_of_string"))
        in (num_to_bv (Numeral.of_int s) (Numeral.of_int n))
        (*with
          | "bv" -> [false;false;true;true]

            let len = String.length s in
              let lenminus1 = (len - 1) in

              match
              (try 
                String.sub s lenminus1 1)
               with
                Invalid_argument _ ->
                  raise (Invalid_argument "bitvector_of_string"))

              with 
                | ")" ->

                  let substr = String.sub s 5 (len - 6) in
                    let num_list = (String.split_on_char ' ' substr) in
                      let n = (List.nth num_list 0) in
                        let s = (List.nth num_list 1) in
                          let n_num = (int_of_string n) in
                            let s_num = (int_of_string s) in
                              int_to_bv s_num n_num
                
                | _ -> raise (Invalid_argument "bitvector_of_string")
          
          | _ -> raise (Invalid_argument "bitvector_of_string")*)

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
(* Comparison operators                                                   *)
(* ********************************************************************** *)

(* Equality *)
let rec equal bv1 bv2 = 
  match bv1, bv2 with
  | [], [] -> true
  | h1 :: t1, h2 :: t2 -> (h1 = h2) && (equal t1 t2)
  | _ -> raise ComparingUnequalBVs

(* Unsigned lesser than *)
let rec ult bv1 bv2 = 
  match bv1, bv2 with
  | [], [] -> false
  | h1 :: t1, h2 :: t2 -> 
    (match h1, h2 with
    | true, false -> false
    | false, true -> true 
    | _ -> (ult t1 t2))
  | _ -> raise ComparingUnequalBVs

(* Unsigned greater than *)
let rec ugt bv1 bv2 =
  match bv1, bv2 with
  | [], [] -> false
  | h1 :: t1, h2 :: t2 -> 
    (match h1, h2 with
    | false, true -> false
    | true, false -> true
    | _ -> (ugt t1 t2))
  | _ -> raise ComparingUnequalBVs

(* Unsigned lesser than or equal to *)
let rec ulte bv1 bv2 =
  match bv1, bv2 with
  | [], [] -> true
  | h1 :: t1, h2 :: t2 ->
    (match h1, h2 with
    | false, true -> true
    | true, false -> false
    | _ -> (ulte t1 t2))
  | _ -> raise ComparingUnequalBVs

(* Unsigned greater than or equal to *)
let rec ugte bv1 bv2 =
  match bv1, bv2 with
  | [], [] -> true
  | h1 :: t1, h2 :: t2 -> 
    (match h1, h2 with
    | true, false -> true
    | false, true -> false
    | _ -> (ugte t1 t2))
  | _ -> raise ComparingUnequalBVs

(* Signed lesser than *)
let lt (bv1 : t) (bv2 : t) : bool = 
  let i1 = bv_to_num (Numeral.of_int (List.length bv1)) bv1 in
  let i2 = bv_to_num (Numeral.of_int (List.length bv2)) bv2 in
    (Numeral.lt i1 i2)

(* Signed greater than *)
let gt (bv1 : t) (bv2 : t) : bool = 
  let i1 = bv_to_num (Numeral.of_int (List.length bv1)) bv1 in
  let i2 = bv_to_num (Numeral.of_int (List.length bv2)) bv2 in
    (Numeral.gt i1 i2)

(* Signed lesser than or equal to *)
let lte (bv1 : t) (bv2 : t) : bool = 
  let i1 = bv_to_num (Numeral.of_int (List.length bv1)) bv1 in
  let i2 = bv_to_num (Numeral.of_int (List.length bv2)) bv2 in
    (Numeral.leq i1 i2)

(* Signed greater than or equal to *)
let gte (bv1 : t) (bv2 : t) : bool = 
  let i1 = bv_to_num (Numeral.of_int (List.length bv1)) bv1 in
  let i2 = bv_to_num (Numeral.of_int (List.length bv2)) bv2 in
    (Numeral.geq i1 i2)


(* ********************************************************************** *)
(* Infix comparison operators                                             *)
(* ********************************************************************** *)

(* Equality *)
let ( = ) = equal

(* Signed lesser than *)
let ( < ) = lt

(* Signed greater than *)
let ( > ) = gt

(* Signed lesser than or equal to *)
let ( <= ) = lte

(* Signed greater than or equal to *)
let ( >= ) = gte