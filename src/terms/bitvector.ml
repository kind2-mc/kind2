open Format

(* Constant bitvector *)
type t = bool list

exception ComparingUnequalBVs
exception NonStandardBVSize

(* Convert a bitvector to an integer *)
let length_of_bitvector b = List.length b

(* Function that inputs bit b, integer n, and repeats b n times *)
let rec repeat_bit (b : bool) (n : int) : t =
 match n with
 | 0 -> []
 | n -> b :: repeat_bit b (n - 1)

(* Bit-vector representing decimal 0 *)
let zero (len : int) : t = 
  repeat_bit false len

(* Bit-vector representing decimal 1 *)
let one (len : int) : t = 
  (repeat_bit false (len - 1)) @ [true]

(* Bit-vector representing hexadecimal F - all bit's are 1 *)
let f (len : int) : t =
  repeat_bit true len

(* Function that extracts m down to n from the input bitvector *)
let bvextract (m : int) (n : int) (b : t) : t =
  Lib.list_slice (List.rev b) n m |> List.rev

(* Function that sign extends the input bitvector by m bits *)
let bvsignext (m : int) (b : t) : t =
  let sign = List.hd b in
    let rec repeat (m : int) (b : bool) : t =
      match m with
      | 0 -> []
      | m' -> b :: repeat (m' - 1) b 
    in List.append (repeat m sign) b

let bvzeroext (m : int) (b : t) : t = zero m @ b

(* Function that concatenates the input bitvectors *)
let bvconcat (b1 : t) (b2 : t) : t =
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
let rec ubv_to_num' (size : Numeral.t) (b : t) : Numeral.t =
  match b with
  | h :: t -> 
      let prod = Numeral.mult (bool_to_bin h) 
                              (pow2 (Numeral.sub size Numeral.one)) 
      in
        Numeral.add prod (ubv_to_num' (Numeral.sub size Numeral.one) t)
  | [] -> Numeral.zero

let ubv_to_num (b : t) : Numeral.t =
  let len = length_of_bitvector b in
  match len with
  | 8 | 16 | 32 | 64 -> ubv_to_num' (Numeral.of_int len) b
  | _ -> raise NonStandardBVSize

let ubv8_to_num = ubv_to_num' (Numeral.of_int 8)

let ubv16_to_num = ubv_to_num' (Numeral.of_int 16)

let ubv32_to_num = ubv_to_num' (Numeral.of_int 32)

let ubv64_to_num = ubv_to_num' (Numeral.of_int 64)


(* ********************************************************************** *)
(* Numeral -> Signed BV                                                   *)
(* ********************************************************************** *)

(* Input any numeral n, input the size of the BV range, output the 
numeral fit into the range.For example, for 4-bit signed integers, 
input -9, 16 (2^4), and output 7 *)
let signed_modulo (n : Numeral.t) (range_size : Numeral.t) : Numeral.t = 
  (* a range of n in signed integers runs from -n/2 to (n/2-1) *)
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

let bv_to_num' (size : Numeral.t) (b : t) : Numeral.t =
  if((List.nth b 0) = false) then
    ubv_to_num' size b
  else
    (Numeral.neg (ubv_to_num' size
                             (plus_one (ones_comp b) 
                                       (bin_one (Numeral.to_int size)))))

let bv_to_num (b : t) : Numeral.t =
  let len = length_of_bitvector b in
  match len with
  | 8 | 16 | 32 | 64 -> bv_to_num' (Numeral.of_int len) b
  | _ -> raise NonStandardBVSize


let bv8_to_num = bv_to_num' (Numeral.of_int 8)

let bv16_to_num = bv_to_num' (Numeral.of_int 16)

let bv32_to_num = bv_to_num' (Numeral.of_int 32)

let bv64_to_num = bv_to_num' (Numeral.of_int 64)


(* ********************************************************************** *)
(* Arithmetic Operations                                                  *)
(* ********************************************************************** *)

(* Addition *)
let sbv_add (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else
    let num1 = bv_to_num' (Numeral.of_int (List.length bv1)) bv1 in
    let num2 = bv_to_num' (Numeral.of_int (List.length bv2)) bv2 in
    let sum = Numeral.add num1 num2 in
    num_to_bv (Numeral.of_int (List.length bv1)) sum

let ubv_add (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else
    let num1 = ubv_to_num' (Numeral.of_int (List.length bv1)) bv1 in
    let num2 = ubv_to_num' (Numeral.of_int (List.length bv2)) bv2 in
    let sum = Numeral.add num1 num2 in
    num_to_ubv (Numeral.of_int (List.length bv1)) sum


(* Multiplication *)
let sbv_mult (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else
    let num1 = bv_to_num' (Numeral.of_int (List.length bv1)) bv1 in
    let num2 = bv_to_num' (Numeral.of_int (List.length bv2)) bv2 in
    let prod = Numeral.mult num1 num2 in
    num_to_bv (Numeral.of_int (List.length bv1)) prod

let ubv_mult (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else
    let num1 = ubv_to_num' (Numeral.of_int (List.length bv1)) bv1 in
    let num2 = ubv_to_num' (Numeral.of_int (List.length bv2)) bv2 in
    let prod = Numeral.mult num1 num2 in
    num_to_ubv (Numeral.of_int (List.length bv1)) prod


(* Division *)
let sbv_div (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else
    let num1 = bv_to_num' (Numeral.of_int (List.length bv1)) bv1 in
    let num2 = bv_to_num' (Numeral.of_int (List.length bv2)) bv2 in
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
    let num1 = ubv_to_num' (Numeral.of_int (List.length bv1)) bv1 in
    let num2 = ubv_to_num' (Numeral.of_int (List.length bv2)) bv2 in
    let q = Numeral.div num1 num2 in
    num_to_ubv (Numeral.of_int (List.length bv1)) q


(* Remainder *)
let sbv_rem (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else
    let num1 = bv_to_num' (Numeral.of_int (List.length bv1)) bv1 in
    let num2 = bv_to_num' (Numeral.of_int (List.length bv2)) bv2 in
    let r = match (num1 < Numeral.zero, num2 < Numeral.zero) with
    | false, false -> Numeral.rem num1 num2
    | true, false -> Numeral.neg (Numeral.rem (Numeral.neg num1) num2)
    | false, true -> Numeral.rem num1 (Numeral.neg num2)
    | true, true -> Numeral.neg (Numeral.rem (Numeral.neg num1) (Numeral.neg num2)) in
    num_to_bv (Numeral.of_int (List.length bv1)) r

let ubv_rem (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else 
    let num1 = ubv_to_num' (Numeral.of_int (List.length bv1)) bv1 in
    let num2 = ubv_to_num' (Numeral.of_int (List.length bv2)) bv2 in
    let r = Numeral.rem num1 num2 in
    num_to_ubv (Numeral.of_int (List.length bv1)) r


(* Subtraction *)
let sbv_sub (bv1 : t) (bv2 : t) : t =
  if ((List.length bv1) != (List.length bv2)) then
    raise ComparingUnequalBVs
  else
    let num1 = bv_to_num' (Numeral.of_int (List.length bv1)) bv1 in
    let num2 = bv_to_num' (Numeral.of_int (List.length bv2)) bv2 in
    let diff = Numeral.sub num1 num2 in
    num_to_bv (Numeral.of_int (List.length bv1)) diff


(* Negation *)
let rec create_one (size : Numeral.t) : t =
  if (Numeral.equal size Numeral.zero) then
    []
  else if (Numeral.equal size Numeral.one) then
    [true]
  else 
    false :: (create_one (Numeral.sub size Numeral.one))
  
(* Using ones_comp and bitwise_add from Numeral -> Signed BV conversion *)
let sbv_neg (bv : t) : t =
  let bv_ones_comp = ones_comp bv in
  let res = bitwise_add 
              (List.rev bv_ones_comp)
              (List.rev (create_one (Numeral.of_int (List.length bv))))
              false
  in List.rev res


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
  let i1 = bv_to_num' (Numeral.of_int (List.length bv1)) bv1 in
  let i2 = bv_to_num' (Numeral.of_int (List.length bv2)) bv2 in
    (Numeral.lt i1 i2)

(* Signed greater than *)
let gt (bv1 : t) (bv2 : t) : bool = 
  let i1 = bv_to_num' (Numeral.of_int (List.length bv1)) bv1 in
  let i2 = bv_to_num' (Numeral.of_int (List.length bv2)) bv2 in
    (Numeral.gt i1 i2)

(* Signed lesser than or equal to *)
let lte (bv1 : t) (bv2 : t) : bool = 
  let i1 = bv_to_num' (Numeral.of_int (List.length bv1)) bv1 in
  let i2 = bv_to_num' (Numeral.of_int (List.length bv2)) bv2 in
    (Numeral.leq i1 i2)

(* Signed greater than or equal to *)
let gte (bv1 : t) (bv2 : t) : bool = 
  let i1 = bv_to_num' (Numeral.of_int (List.length bv1)) bv1 in
  let i2 = bv_to_num' (Numeral.of_int (List.length bv2)) bv2 in
    (Numeral.geq i1 i2)


(* ********************************************************************** *)
(* Shift operators                                                   *)
(* ********************************************************************** *)

(* Left shift *)
let rec shift_left (bv : t) (n : Numeral.t) : t =
  if (Numeral.equal n Numeral.zero) then
    bv
  else
    (match bv with
    | [] -> []
    | _ :: t -> shift_left 
                  (List.append t [false]) 
                  (Numeral.sub n Numeral.one))

let bv_lsh (bv1 : t) (bv2 : t) : t =
  let n = ubv_to_num' (Numeral.of_int (List.length bv2)) bv2 in
    shift_left bv1 n


(* Right shift *)
let rec remove_last (bv : t) : t =
  match bv with
  | [] -> []
  | [_] -> []
  | h :: t -> h :: (remove_last t)

let rec shift_right (bv : t) (n : Numeral.t) : t =
  if (Numeral.equal n Numeral.zero) then
    bv
  else
    (match bv with
    | [] -> []
    | h :: t -> shift_right
                  (false :: (h :: (remove_last t)))
                  (Numeral.sub n Numeral.one))

let bv_rsh (bv1 : t) (bv2 : t) : t =
  let n = ubv_to_num' (Numeral.of_int (List.length bv2)) bv2 in
    shift_right bv1 n


(* Arithmetic right shift *)
let rec ar_shift_right (bv : t) (n : Numeral.t) (sign : bool) : t =
  if(Numeral.equal n Numeral.zero) then
    bv
  else
    (match bv with
    | [] -> []
    | h :: t -> ar_shift_right
                  (sign :: (h :: (remove_last t)))
                  (Numeral.sub n Numeral.one)
                  sign)

let bv_arsh (bv1 : t) (bv2 : t) : t =
  let n = ubv_to_num' (Numeral.of_int (List.length bv2)) bv2 in
  let sign = List.hd bv1 in
    ar_shift_right bv1 n sign


(* ********************************************************************** *)
(* Auxiliary Functions                                                    *)
(* ********************************************************************** *)




(* ********************************************************************** *)
(* Pretty-printing                                                        *)
(* ********************************************************************** *)


(* Binary *)

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


(* Decimal *) 

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
let pp_smtlib_print_bitvector_d ppf b =
  let len = length_of_bitvector b in
  let num = ubv_to_num' (Numeral.of_int len) b in
  fprintf ppf "(_ bv%a %d)" Numeral.pp_print_numeral num len

(* Pretty-print an unsigned Lustre machine integer *)
let pp_print_unsigned_machine_integer ppf b =
  let len = length_of_bitvector b in
    let num = (match len with
               | 8 -> ubv8_to_num b
               | 16 -> ubv16_to_num b
               | 32 -> ubv32_to_num b
               | 64 -> ubv64_to_num b
               | _ -> raise NonStandardBVSize) in
      let num_str = Numeral.string_of_numeral num in
        pp_print_string ppf ("(uint" ^  (string_of_int len) ^ " " ^ num_str ^ ")")

(* Pretty-print a signed Lustre machine integer *)
let pp_print_signed_machine_integer ppf b =
  let len = length_of_bitvector b in
    let num = (match len with
               | 8 -> bv8_to_num b
               | 16 -> bv16_to_num b
               | 32 -> bv32_to_num b
               | 64 -> bv64_to_num b
               | _ -> raise NonStandardBVSize) in
      let num_str = Numeral.string_of_numeral num in
        pp_print_string ppf ("(int" ^  (string_of_int len) ^ " " ^ num_str ^ ")")


(* Hexadecimal *)

(* Pretty-print a bitvector in hexadecimal format *)
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

(*
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
*)

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


(*
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
*)

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

(*
(* Convert an infinite-precision integer numeral to a string *)
let string_of_numeral s = HString.string_of_hstring s

(* Convert an infinite-precision real decimal to a string *)
let string_of_decimal s = HString.string_of_hstring s 
*)

(* Convert a hashconsed string to a Boolean value *)
let bool_of_hstring s = bool_of_string (HString.string_of_hstring s) 


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


(* ********************************************************************** *)
(* Currently unused operators                                             *)
(* ********************************************************************** *)

(* Function that returns the first bit of bitvector b *)
let first_bit (b : t) : bool =
  match b with
  | h :: _ -> h
  | _ -> raise NonStandardBVSize
