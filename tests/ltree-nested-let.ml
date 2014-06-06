let t_bool = Type.t_bool;;
let t_int = Type.t_int;;

let s_e_s1_1 = UfSymbol.mk_uf_symbol "__top.e_s1.1" [] t_bool;;
let s_e_s2_1 = UfSymbol.mk_uf_symbol "__top.e_s2.1" [] t_bool;;
let s_e_s3_1 = UfSymbol.mk_uf_symbol "__top.e_s3.1" [] t_bool;;
let s_init_invalid_s_1 = UfSymbol.mk_uf_symbol "__top.init_invalid_s.1" [] t_int;; 
let s___nondet_2 = UfSymbol.mk_uf_symbol "__top.__nondet_2" [] t_int;; 
let s___nondet_1 = UfSymbol.mk_uf_symbol "__top.__nondet_1" [] t_int;;
let s___nondet_0 = UfSymbol.mk_uf_symbol "__top.__nondet_0" [] t_int;;
let s_OK_1 = UfSymbol.mk_uf_symbol "__top.OK.1" [] t_int;;
let s_invalid_s_1 = UfSymbol.mk_uf_symbol "__top.invalid_s.1" [] t_bool;; 
let s_valid_s_1 = UfSymbol.mk_uf_symbol "__top.valid_s.1" [] t_int;;
let s_dirty_s_1 = UfSymbol.mk_uf_symbol "__top.dirty_s.1" [] t_int;;
let s_mem_init_s_1 = UfSymbol.mk_uf_symbol "__top.mem_init_s.1" [] t_int;;
let s_env_1 = UfSymbol.mk_uf_symbol "__top.env.1" [] t_bool;;
let s___abs_4_1 = UfSymbol.mk_uf_symbol "__top.__abs_4.1" [] t_bool;;
let s___abs_6_1 = UfSymbol.mk_uf_symbol "__top.__abs_6.1" [] t_int;;
let s_e_s1_0 = UfSymbol.mk_uf_symbol "__top.e_s1.0" [] t_bool;;
let s_e_s2_0 = UfSymbol.mk_uf_symbol "__top.e_s2.0" [] t_bool;;
let s_e_s3_0 = UfSymbol.mk_uf_symbol "__top.e_s3.0" [] t_bool;;
let s_init_invalid_s_0 = UfSymbol.mk_uf_symbol "__top.init_invalid_s.0" [] t_int;; 
let s___nondet_2 = UfSymbol.mk_uf_symbol "__top.__nondet_2" [] t_int;; 
let s___nondet_1 = UfSymbol.mk_uf_symbol "__top.__nondet_1" [] t_int;;
let s___nondet_0 = UfSymbol.mk_uf_symbol "__top.__nondet_0" [] t_int;;
let s_OK_0 = UfSymbol.mk_uf_symbol "__top.OK.0" [] t_int;;
let s_invalid_s_0 = UfSymbol.mk_uf_symbol "__top.invalid_s.0" [] t_bool;; 
let s_valid_s_0 = UfSymbol.mk_uf_symbol "__top.valid_s.0" [] t_int;;
let s_dirty_s_0 = UfSymbol.mk_uf_symbol "__top.dirty_s.0" [] t_int;;
let s_mem_init_s_0 = UfSymbol.mk_uf_symbol "__top.mem_init_s.0" [] t_int;;
let s_env_0 = UfSymbol.mk_uf_symbol "__top.env.0" [] t_bool;;
let s___abs_4_0 = UfSymbol.mk_uf_symbol "__top.__abs_4.0" [] t_bool;;
let s___abs_6_0 = UfSymbol.mk_uf_symbol "__top.__abs_6.0" [] t_int;;

let v_e_s1_1 = Var.mk_fresh_var t_bool;;
let v_e_s2_1 = Var.mk_fresh_var t_bool;;
let v_e_s3_1 = Var.mk_fresh_var t_bool;;
let v_init_invalid_s_1 = Var.mk_fresh_var t_int;; 
let v___nondet_2 = Var.mk_fresh_var t_int;; 
let v___nondet_1 = Var.mk_fresh_var t_int;;
let v___nondet_0 = Var.mk_fresh_var t_int;;
let v_OK_1 = Var.mk_fresh_var t_int;;
let v_invalid_s_1 = Var.mk_fresh_var t_bool;; 
let v_valid_s_1 = Var.mk_fresh_var t_int;;
let v_dirty_s_1 = Var.mk_fresh_var t_int;;
let v_mem_init_s_1 = Var.mk_fresh_var t_int;;
let v_env_1 = Var.mk_fresh_var t_bool;;
let v___abs_4_1 = Var.mk_fresh_var t_bool;;
let v___abs_6_1 = Var.mk_fresh_var t_int;;
let v_e_s1_0 = Var.mk_fresh_var t_bool;;
let v_e_s2_0 = Var.mk_fresh_var t_bool;;
let v_e_s3_0 = Var.mk_fresh_var t_bool;;
let v_init_invalid_s_0 = Var.mk_fresh_var t_int;; 
let v___nondet_2 = Var.mk_fresh_var t_int;; 
let v___nondet_1 = Var.mk_fresh_var t_int;;
let v___nondet_0 = Var.mk_fresh_var t_int;;
let v_OK_0 = Var.mk_fresh_var t_int;;
let v_invalid_s_0 = Var.mk_fresh_var t_bool;; 
let v_valid_s_0 = Var.mk_fresh_var t_int;;
let v_dirty_s_0 = Var.mk_fresh_var t_int;;
let v_mem_init_s_0 = Var.mk_fresh_var t_int;;
let v_env_0 = Var.mk_fresh_var t_bool;;
let v___abs_4_0 = Var.mk_fresh_var t_bool;;
let v___abs_6_0 = Var.mk_fresh_var t_int;;

let l =
  [(v_e_s1_1, Term.mk_uf s_e_s1_1 []);
   (v_e_s2_1, Term.mk_uf s_e_s2_1 []);
   (v_e_s3_1, Term.mk_uf s_e_s3_1 []);
   (v_init_invalid_s_1, Term.mk_uf s_init_invalid_s_1 []);
   (v___nondet_2, Term.mk_uf s___nondet_2 []);
   (v___nondet_1, Term.mk_uf s___nondet_1 []);
   (v___nondet_0, Term.mk_uf s___nondet_0 []);
   (v_OK_1, Term.mk_uf s_OK_1 []);
   (v_invalid_s_1, Term.mk_uf s_invalid_s_1 []);
   (v_valid_s_1, Term.mk_uf s_valid_s_1 []);
   (v_dirty_s_1, Term.mk_uf s_dirty_s_1 []);
   (v_mem_init_s_1, Term.mk_uf s_mem_init_s_1 []);
   (v_env_1, Term.mk_uf s_env_1 []);
   (v___abs_4_1, Term.mk_uf s___abs_4_1 []);
   (v___abs_6_1, Term.mk_uf s___abs_6_1 []);
   (v_e_s1_0, Term.mk_uf s_e_s1_0 []);
   (v_e_s2_0, Term.mk_uf s_e_s2_0 []);
   (v_e_s3_0, Term.mk_uf s_e_s3_0 []);
   (v_init_invalid_s_0, Term.mk_uf s_init_invalid_s_0 []);
   (v___nondet_2, Term.mk_uf s___nondet_2 []);
   (v___nondet_1, Term.mk_uf s___nondet_1 []);
   (v___nondet_0, Term.mk_uf s___nondet_0 []);
   (v_OK_0, Term.mk_uf s_OK_0 []);
   (v_invalid_s_0, Term.mk_uf s_invalid_s_0 []);
   (v_valid_s_0, Term.mk_uf s_valid_s_0 []);
   (v_dirty_s_0, Term.mk_uf s_dirty_s_0 []);
   (v_mem_init_s_0, Term.mk_uf s_mem_init_s_0 []);
   (v_env_0, Term.mk_uf s_env_0 []);
   (v___abs_4_0, Term.mk_uf s___abs_4_0 []);
   (v___abs_6_0, Term.mk_uf s___abs_6_0 [])];;

 
let v_1 = Var.mk_fresh_var t_bool;;
let v_2 = Var.mk_fresh_var t_bool;;
let v_3 = Var.mk_fresh_var t_bool;;
let v_4 = Var.mk_fresh_var t_bool;;
let v_5 = Var.mk_fresh_var t_bool;;
let v_6 = Var.mk_fresh_var t_bool;;
let v_7 = Var.mk_fresh_var t_bool;;
let v_8 = Var.mk_fresh_var t_bool;;
let v_9 = Var.mk_fresh_var t_bool;;
let v_10 = Var.mk_fresh_var t_bool;;
let v_11 = Var.mk_fresh_var t_bool;;
let v_12 = Var.mk_fresh_var t_bool;;
let v_13 = Var.mk_fresh_var t_bool;;
let v_14 = Var.mk_fresh_var t_bool;;
let v_15 = Var.mk_fresh_var t_bool;;
let v_16 = Var.mk_fresh_var t_bool;;
let v_17 = Var.mk_fresh_var t_bool;;
let v_18 = Var.mk_fresh_var t_bool;;
let v_19 = Var.mk_fresh_var t_bool;;
let v_20 = Var.mk_fresh_var t_bool;;
let v_21 = Var.mk_fresh_var t_bool;;
let v_22 = Var.mk_fresh_var t_bool;;
let v_23 = Var.mk_fresh_var t_bool;;
let v_24 = Var.mk_fresh_var t_bool;;
let v_25 = Var.mk_fresh_var t_bool;;
let v_26 = Var.mk_fresh_var t_bool;;
let v_27 = Var.mk_fresh_var t_bool;;
let v_28 = Var.mk_fresh_var t_bool;;
let v_29 = Var.mk_fresh_var t_bool;;

let v = Term.mk_var;;

open Term.Abbrev

let t1 = Term.mk_let l (Term.mk_var v_e_s1_1);;

let t2 = Term.mk_let l (Term.mk_var v_e_s2_1);;

let t3 = Term.mk_let l (Term.mk_var v_e_s3_1);;

let t4 = Term.mk_let l (Term.mk_var v_init_invalid_s_1);;

let t5 = Term.mk_let l (Term.mk_var v___nondet_0);;

let t6 = Term.mk_let l (Term.mk_var v___nondet_1);;

let t7 = Term.mk_let l (Term.mk_var v___nondet_2);;

let t8 = Term.mk_let l (Term.mk_var v_invalid_s_1);;

let t9 = Term.mk_let l (Term.mk_var v_valid_s_1);;

let t10 = Term.mk_let l (Term.mk_var v_dirty_s_1);;

let t11 = Term.mk_let l (Term.mk_var v_mem_init_s_1);;

let t12 = Term.mk_let l (Term.mk_var v_e_s1_0);;

let t13 = Term.mk_let l (Term.mk_var v_e_s2_0);;

let t14 = Term.mk_let l (Term.mk_var v_e_s3_0);;

let t15 = Term.mk_let l (Term.mk_var v_init_invalid_s_0);;

let t16 = Term.mk_let l (Term.mk_var v___nondet_0);;

let t17 = Term.mk_let l (Term.mk_var v___nondet_1);;

let t18 = Term.mk_let l (Term.mk_var v___nondet_2);;

let t19 = Term.mk_let l (Term.mk_var v_invalid_s_0);;

let t20 = Term.mk_let l (Term.mk_var v_valid_s_0);;

let t21 = Term.mk_let l (Term.mk_var v_dirty_s_0);;

let t22 = Term.mk_let l (Term.mk_var v_mem_init_s_0);;

let l1 = 
  Term.mk_let 
    [(v_1, t1);
     (v_2, t2);
     (v_3, t3);
     (v_4, t4);
     (v_5, t5);
     (v_6, t6);
     (v_7, t7);
     (v_8, t8);
     (v_9, t9);
     (v_10, t10);
     (v_11, t11);
     (v_12, t12);
     (v_13, t13);
     (v_14, t14);
     (v_15, t15);
     (v_16, t16);
     (v_17, t17);
     (v_18, t18);
     (v_19, t19);
     (v_20, t20);
     (v_21, t21);
     (v_22, t22)];;

let t23 = v v_19 >=@ ?%@ 1;;

let l2 = Term.mk_let [(v_23, t23)];;

let t24 = v v_20 >=@ ?%@ 1;;

let l3 =  Term.mk_let [(v_24, t24)];;

let t25 = v v_19 >=@ ?%@ 1;;

let l4 =  Term.mk_let [(v_25, t25)];;

let e_l = l1 (l2 (l3 (l4 (v v_8))));;

let ite = Term.mk_ite;;

let t_r = 
  (ite
     (v v_1)
     (ite (v v_25) (((v v_19) +@ (v v_21)) -@ ?%@ 1) (v v_19))
     (ite
       (v v_2)
       (ite (v v_24) ((((v v_19) +@ (v v_21)) +@ (v v_20)) -@ ?%@ 1) (v v_19))
       (ite
         (v v_3)
         (ite (v v_23) ((((v v_19) +@ (v v_21)) +@ (v v_20)) -@ ?%@ 1) (v v_19))
         (v v_19))));;
       

let e_r = l1 (l2 (l3 (l4 t_r)));;

let t = e_l =@ r_r;;

let t' = Term.eval_t (fun t _ -> t) t;;
