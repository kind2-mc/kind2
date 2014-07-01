(set-option :print-success true)
(set-option :produce-assignments true)
(set-option :produce-models true)
(set-option :produce-proofs false)
(set-option :produce-unsat-cores true)

(declare-fun __top.X.i (Int) Bool)
(declare-fun __top.X.x (Int) Int)
(declare-fun __top.X.OK (Int) Bool)

(define-fun __node_trans_X
  ((X.i.1 Bool)
   (X.x.1 Int)
   (X.OK.1 Bool)
   (X.i.0 Bool)
   (X.x.0 Int)
   (X.OK.0 Bool))
  Bool
  (and
   (= X.x.1 (ite (< X.x.0 2) (- 1 X.x.0) (ite X.i.1 3 2)))
   (= X.OK.1 (< X.x.1 3))))

(define-fun __node_init_X
  ((X.i.0 Bool) (X.x.0 Int) (X.OK.0 Bool))
  Bool
  (and (= X.x.0 0) (= X.OK.0 (< X.x.0 3))))

(define-fun __eq ((X1 Int) (X0 Int)) Bool
  (and
   (= (__top.X.i X1) (__top.X.i X0))
   (= (__top.X.x X1)  (__top.X.x X0))
   (= (__top.X.OK X1) (__top.X.OK X0))))

;; (assert (__node_init_X (__top.X.i 0) (__top.X.x 0) (__top.X.OK 0)))

(assert
 (__node_trans_X 
  (__top.X.i 1) (__top.X.x 1) (__top.X.OK 1)
  (__top.X.i 0) (__top.X.x 0) (__top.X.OK 0)))

(assert
 (__node_trans_X 
  (__top.X.i 2) (__top.X.x 2) (__top.X.OK 2)
  (__top.X.i 1) (__top.X.x 1) (__top.X.OK 1)))

(assert (__top.X.OK 0))
(assert (__top.X.OK 1))
(assert (__top.X.OK 2))

(assert (not (__eq 0 1)))
(assert (not (__eq 0 2)))
(assert (not (__eq 0 3)))
(assert (not (__eq 1 2)))
(assert (not (__eq 1 3)))
(assert (not (__eq 2 3)))

(assert (not (__top.X.OK 3)))

(check-sat)

(get-value
 ((__top.X.i 0) (__top.X.x 0) (__top.X.OK 0)
  (__top.X.i 1) (__top.X.x 1) (__top.X.OK 1)
  (__top.X.i 2) (__top.X.x 2) (__top.X.OK 2)
  (__top.X.i 3) (__top.X.x 3) (__top.X.OK 3)))

(exit)
