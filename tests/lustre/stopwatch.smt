(set-logic QF_UFLIA)
(set-option :produce-assignments true)


;; ======================================================================

;; node Switch(on, off: bool) returns (s: bool);
;; --@requires true
;; --@ensures ((on and pre (not s)) => s);
;; --@ensures ((off and pre s) => not s);
;; -- --@ensures (not (on or off) => (s = pre s);
;; let
;;   s = if (false -> pre s) then not off else on; 
;; tel

;; Initial state 
(define-fun 
  I_Switch
  ((on Bool) (off Bool) (s Bool))
  Bool
  (= s (ite false (not off) on)))

;; Transition relation from stream definition

(define-fun 
  T_Switch_Def 
  ((on_0 Bool) (on_1 Bool) (off_0 Bool) (off_1 Bool) (s_0 Bool) (s_1 Bool))
  Bool
  (= s_1 (ite s_0 (not off_1) on_1)))

;; Transition relation from pre- and postcondition

(define-fun
  T_Switch
  ((on_0 Bool) (on_1 Bool) (off_0 Bool) (off_1 Bool) (s_0 Bool) (s_1 Bool))
  Bool
  (=> 
   true
   (and
    (=> (and on_1 (not s_0)) s_1)
    (=> (and off_1 s_0) (not s_1)))))
;; Commenting out third ensures to get different behavior 
;;    (=> (not (or on_1 off_1)) (= s_0 s_1))))) 
   

;; ======================================================================

;; node Count(reset, x: bool) returns (c: int);
;; let
;;   c = if reset then 0
;;       else if x then (0 -> pre c) + 1
;;       else (0 -> pre c);
;; tel

;; Initial state 
(define-fun 
  I_Count
  ((reset Bool) (x Bool) (c Int)) 
  Bool
  (= c (ite reset 0 (ite x (+ 0 1) 0))))

;; Transition relation 
(define-fun 
  T_Count
  ((reset_0 Bool) (reset_1 Bool) (x_0 Bool) (x_1 Bool) (c_0 Int) (c_1 Int)) 
  Bool
  (= c_1 (ite reset_1 0 (ite x_1 (+ c_0 1) c_0))))

 
;; ======================================================================

;; node Stopwatch(on_off, reset, freeze: bool) returns (time: int);
;; var
;;   running, frozen:bool;
;;   cpt:int;
;; let
;;   running = Switch(on_off, on_off);
;;   frozen = Switch(freeze and running,
;;                   freeze or on_off);
;;   cpt = Count(reset and not running, running);
;;   time = if frozen then (0 -> pre time) else cpt;
;; tel

;; Initial state  
(define-fun 
  I_Stopwatch
  ((on_off Bool)
   (reset Bool)
   (freeze Bool)
   (running Bool)
   (frozen Bool)
   (cpt Int)
   (time Int))
  Bool
  (and
   (I_Switch on_off on_off running)
   (I_Switch 
    (and freeze running) 
    (or freeze on_off) 
    frozen)
   (I_Count 
    (and reset (not running))
    running
    cpt)
   (= time (ite frozen 0 cpt))))

;; Transition relation 
(define-fun 
  T_Stopwatch
  ((on_off_0 Bool)
   (on_off_1 Bool) 
   (reset_0 Bool)
   (reset_1 Bool) 
   (freeze_0 Bool)
   (freeze_1 Bool)
   (running_0 Bool)
   (running_1 Bool)
   (frozen_0 Bool)
   (frozen_1 Bool)
   (cpt_0 Int)
   (cpt_1 Int)
   (time_0 Int)
   (time_1 Int))
  Bool
  (and
   (T_Switch on_off_0 on_off_1 on_off_0 on_off_1 running_0 running_1)
   (T_Switch 
    (and freeze_0 running_0) 
    (and freeze_1 running_1) 
    (or freeze_0 on_off_0) 
    (or freeze_1 on_off_1) 
    frozen_0 
    frozen_1)
   (T_Count 
    (and reset_0 (not running_0))
    (and reset_1 (not running_1))
    running_0
    running_1
    cpt_0
    cpt_1)
   (= time_1 (ite frozen_1 time_0 cpt_1))))


;; Transition relation refined with definition T_Switch_Def
(define-fun 
  T_Stopwatch_Def
  ((on_off_0 Bool)
   (on_off_1 Bool) 
   (reset_0 Bool)
   (reset_1 Bool) 
   (freeze_0 Bool)
   (freeze_1 Bool)
   (running_0 Bool)
   (running_1 Bool)
   (frozen_0 Bool)
   (frozen_1 Bool)
   (cpt_0 Int)
   (cpt_1 Int)
   (time_0 Int)
   (time_1 Int))
  Bool
  (and
   (T_Switch_Def on_off_0 on_off_1 on_off_0 on_off_1 running_0 running_1)
   (T_Switch_Def 
    (and freeze_0 running_0) 
    (and freeze_1 running_1) 
    (or freeze_0 on_off_0) 
    (or freeze_1 on_off_1) 
    frozen_0 
    frozen_1)
   (T_Count 
    (and reset_0 (not running_0))
    (and reset_1 (not running_1))
    running_0
    running_1
    cpt_0
    cpt_1)
   (= time_1 (ite frozen_1 time_0 cpt_1))))

;; ======================================================================

;; State variables of the system
(declare-fun on_off (Int) Bool)
(declare-fun reset (Int) Bool)
(declare-fun freeze (Int) Bool)
(declare-fun running (Int) Bool)
(declare-fun frozen (Int) Bool)
(declare-fun cpt (Int) Int)
(declare-fun time (Int) Int)


;; Initial state 
(define-fun I ((s Int)) Bool
  (I_Stopwatch 
   (on_off s) 
   (reset s) 
   (freeze s) 
   (running s)
   (frozen s)
   (cpt s)
   (time s)))


;; Transition relation 
(define-fun T ((s Int) (t Int)) Bool
  (T_Stopwatch 
   (on_off s) 
   (on_off t) 
   (reset s) 
   (reset t) 
   (freeze s) 
   (freeze t)
   (running s)
   (running t)
   (frozen s)
   (frozen t)
   (cpt s)
   (cpt t)
   (time s)
   (time t)))

;; Transition relation refined with T_Stopwatch_Def
(define-fun T_Def ((s Int) (t Int)) Bool
  (T_Stopwatch_Def 
   (on_off s) 
   (on_off t) 
   (reset s) 
   (reset t) 
   (freeze s) 
   (freeze t)
   (running s)
   (running t)
   (frozen s)
   (frozen t)
   (cpt s)
   (cpt t)
   (time s)
   (time t)))

;; Initial state and four steps
(assert (I 0))
(assert (T 0 1))
(assert (T 1 2))
(assert (T 2 3))
(assert (T 3 4))
 

;; ======================================================================

;; Assert input 
(assert
 (and 
  (= (on_off 0) false)
  (= (on_off 1) false)
  (= (on_off 2) false) 
  (= (on_off 3) false)
  (= (on_off 4) false)
  (= (reset 0) false)
  (= (reset 1) false)
  (= (reset 2) false)
  (= (reset 3) false)
  (= (reset 4) false)
  (= (freeze 0) false) 
  (= (freeze 1) false) 
  (= (freeze 2) false) 
  (= (freeze 3) false) 
  (= (freeze 4) false)))

;; Simulate
(check-sat)

;; Get stream values
(get-value
 ((on_off 0) 
  (on_off 1) 
  (on_off 2) 
  (on_off 3) 
  (on_off 4) 
  (reset 0) 
  (reset 1) 
  (reset 2) 
  (reset 3) 
  (reset 4) 
  (freeze 0) 
  (freeze 1) 
  (freeze 2) 
  (freeze 3) 
  (freeze 4)
  (running 0)
  (running 1)
  (running 2)
  (running 3)
  (running 4)
  (frozen 0)
  (frozen 1)
  (frozen 2)
  (frozen 3)
  (frozen 4)
  (cpt 0)
  (cpt 1)
  (cpt 2)
  (cpt 3)
  (cpt 4)
  (time 0)
  (time 1)
  (time 2)
  (time 3)
  (time 4)))

;; Assert refined transition relation
(assert (T_Def 0 1))
(assert (T_Def 1 2))
(assert (T_Def 2 3))
(assert (T_Def 3 4))

;; Simulate
(check-sat)

;; Get stream values
(get-value
 ((on_off 0) 
  (on_off 1) 
  (on_off 2) 
  (on_off 3) 
  (on_off 4) 
  (reset 0) 
  (reset 1) 
  (reset 2) 
  (reset 3) 
  (reset 4) 
  (freeze 0) 
  (freeze 1) 
  (freeze 2) 
  (freeze 3) 
  (freeze 4)
  (running 0)
  (running 1)
  (running 2)
  (running 3)
  (running 4)
  (frozen 0)
  (frozen 1)
  (frozen 2)
  (frozen 3)
  (frozen 4)
  (cpt 0)
  (cpt 1)
  (cpt 2)
  (cpt 3)
  (cpt 4)
  (time 0)
  (time 1)
  (time 2)
  (time 3)
  (time 4)))
