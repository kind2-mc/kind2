;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; node Rise 
;;   (I : bool)
;; returns 
;;   (O : bool);
;; let 
;;   O = false -> pre(I) and I;
;; tel;


;; Initial state of node Rise
(define-fun I_Rise
  
  (

   ;; Inputs
   (I Bool)

   ;; Outputs 
   (O Bool)

   )

  ;; Predicate is Boolean
  Bool

  ;; Equation of output 
  (= O false))


;; Transition relation of node Rise
(define-fun

  T_Rise

  (

   ;; Stateless inputs

   ;; Stateful inputs
   (I Bool)
   (pre_I Bool)

   ;; Stateful variables

   ;; Stateless outputs
   (O Bool)

   ;; Stateful outputs 

   )

  ;; Predicate is Boolean
  Bool
  
  ;; Equation of output 
  (= O (and pre_I I)))


;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; node PFS_Logic
;;   (riseTS, riseOSPF : bool;
;;    const Primary_Side : bool; 
;;    const PFS_Initial_Value : bool) 
;; 
;; returns 
;;   (PFS : bool);
;; 
;; const inhibit_count_max = 2;
;; 
;; var
;;   Start_to_Pilot_Flying, 
;;   Start_to_Inhibited, 
;;   Inhibited_to_Listening, 
;;   Inhibited_to_Inhibited, 
;;   Listening_to_Pilot_Flying, 
;;   Pilot_Flying_to_Inhibited : bool;
;; 
;;   state : 
;;     enum { St_Start, St_Inhibited,  St_Listening, St_Pilot_Flying};
;; 
;;   inhibit_count : subrange [0, inhibit_count_max] of int;
;; 
;;   inhibit_count_bounded : bool;
;;   pfs_state_consistency : bool;
;; 
;; let
;;  
;;   Start_to_Pilot_Flying = 
;;     (St_Start -> pre(state)) = St_Start and Primary_Side;
;; 
;;   Start_to_Inhibited = 
;;     (St_Start -> pre(state)) = St_Start and (not Primary_Side);
;; 
;;   Inhibited_to_Listening = 
;;     (St_Start -> pre(state)) = St_Inhibited and 
;;       (0 -> pre(inhibit_count)) >= inhibit_count_max;
;;   
;;   Inhibited_to_Inhibited = 
;;     (St_Start -> pre(state)) = St_Inhibited and 
;;       not Inhibited_to_Listening;
;; 
;;   Listening_to_Pilot_Flying = 
;;     (St_Start -> pre(state)) = St_Listening and riseTS;
;; 
;;   Pilot_Flying_to_Inhibited = 
;;     (St_Start -> pre(state)) = St_Pilot_Flying and riseOSPF;
;; 
;;   state =
;;     if
;;       Inhibited_to_Inhibited or 
;;       Pilot_Flying_to_Inhibited or 
;;       Start_to_Inhibited
;;     then 
;;       St_Inhibited 
;;     else if 
;;       Inhibited_to_Listening 
;;     then 
;;       St_Listening
;;     else if 
;;       Listening_to_Pilot_Flying or 
;;       Start_to_Pilot_Flying 
;;     then 
;;       St_Pilot_Flying 
;;     else 
;;       (St_Start -> pre(state));
;;   
;;   PFS = 
;;     if 
;;       Listening_to_Pilot_Flying 
;;     then 
;;       true
;;     else if 
;;       Pilot_Flying_to_Inhibited 
;;     then 
;;       false
;;     else if 
;;       Start_to_Pilot_Flying 
;;     then 
;;       true
;;     else if 
;;       Start_to_Inhibited 
;;     then 
;;       false
;;     else 
;;       PFS_Initial_Value -> pre(PFS);
;;   
;;   inhibit_count = 
;;     if 
;;       Inhibited_to_Inhibited 
;;     then 
;;       (0 -> pre(inhibit_count)) + 1
;;     else if 
;;       Pilot_Flying_to_Inhibited 
;;     then 
;;       0
;;     else if 
;;       Start_to_Inhibited 
;;     then 
;;       0
;;     else 
;;       0 -> pre(inhibit_count);
;;   
;;   pfs_state_consistency = 
;;     not (state = St_Start) => (PFS = (state = St_Pilot_Flying));
;;   
;;   --%PROPERTY pfs_state_consistency;
;;        
;;   inhibit_count_bounded = 
;;     inhibit_count >= 0 and inhibit_count <= inhibit_count_max;
;;   
;;   --%PROPERTY inhibit_count_bounded;
;; 
;;   -- state_bounded = state >= St_Start and state < St_Stop;
;;   
;;   -- --%PROPERTY state_bounded;
;;   	
;; tel;

;; Enum datatype
(declare-datatypes () ((PFS_Logic_state A B C D)))

(declare-const St_Start_PFSL PFS_Logic_state)
(declare-const St_Inhibited PFS_Logic_state)
(declare-const St_Listening PFS_Logic_state)
(declare-const St_Pilot_Flying PFS_Logic_state)


;; Initial state of node PFS_Logic
(define-fun I_PFS_Logic 

  (

   ;; Inputs  
   (riseTS Bool)
   (riseOSPF Bool)
   (Primary_Side Bool)
   (PFS_Initial_Value Bool)

   ;; Stateful variables
   (state PFS_Logic_state)
   (inhibit_count Int)

   ;; Output   
   (PFS Bool)

   ) 

  ;; Predicate is Boolean
  Bool


  (let 

      ;; Constant declaration
      ((inhibit_count_max 2))
    
    (let 

        (

         ;; Stateless variable
         (Start_to_Pilot_Flying 
          (and (= St_Start_PFSL St_Start_PFSL) Primary_Side))
         
         ;; Stateless variable
         (Start_to_Inhibited 
          (and (= St_Start_PFSL St_Start_PFSL) (not Primary_Side)))
         
         ;; Stateless variable
         (Inhibited_to_Listening  
          (and (= St_Start_PFSL St_Inhibited) (>= 0 inhibit_count_max))))

      (let
         
          (

           ;; Stateless variable
           (Inhibited_to_Inhibited 
            (and (= St_Start_PFSL St_Inhibited) (not Inhibited_to_Listening)))
           
           ;; Stateless variable
           (Listening_to_Pilot_Flying 
            (and (= St_Start_PFSL St_Listening) riseTS))
           
           ;; Stateless variable
           (Pilot_Flying_to_Inhibited 
            (and (= St_Start_PFSL St_Pilot_Flying) riseOSPF)))

        ;; Equation of stateful variable 
        (= state 
           
           (ite 
            (or 
             Inhibited_to_Inhibited 
             Pilot_Flying_to_Inhibited 
             Start_to_Inhibited)
            St_Inhibited 
            (ite 
             Inhibited_to_Listening 
             St_Listening
             (ite
              (or 
               Listening_to_Pilot_Flying 
               Start_to_Pilot_Flying)
              St_Pilot_Flying 
              St_Start_PFSL))))
        
        ;; Equation of stateful variable 
        (= inhibit_count
           (ite
            Inhibited_to_Inhibited 
            (+ 0 1)
            (ite 
             Pilot_Flying_to_Inhibited 
             0
             (ite 
              Start_to_Inhibited 
              0
              0))))
      
      
        ;; Equation of output
        (= PFS 
           (ite
            Listening_to_Pilot_Flying 
            true
            (ite
             Pilot_Flying_to_Inhibited 
             false
             (ite
              Start_to_Pilot_Flying 
              true
              (ite
               Start_to_Inhibited 
               false
               PFS_Initial_Value)))))))))
  

;; Transition relation of node PFS_Logic
(define-fun T_PFS_Logic 
  
  (
   
   ;; Stateless inputs 
   (riseTS Bool)
   (riseOSPF Bool)
   (Primary_Side Bool)
   (PFS_Initial_Value Bool)

   ;; Stateful inputs 
   
   ;; Stateful variables 
   (state PFS_Logic_state)
   (pre_state PFS_Logic_state)
   (inhibit_count Int)
   (pre_inhibit_count Int)
   
   ;; Stateless outputs

   ;; Stateful outputs 
   (PFS Bool)
   (pre_PFS Bool)
   
   )
  
  ;; Predicate is Boolean
  Bool
  
  (let
      
       ;; Constant declaration
      ((inhibit_count_max 2))

    (let

        (

         ;; Stateless variable
         (Start_to_Pilot_Flying
          (and (= pre_state St_Start_PFSL) Primary_Side))
         
         ;; Stateless variable 
         (Start_to_Inhibited
          (and (= pre_state St_Start_PFSL) (not Primary_Side)))
       
         ;; Stateless variable 
         (Inhibited_to_Listening 
          (and
           (= pre_state St_Inhibited) 
           (>= pre_inhibit_count inhibit_count_max))))
      
      (let
          
          (
           
           ;; Stateless variable
           (Inhibited_to_Inhibited 
            (and (= pre_state St_Inhibited) (not Inhibited_to_Listening)))
           
           ;; Stateless variable 
           (Listening_to_Pilot_Flying  
            (and (= pre_state St_Listening) riseTS))
           
           ;; Stateless variable 
           (Pilot_Flying_to_Inhibited  
            (and (= pre_state St_Pilot_Flying) riseOSPF)))

        ;; Equation of stateful variable 
        (= state
           (ite 
            (or 
             Inhibited_to_Inhibited 
             Pilot_Flying_to_Inhibited 
             Start_to_Inhibited)
            St_Inhibited 
            (ite
             Inhibited_to_Listening 
             St_Listening
             (ite 
              (or Listening_to_Pilot_Flying Start_to_Pilot_Flying)
              St_Pilot_Flying 
              pre_state))))
        
        ;; Equation of stateful variable 
        (= PFS 
           (ite
            Listening_to_Pilot_Flying 
            true
            (ite
             Pilot_Flying_to_Inhibited 
             false
             (ite 
              Start_to_Pilot_Flying 
              true
              (ite
               Start_to_Inhibited 
               false
               pre_PFS)))))
        
        ;; Equation of stateful variable 
        (= inhibit_count
           (ite
            Inhibited_to_Inhibited 
            (+ pre_inhibit_count 1)
            (ite
             Pilot_Flying_to_Inhibited 
             0
             (ite
              Start_to_Inhibited 
              0
              pre_inhibit_count))))))))


;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; node PFS_Side
;;   (TS, OSPF : bool;
;;    const Primary_Side : bool; 
;;    const PFS_Initial_Value : bool)
;; 
;; returns 
;;   (PFS : bool);
;; 
;; var
;;   PFSL_PFS : bool;
;;   riseTS_O : bool;
;;   riseOSPF_O : bool;
;;   
;; let
;; 
;;   PFSL_PFS =
;;     PFS_Logic(riseTS_O, riseOSPF_O, Primary_Side, PFS_Initial_Value);
;; 
;;   riseTS_O = Rise(TS);
;; 
;;   riseOSPF_O = Rise(OSPF);
;; 
;;   PFS = PFSL_PFS;
;; 
;; tel;



;; Initial state of node PFS_Logic
(define-fun I_PFS_Side

  (

   ;; Inputs
   (TS Bool)
   (OSPF Bool)
   (Primary_Side Bool)
   (PFS_Initial_Value Bool)

   ;; Stateful variables (here: from node calls)
   (riseTS_O Bool)
   (riseOSPF_O Bool)
   (PFSL_PFS Bool)
   (PFS_Logic_0_state PFS_Logic_state)
   (PFS_Logic_0_inhibit_count Int)
   
   ;; Outputs 
   (PFS bool)

  )

  Bool

  (and 
  
   ;; Node call 
   (I_Rise TS riseTS_O)
   
   ;; Node call 
   (I_Rise OSPF riseOSPF_O)
   
   ;; Node call 
   (I_PFS_Logic 
    riseTS_O 
    riseOSPF_O 
    Primary_Side 
    PFS_Initial_Value 
    PFS_Logic_0_state 
    PFS_Logic_0_inhibit_count 
    PFSL_PFS)
   
   ;;  Equation for output 
   (= PFS PFSL_PFS))
  
)


;; Transition relation of node PFS_Side
(define-fun T_PFS_Side 
  
  (
   
   ;; Stateless inputs 
   (Primary_Side Bool)
   (PFS_Initial_Value Bool)

   ;; Stateful inputs 
   (TS Bool)
   (pre_TS Bool)
   (OSPF Bool)
   (pre_OSPF Bool)
   
   ;; Stateful variables 
   (riseTS_O Bool)
   (riseOSPF_O Bool)
   (PFSL_PFS Bool)
   (pre_PFSL_PFS Bool)
   
   ;; Stateful variables of called nodes 
   (PFS_Logic_0_state PFS_Logic_state)
   (PFS_Logic_0_pre_state PFS_Logic_state)
   (PFS_Logic_0_inhibit_count Int)
   (PFS_Logic_0_pre_inhibit_count Int)

   ;; Stateless outputs

   ;; Stateful outputs 
   (PFS Bool)
   (pre_PFS Bool)
   
   )
  
  ;; Predicate is Boolean
  Bool
 
  (and

   ;; Node call 
   (T_Rise TS pre_TS riseTS_O)
   
   ;; Node call 
   (T_Rise OSPF pre_OSPF riseOSPF_O)
   
   ;; Node call 
   (T_PFS_Logic 
    riseTS_O 
    riseOSPF_O 
    Primary_Side 
    PFS_Initial_Value 
    PFS_Logic_0_state
    PFS_Logic_0_pre_state
    PFS_Logic_0_inhibit_count
    PFS_Logic_0_pre_inhibit_count
    PFSL_PFS
    pre_PFSL_PFS)
   
   ;;  Equation for output 
   (= PFS PFSL_PFS))
  
)


;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; node Cross_Channel_Bus
;;   (I : bool;
;;    const O_Initial_Value : bool; 
;;    const prev_I_Initial_Value : bool)
;; 
;; returns
;;   (O : bool);
;; 
;; var
;;   prev_I : bool;
;;   T2 : bool;
;;   T1 : bool;
;; 
;;   state :
;;     enum { St_Step, St_Start };
;; 
;; let
;; 
;;   Start_to_Step = (St_Start -> pre(state)) = St_Start;
;; 
;;   Step_to_Step = (St_Start -> pre(state)) = St_Step;
;; 
;;   state = 
;;     if 
;;       Start_to_Step or Step_to_Step 
;;     then 
;;       St_Step 
;;     else 
;;       (St_Start -> pre(state));
;; 
;;   prev_I = 
;;     if St_Start_to_Step then I
;;     else if St_Step_to_Step then I
;;          else prev_I_Initial_Value -> pre(prev_I);
;; 
;;   O = 
;;     if 
;;       St_Start_to_Step 
;;     then 
;;       prev_I_Initial_Value -> pre(prev_I)
;;     else if 
;;       St_Step_to_Step 
;;     then 
;;       prev_I_Initial_Value -> pre(prev_I)
;;     else 
;;       O_Initial_Value -> pre(O);
;;       
;; tel;


;; Enum datatype
(declare-datatypes () ((Cross_Channel_Bus_state A B)))

(declare-const St_Start_CCB Cross_Channel_Bus_state)
(declare-const St_Step Cross_Channel_Bus_state)


;; Transition relation of node Cross_Channel_Bus
(define-fun I_Cross_Channel_Bus

  (

   ;; Inputs  
   (I Bool)
   (O_Initial_Value Bool)
   (prev_I_Initial_Value Bool)

   ;; Stateful variables
   (prev_I Bool)
   (state Cross_Channel_Bus_state)

   ;; Output   
   (O Bool)
   
   )
  
  ;; Predicate is Boolean
  Bool
 
  (let

      (

       ;; Stateless variable
       (Start_to_Step (= St_Start_CCB St_Start_CCB))
       
       ;; Stateless variable
       (Step_to_Step (= St_Start_CCB St_Step))
       
       )

    ;; Equation of stateful variable 
    (= state
       (ite 
        (or Start_to_Step Step_to_Step)
        St_Step 
        St_Start_CCB))

    ;; Equation of stateful variable 
    (= prev_I 
       (ite 
        Start_to_Step 
        I
        (ite
         Step_to_Step 
         I
         prev_I_Initial_Value)))

    ;; Equation of stateful variable 
    (= O 
       (ite 
        Start_to_Step 
        prev_I_Initial_Value
        (ite
         Step_to_Step 
         prev_I_Initial_Value
         O_Initial_Value)))))


;; Transition relation of node Cross_Channel_Bus
(define-fun T_Cross_Channel_Bus

  (

   ;; Stateless inputs 
   (I Bool)
   (O_Initial_Value Bool)
   (prev_I_Initial_Value Bool)

   ;; Stateful inputs 
   
   ;; Stateful variables 
   (prev_I Bool)
   (pre_prev_I Bool)
   (state Cross_Channel_Bus_state)
   (pre_state Cross_Channel_Bus_state)

   ;; Stateless outputs

   ;; Stateful outputs 
   (O Bool)
   (pre_O Bool)

   )

  ;; Predicate is Boolean
  Bool
 
  (let

      (

       ;; Stateless variable
       (Start_to_Step (= pre_state St_Start_CCB))

       ;; Stateless variable
       (Step_to_Step (= pre_state St_Step))

       )

    ;; Equation of stateful variable 
    (= state
       (ite 
        (or Start_to_Step Step_to_Step)
        St_Step 
        pre_state))

    ;; Equation of stateful variable 
    (= prev_I 
       (ite 
        Start_to_Step 
        I
        (ite
         Step_to_Step 
         I
         pre_prev_I)))

    ;; Equation of stateful variable 
    (= O 
       (ite 
        Start_to_Step 
        pre_prev_I
        (ite
         Step_to_Step 
         pre_prev_I
         pre_O)))))


;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; node PFS
;;   (TS, CLK1, CLK3, CLK2, CLK4 : bool) 
;; returns 
;;   (LPFS, RPFS : bool);
;; 
;; var
;;   RL_O : bool;
;;   RS_PFS : bool;
;;   LR_O : bool;
;;   LS_PFS : bool;
;; 
;; let
;; 
;;   LS_PFS = 
;;     condact(CLK1, PFS_Side(TS, RL_O, true, true), true);
;; 
;;   RS_PFS = 
;;     condact(CLK3, PFS_Side(TS, LR_O, false, false), false);
;; 
;;   LR_O = 
;;     condact(CLK2, Cross_Channel_Bus (LS_PFS, true, true), true);
;; 
;;   RL_O = 
;;     condact(CLK4, Cross_Channel_Bus (RS_PFS, false, false), false);
;; 
;;   LPFS = LS_PFS;
;; 
;;   RPFS = RS_PFS;
;;   
;; tel;

(define-fun I_PFS

  (

   ;; Inputs
   (TS Bool)
   (CLK1 Bool)
   (CLK2 Bool)
   (CLK3 Bool)
   (CLK4 Bool)
   
   ;; Stateful variables (here: from node calls)
   (RL_O Bool)
   (LR_O Bool)
   (LS_PFS Bool)
   (RS_PFS Bool)

   ;; Stateful variables from node calls
   (PFS_Side_0_riseTS_O Bool)
   (PFS_Side_0_riseOSPF_O Bool)
   (PFS_Side_0_PFSL_PFS Bool)
   (PFS_Side_0_PFS_Logic_0_state Bool)
   (PFS_Side_0_PFS_Logic_0_inhibit_count Bool)
   (PFS_Side_1_riseTS_O Bool)
   (PFS_Side_1_riseOSPF_O Bool)
   (PFS_Side_1_PFSL_PFS Bool)
   (PFS_Side_1_PFS_Logic_0_state Bool)
   (PFS_Side_1_PFS_Logic_0_inhibit_count Bool)

   (Cross_Channel_Bus_0_prev_I Bool)
   (Cross_Channel_Bus_0_state Cross_Channel_Bus_state)
   (Cross_Channel_Bus_1_prev_I Bool)
   (Cross_Channel_Bus_1_state Cross_Channel_Bus_state)

   ;; Outputs 
   (LPFS Bool)
   (RPFS Bool)

   )

  Bool

  (and
   
   ;; Condact with activation condition 
   (=> 
    CLK1 
    (I_PFS_Side 
     TS 
     RL_O 
     true 
     true 
     PFS_Side_0_riseTS_O 
     PFS_Side_0_riseOSPF_O 
     PFS_Side_0_PFSL_PFS 
     PFS_Side_0_PFS_Logic_0_state 
     PFS_Side_0_PFS_Logic_0_inhibit_count 
     LS_PFS))

   (=> (not CLK1) (= LS_PFS true))

   ;; Condact with activation condition 
   (=> 
    CLK3 
    (I_PFS_Side 
     TS 
     LR_O 
     false 
     false 
     PFS_Side_1_riseTS_O 
     PFS_Side_1_riseOSPF_O 
     PFS_Side_1_PFSL_PFS 
     PFS_Side_1_PFS_Logic_0_state 
     PFS_Side_1_PFS_Logic_0_inhibit_count 
     RS_PFS))

   (=> (not CLK3) (= RS_PFS false))

   ;; Condact with activation condition 
   (=> 
    CLK2 
    (I_Cross_Channel_Bus 
     LS_PFS 
     true 
     true 
     Cross_Channel_Bus_0_prev_I
     Cross_Channel_Bus_0_state
     LR_O))
   
   (=> (not CLK2) (= LR_O true))

   ;; Condact with activation condition 
   (=> 
    CLK4 
    (I_Cross_Channel_Bus 
     RS_PFS 
     false 
     false 
     Cross_Channel_Bus_1_prev_I
     Cross_Channel_Bus_1_state
     RL_O))

   (=> (not CLK4) (= RL_O false))

   (= LPFS LS_PFS)
   (= RPFS RS_PFS)

   )
  
)

(define-fun T_PFS

  (

   ;; Stateless inputs 
   (CLK1 Bool)
   (CLK2 Bool)
   (CLK3 Bool)
   (CLK4 Bool)

   ;; Stateful inputs
   (TS Bool)
   (pre_TS Bool)
   (RL_O Bool)
   (pre_RL_O Bool)
   (LR_O Bool)
   (pre_LR_O Bool)
   (LS_PFS Bool)
   (pre_LS_PFS Bool)
   (RS_PFS Bool)
   (pre_RS_PFS Bool)
   
   ;; Stateful variables
   (PFS_Side_0_riseTS_O Bool)
   (PFS_Side_0_riseOSPF_O Bool)
   (PFS_Side_0_PFSL_PFS Bool)
   (PFS_Side_0_pre_PFSL_PFS Bool)
   (PFS_Side_0_PFS_Logic_0_state PFS_Logic_state)
   (PFS_Side_0_PFS_Logic_0_pre_state PFS_Logic_state)
   (PFS_Side_0_PFS_Logic_0_inhibit_count Int)
   (PFS_Side_0_PFS_Logic_0_pre_inhibit_count Int)
   (PFS_Side_1_riseTS_O Bool)
   (PFS_Side_1_riseOSPF_O Bool)
   (PFS_Side_1_PFSL_PFS Bool)
   (PFS_Side_1_pre_PFSL_PFS Bool)
   (PFS_Side_1_PFS_Logic_0_state PFS_Logic_state)
   (PFS_Side_1_PFS_Logic_0_pre_state PFS_Logic_state)
   (PFS_Side_1_PFS_Logic_0_inhibit_count Int)
   (PFS_Side_1_PFS_Logic_0_pre_inhibit_count Int)
   (Cross_Channel_Bus_0_prev_I Bool)
   (Cross_Channel_Bus_0_pre_prev_I Bool)
   (Cross_Channel_Bus_0_state Cross_Channel_Bus_state)
   (Cross_Channel_Bus_0_pre_state Cross_Channel_Bus_state)
   (Cross_Channel_Bus_1_prev_I Bool)
   (Cross_Channel_Bus_1_pre_prev_I Bool)
   (Cross_Channel_Bus_1_state Cross_Channel_Bus_state)
   (Cross_Channel_Bus_1_pre_state Cross_Channel_Bus_state)
   
   ;; Stateful outputs 
   (LPFS Bool)
   (pre_LPFS Bool)
   (RPFS Bool)
   (pre_RPFS Bool)

   )

  Bool

  (and
   
   ;; Condact with activation condition 
   (=> 
    CLK1 
    (T_PFS_Side 
     true 
     true 
     TS 
     pre_TS
     RL_O 
     pre_RL_O
     PFS_Side_0_riseTS_O 
     PFS_Side_0_riseOSPF_O 
     PFS_Side_0_PFSL_PFS 
     PFS_Side_0_pre_PFSL_PFS 
     PFS_Side_0_PFS_Logic_0_state
     PFS_Side_0_PFS_Logic_0_pre_state
     PFS_Side_0_PFS_Logic_0_inhibit_count
     PFS_Side_0_PFS_Logic_0_pre_inhibit_count
     LS_PFS
     pre_LS_PFS))

   (=> (not CLK1) (= LS_PFS true))

   ;; Condact with activation condition 
   (=> 
    CLK3 
    (T_PFS_Side 
     false 
     false 
     TS 
     pre_TS 
     LR_O 
     pre_LR_O 
     PFS_Side_1_riseTS_O 
     PFS_Side_1_riseOSPF_O 
     PFS_Side_1_PFSL_PFS 
     PFS_Side_1_pre_PFSL_PFS 
     PFS_Side_1_PFS_Logic_0_state
     PFS_Side_1_PFS_Logic_0_pre_state
     PFS_Side_1_PFS_Logic_0_inhibit_count
     PFS_Side_1_PFS_Logic_0_pre_inhibit_count
     RS_PFS
     pre_RS_PFS))

   (=> (not CLK3) (= RS_PFS false))

   ;; Condact with activation condition 
   (=> 
    CLK2 
    (T_Cross_Channel_Bus 
     LS_PFS 
     true 
     true 
     Cross_Channel_Bus_0_prev_I
     Cross_Channel_Bus_0_pre_prev_I
     Cross_Channel_Bus_0_state
     Cross_Channel_Bus_0_pre_state
     LR_O
     pre_LR_O))
   
   (=> (not CLK2) (= LR_O true))

   ;; Condact with activation condition 
   (=> 
    CLK4 
    (T_Cross_Channel_Bus 
     RS_PFS 
     false 
     false 
     Cross_Channel_Bus_1_prev_I
     Cross_Channel_Bus_1_pre_prev_I
     Cross_Channel_Bus_1_state
     Cross_Channel_Bus_1_pre_state
     RL_O
     pre_RL_O))

   (=> (not CLK4) (= RL_O false))

   (= LPFS LS_PFS)
   (= RPFS RS_PFS)

   )
  
)


;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inputs 
(declare-fun CLK1 (Int) Bool)
(declare-fun CLK2 (Int) Bool)
(declare-fun CLK3 (Int) Bool)
(declare-fun CLK4 (Int) Bool)
(declare-fun TS (Int) Bool)

;; State variables
(declare-fun RL_O (Int) Bool)
(declare-fun LR_O (Int) Bool)
(declare-fun LS_PFS (Int) Bool)
(declare-fun RS_PFS (Int) Bool)
(declare-fun PFS_Side_0_riseTS_O (Int) Bool)
(declare-fun PFS_Side_0_riseOSPF_O (Int) Bool)
(declare-fun PFS_Side_0_PFSL_PFS (Int) Bool)
(declare-fun PFS_Side_0_PFS_Logic_0_state (Int) PFS_Logic_state)
(declare-fun PFS_Side_0_PFS_Logic_0_inhibit_count (Int) Int)
(declare-fun PFS_Side_1_riseTS_O (Int) Bool)
(declare-fun PFS_Side_1_riseOSPF_O (Int) Bool)
(declare-fun PFS_Side_1_PFSL_PFS (Int) Bool)
(declare-fun PFS_Side_1_PFS_Logic_0_state (Int) PFS_Logic_state)
(declare-fun PFS_Side_1_PFS_Logic_0_inhibit_count (Int) Int)
(declare-fun Cross_Channel_Bus_0_prev_I (Int) Bool)
(declare-fun Cross_Channel_Bus_0_state (Int) Cross_Channel_Bus_state)
(declare-fun Cross_Channel_Bus_1_prev_I (Int) Bool)
(declare-fun Cross_Channel_Bus_1_state (Int) Cross_Channel_Bus_state)

;; Outputs 
(declare-fun LPFS (Int) Bool)
(declare-fun RPFS (Int) Bool)
   
;; Initial state
(define-fun I ((s Int)) Bool
  (I_PFS
   (TS s)
   (CLK1 s)
   (CLK2 s)
   (CLK3 s)
   (CLK4 s)
   (RL_O s)
   (LR_O s)
   (LS_PFS s)
   (RS_PFS s)
   (PFS_Side_0_riseTS_O s)
   (PFS_Side_0_riseOSPF_O s)
   (PFS_Side_0_PFSL_PFS s)
   (PFS_Side_0_PFS_Logic_0_state s)
   (PFS_Side_0_PFS_Logic_0_inhibit_count s)
   (PFS_Side_1_riseTS_O s)
   (PFS_Side_1_riseOSPF_O s)
   (PFS_Side_1_PFSL_PFS s)
   (PFS_Side_1_PFS_Logic_0_state s)
   (PFS_Side_1_PFS_Logic_0_inhibit_count s)
   (Cross_Channel_Bus_0_prev_I s)
   (Cross_Channel_Bus_0_state s)
   (Cross_Channel_Bus_1_prev_I s)
   (Cross_Channel_Bus_1_state s)
   (LPFS s)
   (RPFS s)))

;; Transition relation
(define-fun T ((s Int) (t Int)) Bool
  (T_PFS
   (CLK1 s)
   (CLK2 s)
   (CLK3 s)
   (CLK4 s)
   (TS s)
   (TS t)
   (RL_O s)
   (RL_O t)
   (LR_O s)
   (LR_O t)
   (LS_PFS s)
   (LS_PFS t)
   (RS_PFS s)
   (RS_PFS t)
   (PFS_Side_0_riseTS_O s)
   (PFS_Side_0_riseOSPF_O s)
   (PFS_Side_0_PFSL_PFS s)
   (PFS_Side_0_PFSL_PFS t)
   (PFS_Side_0_PFS_Logic_0_state s)
   (PFS_Side_0_PFS_Logic_0_state t)
   (PFS_Side_0_PFS_Logic_0_inhibit_count s)
   (PFS_Side_0_PFS_Logic_0_inhibit_count t)
   (PFS_Side_1_riseTS_O s)
   (PFS_Side_1_riseOSPF_O s)
   (PFS_Side_1_PFSL_PFS s)
   (PFS_Side_1_PFSL_PFS t)
   (PFS_Side_1_PFS_Logic_0_state s)
   (PFS_Side_1_PFS_Logic_0_state t)
   (PFS_Side_1_PFS_Logic_0_inhibit_count s)
   (PFS_Side_1_PFS_Logic_0_inhibit_count t)
   (Cross_Channel_Bus_0_prev_I s)
   (Cross_Channel_Bus_0_prev_I t)
   (Cross_Channel_Bus_0_state s)
   (Cross_Channel_Bus_0_state t)
   (Cross_Channel_Bus_1_prev_I s)
   (Cross_Channel_Bus_1_prev_I t)
   (Cross_Channel_Bus_1_state s)
   (Cross_Channel_Bus_1_state t)
   (LPFS s)
   (LPFS t)
   (RPFS s)
   (RPFS t)))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert (I 0))
(assert (T 0 1))
(assert (T 2 3))
(assert (T 3 4))

(check-sat)

(get-value
 ((TS 0)
  (CLK1 0)
  (CLK2 0)
  (CLK3 0)
  (CLK4 0)
  (RL_O 0)
  (LR_O 0)
  (LS_PFS 0)
  (RS_PFS 0)
  (PFS_Side_0_riseTS_O 0)
  (PFS_Side_0_riseOSPF_O 0)
  (PFS_Side_0_PFSL_PFS 0)
  (PFS_Side_0_PFS_Logic_0_state 0)
  (PFS_Side_0_PFS_Logic_0_inhibit_count 0)
  (PFS_Side_1_riseTS_O 0)
  (PFS_Side_1_riseOSPF_O 0)
  (PFS_Side_1_PFSL_PFS 0)
  (PFS_Side_1_PFS_Logic_0_state 0)
  (PFS_Side_1_PFS_Logic_0_inhibit_count 0)
  (Cross_Channel_Bus_0_prev_I 0)
  (Cross_Channel_Bus_0_state 0)
  (Cross_Channel_Bus_1_prev_I 0)
  (Cross_Channel_Bus_1_state 0)
  (LPFS 0)
  (RPFS 0)))

(get-value
 ((TS 1)
  (CLK1 1)
  (CLK2 1)
  (CLK3 1)
  (CLK4 1)
  (RL_O 1)
  (LR_O 1)
  (LS_PFS 1)
  (RS_PFS 1)
  (PFS_Side_0_riseTS_O 1)
  (PFS_Side_0_riseOSPF_O 1)
  (PFS_Side_0_PFSL_PFS 1)
  (PFS_Side_0_PFS_Logic_0_state 1)
  (PFS_Side_0_PFS_Logic_0_inhibit_count 1)
  (PFS_Side_1_riseTS_O 1)
  (PFS_Side_1_riseOSPF_O 1)
  (PFS_Side_1_PFSL_PFS 1)
  (PFS_Side_1_PFS_Logic_0_state 1)
  (PFS_Side_1_PFS_Logic_0_inhibit_count 1)
  (Cross_Channel_Bus_0_prev_I 1)
  (Cross_Channel_Bus_0_state 1)
  (Cross_Channel_Bus_1_prev_I 1)
  (Cross_Channel_Bus_1_state 1)
  (LPFS 1)
  (RPFS 1)))

(get-value
 ((TS 2)
  (CLK1 2)
  (CLK2 2)
  (CLK3 2)
  (CLK4 2)
  (RL_O 2)
  (LR_O 2)
  (LS_PFS 2)
  (RS_PFS 2)
  (PFS_Side_0_riseTS_O 2)
  (PFS_Side_0_riseOSPF_O 2)
  (PFS_Side_0_PFSL_PFS 2)
  (PFS_Side_0_PFS_Logic_0_state 2)
  (PFS_Side_0_PFS_Logic_0_inhibit_count 2)
  (PFS_Side_1_riseTS_O 2)
  (PFS_Side_1_riseOSPF_O 2)
  (PFS_Side_1_PFSL_PFS 2)
  (PFS_Side_1_PFS_Logic_0_state 2)
  (PFS_Side_1_PFS_Logic_0_inhibit_count 2)
  (Cross_Channel_Bus_0_prev_I 2)
  (Cross_Channel_Bus_0_state 2)
  (Cross_Channel_Bus_1_prev_I 2)
  (Cross_Channel_Bus_1_state 2)
  (LPFS 2)
  (RPFS 2)))

(get-value
 ((TS 3)
  (CLK1 3)
  (CLK2 3)
  (CLK3 3)
  (CLK4 3)
  (RL_O 3)
  (LR_O 3)
  (LS_PFS 3)
  (RS_PFS 3)
  (PFS_Side_0_riseTS_O 3)
  (PFS_Side_0_riseOSPF_O 3)
  (PFS_Side_0_PFSL_PFS 3)
  (PFS_Side_0_PFS_Logic_0_state 3)
  (PFS_Side_0_PFS_Logic_0_inhibit_count 3)
  (PFS_Side_1_riseTS_O 3)
  (PFS_Side_1_riseOSPF_O 3)
  (PFS_Side_1_PFSL_PFS 3)
  (PFS_Side_1_PFS_Logic_0_state 3)
  (PFS_Side_1_PFS_Logic_0_inhibit_count 3)
  (Cross_Channel_Bus_0_prev_I 3)
  (Cross_Channel_Bus_0_state 3)
  (Cross_Channel_Bus_1_prev_I 3)
  (Cross_Channel_Bus_1_state 3)
  (LPFS 3)
  (RPFS 3)))
