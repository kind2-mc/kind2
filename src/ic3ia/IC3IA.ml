(* This file is part of the Kind 2 model checker.

   Copyright (c) 2022 by the Board of Trustees of the University of Iowa

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

open Lib

module TS = Term.TermSet
module CS = Cube.CubeSet
module CM = Cube.CubeMap

let base_offset = Numeral.zero
let base_abstr_offset = Numeral.one
let prime_abstr_offset = Numeral.succ base_abstr_offset
let prime_offset = Numeral.of_int 3
let max_offset = prime_abstr_offset

(* Interpolation instance if created *)
let ref_interpolator = ref None

let max_unrolling = ref 0

let added_logic = ref None

let init_svar () =
  StateVar.mk_state_var
    ~is_input:false
    ~is_const:false
    ~for_inv_gen:false
    "%init"
    []
    Type.t_bool

let get_init offset =
  Var.mk_state_var_instance (init_svar ()) offset
  |> Term.mk_var

let rec declare_init_var declare lbound ubound =
  if Numeral.(lbound <= ubound) then
    let var = Var.mk_state_var_instance (init_svar ()) lbound in
    declare (Var.unrolled_uf_of_state_var_instance var) ;
    declare_init_var declare (Numeral.succ lbound) ubound

let on_exit _ =
  max_unrolling := 0 ;
  match !ref_interpolator with
  | None -> ()
  | Some s -> SMTSolver.delete_instance s

(* Counterexample trace for some property *)
exception Counterexample of Model.path

type solving_options =
  | Default
  | ExtractModel
  | NoInd

exception Terminate

let handle_events in_sys param sys prop_name =
  (* Receive queued messages 
     Side effect: Terminate when ControlMessage TERM is received.*)
  let messages = KEvent.recv () in

  (* Update transition system from messages *)
  let _ = 
    KEvent.update_trans_sys in_sys param sys messages 
  in

  match TransSys.get_prop_status sys prop_name with
  | Property.PropFalse _
  | Property.PropInvariant _ -> raise Terminate
  | _ -> ()

let sys_def solver sys offset =
  let init_term_curr =
    get_init offset
  in
  let init_term_prev =
    get_init (Numeral.pred offset)
  in
  let init =
    Term.mk_and
      [TransSys.init_of_bound
        (Some (SMTSolver.declare_fun solver))
        sys
        offset;
        Term.mk_not init_term_curr;
        init_term_prev
      ]
   in
   let trans =
    Term.mk_and
      [TransSys.trans_of_bound
        (Some (SMTSolver.declare_fun solver))
        sys
        offset;
        Term.mk_not init_term_curr;
        Term.mk_not init_term_prev
      ]
   in
   Term.mk_or [init; trans]

let sys_def_unrolling solver sys offset =
  let init_term_curr =
    get_init offset
  in
  if Numeral.(equal offset zero) then
    Term.mk_and
      [TransSys.init_of_bound
        (Some (SMTSolver.declare_fun solver))
        sys
        offset;
        Term.mk_not init_term_curr
      ]
  else
    Term.mk_and
      [TransSys.trans_of_bound
        (Some (SMTSolver.declare_fun solver))
        sys
        offset;
        Term.mk_not init_term_curr
      ]

let get_logic sys =
  added_logic := None;
  match Flags.Smt.itp_solver () with
  | `MathSAT_SMTLIB -> (
    let open TermLib in
    let open TermLib.FeatureSet in
    match TransSys.get_logic sys with
    (* The interpolants MathSAT computes in QF_LIA / QF_LRA can use the floor function
       (implemented using to_real/to_int in SMT-LIB 2)
    *)
    | `Inferred l when mem IA l && not (mem RA l) ->
      added_logic := Some RA; `Inferred (FeatureSet.add RA l)
    | `Inferred l when mem RA l && not (mem IA l) ->
      added_logic := Some IA; `Inferred (FeatureSet.add IA l)
    | l -> l
  )
  | _ -> TransSys.get_logic sys

let mk_solver sys =
   let solver =
     SMTSolver.create_instance
       ~produce_models:true
       ~produce_unsat_cores:true
       (get_logic sys)
       (Flags.Smt.solver ())
   in

   TransSys.define_and_declare_of_bounds
     sys
     (SMTSolver.define_fun solver)
     (SMTSolver.declare_fun solver)
     (SMTSolver.declare_sort solver)
     (SMTSolver.assert_expr solver)
     (Numeral.zero)
     (Numeral.succ max_offset) ;

   declare_init_var
     (SMTSolver.declare_fun solver)
     (Numeral.zero)
     (Numeral.succ max_offset) ;

   SMTSolver.assert_term solver 
     (sys_def solver sys prime_abstr_offset) ;

   solver


let depth frames = List.length frames - 2

let get_R frames k =
  list_suffix frames k
  |> List.map (fun f -> Frame.to_term f)
  |> Term.mk_and
  
let check_sat solver predicates term =
  SMTSolver.push solver ;
  SMTSolver.assert_term solver term ;
  let res =
    SMTSolver.check_sat_and_get_term_values
      solver
      (fun _ predicate_evaluations -> (* If sat. *)
        Some predicate_evaluations
      )
      (fun _ -> None) (* If unsat. *)
      (TS.elements predicates)
  in
  SMTSolver.pop solver ; res

let extract_cube predicates predicate_evaluations =
  let eval p =
    let is_true =
      match List.assoc_opt p predicate_evaluations with
      | Some v -> assert (Term.is_bool v); v = Term.t_true
      | None -> assert false
    in
    if is_true then p else Term.negate p
  in
  let cube =
    List.fold_left
      (fun c p -> Cube.add (eval p) c)
      Cube.empty
      (TS.elements predicates)
  in
  cube


let get_bad_cube solver predicates frames prop =
  let r_and_not_p =
    Term.mk_and [get_R frames (depth frames); Term.mk_not prop]
  in
  match check_sat solver predicates r_and_not_p with
  | Some predicate_evaluations -> (
    Some (extract_cube predicates predicate_evaluations)
  )
  | None -> None


let get_cubes next_cube init_c =
  let rec loop acc c =
    match CM.find_opt c next_cube with
    | None -> acc
    | Some n -> loop (n :: acc) n
  in
  loop [init_c] init_c |> List.rev


let add_predicates solver old_predicates new_predicates =
  let new_predicates =
    TS.diff new_predicates old_predicates
  in
  TS.iter
  (fun p ->
     SMTSolver.trace_comment solver
       (Format.asprintf "New predicate: %a" Term.pp_print_term p) ;

     SMTSolver.assert_term
       solver
       (Term.mk_eq
          [Term.bump_state base_offset p;
           Term.bump_state base_abstr_offset p]);

     SMTSolver.assert_term
       solver
       (Term.mk_eq
          [Term.bump_state prime_abstr_offset p;
           Term.bump_state prime_offset p]);
  )
  new_predicates ;
  TS.union old_predicates new_predicates

(* Interpolation Group ids for MathSAT *)
let ig_newid =
  let r = ref 0 in
  fun () -> incr r; Format.sprintf "g%d" !r

let refine fwd solver sys predicates cubes =

  let len = List.length cubes in

  let intrpo =
    match !ref_interpolator with
      | Some s ->
        
        if len > !max_unrolling then (
          
          TransSys.declare_vars_of_bounds
            sys
            (SMTSolver.declare_fun s)
            (Numeral.of_int (!max_unrolling + 1))
            (Numeral.of_int len);

          declare_init_var
            (SMTSolver.declare_fun s)
            (Numeral.of_int (!max_unrolling + 1))
            (Numeral.of_int len);

          max_unrolling := len;
        );
        s

      | None ->

        let produce_interpolants, logic =
          match Flags.Smt.itp_solver () with
          | `cvc5_QE
          | `Z3_QE -> (
            Flags.Smt.set_z3_qe_light true ;
            false, TermLib.add_quantifiers (TransSys.get_logic sys)
          )
          | _ -> (
            true, get_logic sys
          )
        in

        let solver = 
          SMTSolver.create_instance
            ~produce_models:true
            ~produce_interpolants
            logic
            (Flags.Smt.get_itp_solver ())
        in

        TransSys.define_and_declare_of_bounds
          sys
          (SMTSolver.define_fun solver)
          (SMTSolver.declare_fun solver)
          (SMTSolver.declare_sort solver)
          (SMTSolver.assert_expr solver)
          (Numeral.(pred zero))
          (Numeral.of_int len);

        declare_init_var
          (SMTSolver.declare_fun solver)
          (Numeral.(pred zero))
          (Numeral.of_int len);

        ref_interpolator := Some solver;
        max_unrolling := len;
        solver

  in

  let interpolizers =
    cubes
    |> List.mapi (fun i c ->
      let cube = Cube.to_term c |> Term.bump_state (Numeral.of_int (i - 1)) in
      if i < (len - 1) then
        Term.mk_and
          [ cube; sys_def_unrolling intrpo sys (Numeral.of_int i) ]
      else
        cube
      (* If prop is not in the set of initial predicates: *)
      (*Term.mk_and
        [ Cube.to_term c |> Term.bump_state (Numeral.of_int (i - 1));
          if i < (len - 1) then
            sys_def_unrolling intrpo sys (Numeral.of_int i)
          else
            Term.mk_not (prop |> Term.bump_state (Numeral.of_int (i - 1)))
        ]*)
    )
  in

  SMTSolver.push intrpo;  

  (* Compute the interpolants *)
  let names =
    match Flags.Smt.itp_solver () with
    | `MathSAT_SMTLIB -> (
      List.map
        (fun t ->
          let id = ig_newid () in
          SMTSolver.assert_term intrpo (Term.set_inter_group t id) ;
          SMTExpr.ArgString id
        )
        interpolizers
    )
    | `OpenSMT_SMTLIB
    | `SMTInterpol_SMTLIB -> (
      List.map
        (fun t ->
        SMTExpr.ArgString
          (SMTSolver.assert_named_term_wr
              intrpo
              t))
      interpolizers
    )
    | `cvc5_QE
    | `Z3_QE -> (
      List.iter (fun i -> SMTSolver.assert_term intrpo i) interpolizers ;
      []
    )
    | _ -> failwith ("Interpolating solver not found or unsupported")
  in

  if SMTSolver.check_sat 
      intrpo
  then (
    let cex_path =
      Model.path_from_model
        (TransSys.state_vars sys)
        (SMTSolver.get_model intrpo)
        (Numeral.of_int (len - 2))
    in

    raise (Counterexample cex_path)
  )
  else (
    
    let interpolants =
      match Flags.Smt.itp_solver () with
      | `cvc5_QE
      | `Z3_QE -> (
        SMTSolver.pop intrpo;
        SMTSolver.get_qe_interpolants fwd intrpo interpolizers
      )
      | _ -> (
        SMTSolver.get_interpolants intrpo names
        |> (fun itps -> SMTSolver.pop intrpo; itps)
      )
    in

    (*interpolants
    |> List.iteri (fun i t -> Format.printf "INTERPOLANT%d: %a@." i Term.pp_print_term t);*)

    let atoms =
      List.mapi
        (fun i t -> Term.bump_state (Numeral.of_int (~-(i))) t)
        interpolants
      |>
      List.filter
        (fun t -> not (t == Term.t_false || t == Term.t_true))
      |>
      List.fold_left
        (fun acc interp -> Term.TermSet.union (Term.get_atoms interp) acc)
        Term.TermSet.empty
    in

    (*atoms
    |> Term.TermSet.elements
    |> List.iteri (fun i t -> Format.printf "ATOM%d: %a@." i Term.pp_print_term t);*)

    add_predicates solver predicates atoms
  )


let is_blocked solver frames s =
  (* Check syntactic subsumption (faster than SAT): *) 
  let blocked =
    list_suffix frames (TCube.frame_index s)
    |> List.exists (fun f ->
      Frame.cubes f
      |> CS.elements
      |> List.exists (fun c -> Cube.subsumes c (TCube.cube s))
    )
  in
  if blocked then
    true
  else (
    (* Semantic subsumption thru SAT: *)
    let query =
      Term.mk_and
        [TCube.cube s |> Cube.to_term;
         get_R frames (TCube.frame_index s)]
    in
    match check_sat solver TS.empty query with
    | None -> true
    | _ -> false
  )

let is_initial init c =
  not (Cube.contains (Term.mk_not init) c)


let get_minimum_f f_names unsat_core =
  match List.find_opt (fun (_, f) -> TS.mem f unsat_core) f_names with
  | None -> TCube.FrameInf
  | Some (i, _) -> TCube.Frame i


let get_minimal_non_initial_cube init p_names unsat_core =
  let cube =
    List.fold_left
      (fun c (l, l') ->
        if TS.mem l' unsat_core then Cube.add l c else c
      )
      Cube.empty
      p_names
  in
  if is_initial init cube then
    Cube.add (Term.mk_not init) cube
  else
    cube

let solve_relative solver predicates frames s option =

  let cube = TCube.cube s in

  SMTSolver.push solver ;

  if option <> NoInd then (
    let not_cube = Term.negate (Cube.to_term cube) in
    SMTSolver.assert_term solver not_cube
  ) ;

  let k = 
    match TCube.frame s with
    | TCube.Frame i -> i - 1
    | TCube.FrameInf -> (List.length frames) - 1
    | TCube.FrameNull -> assert false
  in

  let named_frames, last_frame  =
    let named_frames = list_suffix frames k in
    named_frames,
    List.rev named_frames |> List.hd
  in

  let f_names =
    List.mapi
      (fun i f ->
        let t = Frame.to_term f in
        SMTSolver.assert_named_term_wr solver t |> ignore ;
        (k+i, t)
      )
      named_frames
  in
  SMTSolver.assert_term solver (Frame.to_term last_frame) ;

  let p_literals = Cube.literals cube in

  let p_names =
    List.map
      (fun l ->
        let l' =
          Term.bump_state Numeral.(prime_offset - base_offset) l
        in
        SMTSolver.assert_named_term_wr solver l' |> ignore ;
        l, l'
      )
      p_literals
  in

  let res =
    SMTSolver.check_sat_and_get_term_values
      solver
      (fun _ predicate_evaluations ->
        Some predicate_evaluations
      )
      (fun _ -> None )
      (TS.elements predicates)
  in

  match res with
  | Some predicate_evaluations -> (
    let c =
      match option with
      | ExtractModel ->
         extract_cube predicates predicate_evaluations
      | _ -> Cube.empty
    in
    SMTSolver.pop solver ;
    TCube.mk c TCube.FrameNull
  )
  | None -> (
    let unsat_core =
      SMTSolver.get_unsat_core_of_names solver |> TS.of_list
    in
    SMTSolver.pop solver ;

    let min_frame = get_minimum_f f_names unsat_core in
    let min_cube =
      let init = get_init base_offset in
      get_minimal_non_initial_cube init p_names unsat_core
    in
    let frame =
      match min_frame with
      | TCube.FrameInf -> min_frame
      | TCube.Frame i when i = depth frames -> min_frame
      | TCube.Frame i -> TCube.Frame (i+1)
      | TCube.FrameNull -> assert false
    in
    TCube.mk min_cube frame
  )

let generalize solver init predicates frames s =
  let c = TCube.cube s in
  let f = TCube.frame s in

  let c' =
    List.fold_left
      (fun c l ->
        let c' = Cube.remove l c in

        if (is_initial init c') then
          c
        else (
          let s' = TCube.mk c' f in
          let z =
            solve_relative solver predicates frames s' Default
          in
          match TCube.frame z with
          | TCube.FrameNull -> c
          | _ -> c'
        )
      )
      c
      (Cube.literals c)
  in
  TCube.mk c' f


let get_invariant init c =
  List.fold_left
    (fun disj l ->
      if not (l == (Term.mk_not init)) then
        Term.negate l :: disj
      else
        disj
    )
    []
    (Cube.literals c)
  |> Term.mk_or

let report_invariant sys inv =
  let broadcast_inv =
    match !added_logic with
    | None -> true
    | Some f -> (
      let inv_logic = TermLib.logic_of_term [] inv in
      not (TermLib.FeatureSet.mem f inv_logic)
    )
  in
  (* Only report an invariant if the term belongs to
     the logic of the original system *)
  if broadcast_inv then
    let cert = (1, inv) in
    KEvent.invariant
      (TransSys.scope_of_trans_sys sys) inv cert false

let add_blocked_cube solver sys init frames s =
  let k =
    match TCube.frame s with
    | Frame f -> min f (depth frames + 1)
    | FrameInf -> depth frames + 1
    | _ -> assert false
  in

  let s_cube = TCube.cube s in

  let frames1, frames2 = list_split (k+1) frames in

  let frames1' =
    List.hd frames1
    ::
    (List.tl frames1
    |> List.map (fun f ->
      match f with
      | Frame.Fi cubes -> (
        let cubes' =
          CS.elements cubes
          |> List.fold_left
              (fun acc c ->
                if (Cube.subsumes s_cube c)
                then CS.remove c acc
                else acc
              )
              cubes
        in
        Frame.Fi cubes'
      )
      | _ -> assert false
    ))
  in

  (* Store clause *)
  let frames =
    (list_apply_at
      (function
        | Frame.Fi cubes -> Frame.Fi (CS.add s_cube cubes)
        | _ -> assert false
      )
      k
      frames1')
    @ frames2
  in

  SMTSolver.trace_comment solver
    (Format.asprintf "Blocked [%d] : %a" k Cube.pp_print_cube s_cube) ;

  (* Report if invariant *)
  if TCube.frame s = TCube.FrameInf then (
    let inv = get_invariant init (TCube.cube s) in
    report_invariant sys inv
  ) ;
  
  frames


let block_cube fwd solver in_sys param sys prop_name predicates next_cube frames s0 =

  let init = get_init base_offset in

  let insert q c =
    PriorityQueue.(insert q (TCube.frame_index c) c)
  in

  let rec loop predicates next_cube frames q =
    match PriorityQueue.extract q with
    | None -> predicates, next_cube, frames
    | Some (_, s, q) -> (

      handle_events in_sys param sys prop_name ;

      match TCube.frame s with
      | Frame 0 -> (
        let predicates =
          get_cubes next_cube (TCube.cube s)
          |> refine fwd solver sys predicates
        in
        SMTSolver.trace_comment solver "Refined abstraction" ;
        predicates, next_cube, frames
      )
      | _ -> (
        let next_cube, frames, q =
          if not (is_blocked solver frames s) then (
            assert (not (is_initial init (TCube.cube s))) ;
            let z =
              solve_relative solver predicates frames s ExtractModel
            in

            match TCube.frame z with
            | TCube.FrameNull -> (
              (* Cube 's' was not blocked by image of predecessor *)
              let frame =
                match TCube.frame s with
                | Frame i -> TCube.Frame (i-1)
                | _ -> assert false
              in
              let c = TCube.cube z in
              let z = TCube.mk c frame in
              let next_cube = CM.add c (TCube.cube s) next_cube in
              let q = insert (insert q z) s in
              next_cube, frames, q
            )
            | _ -> (
              (* Cube 's' was blocked by image of predecessor *)
              let z =
                generalize solver init predicates frames z
              in
              (* Push z as far forward as possible *)
              let rec push_forward z' =
                match TCube.frame z' with
                | Frame f when f < (depth frames) - 1 -> (
                  let nz =
                    let nxt = TCube.next z' in
                    solve_relative solver predicates frames nxt Default
                  in
                  match TCube.frame nz with
                  | FrameNull -> z'
                  | _ -> push_forward nz
                )
                | _ -> z'
              in
              let z = push_forward z in
              let frames = add_blocked_cube solver sys init frames z in
              let q =
                if (TCube.frame_index s < (depth frames) &&
                    TCube.frame z <> TCube.FrameInf)
                then (
                  insert q (TCube.next s)
                )
                else q
              in
              next_cube, frames, q
            )
          )
          else (
            next_cube, frames, q
          )
        in
        loop predicates next_cube frames q
      )
    )
  in

  let q = insert PriorityQueue.empty s0 in

  loop predicates next_cube frames q


let add_frame f frames =
  Lib.list_insert_at f (List.length frames - 1) frames


let get_invariants init frames k =
  List.fold_left
    (fun invs f ->
      CS.fold
        (fun c invs -> get_invariant init c :: invs)
        (Frame.cubes f)
        invs
    )
    []
    (list_suffix frames k)

let propogate_blocked_cubes solver in_sys param sys prop_name predicates frames =
  let init = get_init base_offset in
  let rec loop frames k =
    if k < depth frames then (
      let frames =
        CS.fold
          (fun c frames' ->
            handle_events in_sys param sys prop_name ;
            let s =
              let tc = TCube.mk c (Frame (k+1)) in
              solve_relative solver predicates frames' tc NoInd
            in
            if TCube.frame s <> TCube.FrameNull then
              add_blocked_cube solver sys init frames s
            else
              frames'
          )
          (List.nth frames k |> Frame.cubes)
          frames
      in
      if List.nth frames k |> Frame.is_empty then (
        Some (get_invariants init frames (k+1)), frames
      )
      else (
        loop frames (k+1)
      )
    )
    else (
      None, frames
    )
  in
  loop frames 1


let main fwd prop in_sys param sys =
   
   let solver = mk_solver sys in

   let prop_name = prop.Property.prop_name in

   let init = get_init base_offset in

   let prop = Term.mk_or [prop.Property.prop_term; init] in

   let predicates =
     add_predicates solver TS.empty
       (Term.get_atoms prop |> TS.add init)
   in

   SMTSolver.trace_comment solver
     (Format.sprintf "Checking property: %s" prop_name);

   let frames =
     Frame.mk_frame init :: [Frame.empty]
   in

   let next_cube = CM.empty in

   try (

    let rec loop predicates next_cube frames =
      match get_bad_cube solver predicates frames prop with
      | Some cube -> (
        let s =
          TCube.mk cube (TCube.Frame (depth frames))
        in
        let predicates, next_cube, frames =
          block_cube fwd solver in_sys param sys prop_name predicates next_cube frames s
        in
        loop predicates next_cube frames
      )
      | None -> (
        let frames = add_frame Frame.empty frames in

        Debug.ic3 "Number of frames: %d" (List.length frames);
        
        SMTSolver.trace_comment solver
          (Format.sprintf "Number of frames: %d" (List.length frames)) ;

        match propogate_blocked_cubes solver in_sys param sys prop_name predicates frames with
        | None, frames -> loop predicates next_cube frames
        | Some invariants, _ -> invariants
      )
    in

    let invariants = loop predicates next_cube frames in
    
    invariants
    |> List.iter (fun i -> report_invariant sys i) ;

    let cert = 1, Term.mk_and invariants in

    KEvent.prop_status
      (Property.PropInvariant cert)
      in_sys
      param
      sys
      prop_name
   )
   with
   | Counterexample cex_path -> (

    KEvent.prop_status 
      (Property.PropFalse (Model.path_to_list cex_path))
      in_sys
      param 
      sys 
      prop_name;

    KEvent.log
      L_info 
      "Property %s disproved by IC3IA"
      prop_name
   ) 
   
  | Terminate -> ();

   SMTSolver.delete_instance solver
