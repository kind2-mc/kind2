(* This file is part of the Kind 2 model checker.

   Copyright (c) 2020 by the Board of Trustees of the University of Iowa

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

(** Testing lustre frontend expected error paths
   
   @author Andrew Marmaduke *)

open OUnit2

let load_file file = LustreInput.of_file ?old_frontend:(Some false) true file

let mk_test label fn = label >:: (fun _ -> assert_bool "expected error" (fn ()))

(* *************************************************************************** *)
(*                           Lustre Parser Checks                              *)
(* *************************************************************************** *)
let _ = run_test_tt_main ("frontend LustreParser error tests" >::: [
  mk_test "test imported function without body" (fun () ->
    match load_file "./lustreParser/imported_fun_no_body.lus" with
    | Error (`LustreParserError  _) -> true
    | _ -> false);
  mk_test "test imported node without body" (fun () ->
    match load_file "./lustreParser/imported_node_no_body.lus" with
    | Error (`LustreParserError  _) -> true
    | _ -> false);
  mk_test "test mode reqs by idents no self ref" (fun () ->
    match load_file "./lustreParser/mode_reqs_by_idents_no_self_ref.lus" with
    | Error (`LustreParserError  _) -> true
    | _ -> false);
])

(* *************************************************************************** *)
(*                   Lustre Ast Inline Constants Checks                        *)
(* *************************************************************************** *)
let _ = run_test_tt_main ("frontend LustreAstInlineConstants error tests" >::: [
  mk_test "test access out of bounds" (fun () ->
    match load_file "./lustreAstInlineConstants/test_access_out_of_bounds.lus" with
    | Error (`LustreAstInlineConstantsError  (_, OutOfBounds _)) -> true
    | _ -> false);
])

(* *************************************************************************** *)
(*                           Lustre Syntax Checks                              *)
(* *************************************************************************** *)
let _ = run_test_tt_main ("frontend LustreSyntaxChecks error tests" >::: [
  mk_test "test undefined local" (fun () ->
    match load_file "./lustreSyntaxChecks/undefined_local.lus" with
    | Error (`LustreSyntaxChecksError (_, UndefinedLocal _)) -> true
    | _ -> false);
  mk_test "test unsupported when expr" (fun () ->
    match load_file "./lustreSyntaxChecks/unsupported_when.lus" with
    | Error (`LustreSyntaxChecksError (_, UnsupportedWhen _)) -> true
    | _ -> false);
  mk_test "test temporal op in const" (fun () ->
    match load_file "./lustreSyntaxChecks/const_not_const.lus" with
    | Error (`LustreSyntaxChecksError (_, IllegalTemporalOperator _)) -> true
    | _ -> false);
  mk_test "test temporal op in ghost const" (fun () ->
    match load_file "./lustreSyntaxChecks/ghost_const_not_const.lus" with
    | Error (`LustreSyntaxChecksError (_, IllegalTemporalOperator _)) -> true
    | _ -> false);
  mk_test "test undefined node" (fun () ->
    match load_file "./lustreSyntaxChecks/dangling_call_in_ghost_var.lus" with
    | Error (`LustreSyntaxChecksError (_, UndefinedNode _)) -> true
    | _ -> false);
  mk_test "test undefined contract" (fun () ->
    match load_file "./lustreSyntaxChecks/dangling_contract_call.lus" with
    | Error (`LustreSyntaxChecksError (_, UndefinedContract _)) -> true
    | _ -> false);
  mk_test "test unknown contract call input" (fun () ->
    match load_file "./lustreSyntaxChecks/unknown_contract_call_input.lus" with
    | Error (`LustreSyntaxChecksError (_, DanglingIdentifier _)) -> true
    | _ -> false);
  mk_test "test unknown contract call output" (fun () ->
    match load_file "./lustreSyntaxChecks/unknown_contract_call_output.lus" with
    | Error (`LustreSyntaxChecksError (_, DanglingIdentifier _)) -> true
    | _ -> false);
  mk_test "test undeclared lhs" (fun () ->
    match load_file "./lustreSyntaxChecks/undeclared_lhs.lus" with
    | Error (`LustreSyntaxChecksError (_, DanglingIdentifier _)) -> true
    | _ -> false);
  mk_test "test inlined contract 2" (fun () ->
    match load_file "./lustreTypeChecker/inlined_contract_02.lus" with
    | Error (`LustreSyntaxChecksError (_, DanglingIdentifier _)) -> true
    | _ -> false);
  mk_test "test function with arrow in body" (fun () ->
    match load_file "./lustreSyntaxChecks/function_no_arrow_in_body.lus" with
    | Error (`LustreSyntaxChecksError (_, IllegalTemporalOperator _)) -> true
    | _ -> false);
  mk_test "test function with node call in body" (fun () ->
    match load_file "./lustreSyntaxChecks/function_no_node_call.lus" with
    | Error (`LustreSyntaxChecksError (_, NodeCallInFunction _)) -> true
    | _ -> false);
  mk_test "test function with pre in body" (fun () ->
    match load_file "./lustreSyntaxChecks/function_no_pre_in_body.lus" with
    | Error (`LustreSyntaxChecksError (_, IllegalTemporalOperator _)) -> true
    | _ -> false);
  mk_test "test function contract with stateful import 1" (fun () ->
    match load_file "./lustreSyntaxChecks/function_stateful_contract_import.lus" with
    | Error (`LustreSyntaxChecksError (_, IllegalImportOfStatefulContract _)) -> true
    | _ -> false);
  mk_test "test function contract with stateful import 2" (fun () ->
    match load_file "./lustreSyntaxChecks/function_stateful_contract_import_2.lus" with
    | Error (`LustreSyntaxChecksError (_, IllegalImportOfStatefulContract _)) -> true
    | _ -> false);
  mk_test "test merge clock mismatch" (fun () ->
    match load_file "./lustreSyntaxChecks/merge_enum2.lus" with
    | Error (`LustreSyntaxChecksError (_, ClockMismatchInMerge)) -> true
    | _ -> false);
  mk_test "test activate clock mismatch" (fun () ->
    match load_file "./lustreSyntaxChecks/test_activate_clock_mismatch.lus" with
    | Error (`LustreSyntaxChecksError (_, ClockMismatchInMerge)) -> true
    | _ -> false);
  mk_test "test call in cone of influence 1" (fun () ->
    match load_file "./lustreSyntaxChecks/no_node_subject_to_refinement_in_contract_1.lus" with
    | Error (`LustreSyntaxChecksError (_, NodeCallInRefinableContract _)) -> true
    | _ -> false);
  mk_test "test call in cone of influence 2" (fun () ->
    match load_file "./lustreSyntaxChecks/no_node_subject_to_refinement_in_contract_2.lus" with
    | Error (`LustreSyntaxChecksError (_, NodeCallInRefinableContract _)) -> true
    | _ -> false);
  mk_test "test call in cone of influence 3" (fun () ->
    match load_file "./lustreSyntaxChecks/no_node_subject_to_refinement_in_contract_3.lus" with
    | Error (`LustreSyntaxChecksError (_, NodeCallInRefinableContract _)) -> true
    | _ -> false);
  mk_test "test dangling identifier 2" (fun () ->
    match load_file "./lustreSyntaxChecks/test_eqn_lhs_not_defined.lus" with
    | Error (`LustreSyntaxChecksError (_, DanglingIdentifier _)) -> true
    | _ -> false);
  mk_test "test unsupported outside merge 2" (fun () ->
    match load_file "./lustreSyntaxChecks/test_merge.lus" with
    | Error (`LustreSyntaxChecksError (_, UnsupportedOutsideMerge _)) -> true
    | _ -> false);
  mk_test "test symbolic array index in not call" (fun () ->
    match load_file "./lustreSyntaxChecks/test_node_call_with_inductive_array_index.lus" with
    | Error (`LustreSyntaxChecksError (_, SymbolicArrayIndexInNodeArgument _)) -> true
    | _ -> false);
  mk_test "test temporal operator in function contract" (fun () ->
    match load_file "./lustreSyntaxChecks/function_no_stateful_contract.lus" with
    | Error (`LustreSyntaxChecksError (_, IllegalTemporalOperator _)) -> true
    | _ -> false);  
  mk_test "test node call in function contract" (fun () ->
    match load_file "./lustreSyntaxChecks/function_no_stateful_contract_2.lus" with
    | Error (`LustreSyntaxChecksError (_, NodeCallInFunction _)) -> true
    | _ -> false);
  mk_test "test defining a variable more than once 1" (fun () ->
    match load_file "./lustreSyntaxChecks/var_redefinition.lus" with
    | Error (`LustreSyntaxChecksError (_, DuplicateOutput _)) -> true
    | _ -> false);  
  mk_test "test defining a variable more than once 1" (fun () ->
    match load_file "./lustreSyntaxChecks/var_redefinition2.lus" with
    | Error (`LustreSyntaxChecksError (_, DuplicateOutput _)) -> true
    | _ -> false);  
  mk_test "test defining a variable more than once 1" (fun () ->
    match load_file "./lustreSyntaxChecks/var_redefinition3.lus" with
    | Error (`LustreSyntaxChecksError (_, DuplicateLocal _)) -> true
    | _ -> false);
])

(* *************************************************************************** *)
(*                   Lustre Ast Array Dependencies Checks                      *)
(* *************************************************************************** *)
let _ = run_test_tt_main ("frontend lustreArrayDependencies error tests" >::: [
  mk_test "test invalid inductive array def 1" (fun () ->
    match load_file "./lustreArrayDependencies/inductive_array1.lus" with
    | Error (`LustreArrayDependencies  (_, Cycle _)) -> true
    | _ -> false);
  mk_test "test invalid inductive array def 2" (fun () ->
    match load_file "./lustreArrayDependencies/inductive_array2.lus" with
    | Error (`LustreArrayDependencies  (_, Cycle _)) -> true
    | _ -> false);
  mk_test "test invalid inductive array def 3" (fun () ->
    match load_file "./lustreArrayDependencies/inductive_array3.lus" with
    | Error (`LustreArrayDependencies  (_, ExprMissingIndex _)) -> true
    | _ -> false);
  mk_test "test invalid inductive array def 4" (fun () ->
    match load_file "./lustreArrayDependencies/inductive_array4.lus" with
    | Error (`LustreArrayDependencies  (_, Cycle _)) -> true
    | _ -> false);
  mk_test "test invalid inductive array def 5" (fun () ->
    match load_file "./lustreArrayDependencies/inductive_array5.lus" with
    | Error (`LustreArrayDependencies  (_, ExprMissingIndex _)) -> true
    | _ -> false);
  mk_test "test invalid inductive array def 6" (fun () ->
    match load_file "./lustreArrayDependencies/inductive_array6.lus" with
    | Error (`LustreArrayDependencies  (_, Cycle _)) -> true
    | _ -> false);
  mk_test "test invalid inductive array def 7" (fun () ->
    match load_file "./lustreArrayDependencies/inductive_array7.lus" with
    | Error (`LustreArrayDependencies  (_, Cycle _)) -> true
    | _ -> false);
  mk_test "test invalid inductive array def 8" (fun () ->
    match load_file "./lustreArrayDependencies/inductive_array8.lus" with
    | Error (`LustreArrayDependencies  (_, Cycle _)) -> true
    | _ -> false);
  mk_test "test invalid inductive array def 9" (fun () ->
    match load_file "./lustreArrayDependencies/inductive_array9.lus" with
    | Error (`LustreArrayDependencies  (_, Cycle _)) -> true
    | _ -> false);
  mk_test "test invalid inductive array def 10" (fun () ->
    match load_file "./lustreArrayDependencies/inductive_array10.lus" with
    | Error (`LustreArrayDependencies  (_, Cycle _)) -> true
    | _ -> false);
  mk_test "test invalid inductive array def 11" (fun () ->
    match load_file "./lustreArrayDependencies/inductive_array11.lus" with
    | Error (`LustreArrayDependencies  (_, Cycle _)) -> true
    | _ -> false);
])

(* *************************************************************************** *)
(*                      Lustre Ast Dependencies Checks                         *)
(* *************************************************************************** *)
let _ = run_test_tt_main ("frontend LustreAstDependencies error tests" >::: [
  mk_test "test cyclic definition of contracts" (fun () ->
    match load_file "./lustreAstDependencies/circular_contracts.lus" with
    | Error (`LustreAstDependenciesError (_, CyclicDependency _)) -> true
    | _ -> false);
  mk_test "test cyclic definition of function contracts" (fun () ->
    match load_file "./lustreAstDependencies/circular_contracts_2.lus" with
    | Error (`LustreAstDependenciesError (_, CyclicDependency _)) -> true
    | _ -> false);
  mk_test "test cyclic definition of a contract of a node called in a contract" (fun () ->
    match load_file "./lustreAstDependencies/circular_contracts_3.lus" with
    | Error (`LustreAstDependenciesError (_, CyclicDependency _)) -> true
    | _ -> false);
  mk_test "test cyclic definition of nodes" (fun () ->
    match load_file "./lustreAstDependencies/circular_nodes.lus" with
    | Error (`LustreAstDependenciesError (_, CyclicDependency _)) -> true
    | _ -> false);
  mk_test "test cyclic definition of types" (fun () ->
    match load_file "./lustreAstDependencies/circular_types.lus" with
    | Error (`LustreAstDependenciesError (_, CyclicDependency _)) -> true
    | _ -> false);
  mk_test "test contract invalid dependency of call on output" (fun () ->
    match load_file "./lustreAstDependencies/cocospec_node_call_check.lus" with
    | Error (`LustreAstDependenciesError (_, ContractDependencyOnCurrentOutput _)) -> true
    | _ -> false);
  mk_test "test contract invalid dependency of mode on output" (fun () ->
    match load_file "./lustreAstDependencies/cocospec_out_assume.lus" with
    | Error (`LustreAstDependenciesError (_, ContractDependencyOnCurrentOutput _)) -> true
    | _ -> false);
  mk_test "test unequal equation widths" (fun () ->
    match load_file "./lustreAstDependencies/test_add_tuples.lus" with
    | Error (`LustreAstDependenciesError (_, EquationWidthsUnequal)) -> true
    | _ -> false);
  mk_test "test circular contract equations" (fun () ->
    match load_file "./lustreAstDependencies/test_circular_contract_eqns.lus" with
    | Error (`LustreAstDependenciesError (_, CyclicDependency _)) -> true
    | _ -> false);
  mk_test "test circular contracts" (fun () ->
    match load_file "./lustreAstDependencies/test_circular_contracts.lus" with
    | Error (`LustreAstDependenciesError (_, CyclicDependency _)) -> true
    | _ -> false);
  mk_test "test circular equations flattened" (fun () ->
    match load_file "./lustreAstDependencies/test_circular_eqns_flatten_nodes.lus" with
    | Error (`LustreAstDependenciesError (_, CyclicDependency _)) -> true
    | _ -> false);
  mk_test "test circular modes" (fun () ->
    match load_file "./lustreAstDependencies/test_circular_mode_defs.lus" with
    | Error (`LustreAstDependenciesError (_, CyclicDependency _)) -> true
    | _ -> false);
  mk_test "test circular node decls" (fun () ->
    match load_file "./lustreAstDependencies/test_circular_node_decls.lus" with
    | Error (`LustreAstDependenciesError (_, CyclicDependency _)) -> true
    | _ -> false);
  mk_test "test circular node equations 1" (fun () ->
    match load_file "./lustreAstDependencies/test_circular_node_eqns.lus" with
    | Error (`LustreAstDependenciesError (_, CyclicDependency _)) -> true
    | _ -> false);
  mk_test "test circular node equations 2" (fun () ->
    match load_file "./lustreAstDependencies/test_circular_node_eqns2.lus" with
    | Error (`LustreAstDependenciesError (_, CyclicDependency _)) -> true
    | _ -> false);
  mk_test "test circular node equations 3" (fun () ->
    match load_file "./lustreAstDependencies/test_fail_to_assign_node_inputs.lus" with
    | Error (`LustreAstDependenciesError (_, CyclicDependency _)) -> true
    | _ -> false);
  mk_test "test output in contract assume 4" (fun () ->
    match load_file "./lustreAstDependencies/test_out_param_in_contract_assume2.lus" with
    | Error (`LustreAstDependenciesError (_, ContractDependencyOnCurrentOutput _)) -> true
    | _ -> false);
  mk_test "test output in contract assume 5" (fun () ->
    match load_file "./lustreAstDependencies/test_out_param_in_contract_assume3.lus" with
    | Error (`LustreAstDependenciesError (_, ContractDependencyOnCurrentOutput _)) -> true
    | _ -> false);
  mk_test "test output in contract import" (fun () ->
    match load_file "./lustreAstDependencies/test_out_param_in_contract_import.lus" with
    | Error (`LustreAstDependenciesError (_, ContractDependencyOnCurrentOutput _)) -> true
    | _ -> false);
  mk_test "test output in contract import 2" (fun () ->
    match load_file "./lustreAstDependencies/test_out_param_in_contract_import2.lus" with
    | Error (`LustreAstDependenciesError (_, ContractDependencyOnCurrentOutput _)) -> true
    | _ -> false);
  mk_test "test output contains contract args" (fun () ->
    match load_file "./lustreAstDependencies/cocospec_out_param.lus" with
    | Error (`LustreAstDependenciesError (_, ContractDependencyOnCurrentOutput _)) -> true
    | _ -> false);
  mk_test "test node equations unequal width after flattening" (fun () ->
    match load_file "./lustreAstDependencies/test_group_type_flattening.lus" with
    | Error (`LustreAstDependenciesError (_, EquationWidthsUnequal)) -> true
    | _ -> false);
  mk_test "test node equations unequal widths 2" (fun () ->
    match load_file "./lustreAstDependencies/test_node_decls2.lus" with
    | Error (`LustreAstDependenciesError (_, EquationWidthsUnequal)) -> true
    | _ -> false);
  mk_test "test width lenghts unequal" (fun () ->
    match load_file "./lustreAstDependencies/test_merge_width_lengths_unequal.lus" with
    | Error (`LustreAstDependenciesError (_,  WidthLengthsUnequal _)) -> true
    | _ -> false);
  mk_test "test output in contract assume" (fun () ->
    match load_file "./lustreAstDependencies/test_out_param_in_contract_assume.lus" with
    | Error (`LustreAstDependenciesError (_, ContractDependencyOnCurrentOutput _)) -> true
    | _ -> false);
  mk_test "test output in contract assume 2" (fun () ->
    match load_file "./lustreAstDependencies/test_output_in_assume.lus" with
    | Error (`LustreAstDependenciesError (_, ContractDependencyOnCurrentOutput _)) -> true
    | _ -> false);
  mk_test "test output in contract assume 3" (fun () ->
    match load_file "./lustreAstDependencies/test_output_in_assume2.lus" with
    | Error (`LustreAstDependenciesError (_, ContractDependencyOnCurrentOutput _)) -> true
    | _ -> false);
  mk_test "test cycle in type synonym" (fun () ->
    match load_file "./lustreAstDependencies/type_synomym_cycle.lus" with
    | Error (`LustreAstDependenciesError (_, CyclicDependency _)) -> true
    | _ -> false);
  mk_test "test constant redeclared" (fun () ->
    match load_file "./lustreAstDependencies/const_02.lus" with
    | Error (`LustreAstDependenciesError (_, IdentifierRedeclared _)) -> true
    | _ -> false);
  mk_test "test local shadows output" (fun () ->
    match load_file "./lustreAstDependencies/local_shadows_output.lus" with
    | Error (`LustreAstDependenciesError (_, IdentifierRedeclared _)) -> true
    | _ -> false);

  mk_test "test ghost variable redeclaration 1" (fun () ->
    match load_file "./lustreAstDependencies/ghost_variable_redeclaration.lus" with
    | Error (`LustreAstDependenciesError (_, IdentifierRedeclared _)) -> true
    | _ -> false);
  
  mk_test "test ghost variable redeclaration 2" (fun () ->
    match load_file "./lustreAstDependencies/ghost_variable_redeclaration2.lus" with
    | Error (`LustreAstDependenciesError (_, IdentifierRedeclared _)) -> true
    | _ -> false);
  
  mk_test "test ghost variable redeclaration 3" (fun () ->
    match load_file "./lustreAstDependencies/ghost_variable_redeclaration3.lus" with
    | Error (`LustreAstDependenciesError (_, IdentifierRedeclared _)) -> true
    | _ -> false);

  mk_test "test node input redeclaration" (fun () ->
    match load_file "./lustreAstDependencies/node_input_redeclaration.lus" with
    | Error (`LustreAstDependenciesError (_, IdentifierRedeclared _)) -> true
    | _ -> false);

  mk_test "test contract output redeclaration" (fun () ->
    match load_file "./lustreAstDependencies/contract_output_redeclaration.lus" with
    | Error (`LustreAstDependenciesError (_, IdentifierRedeclared _)) -> true
    | _ -> false);

  mk_test "test circular merge" (fun () ->
    match load_file "./lustreAstDependencies/test_circular_merge.lus" with
    | Error (`LustreAstDependenciesError (_, CyclicDependency _)) -> true
    | _ -> false);

  mk_test "test activate" (fun () ->
    match load_file "./lustreAstDependencies/test_activate.lus" with
    | Error _ -> false
    | _ -> true);
])

(* *************************************************************************** *)
(*                        Lustre Type Checker Checks                           *)
(* *************************************************************************** *)
let _ = run_test_tt_main ("frontend LustreTypeChecker error tests" >::: [
  mk_test "test abstract type" (fun () ->
    match load_file "./lustreTypeChecker/abstract_type.lus" with
    | Error (`LustreTypeCheckerError (_, ExpectedNumberTypes _)) -> true
    | _ -> false);
  mk_test "test non-number (bool) cast to int" (fun () ->
    match load_file "./lustreTypeChecker/cast_01.lus" with
    | Error (`LustreTypeCheckerError (_, InvalidConversion _)) -> true
    | _ -> false);
  mk_test "test non-number (bool) cast to real" (fun () ->
    match load_file "./lustreTypeChecker/cast_02.lus" with
    | Error (`LustreTypeCheckerError (_, InvalidConversion _)) -> true
    | _ -> false);
  mk_test "test non-number (bool) cast to int8" (fun () ->
    match load_file "./lustreTypeChecker/cast_03.lus" with
    | Error (`LustreTypeCheckerError (_, InvalidConversion _)) -> true
    | _ -> false);
  mk_test "test non-number (record type) cast to int" (fun () ->
    match load_file "./lustreTypeChecker/cast_04.lus" with
    | Error (`LustreTypeCheckerError (_, InvalidConversion _)) -> true
    | _ -> false);
  mk_test "test non-number (array type) cast to real" (fun () ->
    match load_file "./lustreTypeChecker/cast_05.lus" with
    | Error (`LustreTypeCheckerError (_, InvalidConversion _)) -> true
    | _ -> false);
  mk_test "test non-number (array type) cast to real" (fun () ->
    match load_file "./lustreTypeChecker/cast_05.lus" with
    | Error (`LustreTypeCheckerError (_, InvalidConversion _)) -> true
    | _ -> false);
  mk_test "test constant reassigned" (fun () ->
    match load_file "./lustreTypeChecker/const_01.lus" with
    | Error (`LustreTypeCheckerError (_, DisallowedReassignment _)) -> true
    | _ -> false);
  mk_test "test empty subrange" (fun () ->
    match load_file "./lustreTypeChecker/empty_range.lus" with
    | Error (`LustreTypeCheckerError (_, EmptySubrange _)) -> true
    | _ -> false);
  mk_test "test disallowed resassignment" (fun () ->
    match load_file "./lustreTypeChecker/enum_01.lus" with
    | Error (`LustreTypeCheckerError (_, DisallowedReassignment _)) -> true
    | _ -> false);
  mk_test "test redeclaration of enum" (fun () ->
    match load_file "./lustreTypeChecker/enum_02.lus" with
    | Error (`LustreTypeCheckerError (_, Redeclaration _)) -> true
    | _ -> false);
  mk_test "test import type mismatch" (fun () ->
    match load_file "./lustreTypeChecker/import_type_mismatch.lus" with
    | Error (`LustreTypeCheckerError (_, DisallowedSubrangeInContractReturn _)) -> true
    | _ -> false);
  mk_test "test inlined contract 1" (fun () ->
    match load_file "./lustreTypeChecker/inlined_contract_01.lus" with
    | Error (`LustreTypeCheckerError (_, UnificationFailed _)) -> true
    | _ -> false);
  mk_test "test int div 1" (fun () ->
    match load_file "./lustreTypeChecker/intdiv_01.lus" with
    | Error (`LustreTypeCheckerError (_, ExpectedIntegerTypes _)) -> true
    | _ -> false);
  mk_test "test machine int op 1" (fun () ->
    match load_file "./lustreTypeChecker/machine_integer_01.lus" with
    | Error (`LustreTypeCheckerError (_, IlltypedBitNot _)) -> true
    | _ -> false);
  mk_test "test machine int op 2" (fun () ->
    match load_file "./lustreTypeChecker/machine_integer_02.lus" with
    | Error (`LustreTypeCheckerError (_, ExpectedMachineIntegerTypes _)) -> true
    | _ -> false);
  mk_test "test machine int op 3" (fun () ->
    match load_file "./lustreTypeChecker/machine_integer_03.lus" with
    | Error (`LustreTypeCheckerError (_, ExpectedMachineIntegerTypes _)) -> true
    | _ -> false);
  mk_test "test machine int op 4" (fun () ->
    match load_file "./lustreTypeChecker/machine_integer_04.lus" with
    | Error (`LustreTypeCheckerError (_, ExpectedBitShiftMachineIntegerType _)) -> true
    | _ -> false);
  mk_test "test machine int op 5" (fun () ->
    match load_file "./lustreTypeChecker/machine_integer_05.lus" with
    | Error (`LustreTypeCheckerError (_, ExpectedBitShiftMachineIntegerType _)) -> true
    | _ -> false);
  mk_test "test merge case missing" (fun () ->
    match load_file "./lustreTypeChecker/merge_enum.lus" with
    | Error (`LustreTypeCheckerError (_, MergeCaseMissing _)) -> true
    | _ -> false);
  mk_test "test merge cases unique" (fun () ->
    match load_file "./lustreTypeChecker/merge_enum1.lus" with
    | Error (`LustreTypeCheckerError (_, MergeCaseNotUnique _)) -> true
    | _ -> false);
  mk_test "test shadowed mode def" (fun () ->
    match load_file "./lustreTypeChecker/mode_reqs_by_idents_shadowing.lus" with
    | Error (`LustreTypeCheckerError (_, Redeclaration _)) -> true
    | _ -> false);
  mk_test "test illtyped call" (fun () ->
    match load_file "./lustreTypeChecker/SteamBoiler2.lus" with
    | Error (`LustreTypeCheckerError (_, IlltypedCall _)) -> true
    | _ -> false);
  mk_test "test expected type 1" (fun () ->
    match load_file "./lustreTypeChecker/test_array_group.lus" with
    | Error (`LustreTypeCheckerError (_, ExpectedType _)) -> true
    | _ -> false);
  mk_test "test expected type 2" (fun () ->
    match load_file "./lustreTypeChecker/test_array_sizes.lus" with
    | Error (`LustreTypeCheckerError (_, ExpectedType _)) -> true
    | _ -> false);
  mk_test "test invalid array bounds" (fun () ->
    match load_file "./lustreTypeChecker/test_const_bool_in_array_type.lus" with
    | Error (`LustreTypeCheckerError (_, ArrayBoundsInvalidExpression)) -> true
    | _ -> false);
  mk_test "test range type integer arguments" (fun () ->
    match load_file "./lustreTypeChecker/test_const_decls_tyalias.lus" with
    | Error (`LustreTypeCheckerError (_, SubrangeArgumentMustBeConstantInteger _)) -> true
    | _ -> false);
  mk_test "test unification failure 1" (fun () ->
    match load_file "./lustreTypeChecker/test_homeomorphic_exn_array.lus" with
    | Error (`LustreTypeCheckerError (_, ExpectedNumberTypes _)) -> true
    | _ -> false);
  mk_test "test unification failure 2" (fun () ->
    match load_file "./lustreTypeChecker/test_homeomorphic_exn_tuples.lus" with
    | Error (`LustreTypeCheckerError (_, ExpectedNumberTypes _)) -> true
    | _ -> false);
  mk_test "test unification failure 3" (fun () ->
    match load_file "./lustreTypeChecker/test_homeomorphic_exn.lus" with
    | Error (`LustreTypeCheckerError (_, ExpectedNumberTypes _)) -> true
    | _ -> false);
  mk_test "test not a field of record 01" (fun () ->
    match load_file "./lustreTypeChecker/test_record_expr.lus" with
    | Error (`LustreTypeCheckerError (_, NotAFieldOfRecord _)) -> true
    | _ -> false);
  mk_test "test not a field of record 02" (fun () ->
    match load_file "./lustreTypeChecker/not_a_field_of_record.lus" with
    | Error (`LustreTypeCheckerError (_, NotAFieldOfRecord _)) -> true
    | _ -> false);
  mk_test "test no value for field 01" (fun () ->
    match load_file "./lustreTypeChecker/no_value_for_field_01.lus" with
    | Error (`LustreTypeCheckerError (_, NoValueForRecordField _)) -> true
    | _ -> false);
  mk_test "test no value for field 02" (fun () ->
    match load_file "./lustreTypeChecker/no_value_for_field_02.lus" with
    | Error (`LustreTypeCheckerError (_, NoValueForRecordField _)) -> true
    | _ -> false);
  mk_test "test unification failure 4" (fun () ->
    match load_file "./lustreTypeChecker/test-func-sliced.lus" with
    | Error (`LustreTypeCheckerError (_, ExpectedNumberTypes _)) -> true
    | _ -> false);
  mk_test "test expected type 3" (fun () ->
    match load_file "./lustreTypeChecker/test-type.lus" with
    | Error (`LustreTypeCheckerError (_, UnequalArrayExpressionType)) -> true
    | _ -> false);
  mk_test "test invalid array bounds 2" (fun () ->
    match load_file "./lustreTypeChecker/type-grammer.lus" with
    | Error (`LustreTypeCheckerError (_, ArrayBoundsInvalidExpression)) -> true
    | _ -> false);
  mk_test "test undeclared 1" (fun () ->
    match load_file "./lustreTypeChecker/undeclared_type_01.lus" with
    | Error (`LustreTypeCheckerError (_, UndeclaredType _)) -> true
    | _ -> false);
  mk_test "test undeclared 2" (fun () ->
    match load_file "./lustreTypeChecker/undeclared_type_02.lus" with
    | Error (`LustreTypeCheckerError (_, UndeclaredType _)) -> true
    | _ -> false);
  mk_test "test undeclared 3" (fun () ->
    match load_file "./lustreTypeChecker/undeclared_type_03.lus" with
    | Error (`LustreTypeCheckerError (_, UndeclaredType _)) -> true
    | _ -> false);
  mk_test "test undeclared 4" (fun () ->
    match load_file "./lustreTypeChecker/undeclared_type_04.lus" with
    | Error (`LustreTypeCheckerError (_, UndeclaredType _)) -> true
    | _ -> false);
  mk_test "test undeclared 5" (fun () ->
    match load_file "./lustreTypeChecker/undeclared_type_05.lus" with
    | Error (`LustreTypeCheckerError (_, UndeclaredType _)) -> true
    | _ -> false);
  mk_test "test local shadowing global" (fun () ->
    match load_file "./lustreTypeChecker/test_shadowing.lus" with
    | Error (`LustreTypeCheckerError (_, Redeclaration _)) -> true
    | _ -> false);
  mk_test "test arity incorrect node call" (fun () ->
    match load_file "./lustreTypeChecker/arity_incorrect_node_call.lus" with
    | Error (`LustreTypeCheckerError (_, IlltypedCall _)) -> true
    | _ -> false);
  mk_test "test nominal record type equality" (fun () ->
    match load_file "./lustreTypeChecker/record_type_nominal_eq.lus" with
    | Error (`LustreTypeCheckerError (_, NoValueForRecordField _)) -> true
    | _ -> false);
  mk_test "test unequal equation widths in parallel ghost variable assignment" (fun () ->
    match load_file "./lustreTypeChecker/unequal_equation_widths_contract.lus" with
    | Error (`LustreTypeCheckerError (_, MismatchOfEquationType _)) -> true
    | _ -> false);
  mk_test "test unequal equation widths in parallel ghost variable assignment 2" (fun () ->
    match load_file "./lustreTypeChecker/unequal_equation_widths_contract2.lus" with
    | Error (`LustreTypeCheckerError (_, ExpectedType _)) -> true
    | _ -> false);
  mk_test "test extensional array equality" (fun () ->
    match load_file "./lustreTypeChecker/extensional_array_equality.lus" with
    | Error (`LustreTypeCheckerError (_, Unsupported _)) -> true
    | _ -> false);
  mk_test "test expected record type" (fun () ->
    match load_file "./lustreTypeChecker/expected_record_type.lus" with
    | Error (`LustreTypeCheckerError (_, ExpectedRecordType _)) -> true
    | _ -> false);
  mk_test "test provided invalid type" (fun () ->
    match load_file "./lustreTypeChecker/provided.lus" with
    | Error (`LustreTypeCheckerError (_, UnificationFailed _)) -> true
    | _ -> false);
  mk_test "test open interval with no bounds" (fun () ->
    match load_file "./lustreTypeChecker/open_interval.lus" with
    | Error (`LustreTypeCheckerError (_, IntervalMustHaveBound)) -> true
    | _ -> false);
  mk_test "test nondeterministic choice type error" (fun () ->
    match load_file "./lustreTypeChecker/nondeterministic_choice.lus" with
    | Error (`LustreTypeCheckerError (_, ExpectedIntegerTypes _)) -> true
    | _ -> false);
  mk_test "test nondeterministic choice type error 2" (fun () ->
    match load_file "./lustreTypeChecker/nondeterministic_choice_2.lus" with
    | Error (`LustreTypeCheckerError (_, UnificationFailed _)) -> true
    | _ -> false);
])

(* *************************************************************************** *)
(*                        Lustre If and Frame Block Checks                     *)
(* *************************************************************************** *)
let _ = run_test_tt_main ("frontend LustreDesugarFrameBlocks and LustreDesugarIfBlocks error tests" >::: [
  mk_test "Misplaced frame block inside if block" (fun () ->
    match load_file "./lustreSyntaxChecks/misplaced_frame_block.lus" with
    | Error (`LustreDesugarIfBlocksError (_, MisplacedNodeItemError _)) -> true
    | _ -> false);  
  mk_test "Misplaced node item inside frame block" (fun () ->
    match load_file "./lustreSyntaxChecks/misplaced_node_item_frame.lus" with
    | Error (`LustreDesugarFrameBlocksError (_, MisplacedNodeItemError _)) -> true
    | _ -> false); 
  mk_test "Uninitialized node item inside frame block" (fun () ->
    match load_file "./lustreSyntaxChecks/uninitialized_node_item_frame.lus" with
    | Error (`LustreSyntaxChecksError (_, MisplacedVarInFrameBlock _)) -> true
    | _ -> false);  
  mk_test "Uninitialized node item inside frame block 2" (fun () ->
    match load_file "./lustreSyntaxChecks/uninitialized_node_item_frame2.lus" with
    | Error (`LustreSyntaxChecksError (_, MisplacedVarInFrameBlock _)) -> true
    | _ -> false);  
])
