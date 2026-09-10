/-
Copyright (c) 2026 PNP Labs.
Complete initial-family branch coverage, physical source preservation, padding,
canonical whole-formula payloads and encoded-input bounds. Fixtures award no
progress credit and do not replace the unbounded source theorem.
-/
import PNP.Concrete.CookLevinBuilderInitialPayload

namespace PNP.Concrete.CookLevin.BuilderInitialPayload.Regression
open BuilderInitialPayload
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside)

example : (List.range 8).map (select .inputOnly) =
    [.state, .head, .inputCells, .inputCells, .inputCells, .inputCells, .inputCells, .inputCells] := by decide
example : (List.range 8).map (select .paired) =
    [.state, .head, .length, .pairedCells, .pairedCells, .pairedCells, .pairedCells, .pairedCells] := by decide
example (mode : InputMode) : select mode 0 = .state := select_state mode
example (mode : InputMode) : select mode 1 = .head := select_head mode
example : select .paired 2 = .length := select_paired_length
example : select .inputOnly 2 ≠ .length := by decide
example (k : Nat) : select .inputOnly (k + 2) = .inputCells := select_input_cell _ (by omega)
example (k : Nat) : select .paired (k + 3) = .pairedCells := select_paired_cell _ (by omega)
example (mode : InputMode) (c : Nat) : testSteps mode c ≤ 18 := testSteps_le mode c
example : testSteps .inputOnly 1000 = 10 := by decide
example : testSteps .paired 1000 = 18 := by decide
example : BuilderRegisterPack.values paddingFields paddingEnvironment = [1] := rfl

section Source
variable {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
variable (output : List CNFToken)
example : sourceFrame problem index remaining =
    BuilderLiteralArgumentSource.inputValues problem index remaining .initial [] := rfl
example : sourceFrame problem index remaining = sourcePrefix problem index remaining ++ [coordinate problem index] :=
  source_suffix problem index remaining
example : selectedRole problem index = select problem.tableauInputMode
    (BuilderConstraintRegionSource.localCoordinate problem index .initial) := rfl
example (expected : Nat) (workspace outside : List WorkSymbol) (h : coordinate problem index = expected) :
    workRunExact? (BuilderUnaryTagMatch.machine expected) (BuilderUnaryTagMatch.workSteps expected (coordinate problem index))
      (workStartConfiguration (BuilderUnaryTagMatch.machine expected) (endTape (sourceFrame problem index remaining) workspace outside)) =
      some {state := (BuilderUnaryTagMatch.machine expected).acceptState, tape := endTape (sourceFrame problem index remaining) workspace outside} :=
  tag_accept problem index remaining expected workspace outside h
example (expected : Nat) (workspace outside : List WorkSymbol) (h : coordinate problem index ≠ expected) :
    workRunExact? (BuilderUnaryTagMatch.machine expected) (BuilderUnaryTagMatch.workSteps expected (coordinate problem index))
      (workStartConfiguration (BuilderUnaryTagMatch.machine expected) (endTape (sourceFrame problem index remaining) workspace outside)) =
      some {state := (BuilderUnaryTagMatch.machine expected).rejectState, tape := endTape (sourceFrame problem index remaining) workspace outside} :=
  tag_reject problem index remaining expected workspace outside h

example (h : BuilderInitialPairedCellSource.selection problem index = none) : pairedPayload problem index = [1] := by
  rw [pairedPayload, h]
example (h : BuilderInitialPairedCellSource.selection problem index = none) : pairedPayload problem index ≠ [0] := by
  rw [pairedPayload, h]
  change ([1] : List Nat) ≠ [0]
  decide
example (h : BuilderInitialPairedCellSource.selection problem index = none) (literal : Nat) :
    pairedPayload problem index ≠ [literal, 1, 2] := by
  rw [pairedPayload, h]
  intro hEq
  have := congrArg List.length hEq
  simp only [List.length_cons, List.length_nil] at this
  omega
example (h : BuilderInitialPairedCellSource.selection problem index = none) :
    pairedValues problem index remaining = BuilderInitialPairedCellPayload.finalValues problem index remaining ++ [1] := by
  rw [pairedValues, h]
example (hPrefix : ¬ coordinate problem index < 3) :
    ∃ older : List Nat, pairedValues problem index remaining = older ++ pairedPayload problem index :=
  paired_suffix problem index remaining hPrefix

example : workSteps problem index remaining = testSteps problem.tableauInputMode (coordinate problem index) +
    branchSteps problem index remaining (selectedRole problem index) := workSteps_decomposition problem index remaining
example : workRunExact? (machine problem.verifier) (workSteps problem index remaining)
    (initialConfiguration problem index remaining output) = some (finalConfiguration problem index remaining output) :=
  workRunExact problem index remaining output
example : run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
    (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
    encodeWorkConfiguration (finalConfiguration problem index remaining output) := run_compile_exact problem index remaining output
example : (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState :=
  final_accept problem index remaining output
example : (finalConfiguration problem index remaining output).tape =
    endTape (finalValues problem index remaining) (inside problem.input output) (exterior problem index) :=
  final_tape problem index remaining output
example : (finalConfiguration problem index remaining output).tape.left = exterior problem index :=
  final_exterior problem index remaining output
example (hMode : problem.tableauInputMode = .paired) (hCoordinate : coordinate problem index = 2) :
    exterior problem index = BuilderInitialLengthPayload.exterior problem index :=
  length_exterior problem index hMode hCoordinate
example (hRole : selectedRole problem index ≠ .length) : exterior problem index = [] :=
  nonlength_exterior problem index hRole
example : finalValues problem index remaining = history problem index remaining ++ payloadValues problem index :=
  final_suffix problem index remaining

variable (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .initial)
example (hMode : problem.tableauInputMode = .paired) (hPrefix : ¬ coordinate problem index < 3) :
    pairedPayload problem index = BuilderInitialConstraintPayload.values problem (coordinate problem index) :=
  paired_payload_canonical problem index hMode hRegion hPrefix
example : payloadValues problem index = BuilderInitialConstraintPayload.values problem (coordinate problem index) :=
  payload_canonical problem index hRegion
example : BuilderLocalConstraintPayload.decode problem.FormulaWidth (payloadValues problem index) =
    some (problem.initialConstraintSlotDirect (coordinate problem index)) := payload_decode problem index hRegion
example : payloadValues problem index = BuilderLocalConstraintPayload.values
    (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)) :=
  whole_formula_payload problem index hRegion
example : workRunExact? (machine problem.verifier) (workSteps problem index remaining)
    (initialConfiguration problem index remaining output) =
    some
      {state := (machine problem.verifier).acceptState,
       tape := endTape (history problem index remaining ++ BuilderLocalConstraintPayload.values
         (problem.formulaConstraintSlotDirect (BuilderClauseDividerExecution.constraintIndex problem index)))
         (inside problem.input output) (exterior problem index)} :=
  source_canonical_payload problem index remaining output hRegion
example (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    (registerWord (finalValues problem index remaining)).length + (exterior problem index).length ≤
        (spanPolynomial problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining ≤ (rawTimePolynomial problem.verifier).eval problem.input.length :=
  source_polynomial_bounds problem index remaining hBody hBalance hRegion

example : (graph problem.verifier).nodes.length = 9 := graph_nodes_length problem.verifier
example : (graph problem.verifier).WellFormed := graph_wellFormed problem.verifier
example : (machine problem.verifier).rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) (machine problem.verifier).acceptState := noRuleAtAccept problem.verifier
example : WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) (machine problem.verifier).rejectState := noRuleAtReject problem.verifier
example : (machine problem.verifier).acceptState ≠ (machine problem.verifier).rejectState := acceptState_ne_rejectState problem.verifier
end Source
end PNP.Concrete.CookLevin.BuilderInitialPayload.Regression
