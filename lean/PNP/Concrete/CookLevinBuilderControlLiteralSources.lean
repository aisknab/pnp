/-
Copyright (c) 2026 PNP Labs.

Source-derived time and literal references for every control implication.
The verifier fixes each program. Runtime values come from the written radix
frame and the already verified action/head computation. Canonical requests
below specify outputs; they are not supplied to the executable machine.
Complete payload packing and runtime conclusion selection remain downstream.
-/

import PNP.Concrete.CookLevinBuilderControlHeadSource

namespace PNP.Concrete.CookLevin.BuilderControlLiteralSources

open BuilderUnaryPolynomial (registerWord registerWord_append)
open BuilderDividerOperands (endTape)
open BuilderLiteralArgumentSource
  (Plan Reference referenceValue field field_eval inputCount inputValues environment environment_values
    argumentEnvironment)
open BuilderControlCoordinates (Coordinates ofSource)

inductive Role where
  | currentState | currentHead | currentRead | nextState | nextHead | nextWrite
  deriving DecidableEq, Repr

def kind : Role → BuilderLiteralIndexExpression.Kind
  | .currentState | .nextState => .state
  | .currentHead | .nextHead => .head
  | .currentRead | .nextWrite => .symbol

def request {language : Language} {problem : VerifierTableauProblem language}
    (role : Role) (coordinates : Coordinates problem) : BuilderLiteralIndexExpression.Request problem.layout :=
  match role with
  | .currentState => BuilderControlCoordinates.stateRequest coordinates
  | .currentHead => BuilderControlCoordinates.headRequest coordinates
  | .currentRead => BuilderControlCoordinates.readRequest coordinates
  | .nextState => .state (problem.nextTime coordinates.step) (BuilderControlCoordinates.action coordinates).targetState
  | .nextHead => .head (problem.nextTime coordinates.step)
      (VerifierTableauProblem.movePosition coordinates.position (BuilderControlCoordinates.action coordinates).move)
  | .nextWrite => .symbol (problem.nextTime coordinates.step) coordinates.position
      (BuilderControlCoordinates.action coordinates).writeSymbol

theorem request_kind {language : Language} {problem : VerifierTableauProblem language}
    (role : Role) (coordinates : Coordinates problem) : (request role coordinates).kind = kind role := by
  cases role <;> rfl

def timeValue {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  referenceValue problem index .control [] (.quotient : Reference .control 0)
def timeValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  [timeValue problem index, 1, timeValue problem index + 1]

def preparedValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  BuilderControlHeadSource.finalRetainedValues problem index hRegion ++ timeValues problem index

theorem preparedValues_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (preparedValues problem index hRegion).length = 15 := by
  simp only [preparedValues, List.length_append, BuilderControlHeadSource.finalRetainedValues_length,
    timeValues, List.length_cons, List.length_nil]

def canonicalValues {language : Language} {problem : VerifierTableauProblem language}
    (coordinates : Coordinates problem) : List Nat :=
  let action := BuilderControlCoordinates.action coordinates
  [coordinates.state.val, 3, coordinates.state.val * 3, coordinates.readCode.val,
    coordinates.state.val * 3 + coordinates.readCode.val,
    action.targetState.val, VariableLayout.tapeSymbolCode action.writeSymbol,
    BuilderRegisterHeadMove.moveCode action.move,
    problem.dimensions.tapeWidth problem.tableauInputMode, coordinates.position.val,
    BuilderRegisterHeadMove.moveCode action.move,
    (VerifierTableauProblem.movePosition coordinates.position action.move).val,
    coordinates.step.val, 1, coordinates.step.val + 1]

theorem prepared_canonical {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    preparedValues problem index hRegion = canonicalValues (ofSource problem index hRegion) := by
  have hCoordinates := BuilderControlCoordinates.source_radix_coordinates problem index hRegion
  have hSource := BuilderControlActionSource.source_values problem index hRegion
  simp only [preparedValues, BuilderControlHeadSource.finalRetainedValues,
    BuilderControlHeadSource.headValues, BuilderRegisterHeadMove.finalValues]
  rw [BuilderControlHeadSource.moved_canonical problem index hRegion]
  simp only [BuilderControlHeadSource.retainedValues, BuilderControlActionSource.keyValues,
    BuilderControlActionSource.keyPrefix, BuilderControlActionSource.keyValue, hSource.1, hSource.2,
    BuilderControlActionSource.selected_canonical problem index hRegion, BuilderControlActionSource.rowValues,
    BuilderControlHeadSource.position_canonical problem index hRegion,
    BuilderControlHeadSource.widthValue, BuilderLiteralArgumentSource.sourceValue,
    BuilderControlHeadSource.actualMove, canonicalValues, BuilderControlCoordinates.action,
    timeValues, timeValue, referenceValue, hCoordinates.2,
    List.cons_append, List.nil_append, List.append_assoc, BuilderRegisterHeadMove.moveCode]

/-- All offsets are fixed syntax; extra registers do not provide literal answers. -/
def plan (role : Role) (extraCount : Nat) : Plan .control (15 + extraCount) :=
  fun fieldIndex => match role, fieldIndex.val with
  | .currentState, 0 | .currentHead, 0 | .currentRead, 0 => .quotient
  | .currentState, 2 => .digit ⟨2, by decide⟩
  | .currentHead, 1 | .currentRead, 1 | .nextWrite, 1 => .digit ⟨3, by decide⟩
  | .currentRead, 3 => .digit ⟨1, by decide⟩
  | .nextState, 0 | .nextHead, 0 | .nextWrite, 0 => .retained ⟨14, by omega⟩
  | .nextState, 2 => .retained ⟨5, by omega⟩
  | .nextHead, 1 => .retained ⟨11, by omega⟩
  | .nextWrite, 3 => .retained ⟨6, by omega⟩
  | _, _ => .constant 0

theorem argument_environment {language : Language} (problem : VerifierTableauProblem language)
    (index extraCount : Nat) (extra : List Nat) (role : Role)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    argumentEnvironment problem index .control (preparedValues problem index hRegion ++ extra) (plan role extraCount) =
      (request role (ofSource problem index hRegion)).environment := by
  have hCoordinates := BuilderControlCoordinates.source_radix_coordinates problem index hRegion
  rw [prepared_canonical problem index hRegion]
  funext fieldIndex
  rcases fieldIndex with ⟨fieldIndex, hField⟩
  have hCases : fieldIndex = 0 ∨ fieldIndex = 1 ∨ fieldIndex = 2 ∨ fieldIndex = 3 ∨
      fieldIndex = 4 ∨ fieldIndex = 5 ∨ fieldIndex = 6 ∨ fieldIndex = 7 := by omega
  cases role <;> rcases hCases with h | h | h | h | h | h | h | h <;> subst fieldIndex <;>
    simp only [argumentEnvironment, BuilderLiteralArgumentSource.references, plan, referenceValue,
      BuilderLiteralArgumentSource.sourceValue, canonicalValues, hCoordinates.1, hCoordinates.2,
      List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ,
      request, BuilderControlCoordinates.stateRequest, BuilderControlCoordinates.headRequest,
      BuilderControlCoordinates.readRequest, BuilderLiteralIndexExpression.Request.environment,
      VerifierTableauProblem.currentTime, VerifierTableauProblem.nextTime] <;>
    first | rfl | exact (BuilderControlCoordinates.symbol_code _).symm

theorem index_eq {language : Language} (problem : VerifierTableauProblem language)
    (index extraCount : Nat) (extra : List Nat) (role : Role)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression (kind role))
      (argumentEnvironment problem index .control (preparedValues problem index hRegion ++ extra) (plan role extraCount)) =
      (request role (ofSource problem index hRegion)).index := by
  rw [argument_environment problem index extraCount extra role hRegion]
  simpa only [request_kind] using
    BuilderLiteralIndexExpression.eval_eq_index (request role (ofSource problem index hRegion))

def timeExpression {language : Language} (verifier : PolynomialTimeVerifier language) :
    BuilderRegisterExpression.Expr (inputCount verifier .control 12) :=
  .binary .add (field verifier .control 12 .quotient).expression (.constant 1)

theorem time_expression_values {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    BuilderRegisterExpression.values (timeExpression problem.verifier)
      (environment problem index remaining .control 12 (BuilderControlHeadSource.finalRetainedValues problem index hRegion)) =
      timeValues problem index := by
  have hRead := field_eval problem index remaining .control 12
    (BuilderControlHeadSource.finalRetainedValues problem index hRegion) .quotient
  change BuilderRegisterExpression.eval (field problem.verifier .control 12 .quotient).expression
    (environment problem index remaining .control 12 (BuilderControlHeadSource.finalRetainedValues problem index hRegion)) =
      timeValue problem index at hRead
  rw [timeExpression, BuilderRegisterExpression.values, BuilderRegisterPack.Field.expression_values]
  change [BuilderRegisterExpression.eval (field problem.verifier .control 12 .quotient).expression
    (environment problem index remaining .control 12 (BuilderControlHeadSource.finalRetainedValues problem index hRegion))] ++ [1] ++
      [BuilderRegisterExpression.eval (field problem.verifier .control 12 .quotient).expression
        (environment problem index remaining .control 12 (BuilderControlHeadSource.finalRetainedValues problem index hRegion)) + 1] = _
  rw [hRead]
  rfl

private theorem head_environment {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    List.ofFn (environment problem index remaining .control 12
      (BuilderControlHeadSource.finalRetainedValues problem index hRegion)) =
      BuilderControlHeadSource.finalValues problem index remaining hRegion :=
  (environment_values problem index remaining .control 12
    (BuilderControlHeadSource.finalRetainedValues problem index hRegion)
    (BuilderControlHeadSource.finalRetainedValues_length problem index hRegion)).trans
      (BuilderControlHeadSource.finalValues_frame problem index remaining hRegion).symm

def timeMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  BuilderRegisterExpression.machine (timeExpression verifier) 0
def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderControlHeadSource.machine verifier) (timeMachine verifier)

def timeSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : Nat :=
  BuilderRegisterExpression.workSteps (timeExpression problem.verifier)
    (environment problem index remaining .control 12 (BuilderControlHeadSource.finalRetainedValues problem index hRegion)) []
def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : Nat :=
  BuilderControlHeadSource.workSteps problem index remaining hRegion + 1 + timeSteps problem index remaining hRegion

def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  inputValues problem index remaining .control (preparedValues problem index hRegion)
def finalOutside {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List WorkSymbol :=
  (BuilderControlHeadSource.finalOutside problem index outside hRegion).drop (registerWord (timeValues problem index)).length

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier)
    (endTape (BuilderControlActionSource.frame problem index remaining) inside outside)
def finalConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : WorkConfiguration :=
  {
    state := (machine problem.verifier).acceptState
    tape := endTape (finalValues problem index remaining hRegion) inside (finalOutside problem index outside hRegion) }

theorem time_workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    workRunExact? (timeMachine problem.verifier) (timeSteps problem index remaining hRegion)
      (workStartConfiguration (timeMachine problem.verifier)
        (endTape (BuilderControlHeadSource.finalValues problem index remaining hRegion) inside outside)) =
      some {
        state := (timeMachine problem.verifier).acceptState
        tape := endTape (finalValues problem index remaining hRegion) inside
          (outside.drop (registerWord (timeValues problem index)).length) } := by
  have h := BuilderRegisterExpression.workRunExact (timeExpression problem.verifier) 0 []
    (environment problem index remaining .control 12 (BuilderControlHeadSource.finalRetainedValues problem index hRegion))
    [] inside outside rfl
  simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
    head_environment problem index remaining hRegion, time_expression_values problem index remaining hRegion,
    List.nil_append, List.append_nil, timeMachine, timeSteps,
    BuilderControlHeadSource.finalValues_frame problem index remaining hRegion,
    finalValues, inputValues, preparedValues, List.append_assoc] using h

private theorem chain_run (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining hRegion)
      (initialConfiguration problem index remaining inside outside) =
      some (finalConfiguration problem index remaining inside outside hRegion) := by
  have hHead := BuilderControlHeadSource.workRunExact problem index remaining inside outside hRegion
  have hTime := time_workRunExact problem index remaining inside
    (BuilderControlHeadSource.finalOutside problem index outside hRegion) hRegion
  simp only [BuilderControlHeadSource.initialConfiguration, BuilderControlHeadSource.finalConfiguration] at hHead
  have h := chain_run (BuilderControlHeadSource.machine problem.verifier)
    (timeMachine problem.verifier) (BuilderControlHeadSource.workSteps problem index remaining hRegion)
    (timeSteps problem index remaining hRegion) _ _ _ hHead hTime
  simpa only [machine, workSteps, initialConfiguration, finalConfiguration, finalOutside] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining hRegion)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside outside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining inside outside hRegion) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining inside outside hRegion)

def spanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial (timeExpression verifier) (BuilderControlHeadSource.spanBound verifier)
def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderControlHeadSource.rawTimeBound verifier) (.constant 6))
    (BuilderRegisterExpression.rawTimePolynomial (timeExpression verifier) (BuilderControlHeadSource.spanBound verifier))

theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (registerWord (finalValues problem index remaining hRegion)).length ≤
        (spanBound problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining hRegion ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hHead := BuilderControlHeadSource.source_polynomial_bounds problem index remaining hBody hBalance hRegion
  have hStart :
      (registerWord ([] ++ List.ofFn (environment problem index remaining .control 12
        (BuilderControlHeadSource.finalRetainedValues problem index hRegion)) ++ [])).length ≤
          (BuilderControlHeadSource.spanBound problem.verifier).eval problem.input.length := by
    simpa only [List.nil_append, List.append_nil, head_environment problem index remaining hRegion] using hHead.1
  have hTime := BuilderRegisterExpression.source_polynomial_bounds (timeExpression problem.verifier)
    (BuilderControlHeadSource.spanBound problem.verifier) problem.input.length []
    (environment problem index remaining .control 12 (BuilderControlHeadSource.finalRetainedValues problem index hRegion)) [] hStart
  constructor
  · simpa only [List.nil_append, List.append_nil, head_environment problem index remaining hRegion,
      time_expression_values problem index remaining hRegion, spanBound,
      BuilderControlHeadSource.finalValues_frame problem index remaining hRegion,
      finalValues, inputValues, preparedValues, List.append_assoc] using hTime.1
  · have hTimeBound := hTime.2
    simp only [rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant, workSteps, timeSteps]
    omega

theorem retained_span_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (registerWord (preparedValues problem index hRegion)).length ≤
      (spanBound problem.verifier).eval problem.input.length := by
  have h := (source_polynomial_bounds problem index remaining hBody hBalance hRegion).1
  simp only [finalValues, inputValues, registerWord_append, List.length_append] at h
  omega

theorem final_inside_preserved {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (finalConfiguration problem index remaining inside outside hRegion).tape.right =
      (registerWord (finalValues problem index remaining hRegion)).reverse ++ inside := rfl

theorem final_exterior_accounted {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (finalConfiguration problem index remaining inside outside hRegion).tape.left =
      finalOutside problem index outside hRegion := rfl

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderControlHeadSource.rules_pairwise_query_distinct verifier)
    (BuilderRegisterExpression.rules_pairwise_query_distinct (timeExpression verifier) 0)
    (BuilderControlHeadSource.noRuleAtAccept verifier)
theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  WorkMachineChain.noRuleAtAccept _ _ (BuilderRegisterExpression.noRuleAtAccept (timeExpression verifier) 0)
theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  WorkMachineChain.noRuleAtAccept (BuilderControlHeadSource.machine verifier)
    {timeMachine verifier with acceptState := (timeMachine verifier).rejectState}
    (BuilderRegisterExpression.noRuleAtReject (timeExpression verifier) 0)
theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _
    (BuilderRegisterExpression.acceptState_ne_rejectState (timeExpression verifier) 0)

def literalCount (role : Role) : Nat :=
  8 + BuilderRegisterExpression.nodeCount (BuilderLiteralIndexExpression.expression (kind role))

def literalWrittenValues {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (role : Role)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  BuilderLiteralArgumentSource.writtenValues problem index .control
    (preparedValues problem index hRegion) (plan role 0) (kind role)

theorem literalWrittenValues_length {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (role : Role)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (literalWrittenValues problem index role hRegion).length = literalCount role := by
  simp only [literalWrittenValues, BuilderLiteralArgumentSource.writtenValues, List.length_append,
    List.length_ofFn, BuilderRegisterExpression.values_length, literalCount]

theorem literalWrittenValues_end {language : Language} (problem : VerifierTableauProblem language)
    (index : Nat) (role : Role)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    ∃ leadingValues, literalWrittenValues problem index role hRegion =
      leadingValues ++ [(request role (ofSource problem index hRegion)).index] := by
  have hIndex := index_eq problem index 0 [] role hRegion
  simp only [List.append_nil] at hIndex
  refine ⟨List.ofFn (argumentEnvironment problem index .control
      (preparedValues problem index hRegion) (plan role 0)) ++
    BuilderRegisterExpression.prefixValues (BuilderLiteralIndexExpression.expression (kind role))
      (argumentEnvironment problem index .control (preparedValues problem index hRegion) (plan role 0)), ?_⟩
  simp only [literalWrittenValues, BuilderLiteralArgumentSource.writtenValues,
    BuilderRegisterExpression.values_root, hIndex, List.append_assoc]

def literalMachine {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) : WorkMachine :=
  BuilderLiteralArgumentSource.machine verifier .control 15 (plan role 0) (kind role)
def firstLiteralMachine {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) : WorkMachine :=
  WorkMachineChain.machine (machine verifier) (literalMachine verifier role)

def literalSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (role : Role) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : Nat :=
  BuilderLiteralArgumentSource.workSteps problem index remaining .control 15
    (preparedValues problem index hRegion) (plan role 0) (kind role)
def firstLiteralSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (role : Role) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : Nat :=
  workSteps problem index remaining hRegion + 1 + literalSteps problem index remaining role hRegion

def firstLiteralRetained {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (role : Role) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  preparedValues problem index hRegion ++ literalWrittenValues problem index role hRegion
def firstLiteralValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (role : Role) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List Nat :=
  inputValues problem index remaining .control (firstLiteralRetained problem index role hRegion)
def firstLiteralOutside {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (role : Role) (outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : List WorkSymbol :=
  (finalOutside problem index outside hRegion).drop (registerWord (literalWrittenValues problem index role hRegion)).length

theorem firstLiteralRetained_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (role : Role) (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (firstLiteralRetained problem index role hRegion).length = 15 + literalCount role := by
  simp only [firstLiteralRetained, List.length_append, preparedValues_length, literalWrittenValues_length]

def firstLiteralInitial {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (role : Role) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (firstLiteralMachine problem.verifier role)
    (endTape (BuilderControlActionSource.frame problem index remaining) inside outside)
def firstLiteralFinal {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (role : Role) (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) : WorkConfiguration :=
  {
    state := (firstLiteralMachine problem.verifier role).acceptState
    tape := endTape (firstLiteralValues problem index remaining role hRegion) inside
      (firstLiteralOutside problem index role outside hRegion) }

theorem firstLiteral_workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (role : Role) (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    workRunExact? (firstLiteralMachine problem.verifier role) (firstLiteralSteps problem index remaining role hRegion)
      (firstLiteralInitial problem index remaining role inside outside) =
      some (firstLiteralFinal problem index remaining role inside outside hRegion) := by
  have hPrepared := workRunExact problem index remaining inside outside hRegion
  simp only [initialConfiguration, finalConfiguration] at hPrepared
  have hLiteral := BuilderLiteralArgumentSource.workRunExact problem index remaining .control 15
    (preparedValues problem index hRegion) (plan role 0) (kind role) inside
    (finalOutside problem index outside hRegion) (preparedValues_length problem index hRegion)
  simp only [BuilderLiteralArgumentSource.initialConfiguration, BuilderLiteralArgumentSource.finalConfiguration] at hLiteral
  have h := chain_run (machine problem.verifier) (literalMachine problem.verifier role)
    (workSteps problem index remaining hRegion) (literalSteps problem index remaining role hRegion)
    _ _ _ hPrepared hLiteral
  simpa only [firstLiteralMachine, firstLiteralSteps, firstLiteralInitial, firstLiteralFinal,
    firstLiteralValues, firstLiteralRetained, firstLiteralOutside, literalWrittenValues,
    BuilderLiteralArgumentSource.finalValues, inputValues, List.append_assoc] using h

theorem firstLiteral_run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (role : Role) (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    run (compileWorkMachine (firstLiteralMachine problem.verifier role)) (6 * firstLiteralSteps problem index remaining role hRegion)
      (encodeWorkConfiguration (firstLiteralInitial problem index remaining role inside outside)) =
      encodeWorkConfiguration (firstLiteralFinal problem index remaining role inside outside hRegion) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (firstLiteral_workRunExact problem index remaining role inside outside hRegion)

def firstLiteralSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) : NatPolynomial :=
  BuilderLiteralArgumentSource.finalSpanBound verifier .control 15 (plan role 0) (kind role) (spanBound verifier)
def firstLiteralRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) (role : Role) : NatPolynomial :=
  .add (.add (rawTimeBound verifier) (.constant 6))
    (BuilderLiteralArgumentSource.rawTimeBound verifier .control 15 (plan role 0) (kind role) (spanBound verifier))

theorem firstLiteral_source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (role : Role)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (registerWord (firstLiteralValues problem index remaining role hRegion)).length ≤
        (firstLiteralSpanBound problem.verifier role).eval problem.input.length ∧
      6 * firstLiteralSteps problem index remaining role hRegion ≤
        (firstLiteralRawTimeBound problem.verifier role).eval problem.input.length := by
  have hPrepared := source_polynomial_bounds problem index remaining hBody hBalance hRegion
  have hLiteral := BuilderLiteralArgumentSource.source_polynomial_bounds problem index remaining .control 15
    (preparedValues problem index hRegion) (plan role 0) (kind role) (spanBound problem.verifier)
    (preparedValues_length problem index hRegion) hBody hBalance hRegion
    (retained_span_le problem index remaining hBody hBalance hRegion)
  constructor
  · simpa only [firstLiteralValues, firstLiteralRetained, literalWrittenValues, firstLiteralSpanBound,
      BuilderLiteralArgumentSource.finalValues, inputValues, List.append_assoc] using hLiteral.1
  · have hTime := hLiteral.2
    simp only [firstLiteralRawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant,
      firstLiteralSteps, literalSteps]
    omega

theorem firstLiteral_rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language)
    (role : Role) : (firstLiteralMachine verifier role).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _ (rules_pairwise_query_distinct verifier)
    (BuilderLiteralArgumentSource.rules_pairwise_query_distinct verifier .control 15 (plan role 0) (kind role))
    (noRuleAtAccept verifier)
theorem firstLiteral_noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language)
    (role : Role) : WorkMachineChain.NoRuleAtAccept (firstLiteralMachine verifier role) :=
  WorkMachineChain.noRuleAtAccept _ _
    (BuilderLiteralArgumentSource.noRuleAtAccept verifier .control 15 (plan role 0) (kind role))
theorem firstLiteral_noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language)
    (role : Role) : WorkMachineProgramGraph.NoRuleAt (firstLiteralMachine verifier role) (firstLiteralMachine verifier role).rejectState :=
  WorkMachineChain.noRuleAtAccept (machine verifier)
    {literalMachine verifier role with acceptState := (literalMachine verifier role).rejectState}
    (BuilderLiteralArgumentSource.noRuleAtReject verifier .control 15 (plan role 0) (kind role))
theorem firstLiteral_acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language)
    (role : Role) : (firstLiteralMachine verifier role).acceptState ≠ (firstLiteralMachine verifier role).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _
    (BuilderLiteralArgumentSource.acceptState_ne_rejectState verifier .control 15 (plan role 0) (kind role))

end PNP.Concrete.CookLevin.BuilderControlLiteralSources
