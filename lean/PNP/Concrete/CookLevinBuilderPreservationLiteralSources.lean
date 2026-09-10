/-
Copyright (c) 2026 PNP Labs.

Fixed source-reference plans for all three canonical preservation literals.
The next-time value is computed by an actual register-expression machine.
No request, literal index, next-time answer or correctness certificate is
supplied to that machine. Payload packing and runtime diagonal dispatch remain
downstream obligations of the complete formula builder.
-/

import PNP.Concrete.CookLevinBuilderPreservationCoordinates

namespace PNP.Concrete.CookLevin.BuilderPreservationLiteralSources

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLiteralArgumentSource
open BuilderPreservationCoordinates
  (ofSource headRequest oldSymbolRequest newSymbolRequest source_radix_coordinates)

def headPlan (afterCount : Nat) : Plan .preservation afterCount :=
  fun field => match field.val with
  | 0 => .quotient
  | 1 => .digit ⟨2, by decide⟩
  | _ => .constant 0

def oldSymbolPlan (afterCount : Nat) : Plan .preservation afterCount :=
  fun field => match field.val with
  | 0 => .quotient
  | 1 => .digit ⟨1, by decide⟩
  | 3 => .digit ⟨0, by decide⟩
  | _ => .constant 0

/-- The first three retained registers are written by `nextTimeMachine`. -/
def newSymbolPlan (extraCount : Nat) : Plan .preservation (3 + extraCount) :=
  fun field => match field.val with
  | 0 => .retained ⟨2, by omega⟩
  | 1 => .digit ⟨1, by decide⟩
  | 3 => .digit ⟨0, by decide⟩
  | _ => .constant 0

def timeValue {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  referenceValue problem index .preservation [] (.quotient : Reference .preservation 0)

def nextTimeValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  [timeValue problem index, 1, timeValue problem index + 1]

theorem nextTimeValues_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (nextTimeValues problem index).length = 3 := rfl

theorem nextTimeValues_eq {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    nextTimeValues problem index =
      [(ofSource problem index hRegion).step.val, 1, (ofSource problem index hRegion).step.val + 1] := by
  have hTime := (source_radix_coordinates problem index hRegion).2
  simp only [nextTimeValues, timeValue, referenceValue, hTime]

theorem head_environment {language : Language} (problem : VerifierTableauProblem language)
    (index afterCount : Nat) (after : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    argumentEnvironment problem index .preservation after (headPlan afterCount) =
      (headRequest (ofSource problem index hRegion)).environment := by
  have hCoordinates := source_radix_coordinates problem index hRegion
  funext field
  rcases field with ⟨field, hField⟩
  have hCases : field = 0 ∨ field = 1 ∨ field = 2 ∨ field = 3 ∨
      field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 := by omega
  rcases hCases with h | h | h | h | h | h | h | h <;> subst field <;>
    simp only [argumentEnvironment, references, headPlan, referenceValue, sourceValue,
      hCoordinates.1, hCoordinates.2, List.getD_cons_zero, List.getD_cons_succ,
      headRequest, BuilderLiteralIndexExpression.Request.environment,
      VerifierTableauProblem.currentTime] <;> rfl

theorem oldSymbol_environment {language : Language} (problem : VerifierTableauProblem language)
    (index afterCount : Nat) (after : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    argumentEnvironment problem index .preservation after (oldSymbolPlan afterCount) =
      (oldSymbolRequest (ofSource problem index hRegion)).environment := by
  have hCoordinates := source_radix_coordinates problem index hRegion
  funext field
  rcases field with ⟨field, hField⟩
  have hCases : field = 0 ∨ field = 1 ∨ field = 2 ∨ field = 3 ∨
      field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 := by omega
  rcases hCases with h | h | h | h | h | h | h | h <;> subst field <;>
    simp only [argumentEnvironment, references, oldSymbolPlan, referenceValue, sourceValue,
      hCoordinates.1, hCoordinates.2, List.getD_cons_zero, List.getD_cons_succ,
      oldSymbolRequest, BuilderLiteralIndexExpression.Request.environment,
      VerifierTableauProblem.currentTime] <;>
    first | rfl | exact (BuilderPreservationCoordinates.symbol_code _).symm

theorem newSymbol_environment {language : Language} (problem : VerifierTableauProblem language)
    (index extraCount : Nat) (extra : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    argumentEnvironment problem index .preservation (nextTimeValues problem index ++ extra)
        (newSymbolPlan extraCount) =
      (newSymbolRequest (ofSource problem index hRegion)).environment := by
  have hCoordinates := source_radix_coordinates problem index hRegion
  have hTime := nextTimeValues_eq problem index hRegion
  funext field
  rcases field with ⟨field, hField⟩
  have hCases : field = 0 ∨ field = 1 ∨ field = 2 ∨ field = 3 ∨
      field = 4 ∨ field = 5 ∨ field = 6 ∨ field = 7 := by omega
  rcases hCases with h | h | h | h | h | h | h | h <;> subst field <;>
    simp only [argumentEnvironment, references, newSymbolPlan, referenceValue, sourceValue,
      hCoordinates.1, hCoordinates.2, hTime, List.cons_append, List.nil_append,
      List.getD_cons_zero, List.getD_cons_succ, newSymbolRequest,
      BuilderLiteralIndexExpression.Request.environment, VerifierTableauProblem.nextTime] <;>
    first | rfl | exact (BuilderPreservationCoordinates.symbol_code _).symm

theorem head_index_eq {language : Language} (problem : VerifierTableauProblem language)
    (index afterCount : Nat) (after : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression .head)
      (argumentEnvironment problem index .preservation after (headPlan afterCount)) =
        (headRequest (ofSource problem index hRegion)).index := by
  rw [head_environment problem index afterCount after hRegion]
  exact BuilderLiteralIndexExpression.eval_eq_index (headRequest (ofSource problem index hRegion))

theorem oldSymbol_index_eq {language : Language} (problem : VerifierTableauProblem language)
    (index afterCount : Nat) (after : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression .symbol)
      (argumentEnvironment problem index .preservation after (oldSymbolPlan afterCount)) =
        (oldSymbolRequest (ofSource problem index hRegion)).index := by
  rw [oldSymbol_environment problem index afterCount after hRegion]
  exact BuilderLiteralIndexExpression.eval_eq_index (oldSymbolRequest (ofSource problem index hRegion))

theorem newSymbol_index_eq {language : Language} (problem : VerifierTableauProblem language)
    (index extraCount : Nat) (extra : List Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    BuilderRegisterExpression.eval (BuilderLiteralIndexExpression.expression .symbol)
      (argumentEnvironment problem index .preservation (nextTimeValues problem index ++ extra)
        (newSymbolPlan extraCount)) =
      (newSymbolRequest (ofSource problem index hRegion)).index := by
  rw [newSymbol_environment problem index extraCount extra hRegion]
  exact BuilderLiteralIndexExpression.eval_eq_index (newSymbolRequest (ofSource problem index hRegion))

def nextTimeExpression {language : Language} (verifier : PolynomialTimeVerifier language) :
    BuilderRegisterExpression.Expr (inputCount verifier .preservation 0) :=
  .binary .add (field verifier .preservation 0 .quotient).expression (.constant 1)

theorem nextTime_expression_values {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) :
    BuilderRegisterExpression.values (nextTimeExpression problem.verifier)
      (environment problem index remaining .preservation 0 []) = nextTimeValues problem index := by
  have hRead := field_eval problem index remaining .preservation 0 [] .quotient
  change BuilderRegisterExpression.eval (field problem.verifier .preservation 0 .quotient).expression
    (environment problem index remaining .preservation 0 []) = timeValue problem index at hRead
  rw [nextTimeExpression, BuilderRegisterExpression.values, BuilderRegisterPack.Field.expression_values]
  change [BuilderRegisterExpression.eval (field problem.verifier .preservation 0 .quotient).expression
    (environment problem index remaining .preservation 0 [])] ++ [1] ++
      [BuilderRegisterExpression.eval (field problem.verifier .preservation 0 .quotient).expression
        (environment problem index remaining .preservation 0 []) + 1] = _
  rw [hRead]
  rfl

def nextTimeMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  BuilderRegisterExpression.machine (nextTimeExpression verifier) 0

def nextTimeSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Nat :=
  BuilderRegisterExpression.workSteps (nextTimeExpression problem.verifier)
    (environment problem index remaining .preservation 0 []) []

def nextTimeInitial {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (nextTimeMachine problem.verifier)
    (endTape (inputValues problem index remaining .preservation []) inside outside)

def nextTimeFinal {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  { state := (nextTimeMachine problem.verifier).acceptState
    tape := endTape (inputValues problem index remaining .preservation [] ++ nextTimeValues problem index)
      inside (outside.drop (registerWord (nextTimeValues problem index)).length) }

theorem nextTime_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) :
    workRunExact? (nextTimeMachine problem.verifier) (nextTimeSteps problem index remaining)
      (nextTimeInitial problem index remaining inside outside) =
        some (nextTimeFinal problem index remaining inside outside) := by
  have h := BuilderRegisterExpression.workRunExact (nextTimeExpression problem.verifier) 0 []
    (environment problem index remaining .preservation 0 []) [] inside outside rfl
  simpa only [nextTimeMachine, nextTimeSteps, nextTimeInitial, nextTimeFinal,
    BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
    environment_values problem index remaining .preservation 0 [] rfl, nextTime_expression_values,
    List.nil_append, List.append_nil] using h

theorem nextTime_run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (nextTimeMachine problem.verifier)) (6 * nextTimeSteps problem index remaining)
      (encodeWorkConfiguration (nextTimeInitial problem index remaining inside outside)) =
        encodeWorkConfiguration (nextTimeFinal problem index remaining inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (nextTime_workRunExact problem index remaining inside outside)

def nextTimeInputBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  inputBound verifier .preservation (.constant 0)

def nextTimeSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial (nextTimeExpression verifier) (nextTimeInputBound verifier)

def nextTimeRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterExpression.rawTimePolynomial (nextTimeExpression verifier) (nextTimeInputBound verifier)

theorem nextTime_source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    (registerWord (inputValues problem index remaining .preservation [] ++ nextTimeValues problem index)).length ≤
      (nextTimeSpanBound problem.verifier).eval problem.input.length ∧
    6 * nextTimeSteps problem index remaining ≤
      (nextTimeRawTimeBound problem.verifier).eval problem.input.length := by
  have hInput := input_span_le problem index remaining .preservation [] (.constant 0) hBody hBalance hRegion (Nat.le_refl 0)
  have hEnvironment :
      (registerWord ([] ++ List.ofFn (environment problem index remaining .preservation 0 []) ++ [])).length ≤
        (nextTimeInputBound problem.verifier).eval problem.input.length := by
    simpa only [List.nil_append, List.append_nil, nextTimeInputBound,
      environment_values problem index remaining .preservation 0 [] rfl] using hInput
  have h := BuilderRegisterExpression.source_polynomial_bounds (nextTimeExpression problem.verifier)
    (nextTimeInputBound problem.verifier) problem.input.length []
    (environment problem index remaining .preservation 0 []) [] hEnvironment
  simpa only [List.nil_append, List.append_nil, nextTimeSpanBound, nextTimeRawTimeBound, nextTimeSteps,
    environment_values problem index remaining .preservation 0 [] rfl, nextTime_expression_values] using h

theorem nextTime_rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (nextTimeMachine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  BuilderRegisterExpression.rules_pairwise_query_distinct (nextTimeExpression verifier) 0

theorem nextTime_noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (nextTimeMachine verifier) :=
  BuilderRegisterExpression.noRuleAtAccept (nextTimeExpression verifier) 0

theorem nextTime_noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (nextTimeMachine verifier) (nextTimeMachine verifier).rejectState :=
  BuilderRegisterExpression.noRuleAtReject (nextTimeExpression verifier) 0

theorem nextTime_acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (nextTimeMachine verifier).acceptState ≠ (nextTimeMachine verifier).rejectState :=
  BuilderRegisterExpression.acceptState_ne_rejectState (nextTimeExpression verifier) 0


/-- Execute next-time arithmetic before reading it in the conclusion plan. -/
def newSymbolMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (nextTimeMachine verifier)
    (machine verifier .preservation 3 (newSymbolPlan 0) .symbol)

def newSymbolSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Nat :=
  nextTimeSteps problem index remaining + 1 +
    workSteps problem index remaining .preservation 3 (nextTimeValues problem index) (newSymbolPlan 0) .symbol

def newSymbolInitial {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (newSymbolMachine problem.verifier)
    (endTape (inputValues problem index remaining .preservation []) inside outside)

def newSymbolFinal {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  { state := (newSymbolMachine problem.verifier).acceptState
    tape := (finalConfiguration problem index remaining .preservation 3 (nextTimeValues problem index)
      (newSymbolPlan 0) .symbol inside (outside.drop (registerWord (nextTimeValues problem index)).length)).tape }

private theorem chain_run (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some { state := first.acceptState, tape := middle })
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) =
      some { state := second.acceptState, tape := final }) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some { state := (WorkMachineChain.machine first second).acceptState, tape := final } :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

theorem newSymbol_workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) :
    workRunExact? (newSymbolMachine problem.verifier) (newSymbolSteps problem index remaining)
      (newSymbolInitial problem index remaining inside outside) =
        some (newSymbolFinal problem index remaining inside outside) := by
  have hFirst := nextTime_workRunExact problem index remaining inside outside
  have hSecond := workRunExact problem index remaining .preservation 3 (nextTimeValues problem index)
    (newSymbolPlan 0) .symbol inside (outside.drop (registerWord (nextTimeValues problem index)).length)
    (nextTimeValues_length problem index)
  simp only [nextTimeInitial, nextTimeFinal, BuilderLiteralArgumentSource.initialConfiguration,
    BuilderLiteralArgumentSource.finalConfiguration, inputValues, List.append_nil] at hFirst hSecond
  have hAll := chain_run (nextTimeMachine problem.verifier)
    (machine problem.verifier .preservation 3 (newSymbolPlan 0) .symbol)
    (nextTimeSteps problem index remaining)
    (workSteps problem index remaining .preservation 3 (nextTimeValues problem index) (newSymbolPlan 0) .symbol)
    _ _ _ hFirst hSecond
  simpa only [newSymbolMachine, newSymbolSteps, newSymbolInitial, newSymbolFinal,
    BuilderLiteralArgumentSource.finalConfiguration, inputValues, List.append_nil] using hAll

theorem newSymbol_run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (newSymbolMachine problem.verifier)) (6 * newSymbolSteps problem index remaining)
      (encodeWorkConfiguration (newSymbolInitial problem index remaining inside outside)) =
        encodeWorkConfiguration (newSymbolFinal problem index remaining inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (newSymbol_workRunExact problem index remaining inside outside)

theorem newSymbol_final_index {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    ∃ leadingValues, finalValues problem index remaining .preservation (nextTimeValues problem index)
      (newSymbolPlan 0) .symbol =
        leadingValues ++ [(newSymbolRequest (ofSource problem index hRegion)).index] := by
  have hIndex := newSymbol_index_eq problem index 0 [] hRegion
  simp only [List.append_nil] at hIndex
  refine ⟨inputValues problem index remaining .preservation (nextTimeValues problem index) ++
    List.ofFn (argumentEnvironment problem index .preservation (nextTimeValues problem index) (newSymbolPlan 0)) ++
    BuilderRegisterExpression.prefixValues (BuilderLiteralIndexExpression.expression .symbol)
      (argumentEnvironment problem index .preservation (nextTimeValues problem index) (newSymbolPlan 0)), ?_⟩
  rw [final_index_register, hIndex]

def newSymbolSpanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  finalSpanBound verifier .preservation 3 (newSymbolPlan 0) .symbol (nextTimeSpanBound verifier)

def newSymbolRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (nextTimeRawTimeBound verifier) (.constant 6))
    (rawTimeBound verifier .preservation 3 (newSymbolPlan 0) .symbol (nextTimeSpanBound verifier))

theorem newSymbol_source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .preservation) :
    (registerWord (finalValues problem index remaining .preservation (nextTimeValues problem index)
      (newSymbolPlan 0) .symbol)).length ≤ (newSymbolSpanBound problem.verifier).eval problem.input.length ∧
    6 * newSymbolSteps problem index remaining ≤
      (newSymbolRawTimeBound problem.verifier).eval problem.input.length := by
  have hNext := nextTime_source_polynomial_bounds problem index remaining hBody hBalance hRegion
  have hRetained : (registerWord (nextTimeValues problem index)).length ≤
      (nextTimeSpanBound problem.verifier).eval problem.input.length := by
    have h := hNext.1
    rw [registerWord_append, List.length_append] at h
    omega
  have hLiteral := source_polynomial_bounds problem index remaining .preservation 3 (nextTimeValues problem index)
    (newSymbolPlan 0) .symbol (nextTimeSpanBound problem.verifier)
    (nextTimeValues_length problem index) hBody hBalance hRegion hRetained
  constructor
  · exact hLiteral.1
  · simp only [newSymbolSteps, newSymbolRawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem newSymbol_rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (newSymbolMachine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (nextTime_rules_pairwise_query_distinct verifier)
    (rules_pairwise_query_distinct verifier .preservation 3 (newSymbolPlan 0) .symbol)
    (nextTime_noRuleAtAccept verifier)

theorem newSymbol_noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (newSymbolMachine verifier) :=
  WorkMachineChain.noRuleAtAccept _ _ (noRuleAtAccept verifier .preservation 3 (newSymbolPlan 0) .symbol)

private theorem chain_noRuleAtReject (first second : WorkMachine)
    (hSecond : WorkMachineProgramGraph.NoRuleAt second second.rejectState) :
    WorkMachineProgramGraph.NoRuleAt (WorkMachineChain.machine first second)
      (WorkMachineChain.machine first second).rejectState :=
  WorkMachineChain.noRuleAtAccept first { second with acceptState := second.rejectState } hSecond

theorem newSymbol_noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (newSymbolMachine verifier) (newSymbolMachine verifier).rejectState :=
  chain_noRuleAtReject (nextTimeMachine verifier)
    (machine verifier .preservation 3 (newSymbolPlan 0) .symbol)
    (noRuleAtReject verifier .preservation 3 (newSymbolPlan 0) .symbol)

theorem newSymbol_acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (newSymbolMachine verifier).acceptState ≠ (newSymbolMachine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _
    (acceptState_ne_rejectState verifier .preservation 3 (newSymbolPlan 0) .symbol)

end PNP.Concrete.CookLevin.BuilderPreservationLiteralSources
