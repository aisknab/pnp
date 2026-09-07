/-
Copyright (c) 2026 PNP Labs.

Source-derived control-action selection for every canonical transition slot.
The finite table is compiled from the verifier alone. The current state and
read symbol are physically read from the existing radix frame; an expression
writes their table key and a literal lookup writes target state, symbol and move.
No action, lookup result or correctness certificate is supplied at runtime.

Head movement and complete implication payload construction remain downstream.
-/

import PNP.Concrete.CookLevinBuilderControlCoordinates
import PNP.Concrete.CookLevinBuilderRegisterTable

namespace PNP.Concrete.CookLevin.BuilderControlActionSource

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLiteralArgumentSource
  (Reference field field_eval inputValues inputCount environment environment_values referenceValue)

def moveCode : HeadMove → Nat
  | .stay => 0
  | .left => 1
  | .right => 2

/-- Only a carrier for the verifier's input-independent transition function. -/
def fixedProblem {language : Language} (verifier : PolynomialTimeVerifier language) : VerifierTableauProblem language :=
  ⟨verifier, []⟩

def stateCount {language : Language} (verifier : PolynomialTimeVerifier language) : Nat :=
  (fixedProblem verifier).dimensions.stateBound

theorem stateCount_eq {language : Language} (problem : VerifierTableauProblem language) :
    stateCount problem.verifier = problem.dimensions.stateBound := rfl

def rowValues {language : Language} (problem : VerifierTableauProblem language)
    (state : Fin problem.dimensions.stateBound) (symbol : TapeSymbol) : List Nat :=
  let action := problem.localAction state symbol
  [action.targetState.val, VariableLayout.tapeSymbolCode action.writeSymbol, moveCode action.move]

theorem rowValues_input_independent {language : Language} (problem : VerifierTableauProblem language)
    (state : Fin problem.dimensions.stateBound) (symbol : TapeSymbol) :
    rowValues (fixedProblem problem.verifier) state symbol = rowValues problem state symbol := by
  have hMachine : (fixedProblem problem.verifier).rawMachine = problem.rawMachine := rfl
  by_cases hHalt : (state.val == problem.rawMachine.acceptState ||
      state.val == problem.rawMachine.rejectState) = true
  · simp only [rowValues, VerifierTableauProblem.localAction, hMachine, if_pos hHalt]
  · simp only [rowValues, VerifierTableauProblem.localAction, hMachine, if_neg hHalt]
    split
    next hFixed =>
      split
      next hRule => rfl
      next selected hRule =>
        have h := hFixed.symm.trans hRule
        cases h
    next selected hFixed =>
      split
      next hRule =>
        have h := hFixed.symm.trans hRule
        cases h
      next selected' hRule =>
        have h : selected = selected' := Option.some.inj (hFixed.symm.trans hRule)
        subst selected'
        rfl

theorem rowValues_length {language : Language} (problem : VerifierTableauProblem language)
    (state : Fin problem.dimensions.stateBound) (symbol : TapeSymbol) :
    (rowValues problem state symbol).length = 3 := rfl

def tableRow {language : Language} (verifier : PolynomialTimeVerifier language)
    (key : Fin (stateCount verifier * 3)) : List Nat :=
  rowValues (fixedProblem verifier)
    ⟨key.val / 3, (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2 key.isLt⟩
    (BuilderControlCoordinates.symbol ⟨key.val % 3, Nat.mod_lt _ (by decide)⟩)

def table {language : Language} (verifier : PolynomialTimeVerifier language) : List (List Nat) :=
  List.ofFn (tableRow verifier)

theorem table_length {language : Language} (verifier : PolynomialTimeVerifier language) :
    (table verifier).length = stateCount verifier * 3 := by
  simp only [table, List.length_ofFn]

theorem key_lt {language : Language} (problem : VerifierTableauProblem language)
    (state : Fin problem.dimensions.stateBound) (code : Fin 3) :
    state.val * 3 + code.val < (table problem.verifier).length := by
  rw [table_length, stateCount_eq]
  have hState := Nat.mul_le_mul_right 3 (Nat.succ_le_of_lt state.isLt)
  have hCode := code.isLt
  omega

theorem table_at {language : Language} (problem : VerifierTableauProblem language)
    (state : Fin problem.dimensions.stateBound) (code : Fin 3) :
    (table problem.verifier)[state.val * 3 + code.val]'(key_lt problem state code) =
      rowValues problem state (BuilderControlCoordinates.symbol code) := by
  have hCode := code.isLt
  have hDiv : (state.val * 3 + code.val) / 3 = state.val := by omega
  have hMod : (state.val * 3 + code.val) % 3 = code.val := by omega
  simp only [table, List.getElem_ofFn, tableRow, hDiv, hMod]
  exact rowValues_input_independent problem state (BuilderControlCoordinates.symbol code)

def stateReference : Reference .control 0 := .digit ⟨2, by decide⟩
def symbolReference : Reference .control 0 := .digit ⟨1, by decide⟩

def stateValue {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  referenceValue problem index .control [] stateReference

def symbolValue {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  referenceValue problem index .control [] symbolReference

def keyValue {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : Nat :=
  stateValue problem index * 3 + symbolValue problem index

def keyExpression {language : Language} (verifier : PolynomialTimeVerifier language) :
    BuilderRegisterExpression.Expr (inputCount verifier .control 0) :=
  .binary .add
    (.binary .mul (field verifier .control 0 stateReference).expression (.constant 3))
    (field verifier .control 0 symbolReference).expression

def keyPrefix {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  [stateValue problem index, 3, stateValue problem index * 3, symbolValue problem index]

def keyValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  keyPrefix problem index ++ [keyValue problem index]

theorem key_expression_values {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) :
    BuilderRegisterExpression.values (keyExpression problem.verifier) (environment problem index remaining .control 0 []) =
      keyValues problem index := by
  have hState : BuilderRegisterExpression.eval (field problem.verifier .control 0 stateReference).expression
      (environment problem index remaining .control 0 []) = stateValue problem index :=
    field_eval problem index remaining .control 0 [] stateReference
  have hSymbol : BuilderRegisterExpression.eval (field problem.verifier .control 0 symbolReference).expression
      (environment problem index remaining .control 0 []) = symbolValue problem index :=
    field_eval problem index remaining .control 0 [] symbolReference
  simp only [keyExpression, BuilderRegisterExpression.values, BuilderRegisterPack.Field.expression_values,
    BuilderRegisterExpression.eval, RegisterBinary.value, hState, hSymbol,
    BuilderRegisterPack.Field.eval, field_eval, stateValue, symbolValue,
    keyValues, keyPrefix, keyValue, List.cons_append, List.nil_append]

theorem keyValues_length {language : Language} (problem : VerifierTableauProblem language) (index : Nat) :
    (keyValues problem index).length = 5 := rfl

theorem source_values {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    stateValue problem index = (BuilderControlCoordinates.ofSource problem index hRegion).state.val ∧
      symbolValue problem index = (BuilderControlCoordinates.ofSource problem index hRegion).readCode.val := by
  have h := (BuilderControlCoordinates.source_radix_coordinates problem index hRegion).1
  simp only [stateValue, symbolValue, referenceValue, stateReference, symbolReference, h,
    List.getD_cons_zero, List.getD_cons_succ]
  exact ⟨True.intro, True.intro⟩

theorem source_key_lt {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    keyValue problem index < (table problem.verifier).length := by
  have h := source_values problem index hRegion
  simpa only [keyValue, h.1, h.2] using
    key_lt problem (BuilderControlCoordinates.ofSource problem index hRegion).state
      (BuilderControlCoordinates.ofSource problem index hRegion).readCode

def selectedValues {language : Language} (problem : VerifierTableauProblem language) (index : Nat) : List Nat :=
  (BuilderRegisterTable.lookup (table problem.verifier) 0 (keyValue problem index)).getD []

theorem selected_canonical {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    selectedValues problem index =
      rowValues problem (BuilderControlCoordinates.ofSource problem index hRegion).state
        (BuilderControlCoordinates.symbol (BuilderControlCoordinates.ofSource problem index hRegion).readCode) := by
  have h := BuilderRegisterTable.lookup_at (table problem.verifier) 0 (keyValue problem index)
    (source_key_lt problem index hRegion)
  simp only [Nat.zero_add] at h
  simp only [selectedValues, h, Option.getD_some]
  have hCoordinates := source_values problem index hRegion
  simp only [keyValue, hCoordinates.1, hCoordinates.2]
  exact table_at problem _ _

def frame {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  inputValues problem index remaining .control []

def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderRegisterExpression.machine (keyExpression verifier) 0)
    (BuilderRegisterTable.machine (table verifier) 0)

def keySteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  BuilderRegisterExpression.workSteps (keyExpression problem.verifier)
    (environment problem index remaining .control 0 []) []

def workSteps {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : Nat :=
  keySteps problem index remaining + 1 +
    BuilderRegisterTable.workSteps (table problem.verifier) 0 (keyValue problem index)

def finalValues {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat) : List Nat :=
  frame problem index remaining ++ keyValues problem index ++ selectedValues problem index

def finalOutside {language : Language} (problem : VerifierTableauProblem language) (index : Nat)
    (outside : List WorkSymbol) : List WorkSymbol :=
  outside.drop ((registerWord (keyValues problem index)).length +
    BuilderRegisterTable.rowSpan (selectedValues problem index))

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (endTape (frame problem index remaining) inside outside)

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  { state := (machine problem.verifier).acceptState
    tape := endTape (finalValues problem index remaining) inside (finalOutside problem index outside) }

theorem key_workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? (BuilderRegisterExpression.machine (keyExpression problem.verifier) 0)
      (keySteps problem index remaining)
      (workStartConfiguration (BuilderRegisterExpression.machine (keyExpression problem.verifier) 0)
        (endTape (frame problem index remaining) inside outside)) =
      some {
        state := (BuilderRegisterExpression.machine (keyExpression problem.verifier) 0).acceptState
        tape := endTape (frame problem index remaining ++ keyValues problem index) inside
          (outside.drop (registerWord (keyValues problem index)).length) } := by
  have h := BuilderRegisterExpression.workRunExact (keyExpression problem.verifier) 0 []
    (environment problem index remaining .control 0 []) [] inside outside rfl
  have hFrame := environment_values problem index remaining .control 0 [] rfl
  simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
    List.nil_append, List.append_nil, hFrame, frame, key_expression_values, keySteps] using h

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

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
      (initialConfiguration problem index remaining inside outside) =
      some (finalConfiguration problem index remaining inside outside) := by
  have hKey := key_workRunExact problem index remaining inside outside
  have hLookup := BuilderRegisterTable.lookup_at (table problem.verifier) 0 (keyValue problem index)
    (source_key_lt problem index hRegion)
  simp only [Nat.zero_add] at hLookup
  have hSelected : selectedValues problem index =
      (table problem.verifier)[keyValue problem index]'(source_key_lt problem index hRegion) := by
    simp only [selectedValues, hLookup, Option.getD_some]
  have hTable := BuilderRegisterTable.selected_workRunExact (table problem.verifier) 0 (keyValue problem index)
    (source_key_lt problem index hRegion) (frame problem index remaining ++ keyPrefix problem index) inside
    (outside.drop (registerWord (keyValues problem index)).length)
  simp only [BuilderRegisterTable.initialConfiguration, Nat.zero_add, ← hSelected, List.append_assoc,
    keyValues, List.drop_drop] at hTable
  have h := chain_run
    (BuilderRegisterExpression.machine (keyExpression problem.verifier) 0)
    (BuilderRegisterTable.machine (table problem.verifier) 0)
    (keySteps problem index remaining)
    (BuilderRegisterTable.workSteps (table problem.verifier) 0 (keyValue problem index))
    _ _ _ hKey hTable
  simpa only [machine, workSteps, initialConfiguration, finalConfiguration, finalValues,
    finalOutside, keyValues, List.append_assoc, BuilderRegisterTable.rowSpan] using h

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language) (index remaining : Nat)
    (inside outside : List WorkSymbol)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
      (encodeWorkConfiguration (initialConfiguration problem index remaining inside outside)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining inside outside hRegion)

def inputBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderLiteralArgumentSource.inputBound verifier .control (.constant 0)

def keySpanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial (keyExpression verifier) (inputBound verifier)

def spanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderRegisterTable.spanPolynomial (table verifier) (keySpanBound verifier)

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderRegisterExpression.rawTimePolynomial (keyExpression verifier) (inputBound verifier)) (.constant 6))
    (BuilderRegisterTable.rawTimePolynomial (table verifier) 0)

theorem source_polynomial_bounds {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBody : BuilderClauseDividerOperands.quotient problem index < BuilderDividerOperands.count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem)
    (hRegion : BuilderConstraintRegionSource.selectedRegion problem index = some .control) :
    (registerWord (finalValues problem index remaining)).length ≤
        (spanBound problem.verifier).eval problem.input.length ∧
      6 * workSteps problem index remaining ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hInput := BuilderLiteralArgumentSource.input_span_le problem index remaining .control [] (.constant 0)
    hBody hBalance hRegion (Nat.le_refl 0)
  have hFrame := environment_values problem index remaining .control 0 [] rfl
  have hStart : (registerWord ([] ++ List.ofFn (environment problem index remaining .control 0 []) ++ [])).length ≤
      (inputBound problem.verifier).eval problem.input.length := by
    simpa only [List.nil_append, List.append_nil, hFrame, inputBound] using hInput
  have hKey := BuilderRegisterExpression.source_polynomial_bounds (keyExpression problem.verifier)
    (inputBound problem.verifier) problem.input.length [] (environment problem index remaining .control 0 []) [] hStart
  simp only [List.nil_append, List.append_nil, hFrame, key_expression_values] at hKey
  have hTable := BuilderRegisterTable.source_polynomial_bounds (table problem.verifier) 0 (keyValue problem index)
    (frame problem index remaining ++ keyPrefix problem index) (keySpanBound problem.verifier) problem.input.length
    (by simpa only [List.append_assoc, keyValues, keySpanBound, frame] using hKey.1)
  constructor
  · simpa only [List.append_assoc, keyValues, selectedValues, finalValues, spanBound] using hTable.1
  · have hTime := hTable.2
    simp only [rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant, workSteps, keySteps]
    omega

theorem final_exterior_length_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration problem index remaining inside outside).tape.left.length ≤ outside.length := by
  simp only [finalConfiguration, endTape, finalOutside, List.length_drop]
  omega

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderRegisterExpression.rules_pairwise_query_distinct (keyExpression verifier) 0)
    (BuilderRegisterTable.rules_pairwise_query_distinct (table verifier) 0)
    (BuilderRegisterExpression.noRuleAtAccept (keyExpression verifier) 0)

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  WorkMachineChain.noRuleAtAccept _ _ (BuilderRegisterTable.noRuleAtAccept (table verifier) 0)

theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  WorkMachineChain.noRuleAtAccept (BuilderRegisterExpression.machine (keyExpression verifier) 0)
    { BuilderRegisterTable.machine (table verifier) 0 with
      acceptState := (BuilderRegisterTable.machine (table verifier) 0).rejectState }
    (BuilderRegisterTable.noRuleAtReject (table verifier) 0)

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _
    (BuilderRegisterTable.acceptState_ne_rejectState (table verifier) 0)

end PNP.Concrete.CookLevin.BuilderControlActionSource
