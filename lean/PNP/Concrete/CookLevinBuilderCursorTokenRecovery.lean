/-
Copyright (c) 2026 PNP Labs.

Actual cursor-token lookup followed by physical scratch erasure and cursor
recovery, preserving all six terminal observations. Source data, execution,
retained registers, nonempty scratch, blank exterior and polynomial bounds
are derived from the cursor. Only the existing body and balance invariants
are premises. Output emission, cursor advancement and the complete builder
loop remain separate downstream obligations.
-/
import PNP.Concrete.CookLevinBuilderCursorTokenLookup
import PNP.Concrete.CookLevinBuilderCursorRecovery
import PNP.Concrete.CookLevinBuilderDividerFootprint
import PNP.Concrete.WorkMachineTerminalHandoff

namespace PNP.Concrete.CookLevin.BuilderCursorTokenRecovery

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape inside count)
open BuilderClauseDividerOperands (quotient)
open BuilderRequestedPairLookup (BlankExterior storedCells)

def encodeResult : Option (Option CNFToken) → Fin 6
  | some (some .t) => 0
  | some (some .f) => 1
  | some none => 2
  | some (some .sep) => 3
  | some (some .finish) => 4
  | none => 5

def decodeState (state : Nat) : Option (Option CNFToken) :=
  if state = 0 then some (some .t)
  else if state = 1 then some (some .f)
  else if state = 2 then some none
  else if state = 3 then some (some .sep)
  else if state = 4 then some (some .finish)
  else none

theorem decode_encode (result : Option (Option CNFToken)) :
    decodeState (encodeResult result).val = result := by
  cases result with
  | none => rfl
  | some token =>
      cases token with
      | none => rfl
      | some token => cases token <;> rfl

theorem encodeResult_injective : Function.Injective encodeResult := by
  intro first second equality
  rw [← decode_encode first, ← decode_encode second, equality]

/-- This classifier is applied when assembling the finite terminal table,
not to the runtime input or any caller-supplied semantic certificate. -/
def classify (state : Nat) : Fin 6 :=
  encodeResult (BuilderCursorTokenLookup.observe {state := state, tape := {left := [], head := .blank, right := []}})

def observe (configuration : WorkConfiguration) : Option (Option CNFToken) :=
  decodeState configuration.state

theorem classify_observe (configuration : WorkConfiguration) (tape : WorkTape) :
    observe {state := (classify configuration.state).val, tape := tape} =
      BuilderCursorTokenLookup.observe configuration :=
  decode_encode _

def recoveryMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  BuilderCursorRecovery.machine (BuilderCursorRecovery.rootCount verifier)

def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineTerminalHandoff.machine (BuilderCursorTokenLookup.machine verifier) (recoveryMachine verifier) classify

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (BuilderCursorSource.cursorTape problem index remaining output)

def recoveryRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderCursorRecovery.rawTimePolynomial (BuilderCursorTokenLookup.canonicalSpanBound verifier)

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderCursorTokenLookup.rawTimeBound verifier) (.constant 12)) (recoveryRawTimeBound verifier)

def spanBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderCursorTokenLookup.spanBound verifier) (recoveryRawTimeBound verifier)

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineTerminalHandoff.rules_pairwise _ _ _
    (BuilderCursorTokenLookup.rules_pairwise_query_distinct verifier)
    (BuilderCursorRecovery.rules_pairwise_query_distinct _)
    (BuilderCursorRecovery.noRuleAtAccept _)

theorem noRuleAtResult {language : Language} (verifier : PolynomialTimeVerifier language) (result : Fin 6) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) result.val :=
  WorkMachineTerminalHandoff.noRuleAt_outcome _ _ _ result

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  noRuleAtResult verifier 0

theorem noRuleAtReject {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineProgramGraph.NoRuleAt (machine verifier) (machine verifier).rejectState :=
  noRuleAtResult verifier 1

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := by
  exact Nat.zero_ne_one

private theorem recovered_layout {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (outside : List WorkSymbol) :
    BuilderCursorRecovery.recoveredCursorTape problem index remaining output outside =
      BuilderRegisterAccess.sourceTape (BuilderTokenAppender.workspaceTape problem.input [] output).head
        (BuilderTokenAppender.workspaceTape problem.input [] output).right
        (registerWord (BuilderOperandRegisters.retainedValues problem index remaining)) outside := by
  unfold BuilderCursorRecovery.recoveredCursorTape BuilderBalancedCursor.outside
  rw [BuilderOperandRegisters.cursorWord_values]
  cases problem.input <;> rfl

/-- The original exterior is derived from initialization, not assumed blank. -/
theorem recovered_original_equivalent {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) (value : Nat) (scratch : List Nat)
    (outside : List WorkSymbol) (hBlank : BlankExterior outside) :
    WorkTape.BlankEquivalent
      (BuilderCursorRecovery.recoveredCursorTape problem index remaining output
        (BuilderCursorRecovery.clearedOutside value scratch outside))
      (BuilderCursorSource.cursorTape problem index remaining output) := by
  have hExpected : BlankExterior (BuilderCursorSource.preservedTail problem) := by
    rw [BuilderDividerFootprint.preservedTail_eq_nil]
    exact fun _ => rfl
  rw [recovered_layout, ← BuilderCursorRecovery.recovered_original_cursor problem index remaining output,
    recovered_layout]
  exact BuilderCursorRecovery.final_blankEquivalent
    (BuilderCursorRecovery.rootCount problem.verifier)
    (BuilderOperandRegisters.retainedValues problem index remaining) value scratch
    (BuilderTokenAppender.workspaceTape problem.input [] output).head
    (BuilderTokenAppender.workspaceTape problem.input [] output).right
    outside (BuilderCursorSource.preservedTail problem) hBlank hExpected

/-- Complete actual lookup and physical recovery. No source, route, scratch,
blank-frame, execution or polynomial certificate is a supplied premise. -/
theorem workRun_polynomial_lookup_recovered {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ (steps : Nat) (final : WorkConfiguration),
      workRunExact? (machine problem.verifier) steps (initialConfiguration problem index remaining output) = some final ∧
      final.state < 6 ∧
      WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) final.state ∧
      observe final = BuilderCursorTokenLookup.canonicalResult problem index ∧
      WorkTape.BlankEquivalent final.tape (BuilderCursorSource.cursorTape problem index remaining output) ∧
      storedCells final.tape ≤ (inside problem.input output).length + (spanBound problem.verifier).eval problem.input.length ∧
      6 * steps ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  obtain ⟨lookupSteps, values, outside, middle, hLookup, _, hNo, hObserve,
      hRoot, hFrame, hBlank, hCanonicalSpan, hLookupSpace, hLookupTime⟩ :=
    BuilderCursorTokenLookup.workRun_polynomial_lookup_with_frame problem index remaining output hBody hBalance
  obtain ⟨scratch, hValues⟩ := hRoot
  rw [hValues] at hFrame hCanonicalSpan
  let recoverySteps :=
    BuilderCursorRecovery.workSteps (BuilderOperandRegisters.retainedValues problem index remaining) (count problem) scratch
  have hCanonicalRecovery :=
    BuilderCursorRecovery.source_workRunExact problem index remaining output (count problem) scratch outside
  have hInitialEquivalent : WorkConfiguration.BlankEquivalent
      (workStartConfiguration (recoveryMachine problem.verifier) middle.tape)
      (workStartConfiguration (recoveryMachine problem.verifier)
        (endTape (BuilderOperandRegisters.retainedValues problem index remaining ++ [count problem] ++ scratch)
          (inside problem.input output) outside)) := ⟨rfl, hFrame⟩
  obtain ⟨recovered, hRecovery, hRecovered⟩ :=
    PNP.Concrete.workRunExact?_transport _ _ hInitialEquivalent hCanonicalRecovery
  have hRecoveredState : recovered.state = (recoveryMachine problem.verifier).acceptState := hRecovered.state
  have hRecoveredConfiguration : recovered =
      {state := (recoveryMachine problem.verifier).acceptState, tape := recovered.tape} := by
    rw [← hRecoveredState]
  have hRecoveryPrepared :
      workRunExact? (recoveryMachine problem.verifier) recoverySteps
        (workStartConfiguration (recoveryMachine problem.verifier) middle.tape) =
        some {state := (recoveryMachine problem.verifier).acceptState, tape := recovered.tape} := by
    rw [← hRecoveredConfiguration]
    exact hRecovery
  have hRun := WorkMachineTerminalHandoff.workRunExact
    (BuilderCursorTokenLookup.machine problem.verifier) (recoveryMachine problem.verifier) classify
    lookupSteps recoverySteps (BuilderCursorSource.cursorTape problem index remaining output) middle recovered.tape
    (BuilderCursorTokenLookup.rules_pairwise_query_distinct problem.verifier)
    (BuilderCursorRecovery.rules_pairwise_query_distinct _)
    (BuilderCursorRecovery.noRuleAtAccept _) hLookup hNo hRecoveryPrepared
  have hRecoverySteps := BuilderCursorRecovery.workSteps_le
    (BuilderOperandRegisters.retainedValues problem index remaining) (count problem) scratch
    ((BuilderCursorTokenLookup.canonicalSpanBound problem.verifier).eval problem.input.length) (by omega)
  have hRecoveryTime : 6 * recoverySteps ≤ (recoveryRawTimeBound problem.verifier).eval problem.input.length := by
    simp only [recoveryRawTimeBound, BuilderCursorRecovery.rawTimePolynomial,
      NatPolynomial.eval_mul, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    exact Nat.mul_le_mul_left 6 hRecoverySteps
  have hRecoveredSpace := BuilderRequestedPairLookup.workRun_storedCells _ _ _ _ hRecovery
  refine ⟨lookupSteps + 1 + recoverySteps + 1,
    {state := (classify middle.state).val, tape := recovered.tape}, hRun, (classify middle.state).isLt,
    noRuleAtResult problem.verifier (classify middle.state), ?_, ?_, ?_, ?_⟩
  · exact (classify_observe middle recovered.tape).trans hObserve
  · exact WorkTape.blankEquivalent_trans hRecovered.tape
      (recovered_original_equivalent problem index remaining output (count problem) scratch outside hBlank)
  · simp only [workStartConfiguration] at hRecoveredSpace
    simp only [spanBound, NatPolynomial.eval_add]
    omega
  · simp only [rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem uniform_polynomial_lookup_recovered {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hBody : quotient problem index < count problem)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    ∃ (rawSteps : Nat) (final : WorkConfiguration),
      rawSteps ≤ (rawTimeBound problem.verifier).eval problem.input.length ∧
      run (compileWorkMachine (machine problem.verifier)) rawSteps
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) = encodeWorkConfiguration final ∧
      final.state < 6 ∧
      WorkMachineProgramGraph.NoRuleAt (machine problem.verifier) final.state ∧
      observe final = BuilderCursorTokenLookup.canonicalResult problem index ∧
      WorkTape.BlankEquivalent final.tape (BuilderCursorSource.cursorTape problem index remaining output) ∧
      storedCells final.tape ≤ (inside problem.input output).length + (spanBound problem.verifier).eval problem.input.length := by
  obtain ⟨steps, final, hRun, hTag, hNo, hObserve, hTape, hSpace, hTime⟩ :=
    workRun_polynomial_lookup_recovered problem index remaining output hBody hBalance
  exact ⟨6 * steps, final, hTime, run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun,
    hTag, hNo, hObserve, hTape, hSpace⟩

end PNP.Concrete.CookLevin.BuilderCursorTokenRecovery
