/-
Copyright (c) 2026 PNP Labs.

One verifier-fixed finite machine initializes the header and registers from
raw work input and executes the entire source-derived physical body loop.
No prepared workspace, token request or execution premise is supplied.
All initialization, loop and bridge costs are bounded in original input size.

The resulting token stream is still named by its exact recursive schedule
specification. Canonical formula equality, FunctionProgram input/output
adapters and the packaged polynomial reduction remain separate obligations.
-/
import PNP.Concrete.CookLevinBuilderCursorLoop

namespace PNP.Concrete.CookLevin.BuilderRawInputLoop

open PipelineTape
open PipelineStateNamespace (renameConfiguration)
open WorkMachineProgramGraph (NoRuleAt)
open BuilderFullScheduleCursorController (bodySlotCount bodySlotCountPolynomial)

def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderInitialization.machine verifier) (BuilderCursorLoop.machine verifier)

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier) (rawInputWorkTape problem.input)

def outputTokens {language : Language} (problem : VerifierTableauProblem language) : List CNFToken :=
  BuilderCursorLoop.completeOutput problem 0 (bodySlotCount problem - 1) (encodeUnaryTokens problem.FormulaWidth)

def outputBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (formulaWidthPolynomial verifier) (.constant 1)) (bodySlotCountPolynomial verifier)

def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderInitialization.rawTimeBound verifier) (.constant 6))
    (.mul (bodySlotCountPolynomial verifier)
      (.add (BuilderCursorLoop.stepPolynomial verifier) (.mul (.constant 12) (outputBound verifier))))

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderInitialization.rules_pairwise_query_distinct verifier)
    (BuilderCursorLoop.rules_pairwise_query_distinct verifier)
    (BuilderInitialization.noRuleAtAccept verifier)

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    NoRuleAt (machine verifier) (machine verifier).acceptState :=
  WorkMachineChain.noRuleAtAccept _ _ (BuilderCursorLoop.noRuleAtAccept verifier)

theorem acceptState_ne_rejectState {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState
    (BuilderInitialization.machine verifier) (BuilderCursorLoop.machine verifier)
    (BuilderCursorLoop.acceptState_ne_rejectState verifier)

theorem initialConfiguration_tape {language : Language} (problem : VerifierTableauProblem language) :
    (initialConfiguration problem).tape = rawInputWorkTape problem.input := rfl

theorem outputBound_eval {language : Language} (problem : VerifierTableauProblem language) :
    (outputBound problem.verifier).eval problem.input.length =
      problem.FormulaWidth + 1 + bodySlotCount problem := by
  change (formulaWidthPolynomial problem.verifier).eval problem.input.length + 1 +
    bodySlotCount problem = _
  have hWidth := problem.formulaWidthPolynomial_eval
  simp only [BitString.size] at hWidth
  rw [hWidth]

theorem rawTimeBound_eval {language : Language} (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderInitialization.rawTimeBound problem.verifier).eval problem.input.length + 6 +
        bodySlotCount problem * ((BuilderCursorLoop.stepPolynomial problem.verifier).eval problem.input.length +
          12 * (problem.FormulaWidth + 1 + bodySlotCount problem)) := by
  change (BuilderInitialization.rawTimeBound problem.verifier).eval problem.input.length + 6 +
    bodySlotCount problem * ((BuilderCursorLoop.stepPolynomial problem.verifier).eval problem.input.length +
      12 * (outputBound problem.verifier).eval problem.input.length) = _
  rw [outputBound_eval]

theorem outputTokens_length_le {language : Language} (problem : VerifierTableauProblem language) :
    (outputTokens problem).length ≤ (outputBound problem.verifier).eval problem.input.length := by
  have hPositive := BuilderFullScheduleCursorController.bodySlotCount_positive problem
  have hLength := BuilderCursorLoop.completeOutput_length_le problem 0 (bodySlotCount problem - 1)
    (encodeUnaryTokens problem.FormulaWidth)
  rw [encodeUnaryTokens_length] at hLength
  rw [outputBound_eval]
  change (BuilderCursorLoop.completeOutput problem 0 (bodySlotCount problem - 1)
    (encodeUnaryTokens problem.FormulaWidth)).length ≤ _
  omega

/-- Physical initialization and the entire emitting loop execute from the
original work input, with no precondition and an original-input-only bound. -/
theorem workRun_from_raw {language : Language} (problem : VerifierTableauProblem language) :
    ∃ (steps : Nat) (final : WorkConfiguration),
      workRunExact? (machine problem.verifier) steps (initialConfiguration problem) = some final ∧
      final.state = (machine problem.verifier).acceptState ∧
      WorkTape.BlankEquivalent final.tape
        (BuilderCursorSource.cursorTape problem (bodySlotCount problem) 0 (outputTokens problem)) ∧
      6 * steps ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hPositive := BuilderFullScheduleCursorController.bodySlotCount_positive problem
  have hCount : (bodySlotCount problem - 1) + 1 = bodySlotCount problem := by omega
  obtain ⟨loopSteps, loopFinal, hLoop, hAccept, hTape, hTime⟩ :=
    BuilderCursorLoop.workRun_complete problem 0 (bodySlotCount problem - 1)
      (encodeUnaryTokens problem.FormulaWidth) (by omega)
  have hPrepared : workRunExact? (BuilderCursorLoop.machine problem.verifier) loopSteps
      (workStartConfiguration (BuilderCursorLoop.machine problem.verifier)
        (BuilderInitialization.finalConfiguration problem).tape) = some loopFinal := by
    rw [BuilderCursorSource.initializer_tape_handoff]
    simpa only [BuilderCursorLoop.initialConfiguration, hCount] using hLoop
  have hRun := WorkMachineChain.workRunExact
    (BuilderInitialization.machine problem.verifier) (BuilderCursorLoop.machine problem.verifier)
    (BuilderInitialization.workSteps problem) loopSteps
    (BuilderInitialization.initialConfiguration problem) (BuilderInitialization.finalConfiguration problem) loopFinal
    (BuilderInitialization.workRunExact problem) (BuilderInitialization.finalConfiguration_state problem) hPrepared
  refine ⟨BuilderInitialization.workSteps problem + 1 + loopSteps,
    renameConfiguration WorkMachineChain.secondState loopFinal, hRun, ?_, ?_, ?_⟩
  · exact congrArg WorkMachineChain.secondState hAccept
  · simpa only [renameConfiguration, outputTokens, Nat.zero_add, hCount] using hTape
  · have hHeader := encodeUnaryTokens_length problem.FormulaWidth
    have hCapacity : problem.FormulaWidth + 1 + (bodySlotCount problem - 1) + 1 =
        problem.FormulaWidth + 1 + bodySlotCount problem := by omega
    rw [hCount, hHeader, hCapacity] at hTime
    have hInitialize := BuilderInitialization.rawTimeBound_le problem
    rw [rawTimeBound_eval]
    omega

theorem uniform_raw_from_input {language : Language} (problem : VerifierTableauProblem language) :
    ∃ (rawSteps : Nat) (final : WorkConfiguration),
      rawSteps ≤ (rawTimeBound problem.verifier).eval problem.input.length ∧
      run (compileWorkMachine (machine problem.verifier)) rawSteps
        (encodeWorkConfiguration (initialConfiguration problem)) = encodeWorkConfiguration final ∧
      final.state = (machine problem.verifier).acceptState ∧
      WorkTape.BlankEquivalent final.tape
        (BuilderCursorSource.cursorTape problem (bodySlotCount problem) 0 (outputTokens problem)) ∧
      (outputTokens problem).length ≤ (outputBound problem.verifier).eval problem.input.length := by
  obtain ⟨steps, final, hRun, hAccept, hTape, hTime⟩ := workRun_from_raw problem
  exact ⟨6 * steps, final, hTime, run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun,
    hAccept, hTape, outputTokens_length_le problem⟩

end PNP.Concrete.CookLevin.BuilderRawInputLoop
