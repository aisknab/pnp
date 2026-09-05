/-
Copyright (c) 2026 PNP Labs.

One verifier-fixed machine constructs the complete header and source-derived
dimension registers directly from raw input. The physical phase handoff and its
connecting transition are included in the execution and polynomial bound.

This initializes workspace only. It does not construct the classifier entry,
select or emit body clauses, run the complete formula loop, or package a reduction.
-/

import PNP.Concrete.CookLevinBuilderDimensionRegisters
import PNP.Concrete.WorkMachineChain

namespace PNP.Concrete.CookLevin.BuilderInitialization

open PipelineTape PipelineStateNamespace PipelineStageBridges

def headerMachine {language : Language}
    (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  BuilderCompleteHeader.machine (VerifierTableauProblem.mk verifier [])

/-- Choosing an empty input to define the table does not specialize execution. -/
theorem headerMachine_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    headerMachine problem.verifier = BuilderCompleteHeader.machine problem := by
  rfl

def machine {language : Language}
    (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (headerMachine verifier)
    (BuilderDimensionRegisters.machine verifier)

theorem rules_pairwise_query_distinct {language : Language}
    (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct := by
  exact WorkMachineChain.rules_pairwise_query_distinct
    (headerMachine verifier) (BuilderDimensionRegisters.machine verifier)
    (BuilderCompleteHeader.rules_pairwise_query_distinct
      (VerifierTableauProblem.mk verifier []))
    (BuilderDimensionRegisters.machine_rules_pairwise verifier)
    (BuilderCompleteHeader.rule_source_ne_acceptState
      (VerifierTableauProblem.mk verifier []))

theorem noRuleAtAccept {language : Language}
    (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) := by
  apply WorkMachineChain.noRuleAtAccept
  intro rule hRule
  exact Nat.ne_of_lt (BuilderUnaryPolynomial.rule_source_lt_acceptState
    (BuilderDimensionRegisters.polynomial verifier) rule hRule)

theorem machine_acceptState_ne_rejectState {language : Language}
    (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState := by
  exact WorkMachineChain.machine_acceptState_ne_rejectState
    (headerMachine verifier) (BuilderDimensionRegisters.machine verifier)
    (BuilderUnaryPolynomial.machine_acceptState_ne_rejectState
      (BuilderDimensionRegisters.polynomial verifier))

def dimensionInitial {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  BuilderUnaryPolynomial.initialConfiguration
    (BuilderDimensionRegisters.polynomial problem.verifier) problem.input
    (BuilderCompleteHeader.finalOutside problem)
    (BuilderCompleteHeader.headerTokens problem)

def dimensionFinal {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  BuilderUnaryPolynomial.finalConfiguration
    (BuilderDimensionRegisters.polynomial problem.verifier) problem.input
    (BuilderCompleteHeader.finalOutside problem)
    (BuilderCompleteHeader.headerTokens problem)

/-- No tape is reconstructed or supplied between the two physical phases. -/
theorem stage_handoff {language : Language}
    (problem : VerifierTableauProblem language) :
    (BuilderCompleteHeader.finalConfiguration problem).tape =
      (dimensionInitial problem).tape := by
  rfl

def initialConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier)
    (rawInputWorkTape problem.input)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState (dimensionFinal problem)

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderCompleteHeader.workSteps problem + 1 +
    BuilderUnaryPolynomial.workSteps
      (BuilderDimensionRegisters.polynomial problem.verifier) problem.input

theorem finalConfiguration_state {language : Language}
    (problem : VerifierTableauProblem language) :
    (finalConfiguration problem).state = (machine problem.verifier).acceptState := by
  rfl

theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem.verifier) (workSteps problem)
        (initialConfiguration problem) = some (finalConfiguration problem) := by
  have hHeader := BuilderCompleteHeader.workRunExact problem
  rw [← headerMachine_eq problem] at hHeader
  have hDimension : workRunExact? (BuilderDimensionRegisters.machine problem.verifier)
      (BuilderUnaryPolynomial.workSteps
        (BuilderDimensionRegisters.polynomial problem.verifier) problem.input)
      { state := (BuilderDimensionRegisters.machine problem.verifier).startState
        tape := (BuilderCompleteHeader.finalConfiguration problem).tape } =
      some (dimensionFinal problem) := by
    exact BuilderUnaryPolynomial.workRunExact
      (BuilderDimensionRegisters.polynomial problem.verifier) problem.input
      (BuilderCompleteHeader.finalOutside problem)
      (BuilderCompleteHeader.headerTokens problem)
  have hHeaderAccept : (BuilderCompleteHeader.finalConfiguration problem).state =
      (headerMachine problem.verifier).acceptState := by
    rw [headerMachine_eq problem]
    rfl
  have hCombined := WorkMachineChain.workRunExact
    (headerMachine problem.verifier) (BuilderDimensionRegisters.machine problem.verifier)
    (BuilderCompleteHeader.workSteps problem)
    (BuilderUnaryPolynomial.workSteps
      (BuilderDimensionRegisters.polynomial problem.verifier) problem.input)
    (workStartConfiguration (headerMachine problem.verifier)
      (rawInputWorkTape problem.input))
    (BuilderCompleteHeader.finalConfiguration problem) (dimensionFinal problem)
    hHeader hHeaderAccept hDimension
  exact hCombined

theorem run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem)
        (encodeWorkConfiguration (initialConfiguration problem)) =
      encodeWorkConfiguration (finalConfiguration problem) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem)

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderCompleteHeader.rawTimeBound verifier) (.constant 6))
    (BuilderDimensionRegisters.rawTimePolynomial verifier)

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderCompleteHeader.rawTimeBound problem.verifier).eval problem.input.length +
        6 + 6 * BuilderUnaryPolynomial.workSteps
          (BuilderDimensionRegisters.polynomial problem.verifier) problem.input := by
  simp only [rawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant,
    BuilderDimensionRegisters.rawTimePolynomial_eval]

theorem rawTimeBound_le {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤ (rawTimeBound problem.verifier).eval problem.input.length := by
  have hHeader := BuilderCompleteHeader.rawTimeBound_le problem
  rw [rawTimeBound_eval]
  unfold workSteps
  omega

theorem finalTape_represents {language : Language}
    (problem : VerifierTableauProblem language) :
    PipelineTape.Represents (Tape.ofInput problem.input)
      (finalConfiguration problem).tape := by
  exact BuilderTokenAppender.workspaceTape_represents problem.input
    (BuilderUnaryPolynomial.finalOutsideLeft
      (BuilderDimensionRegisters.polynomial problem.verifier) problem.input
      (BuilderCompleteHeader.finalOutside problem))
    (BuilderCompleteHeader.headerTokens problem)

/-- A single finite machine builds both phases from raw input, not from a
caller-prepared header, dimension word or inter-stage configuration. -/
theorem initialize_from_raw {language : Language}
    (problem : VerifierTableauProblem language) :
    ∃ wordPrefix,
      workRunExact? (machine problem.verifier) (workSteps problem)
          (workStartConfiguration (machine problem.verifier)
            (rawInputWorkTape problem.input)) = some (finalConfiguration problem) ∧
      run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem)
          (encodeWorkConfiguration (initialConfiguration problem)) =
        encodeWorkConfiguration (finalConfiguration problem) ∧
      (finalConfiguration problem).tape =
        BuilderTokenAppender.workspaceTape problem.input
          ((wordPrefix ++ BuilderDimensionRegisters.dimensionWord
            problem.formulaClauseSlotsPerConstraint
            (BuilderFullScheduleCursorController.bodySlotCount problem)) ++
            BuilderUnaryPolynomial.scratchEndSymbol ::
              (BuilderCompleteHeader.finalOutside problem).drop
                ((BuilderUnaryPolynomial.scratchWord
                  (BuilderDimensionRegisters.polynomial problem.verifier)
                  problem.input.length).length + 1))
          (encodeUnaryTokens problem.FormulaWidth) ∧
      6 * workSteps problem ≤
        (rawTimeBound problem.verifier).eval problem.input.length := by
  obtain ⟨wordPrefix, _, _, hTape, _⟩ := BuilderDimensionRegisters.construct_dimensions
    problem (BuilderCompleteHeader.finalOutside problem)
    (BuilderCompleteHeader.headerTokens problem)
  refine ⟨wordPrefix, workRunExact problem, run_compile_exact problem, ?_,
    rawTimeBound_le problem⟩
  change (finalConfiguration problem).tape = _ at hTape
  rw [BuilderCompleteHeader.headerTokens_eq_encodeUnaryTokens] at hTape
  exact hTape

end PNP.Concrete.CookLevin.BuilderInitialization
