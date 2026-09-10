/-
Copyright (c) 2026 PNP Labs.

Complete all-input concrete Cook-Levin formula construction.
One finite machine runs the source-derived builder and its physical output
finalizer. The ordinary-input bridge preserves every raw bitstring, including
empty and odd lengths. All execution, bridge, framing and output costs are
bounded in the original input length.

The exact canonical polynomial reduction below does not prove CNFSAT in P,
unconditional ZeroSlack, residual minimization, or P = NP.
-/
import PNP.Concrete.CookLevinBuilderOutputFinalizer
import PNP.Concrete.LockedNANDTargetEmitterControllerCompletionTrace
import PNP.Concrete.PipelineRefinement

namespace PNP.Concrete.CookLevin

open PipelineStateNamespace (renameConfiguration)

private def completeWorkMachine {language : Language}
    (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderRawInputLoop.machine verifier) BuilderOutputFinalizer.machine

/-- One literal finite raw machine, fixed independently of the source input
and of any accepting certificate. -/
def formulaBuilderMachine {language : Language}
    (verifier : PolynomialTimeVerifier language) : Machine :=
  compileWorkMachine (completeWorkMachine verifier)

/-- Complete original-input raw budget, including the inter-stage launch. -/
def formulaBuilderTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderRawInputLoop.rawTimeBound verifier) (.constant 6))
    (BuilderOutputFinalizer.rawTimeBound verifier)

private theorem initial_renamed {language : Language}
    (problem : VerifierTableauProblem language) :
    renameConfiguration WorkMachineChain.firstState (BuilderRawInputLoop.initialConfiguration problem) =
      workStartConfiguration (completeWorkMachine problem.verifier) (rawInputWorkTape problem.input) := rfl

private theorem complete_workRun {language : Language}
    (problem : VerifierTableauProblem language) :
    ∃ (steps : Nat) (final : WorkConfiguration),
      workRunExact? (completeWorkMachine problem.verifier) steps
        (workStartConfiguration (completeWorkMachine problem.verifier) (rawInputWorkTape problem.input)) =
          some final ∧
      final.state = (completeWorkMachine problem.verifier).acceptState ∧
      (encodeWorkTape final.tape).outputBits = problem.encodedFormula ∧
      6 * steps ≤ (formulaBuilderTimeBound problem.verifier).eval problem.input.length := by
  obtain ⟨steps, middle, hBuilder, hAccept, hTape, hTime⟩ :=
    BuilderCanonicalOutput.workRun_canonical_from_raw problem
  have hInitial : WorkConfiguration.BlankEquivalent
      (workStartConfiguration BuilderOutputFinalizer.machine middle.tape)
      (workStartConfiguration BuilderOutputFinalizer.machine
        (BuilderCursorSource.cursorTape problem (BuilderFullScheduleCursorController.bodySlotCount problem) 0
          (encodeCNFTokens problem.formula))) := ⟨rfl, hTape⟩
  obtain ⟨last, hFinalizer, hFinalEquivalent⟩ := workRunExact?_transport
    BuilderOutputFinalizer.machine
    (BuilderOutputFinalizer.workSteps problem.input (encodeCNFTokens problem.formula))
    hInitial (BuilderOutputFinalizer.canonical_workRun_exact problem)
  have hChain := WorkMachineChain.workRunExact
    (BuilderRawInputLoop.machine problem.verifier) BuilderOutputFinalizer.machine
    steps (BuilderOutputFinalizer.workSteps problem.input (encodeCNFTokens problem.formula))
    (BuilderRawInputLoop.initialConfiguration problem) middle last hBuilder hAccept hFinalizer
  rw [initial_renamed] at hChain
  refine ⟨steps + 1 + BuilderOutputFinalizer.workSteps problem.input (encodeCNFTokens problem.formula),
    renameConfiguration WorkMachineChain.secondState last, hChain, ?_, ?_, ?_⟩
  · exact congrArg WorkMachineChain.secondState hFinalEquivalent.state
  · have hOutput := LockedNAND.TargetEmitterControllerCompletionTrace.encodeWorkTape_outputBits_eq_of_blankEquivalent
      hFinalEquivalent.tape
    exact hOutput.trans (BuilderOutputFinalizer.canonical_output_eq problem)
  · have hFinalizerTime := BuilderOutputFinalizer.canonical_rawTime_le problem
    simp only [formulaBuilderTimeBound, NatPolynomial.eval]
    omega

private theorem raw_result {language : Language}
    (problem : VerifierTableauProblem language) :
    (run (formulaBuilderMachine problem.verifier)
      ((formulaBuilderTimeBound problem.verifier).eval problem.input.length)
      (startConfig (formulaBuilderMachine problem.verifier) problem.input)).state =
        (formulaBuilderMachine problem.verifier).acceptState ∧
    machineOutput (formulaBuilderMachine problem.verifier)
      ((formulaBuilderTimeBound problem.verifier).eval problem.input.length) problem.input =
        problem.encodedFormula := by
  obtain ⟨steps, final, hRun, hAccept, hOutput, hTime⟩ := complete_workRun problem
  have hHalted : (completeWorkMachine problem.verifier).isHalted final = true := by
    rw [WorkMachine.isHalted, hAccept] <;> rfl
  have hEncoded := run_compileWorkMachine_of_workRunExact_halted_le
    (completeWorkMachine problem.verifier) steps
    ((formulaBuilderTimeBound problem.verifier).eval problem.input.length)
    (workStartConfiguration (completeWorkMachine problem.verifier) (rawInputWorkTape problem.input))
    final hRun hHalted hTime
  have hRaw := run_blankEquivalent (compileWorkMachine (completeWorkMachine problem.verifier))
    ((formulaBuilderTimeBound problem.verifier).eval problem.input.length)
    (startConfig_compileWorkMachine_blankEquivalent (completeWorkMachine problem.verifier) problem.input)
  rw [hEncoded] at hRaw
  constructor
  · exact hRaw.1.trans ((encodeWorkConfiguration_accept_iff
      (completeWorkMachine problem.verifier) final).mpr hAccept)
  · exact (Tape.outputBits_eq_of_blankEquivalent hRaw.2).trans hOutput

theorem formulaBuilderMachine_accept {language : Language}
    (verifier : PolynomialTimeVerifier language) (input : BitString) :
    boundedDecide (formulaBuilderMachine verifier)
      ((formulaBuilderTimeBound verifier).eval input.length) input = .accept := by
  apply (boundedDecide_accept_iff_final _ _ _).mpr
  exact (raw_result (VerifierTableauProblem.mk verifier input)).1

theorem formulaBuilderMachine_output {language : Language}
    (verifier : PolynomialTimeVerifier language) (input : BitString) :
    machineOutput (formulaBuilderMachine verifier)
      ((formulaBuilderTimeBound verifier).eval input.length) input =
        (VerifierTableauProblem.mk verifier input).encodedFormula :=
  (raw_result (VerifierTableauProblem.mk verifier input)).2

/-- The complete construction is an actual finite machine leaf, with no
semantic oracle, caller-supplied family, trace or correctness certificate. -/
def formulaBuilder {language : Language}
    (verifier : PolynomialTimeVerifier language) : PolynomialTimeFunction :=
  {program := .machine (formulaBuilderMachine verifier) (formulaBuilderTimeBound verifier)
   runtimeBound := formulaBuilderTimeBound verifier
   outputSizeBound := BuilderCanonicalOutput.encodedSizeBound verifier
   haltsWithin := by
     intro input
     change boundedDecide (formulaBuilderMachine verifier)
       ((formulaBuilderTimeBound verifier).eval input.length) input ≠ .timeout
     rw [formulaBuilderMachine_accept]
     decide
   runtime_le := by
     intro input
     exact Nat.le_refl _
   output_size_le := by
     intro input
     have bound := BuilderCanonicalOutput.encodedFormula_length_le (VerifierTableauProblem.mk verifier input)
     rw [← formulaBuilderMachine_output verifier input] at bound
     exact bound}

private theorem formulaBuilder_output_projection {language : Language}
    (verifier : PolynomialTimeVerifier language) (input : BitString) :
    (formulaBuilder verifier).output input =
      machineOutput (formulaBuilderMachine verifier)
        ((formulaBuilderTimeBound verifier).eval input.length) input := rfl

theorem formulaBuilder_output {language : Language}
    (verifier : PolynomialTimeVerifier language) (input : BitString) :
    (formulaBuilder verifier).output input =
      (VerifierTableauProblem.mk verifier input).encodedFormula := by
  rw [formulaBuilder_output_projection]
  exact formulaBuilderMachine_output verifier input

/-- The existing recursive raw-refinement compiler applies to the entire
proved function and preserves its exact canonical output. -/
theorem formulaBuilder_rawRefinement_output {language : Language}
    (verifier : PolynomialTimeVerifier language) (input : BitString) :
    machineOutput (FunctionProgram.RawRefinement.compile (formulaBuilder verifier).program).machine
      ((FunctionProgram.RawRefinement.compile (formulaBuilder verifier).program).timeBound.eval
        (BitString.size input)) input = (VerifierTableauProblem.mk verifier input).encodedFormula := by
  have h := FunctionProgram.RawRefinement.compile_output_eq (formulaBuilder verifier).program input
    ((formulaBuilder verifier).haltsWithin input)
  exact h.trans (formulaBuilder_output verifier input)

/-- Exact concrete polynomial many-one reduction for every polynomial verifier
language, using the original canonical formula semantics. -/
def polynomialReduction {language : Language}
    (verifier : PolynomialTimeVerifier language) : PolynomialReduction language CNFSAT :=
  {function := formulaBuilder verifier
   correctness := by
     intro input
     rw [formulaBuilder_output]
     exact (VerifierTableauProblem.encodedFormula_mem_CNFSAT_iff_language
       (VerifierTableauProblem.mk verifier input)).symm}

private theorem polynomialReduction_function {language : Language}
    (verifier : PolynomialTimeVerifier language) :
    (polynomialReduction verifier).function = formulaBuilder verifier := rfl

theorem polynomialReduction_output {language : Language}
    (verifier : PolynomialTimeVerifier language) (input : BitString) :
    (polynomialReduction verifier).function.output input =
      (VerifierTableauProblem.mk verifier input).encodedFormula := by
  rw [polynomialReduction_function]
  exact formulaBuilder_output verifier input

/-- Complete all-input formula construction, including the concrete executable
polynomial reduction, at the exact interface selected for M230. -/
theorem cook_levin_formula_builder_checked_complete {language : Language}
    (verifier : PolynomialTimeVerifier language) :
    ∀ input, (polynomialReduction verifier).function.output input =
      (VerifierTableauProblem.mk verifier input).encodedFormula :=
  polynomialReduction_output verifier

end PNP.Concrete.CookLevin
