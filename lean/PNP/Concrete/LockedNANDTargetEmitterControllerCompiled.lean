/-
Copyright (c) 2026 PNP Labs.

Compiled all-input boundary for the fixed grammar-only locked-NAND target
emitter, followed by the strict parser/emitter composition used by the
source-language reduction.

The executable table remains the literal controller graph.  Decoder results
appear only in correctness statements, never in a transition-table lookup.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerTotalTrace
import PNP.Concrete.LockedNANDSourceParserCompiled
import PNP.Concrete.PipelineRefinement

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerCompiled

open PNP.Concrete

abbrev machine : WorkMachine :=
  TargetEmitterController.machine

abbrev compiledMachine : Machine :=
  TargetEmitterController.compiledMachine

/-- Language recognized by the grammar-only emitter.  Intrinsic reference
validity is intentionally not part of this boundary. -/
def GrammarDecodableCircuit : Language := fun bits =>
  ∃ raw, decodeCircuit bits = some raw

/-- Ordinary raw-input starts and encoded work starts denote the same
blank-extended tape and compiled control state. -/
theorem compiledStart_blankEquivalent (bits : BitString) :
    Configuration.BlankEquivalent
      (startConfig compiledMachine bits)
      (encodeWorkConfiguration
        (workStartConfiguration machine
          (rawInputWorkTape bits))) := by
  exact startConfig_compileWorkMachine_blankEquivalent machine bits

private theorem compiledRun_encoded_eq_of_exact
    (bits : BitString) (steps : Nat)
    (final : WorkConfiguration)
    (runExact :
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final)
    (halted : machine.isHalted final = true)
    (bounded :
      steps ≤
        TargetEmitterControllerPolynomialBound.allInputWorkBound
          bits.length) :
    run compiledMachine
        (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length)
        (encodeWorkConfiguration
          (workStartConfiguration machine
            (rawInputWorkTape bits))) =
      encodeWorkConfiguration final := by
  apply run_compileWorkMachine_of_workRunExact_halted_le
    machine steps
      (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
        bits.length)
    (workStartConfiguration machine (rawInputWorkTape bits))
    final runExact halted
  rw [
    TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial_eval]
  exact Nat.mul_le_mul_left 6 bounded

private theorem compiledRun_blankEquivalent_of_exact
    (bits : BitString) (steps : Nat)
    (final : WorkConfiguration)
    (runExact :
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final)
    (halted : machine.isHalted final = true)
    (bounded :
      steps ≤
        TargetEmitterControllerPolynomialBound.allInputWorkBound
          bits.length) :
    Configuration.BlankEquivalent
      (run compiledMachine
        (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length)
        (startConfig compiledMachine bits))
      (encodeWorkConfiguration final) := by
  have transported :=
    run_blankEquivalent compiledMachine
      (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
        bits.length)
      (compiledStart_blankEquivalent bits)
  rw [compiledRun_encoded_eq_of_exact
    bits steps final runExact halted bounded] at transported
  exact transported

private theorem compiledRun_state_eq_of_exact
    (bits : BitString) (steps : Nat)
    (final : WorkConfiguration)
    (runExact :
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final)
    (halted : machine.isHalted final = true)
    (bounded :
      steps ≤
        TargetEmitterControllerPolynomialBound.allInputWorkBound
          bits.length) :
    (run compiledMachine
      (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
        bits.length)
      (startConfig compiledMachine bits)).state =
        (encodeWorkConfiguration final).state :=
  (compiledRun_blankEquivalent_of_exact
    bits steps final runExact halted bounded).1

private theorem compiledRun_output_eq_of_exact
    (bits : BitString) (steps : Nat)
    (final : WorkConfiguration)
    (runExact :
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final)
    (halted : machine.isHalted final = true)
    (bounded :
      steps ≤
        TargetEmitterControllerPolynomialBound.allInputWorkBound
          bits.length) :
    (run compiledMachine
      (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
        bits.length)
      (startConfig compiledMachine bits)).tape.outputBits =
        (encodeWorkConfiguration final).tape.outputBits := by
  exact Tape.outputBits_eq_of_blankEquivalent
    (compiledRun_blankEquivalent_of_exact
      bits steps final runExact halted bounded).2

private theorem compiledBoundedDecide_accept_iff_of_exact
    (bits : BitString) (steps : Nat)
    (final : WorkConfiguration)
    (runExact :
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final)
    (halted : machine.isHalted final = true)
    (bounded :
      steps ≤
        TargetEmitterControllerPolynomialBound.allInputWorkBound
          bits.length) :
    boundedDecide compiledMachine
        (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length) bits = .accept ↔
      final.state = machine.acceptState := by
  rw [boundedDecide_accept_iff_final]
  rw [compiledRun_state_eq_of_exact
    bits steps final runExact halted bounded]
  exact encodeWorkConfiguration_accept_iff machine final

private theorem compiledBoundedDecide_ne_timeout_of_exact
    (bits : BitString) (steps : Nat)
    (final : WorkConfiguration)
    (runExact :
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final)
    (halted : machine.isHalted final = true)
    (bounded :
      steps ≤
        TargetEmitterControllerPolynomialBound.allInputWorkBound
          bits.length) :
    boundedDecide compiledMachine
        (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length) bits ≠ .timeout := by
  apply (boundedDecide_ne_timeout_iff_final_isHalted
    compiledMachine
    (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
      bits.length) bits).mpr
  have stateEq :=
    compiledRun_state_eq_of_exact
      bits steps final runExact halted bounded
  change
    compiledMachine.isHalted
        (run compiledMachine
          (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
            bits.length)
          (startConfig compiledMachine bits)) =
      true
  unfold Machine.isHalted
  rw [stateEq]
  exact (compileWorkMachine_isHalted_encode machine final).trans halted

private theorem compiledMachineOutput_eq_of_exact
    (bits : BitString) (steps : Nat)
    (final : WorkConfiguration)
    (runExact :
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final)
    (halted : machine.isHalted final = true)
    (bounded :
      steps ≤
        TargetEmitterControllerPolynomialBound.allInputWorkBound
          bits.length) :
    machineOutput compiledMachine
        (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length) bits =
      (encodeWorkTape final.tape).outputBits := by
  unfold machineOutput
  simpa [encodeWorkConfiguration] using
    (compiledRun_output_eq_of_exact
      bits steps final runExact halted bounded)

/-! ### Unconditional compiled interface -/

/-- The compiled literal machine computes the grammar-only raw target on
every bitstring. -/
theorem compiledMachineOutput_eq_targetBytes (bits : BitString) :
    machineOutput compiledMachine
        (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length) bits =
      RawBuilder.targetBytes bits := by
  rcases TargetEmitterControllerTotalTrace.allInput_bounded_exact bits with
    ⟨steps, final, bounded, runExact, halted,
      _acceptanceIff, outputEq⟩
  exact
    (compiledMachineOutput_eq_of_exact
      bits steps final runExact halted bounded).trans outputEq

/-- Compiled acceptance is exactly grammar decoding, including raw circuits
whose references are not intrinsically valid. -/
theorem compiledBoundedDecide_accept_iff (bits : BitString) :
    boundedDecide compiledMachine
        (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length) bits = .accept ↔
      GrammarDecodableCircuit bits := by
  rcases TargetEmitterControllerTotalTrace.allInput_bounded_exact bits with
    ⟨steps, final, bounded, runExact, halted,
      acceptanceIff, _outputEq⟩
  exact
    (compiledBoundedDecide_accept_iff_of_exact
      bits steps final runExact halted bounded).trans acceptanceIff

/-- The compiled emitter never times out at its advertised polynomial. -/
theorem compiledBoundedDecide_ne_timeout (bits : BitString) :
    boundedDecide compiledMachine
        (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length) bits ≠ .timeout := by
  rcases TargetEmitterControllerTotalTrace.allInput_bounded_exact bits with
    ⟨steps, final, bounded, runExact, halted,
      _acceptanceIff, _outputEq⟩
  exact compiledBoundedDecide_ne_timeout_of_exact
    bits steps final runExact halted bounded

/-- Grammar-only polynomial-time decider implemented by the same table. -/
def polynomialTimeMachine :
    PolynomialTimeMachine GrammarDecodableCircuit :=
  { machine := compiledMachine
    timeBound :=
      TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial
    haltsWithin := by
      intro bits
      simpa [BitString.size] using
        compiledBoundedDecide_ne_timeout bits
    accepts_iff := by
      intro bits
      simpa [BitString.size] using
        compiledBoundedDecide_accept_iff bits }

/-- Proof-bearing polynomial-time function for the standalone grammar-only
raw target builder. -/
def rawTargetBytesPolynomialTimeFunction :
    PolynomialTimeFunction :=
  { program := .machine compiledMachine
      TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial
    runtimeBound :=
      TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial
    outputSizeBound := TargetEmitterSpec.rawTargetOutputSizePolynomial
    haltsWithin := by
      intro bits
      change boundedDecide compiledMachine
          (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
            (BitString.size bits)) bits ≠
        .timeout
      simpa [BitString.size] using
        compiledBoundedDecide_ne_timeout bits
    runtime_le := by
      intro bits
      exact Nat.le_refl _
    output_size_le := by
      intro bits
      change BitString.size
          (machineOutput compiledMachine
            (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
              (BitString.size bits))
            bits) ≤
        TargetEmitterSpec.rawTargetOutputSizePolynomial.eval
          (BitString.size bits)
      rw [show
        TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
            (BitString.size bits) =
          TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
            bits.length by rfl]
      rw [compiledMachineOutput_eq_targetBytes]
      exact TargetEmitterSpec.targetBytes_size_le bits }

/-- Exact semantic output of the standalone proof-bearing function witness. -/
theorem rawTargetBytesPolynomialTimeFunction_output
    (bits : BitString) :
    rawTargetBytesPolynomialTimeFunction.output bits =
      RawBuilder.targetBytes bits := by
  change machineOutput compiledMachine
      (TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial.eval
        (BitString.size bits)) bits =
    RawBuilder.targetBytes bits
  simpa [BitString.size] using
    compiledMachineOutput_eq_targetBytes bits

/-- The standalone function leaf is already its exact raw-machine
refinement. -/
def rawTargetBytesRawRefinement :
    FunctionProgram.RawRefinement
      rawTargetBytesPolynomialTimeFunction.program := by
  change FunctionProgram.RawRefinement
    (.machine compiledMachine
      TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial)
  exact FunctionProgram.RawRefinement.ofMachine compiledMachine
    TargetEmitterControllerPolynomialBound.compiledRawTimePolynomial

/-! ### Strict source-language composition -/

/-- Validate strict-v0 source semantics first, then run the grammar-only
emitter.  This composition is the existing pure locked-NAND reduction. -/
def strictLockedNANDPolynomialTimeFunction :
    PolynomialTimeFunction :=
  PolynomialTimeFunction.compose
    SourceParser.validatedSourceBytesPolynomialTimeFunction
    rawTargetBytesPolynomialTimeFunction

theorem strictLockedNANDPolynomialTimeFunction_output
    (bits : BitString) :
    strictLockedNANDPolynomialTimeFunction.output bits =
      buildLockedNANDInstance bits := by
  change rawTargetBytesPolynomialTimeFunction.output
      (SourceParser.validatedSourceBytesPolynomialTimeFunction.output bits) =
    buildLockedNANDInstance bits
  rw [SourceParser.validatedSourceBytesPolynomialTimeFunction_output,
    rawTargetBytesPolynomialTimeFunction_output]
  exact
    TargetEmitterSpec.targetBytes_validatedSourceBytes_eq_buildLockedNANDInstance
      bits

/-- The strict parser/emitter composition compiles recursively to one literal
raw machine with no caller certificate. -/
def strictLockedNANDRawRefinement :
    FunctionProgram.RawRefinement
      strictLockedNANDPolynomialTimeFunction.program := by
  change FunctionProgram.RawRefinement
    (.compose
      SourceParser.validatedSourceBytesPolynomialTimeFunction.program
      rawTargetBytesPolynomialTimeFunction.program)
  exact FunctionProgram.RawRefinement.compose
    SourceParser.validatedSourceBytesRawRefinement
    rawTargetBytesRawRefinement

end PNP.Concrete.LockedNAND.TargetEmitterControllerCompiled
