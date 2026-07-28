/-
Copyright (c) 2026 PNP Labs.

Constructive transfer of bounded exact executions of the literal strict-v0
locked-NAND source parser through the six-step work-machine compiler.

The executable compiled machine is already defined beside the literal work
rule table.  This module supplies its explicit cubic raw-transition budget and
the blank-tape transport needed to relate an ordinary raw-input start to the
packed macro-boundary work start.  Trace-parameterized helpers remain private;
the public compiled observations obtain their exact all-input trace internally,
without accepting a caller-supplied certificate.
-/

import PNP.Concrete.LockedNANDSourceParserCorrectness
import PNP.Concrete.PipelineRefinement

namespace PNP.Concrete.LockedNAND.SourceParser

/-! ### Explicit compiled runtime polynomial -/

/-- The six-transition compilation of the conservative cubic work bound.

The expression is deliberately written in the same association as
`validRawBound`, so its evaluation theorem exposes the literal externally
auditable arithmetic rather than relying on an asymptotic estimate. -/
def validRawTimePolynomial : NatPolynomial :=
  let shifted : NatPolynomial :=
    .add .variable (.constant 1)
  .mul (.constant 6)
    (.mul
      (.mul
        (.mul (.constant 4096) shifted)
        shifted)
      shifted)

/-- Exact evaluation of the concrete compiled runtime polynomial. -/
theorem validRawTimePolynomial_eval (bitLength : Nat) :
    validRawTimePolynomial.eval bitLength =
      validRawBound bitLength := by
  rfl

/-! ### Raw-input blank-equivalence boundary -/

/-- An ordinary raw-input start and the encoded packed work start denote the
same infinite blank-extended tape and the same compiled control state. -/
theorem compiledStart_blankEquivalent (bits : BitString) :
    Configuration.BlankEquivalent
      (startConfig compiledMachine bits)
      (encodeWorkConfiguration
        (workStartConfiguration machine
          (rawInputWorkTape bits))) := by
  exact startConfig_compileWorkMachine_blankEquivalent machine bits

/-! ### Private exact-trace transfer -/

private theorem compiledRun_encoded_eq_of_exact
    (bits : BitString) (steps : Nat)
    (final : WorkConfiguration)
    (runExact :
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final)
    (halted : machine.isHalted final = true)
    (bounded : steps ≤ validWorkBound bits.length) :
    run compiledMachine
        (validRawTimePolynomial.eval bits.length)
        (encodeWorkConfiguration
          (workStartConfiguration machine
            (rawInputWorkTape bits))) =
      encodeWorkConfiguration final := by
  apply run_compileWorkMachine_of_workRunExact_halted_le
    machine steps (validRawTimePolynomial.eval bits.length)
    (workStartConfiguration machine (rawInputWorkTape bits))
    final runExact halted
  rw [validRawTimePolynomial_eval, validRawBound_eq]
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
    (bounded : steps ≤ validWorkBound bits.length) :
    Configuration.BlankEquivalent
      (run compiledMachine
        (validRawTimePolynomial.eval bits.length)
        (startConfig compiledMachine bits))
      (encodeWorkConfiguration final) := by
  have transported :=
    run_blankEquivalent compiledMachine
      (validRawTimePolynomial.eval bits.length)
      (compiledStart_blankEquivalent bits)
  rw [compiledRun_encoded_eq_of_exact
    bits steps final runExact halted bounded] at transported
  exact transported

/-- Trace-parametric state transport is intentionally private.  Public state
claims are introduced only after the operational trace has been constructed
from the source-language hypotheses. -/
private theorem compiledRun_state_eq_of_exact
    (bits : BitString) (steps : Nat)
    (final : WorkConfiguration)
    (runExact :
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final)
    (halted : machine.isHalted final = true)
    (bounded : steps ≤ validWorkBound bits.length) :
    (run compiledMachine
      (validRawTimePolynomial.eval bits.length)
      (startConfig compiledMachine bits)).state =
        (encodeWorkConfiguration final).state :=
  (compiledRun_blankEquivalent_of_exact
    bits steps final runExact halted bounded).1

/-- Trace-parametric output transport is intentionally private for the same
reason as the state helper above. -/
private theorem compiledRun_output_eq_of_exact
    (bits : BitString) (steps : Nat)
    (final : WorkConfiguration)
    (runExact :
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final)
    (halted : machine.isHalted final = true)
    (bounded : steps ≤ validWorkBound bits.length) :
    (run compiledMachine
      (validRawTimePolynomial.eval bits.length)
      (startConfig compiledMachine bits)).tape.outputBits =
        (encodeWorkConfiguration final).tape.outputBits := by
  exact Tape.outputBits_eq_of_blankEquivalent
    (compiledRun_blankEquivalent_of_exact
      bits steps final runExact halted bounded).2

/-! ### Private compiled-observation transport

These helpers still consume an exact trace internally.  They are kept private
so the public API obtains that trace only from the unconditional
all-input correctness theorem, never from a caller-supplied certificate. -/

private theorem compiledBoundedDecide_accept_iff_of_exact
    (bits : BitString) (steps : Nat)
    (final : WorkConfiguration)
    (runExact :
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final)
    (halted : machine.isHalted final = true)
    (bounded : steps ≤ validWorkBound bits.length) :
    boundedDecide compiledMachine
        (validRawTimePolynomial.eval bits.length) bits = .accept ↔
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
    (bounded : steps ≤ validWorkBound bits.length) :
    boundedDecide compiledMachine
        (validRawTimePolynomial.eval bits.length) bits ≠ .timeout := by
  apply (boundedDecide_ne_timeout_iff_final_isHalted
    compiledMachine (validRawTimePolynomial.eval bits.length) bits).mpr
  have stateEq :=
    compiledRun_state_eq_of_exact
      bits steps final runExact halted bounded
  change
    compiledMachine.isHalted
        (run compiledMachine
          (validRawTimePolynomial.eval bits.length)
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
    (bounded : steps ≤ validWorkBound bits.length) :
    machineOutput compiledMachine
        (validRawTimePolynomial.eval bits.length) bits =
      (encodeWorkTape final.tape).outputBits := by
  unfold machineOutput
  simpa [encodeWorkConfiguration] using
    (compiledRun_output_eq_of_exact
      bits steps final runExact halted bounded)

/-! ### Unconditional compiled parser interface -/

/-- The compiled parser implements the total validated-byte function. -/
theorem compiledMachineOutput_eq_validatedSourceBytes
    (bits : BitString) :
    machineOutput compiledMachine
        (validRawTimePolynomial.eval bits.length) bits =
      validatedSourceBytes bits := by
  rcases allInput_exact bits with
    ⟨steps, final, bounded, runExact, halted,
      _acceptanceIff, outputEq⟩
  exact
    (compiledMachineOutput_eq_of_exact
      bits steps final runExact halted bounded).trans outputEq

/-- Compiled acceptance is exactly strict-v0 source validity. -/
theorem compiledBoundedDecide_accept_iff (bits : BitString) :
    boundedDecide compiledMachine
        (validRawTimePolynomial.eval bits.length) bits = .accept ↔
      ValidEncodedCircuit bits := by
  rcases allInput_exact bits with
    ⟨steps, final, bounded, runExact, halted,
      acceptanceIff, _outputEq⟩
  exact
    (compiledBoundedDecide_accept_iff_of_exact
      bits steps final runExact halted bounded).trans (by
        simpa [machine] using acceptanceIff)

/-- The compiled parser never times out at its stated polynomial. -/
theorem compiledBoundedDecide_ne_timeout (bits : BitString) :
    boundedDecide compiledMachine
        (validRawTimePolynomial.eval bits.length) bits ≠ .timeout := by
  rcases allInput_exact bits with
    ⟨steps, final, bounded, runExact, halted,
      _acceptanceIff, _outputEq⟩
  exact compiledBoundedDecide_ne_timeout_of_exact
    bits steps final runExact halted bounded

/-- Raw polynomial-time decider for strict-v0 valid encodings. -/
def polynomialTimeMachine :
    PolynomialTimeMachine ValidEncodedCircuit :=
  { machine := compiledMachine
    timeBound := validRawTimePolynomial
    haltsWithin := by
      intro bits
      simpa [BitString.size] using
        compiledBoundedDecide_ne_timeout bits
    accepts_iff := by
      intro bits
      simpa [BitString.size] using
        compiledBoundedDecide_accept_iff bits }

/-- Polynomial-time total validator: preserve valid bytes, clear malformed
bytes.  The output-size polynomial is the identity because validation never
increases length. -/
def validatedSourceBytesPolynomialTimeFunction :
    PolynomialTimeFunction :=
  { program := .machine compiledMachine validRawTimePolynomial
    runtimeBound := validRawTimePolynomial
    outputSizeBound := .variable
    haltsWithin := by
      intro bits
      change boundedDecide compiledMachine
          (validRawTimePolynomial.eval (BitString.size bits)) bits ≠
        .timeout
      simpa [BitString.size] using
        compiledBoundedDecide_ne_timeout bits
    runtime_le := by
      intro bits
      exact Nat.le_refl
        (validRawTimePolynomial.eval (BitString.size bits))
    output_size_le := by
      intro bits
      change BitString.size
          (machineOutput compiledMachine
            (validRawTimePolynomial.eval (BitString.size bits)) bits) ≤
        BitString.size bits
      simpa [BitString.size,
        compiledMachineOutput_eq_validatedSourceBytes] using
          validatedSourceBytes_size_le bits }

/-- Exact semantic output of the proof-bearing function witness. -/
theorem validatedSourceBytesPolynomialTimeFunction_output
    (bits : BitString) :
    validatedSourceBytesPolynomialTimeFunction.output bits =
      validatedSourceBytes bits := by
  change machineOutput compiledMachine
      (validRawTimePolynomial.eval (BitString.size bits)) bits =
    validatedSourceBytes bits
  simpa [BitString.size] using
    compiledMachineOutput_eq_validatedSourceBytes bits

/-- The function witness's leaf program is already its exact raw-machine
refinement. -/
def validatedSourceBytesRawRefinement :
    FunctionProgram.RawRefinement
      validatedSourceBytesPolynomialTimeFunction.program := by
  change FunctionProgram.RawRefinement
    (.machine compiledMachine validRawTimePolynomial)
  exact FunctionProgram.RawRefinement.ofMachine
    compiledMachine validRawTimePolynomial

end PNP.Concrete.LockedNAND.SourceParser
