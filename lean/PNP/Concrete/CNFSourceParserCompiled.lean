/-
Copyright (c) 2026 PNP Labs.

Compiled polynomial-time interface for the standalone strict canonical-CNF
parser.  The literal work-machine proof is transferred through the generic
six-raw-transition compiler; public observations construct the all-input
trace internally and accept no caller-supplied execution certificate.
-/

import PNP.Concrete.CNFSourceParserCorrectness
import PNP.Concrete.PipelineRefinement

namespace PNP.Concrete.CNFSourceParser

open PNP.Concrete

/-! ### Explicit compiled runtime polynomial -/

def rawTimePolynomial : NatPolynomial :=
  .mul (.constant 6)
    (.add
      (.mul (.constant 8) .variable)
      (.constant 32))

theorem rawTimePolynomial_eval (bitLength : Nat) :
    rawTimePolynomial.eval bitLength =
      6 * parserWorkBound bitLength := by
  rfl

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
    (bounded : steps ≤ parserWorkBound bits.length) :
    run compiledMachine
        (rawTimePolynomial.eval bits.length)
        (encodeWorkConfiguration
          (workStartConfiguration machine
            (rawInputWorkTape bits))) =
      encodeWorkConfiguration final := by
  apply run_compileWorkMachine_of_workRunExact_halted_le
    machine steps (rawTimePolynomial.eval bits.length)
    (workStartConfiguration machine (rawInputWorkTape bits))
    final runExact halted
  rw [rawTimePolynomial_eval]
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
    (bounded : steps ≤ parserWorkBound bits.length) :
    Configuration.BlankEquivalent
      (run compiledMachine
        (rawTimePolynomial.eval bits.length)
        (startConfig compiledMachine bits))
      (encodeWorkConfiguration final) := by
  have transported :=
    run_blankEquivalent compiledMachine
      (rawTimePolynomial.eval bits.length)
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
    (bounded : steps ≤ parserWorkBound bits.length) :
    (run compiledMachine
      (rawTimePolynomial.eval bits.length)
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
    (bounded : steps ≤ parserWorkBound bits.length) :
    (run compiledMachine
      (rawTimePolynomial.eval bits.length)
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
    (bounded : steps ≤ parserWorkBound bits.length) :
    boundedDecide compiledMachine
        (rawTimePolynomial.eval bits.length) bits = .accept ↔
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
    (bounded : steps ≤ parserWorkBound bits.length) :
    boundedDecide compiledMachine
        (rawTimePolynomial.eval bits.length) bits ≠ .timeout := by
  apply (boundedDecide_ne_timeout_iff_final_isHalted
    compiledMachine (rawTimePolynomial.eval bits.length) bits).mpr
  have stateEq :=
    compiledRun_state_eq_of_exact
      bits steps final runExact halted bounded
  change
    compiledMachine.isHalted
        (run compiledMachine
          (rawTimePolynomial.eval bits.length)
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
    (bounded : steps ≤ parserWorkBound bits.length) :
    machineOutput compiledMachine
        (rawTimePolynomial.eval bits.length) bits =
      (encodeWorkTape final.tape).outputBits := by
  unfold machineOutput
  simpa [encodeWorkConfiguration] using
    (compiledRun_output_eq_of_exact
      bits steps final runExact halted bounded)

/-! ### Unconditional compiled interface -/

theorem compiledMachineOutput_eq_validatedCNFBytes
    (bits : BitString) :
    machineOutput compiledMachine
        (rawTimePolynomial.eval bits.length) bits =
      validatedCNFBytes bits := by
  rcases allInput_exact bits with
    ⟨steps, final, bounded, runExact, halted,
      outputEq, _acceptanceIff⟩
  exact
    (compiledMachineOutput_eq_of_exact
      bits steps final runExact halted bounded).trans outputEq

theorem compiledBoundedDecide_accept_iff (bits : BitString) :
    boundedDecide compiledMachine
        (rawTimePolynomial.eval bits.length) bits = .accept ↔
      ValidEncodedCNF bits := by
  rcases allInput_exact bits with
    ⟨steps, final, bounded, runExact, halted,
      _outputEq, acceptanceIff⟩
  exact
    (compiledBoundedDecide_accept_iff_of_exact
      bits steps final runExact halted bounded).trans
      acceptanceIff

theorem compiledBoundedDecide_ne_timeout (bits : BitString) :
    boundedDecide compiledMachine
        (rawTimePolynomial.eval bits.length) bits ≠ .timeout := by
  rcases allInput_exact bits with
    ⟨steps, final, bounded, runExact, halted,
      _outputEq, _acceptanceIff⟩
  exact compiledBoundedDecide_ne_timeout_of_exact
    bits steps final runExact halted bounded

def polynomialTimeMachine :
    PolynomialTimeMachine ValidEncodedCNF :=
  { machine := compiledMachine
    timeBound := rawTimePolynomial
    haltsWithin := by
      intro bits
      simpa [BitString.size] using
        compiledBoundedDecide_ne_timeout bits
    accepts_iff := by
      intro bits
      simpa [BitString.size] using
        compiledBoundedDecide_accept_iff bits }

def validatedCNFBytesPolynomialTimeFunction :
    PolynomialTimeFunction :=
  { program := .machine compiledMachine rawTimePolynomial
    runtimeBound := rawTimePolynomial
    outputSizeBound := .variable
    haltsWithin := by
      intro bits
      change boundedDecide compiledMachine
          (rawTimePolynomial.eval (BitString.size bits)) bits ≠
        .timeout
      simpa [BitString.size] using
        compiledBoundedDecide_ne_timeout bits
    runtime_le := by
      intro bits
      exact Nat.le_refl
        (rawTimePolynomial.eval (BitString.size bits))
    output_size_le := by
      intro bits
      change BitString.size
          (machineOutput compiledMachine
            (rawTimePolynomial.eval (BitString.size bits)) bits) ≤
        BitString.size bits
      simpa [BitString.size,
        compiledMachineOutput_eq_validatedCNFBytes] using
          validatedCNFBytes_size_le bits }

theorem validatedCNFBytesPolynomialTimeFunction_output
    (bits : BitString) :
    validatedCNFBytesPolynomialTimeFunction.output bits =
      validatedCNFBytes bits := by
  change machineOutput compiledMachine
      (rawTimePolynomial.eval (BitString.size bits)) bits =
    validatedCNFBytes bits
  simpa [BitString.size] using
    compiledMachineOutput_eq_validatedCNFBytes bits

def validatedCNFBytesRawRefinement :
    FunctionProgram.RawRefinement
      validatedCNFBytesPolynomialTimeFunction.program := by
  change FunctionProgram.RawRefinement
    (.machine compiledMachine rawTimePolynomial)
  exact FunctionProgram.RawRefinement.ofMachine
    compiledMachine rawTimePolynomial

end PNP.Concrete.CNFSourceParser
