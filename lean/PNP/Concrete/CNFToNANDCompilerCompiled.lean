/-
Copyright (c) 2026 PNP Labs.

Compiled all-input boundary for the fixed literal CNF-to-NAND compiler.
The external decoder appears only in correctness statements.  The executable
is the closed three-node parser/carrier/controller graph and callers provide
no schedule or trace certificate.
-/

import PNP.Concrete.CNFToNANDCompilerTotalTrace
import PNP.Concrete.CNFSourceParserCompiled
import PNP.Concrete.PipelineRefinement

namespace PNP.Concrete.CNFToNANDCompilerCompiled

open PNP.Concrete

abbrev machine : WorkMachine :=
  CNFToNANDCompilerMachine.machine

abbrev compiledMachine : Machine :=
  CNFToNANDCompilerMachine.compiledMachine

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
        CNFToNANDCompilerPolynomialBound.allInputWorkBound
          bits.length) :
    run compiledMachine
        (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length)
        (encodeWorkConfiguration
          (workStartConfiguration machine
            (rawInputWorkTape bits))) =
      encodeWorkConfiguration final := by
  apply run_compileWorkMachine_of_workRunExact_halted_le
    machine steps
      (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
        bits.length)
    (workStartConfiguration machine (rawInputWorkTape bits))
    final runExact halted
  rw [CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial_eval]
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
        CNFToNANDCompilerPolynomialBound.allInputWorkBound
          bits.length) :
    Configuration.BlankEquivalent
      (run compiledMachine
        (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length)
        (startConfig compiledMachine bits))
      (encodeWorkConfiguration final) := by
  have transported :=
    run_blankEquivalent compiledMachine
      (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
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
        CNFToNANDCompilerPolynomialBound.allInputWorkBound
          bits.length) :
    (run compiledMachine
      (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
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
        CNFToNANDCompilerPolynomialBound.allInputWorkBound
          bits.length) :
    (run compiledMachine
      (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
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
        CNFToNANDCompilerPolynomialBound.allInputWorkBound
          bits.length) :
    boundedDecide compiledMachine
        (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
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
        CNFToNANDCompilerPolynomialBound.allInputWorkBound
          bits.length) :
    boundedDecide compiledMachine
        (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length) bits ≠ .timeout := by
  apply (boundedDecide_ne_timeout_iff_final_isHalted
    compiledMachine
    (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
      bits.length) bits).mpr
  have stateEq :=
    compiledRun_state_eq_of_exact
      bits steps final runExact halted bounded
  change
    compiledMachine.isHalted
        (run compiledMachine
          (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
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
        CNFToNANDCompilerPolynomialBound.allInputWorkBound
          bits.length) :
    machineOutput compiledMachine
        (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length) bits =
      (encodeWorkTape final.tape).outputBits := by
  unfold machineOutput
  simpa [encodeWorkConfiguration] using
    (compiledRun_output_eq_of_exact
      bits steps final runExact halted bounded)

/-! ## Unconditional compiled interface -/

/-- The compiled literal machine computes the total fail-closed pure
CNF-to-NAND transformation on every bitstring. -/
theorem compiledMachineOutput_eq_compileEncodedCNFToNAND
    (bits : BitString) :
    machineOutput compiledMachine
        (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length) bits =
      CNFToNAND.compileEncodedCNFToNAND bits := by
  rcases CNFToNANDCompilerTotalTrace.allInput_bounded_exact bits with
    ⟨steps, final, bounded, runExact, halted,
      _acceptanceIff, outputEq⟩
  exact
    (compiledMachineOutput_eq_of_exact
      bits steps final runExact halted bounded).trans outputEq

/-- The compiler accepts exactly strict decodable CNF words; malformed
sources reject after producing the empty fail-closed output. -/
theorem compiledBoundedDecide_accept_iff (bits : BitString) :
    boundedDecide compiledMachine
        (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length) bits = .accept ↔
      CNFSourceParser.ValidEncodedCNF bits := by
  rcases CNFToNANDCompilerTotalTrace.allInput_bounded_exact bits with
    ⟨steps, final, bounded, runExact, halted,
      acceptanceIff, _outputEq⟩
  exact
    (compiledBoundedDecide_accept_iff_of_exact
      bits steps final runExact halted bounded).trans acceptanceIff

/-- The compiled compiler never times out at its advertised polynomial. -/
theorem compiledBoundedDecide_ne_timeout (bits : BitString) :
    boundedDecide compiledMachine
        (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
          bits.length) bits ≠ .timeout := by
  rcases CNFToNANDCompilerTotalTrace.allInput_bounded_exact bits with
    ⟨steps, final, bounded, runExact, halted,
      _acceptanceIff, _outputEq⟩
  exact compiledBoundedDecide_ne_timeout_of_exact
    bits steps final runExact halted bounded

def polynomialTimeMachine :
    PolynomialTimeMachine CNFSourceParser.ValidEncodedCNF :=
  { machine := compiledMachine
    timeBound :=
      CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial
    haltsWithin := by
      intro bits
      simpa [BitString.size] using
        compiledBoundedDecide_ne_timeout bits
    accepts_iff := by
      intro bits
      simpa [BitString.size] using
        compiledBoundedDecide_accept_iff bits }

/-- Proof-bearing polynomial-time implementation of the total fail-closed
CNF-to-NAND byte function. -/
def cnfToNANDPolynomialTimeFunction :
    PolynomialTimeFunction :=
  { program := .machine compiledMachine
      CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial
    runtimeBound :=
      CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial
    outputSizeBound := CNFToNAND.cnfToNANDOutputSizePolynomial
    haltsWithin := by
      intro bits
      change boundedDecide compiledMachine
          (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
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
            (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
              (BitString.size bits))
            bits) ≤
        CNFToNAND.cnfToNANDOutputSizePolynomial.eval
          (BitString.size bits)
      rw [show
        CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
            (BitString.size bits) =
          CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
            bits.length by rfl]
      rw [compiledMachineOutput_eq_compileEncodedCNFToNAND]
      exact CNFToNAND.compileEncodedCNFToNAND_size_le bits }

theorem cnfToNANDPolynomialTimeFunction_output
    (bits : BitString) :
    cnfToNANDPolynomialTimeFunction.output bits =
      CNFToNAND.compileEncodedCNFToNAND bits := by
  change machineOutput compiledMachine
      (CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial.eval
        (BitString.size bits)) bits =
    CNFToNAND.compileEncodedCNFToNAND bits
  simpa [BitString.size] using
    compiledMachineOutput_eq_compileEncodedCNFToNAND bits

/-- The function leaf is already its exact literal raw-machine refinement. -/
def cnfToNANDRawRefinement :
    FunctionProgram.RawRefinement
      cnfToNANDPolynomialTimeFunction.program := by
  change FunctionProgram.RawRefinement
    (.machine compiledMachine
      CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial)
  exact FunctionProgram.RawRefinement.ofMachine compiledMachine
    CNFToNANDCompilerPolynomialBound.compiledRawTimePolynomial

end PNP.Concrete.CNFToNANDCompilerCompiled
