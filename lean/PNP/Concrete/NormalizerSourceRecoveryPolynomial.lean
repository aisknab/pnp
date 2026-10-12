/-
Copyright (c) 2026 PNP Labs.

The actual checker and full-width candidate recovery execute as one closed
finite machine. Every bitstring has a polynomial execution bound. The
returned candidate is a model only when its computed clause check succeeds.
The outer frontend still must retain the original width for final projection.
-/
import PNP.Concrete.NormalizerSourceRecoveryState

namespace PNP.Concrete.NormalizerBlocks.SourceRecovery
open BitRegister

def block : Block 36 := .seq SourceCheck.block fullWidth
def program : Program 36 := block.program 0 8
def result (input : BitString) : State := fullWidthResult (SourceCheck.result input)
def sourceSteps (input : BitString) : Nat :=
  SourceCheck.sourceSteps input+fullWidthSteps (SourceCheck.result input)
theorem block_exec (input : BitString) :
    Exec block (CutDriver.initial input).store (sourceSteps input) (result input).store :=
  Exec.seq (SourceCheck.block_exec input) (fullWidth_exec (SourceCheck.result input))
theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0,(CutDriver.initial input).store⟩ := by
  simpa only [BitRegister.initial,program,SourceCheck.program,Block.program] using
    SourceCheck.initial_registers input
attribute [local irreducible] CutDriver.State.store
theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input+1) (BitRegister.initial program input) =
      ⟨.accepted,(result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8

def recoveryInputFuel : NatPolynomial := fullWidthBound.substitute SourceCheck.resultSize
def sourceFuel : NatPolynomial := .add (.add SourceCheck.sourceFuel recoveryInputFuel) (.constant 1)
def resultSize : NatPolynomial := .add .variable sourceFuel
theorem recoveryInputFuel_eval (n : Nat) :
    recoveryInputFuel.eval n = fullWidthBound.eval (SourceCheck.resultSize.eval n) :=
  NatPolynomial.eval_substitute _ _ _
theorem sourceFuel_eval (n : Nat) :
    sourceFuel.eval n = SourceCheck.sourceFuel.eval n+recoveryInputFuel.eval n+1 := rfl
theorem resultSize_eval (n : Nat) : resultSize.eval n = n+sourceFuel.eval n := rfl
theorem recoverySteps_input_bound (input : BitString) :
    fullWidthSteps (SourceCheck.result input) ≤ recoveryInputFuel.eval input.length := by
  rw [recoveryInputFuel_eval]
  exact fullWidthSteps_bound (SourceCheck.result input) _ (SourceCheck.result_bounded input)
theorem sourceSteps_bound (input : BitString) :
    sourceSteps input+1 ≤ sourceFuel.eval input.length := by
  have first := SourceCheck.sourceSteps_bound input
  have last := recoverySteps_input_bound input
  rw [sourceFuel_eval]
  unfold sourceSteps
  omega
theorem result_bounded (input : BitString) :
    (result input).store.Bounded (resultSize.eval input.length) := by
  have execution := (block_exec input).bounded input.length (CutDriver.initial_bounded input)
  apply Store.bounded_mono (store := (result input).store) execution
  rw [resultSize_eval]
  have cost := sourceSteps_bound input
  exact Nat.add_le_add_left (by omega : sourceSteps input ≤ sourceFuel.eval input.length) input.length
theorem padded_run (input : BitString) :
    BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input) =
      ⟨.accepted,(result input).store⟩ := by
  have cost := sourceSteps_bound input
  have split : sourceFuel.eval input.length =
      (sourceSteps input+1)+(sourceFuel.eval input.length-(sourceSteps input+1)) := by omega
  rw [split,BitRegister.run_add,closed_run,BitRegister.run_accepted]
theorem acceptsWithin : CompilerIO.AcceptsWithin program sourceFuel := by
  intro input
  change (BitRegister.run program (sourceFuel.eval input.length)
    (BitRegister.initial program input)).control = .accepted
  rw [padded_run]

def polynomial : PolynomialTimeFunction := CompilerIO.compilePolynomial program sourceFuel acceptsWithin
theorem polynomial_program :
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 36 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem polynomial_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = (result input).registers.output := by
  rw [polynomial_projection,CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length)
    (BitRegister.initial program input)).store.get 8 = _
  rw [padded_run,CutDriver.State.get_output]
theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 36 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length+sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input
theorem result_output_length (input : BitString) :
    (result input).registers.output.length = (SourceCheck.result input).core.width.length :=
  fullWidth_output_length (SourceCheck.result input)
private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 36 sourceFuel).eval input.length) input := rfl
theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 36 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm

end PNP.Concrete.NormalizerBlocks.SourceRecovery
