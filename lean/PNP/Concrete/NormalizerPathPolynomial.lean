/-
Copyright (c) 2026 PNP Labs.

Complete path reconstruction compiled to a deterministic finite tape
machine. One encoded-input polynomial bounds loading, all suffix searches,
accumulator growth, and output serialization for every raw input word.
-/
import PNP.Concrete.NormalizerPathLoader

namespace PNP.Concrete.NormalizerBlocks.TracePath
open BitRegister

def block : Block 23 := .seq loader phase
def program : Program 23 := block.program 0 8
def result (input : BitString) : State := phaseResult (loaded input)
def sourceSteps (input : BitString) : Nat := loaderFuel input + phaseFuel (loaded input)
def sourceFuel : NatPolynomial :=
  .add (.linear 24 116) (.mul (.constant 5) (.mul (.linear 47 125) (.linear 1 1)))

theorem block_exec (input : BitString) : Exec block (initial input).store (sourceSteps input) (result input).store :=
  Exec.seq (loader_exec input) (phase_exec (loaded input))
theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (initial input).store⟩ := rfl
theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8

theorem sourceFuel_eval (size : Nat) :
    sourceFuel.eval size = 24 * size + 116 + 5 * ((47 * size + 125) * (size + 1)) := by
  change 24 * size + 116 + 5 * ((47 * size + 125) * (1 * size + 1)) = _
  rw [Nat.one_mul]

theorem loaded_bounded (input : BitString) : (loaded input).store.Bounded (input.length + loaderFuel input) := by
  have bounded := BitRegister.initial_bounded program input
  rw [initial_registers] at bounded
  exact (loader_exec input).bounded input.length bounded

theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have load := loaderFuel_bound input
  have size := loaded_pending_bound input
  have phaseBound := phaseFuel_bound (loaded input) (input.length + loaderFuel input) (loaded_bounded input)
  have first : 47 * (loaded input).core.pending.length + 125 ≤ 47 * input.length + 125 := by omega
  have product := Nat.mul_le_mul first (Nat.add_le_add_right size 1)
  rw [sourceFuel_eval]
  unfold sourceSteps
  omega

theorem padded_run (input : BitString) :
    BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  have bound := sourceSteps_bound input
  have split : sourceFuel.eval input.length =
      (sourceSteps input + 1) + (sourceFuel.eval input.length - (sourceSteps input + 1)) := by omega
  rw [split, BitRegister.run_add, closed_run, BitRegister.run_accepted]

theorem acceptsWithin : CompilerIO.AcceptsWithin program sourceFuel := by
  intro input
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).control = .accepted
  rw [padded_run]

def polynomial : PolynomialTimeFunction := CompilerIO.compilePolynomial program sourceFuel acceptsWithin
theorem polynomial_program :
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 23 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin

private theorem polynomial_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = (result input).registers.output := by
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).store.get 8 = _
  rw [padded_run]
  rfl
theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 23 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

theorem polynomial_canonical (target : CNFLiteral) (trace : List TraceData.Row) :
    polynomial.output (encode target trace) = PathData.answer (value trace target) := by
  rw [polynomial_output]
  have data := loaded_canonical target trace
  exact phase_canonical _ target trace data.1 data.2.1 data.2.2

private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 23 sourceFuel).eval input.length) input := rfl
theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 23 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm
theorem machine_canonical (target : CNFLiteral) (trace : List TraceData.Row) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 23 sourceFuel).eval (encode target trace).length)
      (encode target trace) = PathData.answer (value trace target) := by
  rw [machine_output, polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.TracePath
