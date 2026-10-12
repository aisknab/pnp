/-
Copyright (c) 2026 PNP Labs.

Closed polynomial finite-tape conversion from encoded paths to ordered
augmentation updates. The bound covers every raw input, final reversal,
and exact stop-on-invalid-pair semantics.
-/
import PNP.Concrete.NormalizerPairPhase

namespace PNP.Concrete.NormalizerBlocks.PathPairs
open BitRegister

def initial (input : BitString) : State := ⟨Occurrence.initialRegisters input, [], [], []⟩
def loader : Block 12 := .action (.copy 9 0)
def loaded (input : BitString) : State := ⟨Occurrence.initialRegisters input, input, [], []⟩
theorem loader_exec (input : BitString) : Exec loader (initial input).store 1 (loaded input).store := .action _ _
def block : Block 12 := .seq loader phase
def program : Program 12 := block.program 0 8
def result (input : BitString) : State := phaseResult (loaded input)
def sourceSteps (input : BitString) : Nat := 1 + phaseFuel (loaded input)
def sourceFuel : NatPolynomial :=
  .add (.linear 4 19) (.mul (.constant 5) (.mul (.linear 64 129) (.linear 1 1)))

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
    sourceFuel.eval size = 4 * size + 19 + 5 * ((64 * size + 129) * (size + 1)) := by
  change 4 * size + 19 + 5 * ((64 * size + 129) * (1 * size + 1)) = _
  rw [Nat.one_mul]
theorem loaded_bounded (input : BitString) : (loaded input).store.Bounded (input.length + 1) := by
  have before := BitRegister.initial_bounded program input
  rw [initial_registers] at before
  exact (loader_exec input).bounded input.length before
theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have bound := phaseFuel_bound (loaded input) (input.length + 1) (loaded_bounded input)
  change phaseFuel (loaded input) ≤ 4 * (input.length + 1) +
    5 * ((64 * input.length + 129) * (input.length + 1)) + 13 at bound
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
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 12 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem polynomial_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = (result input).core.output := by
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).store.get 8 = _
  rw [padded_run]
  rfl
theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 12 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input
theorem polynomial_canonical (xs : List CNFLiteral) :
    polynomial.output (PathData.encode xs) = TableBatch.encodeUpdates (value xs) := by
  rw [polynomial_output]
  exact phase_canonical _ xs rfl
private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 12 sourceFuel).eval input.length) input := rfl
theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 12 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm
theorem machine_canonical (xs : List CNFLiteral) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 12 sourceFuel).eval (PathData.encode xs).length)
      (PathData.encode xs) = TableBatch.encodeUpdates (value xs) := by
  rw [machine_output, polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.PathPairs
