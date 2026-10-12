/-
Copyright (c) 2026 PNP Labs.

Closed path-derived augmentation machine. One packet contains the current
table and path, not precomputed update pairs. All raw packets terminate in
polynomial encoded time; canonical results match ordered table updates.
-/
import PNP.Concrete.NormalizerAugmentationBounds

namespace PNP.Concrete.NormalizerBlocks.Augmentation
open BitRegister

def initial (input : BitString) : State := ⟨⟨Occurrence.initialRegisters input, [], [], []⟩, []⟩
def loader : Block 13 := liftBatch BatchPacket.loader
def loaded (input : BitString) : State := (initial input).withBatch (BatchPacket.loaded input)
def loaderFuel (input : BitString) : Nat := BatchPacket.loaderFuel input
theorem loader_exec (input : BitString) :
    Exec loader (initial input).store (loaderFuel input) (loaded input).store :=
  liftBatch_exec _ (initial input) _ _ (BatchPacket.loader_exec input)
def block : Block 13 := .seq loader phase
def program : Program 13 := block.program 0 8
def result (input : BitString) : State := phaseResult (loaded input)
def sourceSteps (input : BitString) : Nat := loaderFuel input + phaseFuel (loaded input)
def loadedBudget : NatPolynomial := .linear 34 44
def sourceFuel : NatPolynomial := .add (.linear 33 45) (phaseBudget.substitute loadedBudget)

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
    sourceFuel.eval size = 33 * size + 45 + phaseBudget.eval (loadedBudget.eval size) := by
  change 33 * size + 45 + (phaseBudget.substitute loadedBudget).eval size = _
  rw [NatPolynomial.eval_substitute]
theorem loaded_bounded (input : BitString) : (loaded input).store.Bounded (loadedBudget.eval input.length) := by
  have before := BitRegister.initial_bounded program input
  rw [initial_registers] at before
  have checked := (loader_exec input).bounded input.length before
  have fuel := BatchPacket.loaderFuel_bound input
  apply Store.bounded_mono checked
  change input.length + BatchPacket.loaderFuel input ≤ 34 * input.length + 44
  omega
theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have phase := phaseFuel_bound (loaded input) _ (loaded_bounded input)
  have loader := BatchPacket.loaderFuel_bound input
  change loaderFuel input ≤ 33 * input.length + 44 at loader
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
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 13 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem polynomial_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = (result input).pairs.core.output := by
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).store.get 8 = _
  rw [padded_run]
  rfl
theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 13 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input
def encode (entries : MatchingTable.Entries) (xs : List CNFLiteral) : BitString :=
  TableInit.encodeCount (MatchingTable.encode entries).length
    (MatchingTable.encode entries ++ PathData.encode xs)
theorem polynomial_canonical (entries : MatchingTable.Entries) (xs : List CNFLiteral) :
    polynomial.output (encode entries xs) = MatchingTable.encode (MatchingTable.writeAll entries (PathPairs.value xs)) := by
  rw [polynomial_output]
  have data := BatchPacket.loaded_canonical (MatchingTable.encode entries) (PathData.encode xs)
  exact phase_canonical (loaded (encode entries xs)) xs entries data.1 data.2
private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 13 sourceFuel).eval input.length) input := rfl
theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 13 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm
theorem machine_canonical (entries : MatchingTable.Entries) (xs : List CNFLiteral) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 13 sourceFuel).eval (encode entries xs).length)
      (encode entries xs) = MatchingTable.encode (MatchingTable.writeAll entries (PathPairs.value xs)) := by
  rw [machine_output, polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.Augmentation
