/-
Copyright (c) 2026 PNP Labs.

Closed original-input-derived first-failure search with finite-tape
polynomial execution. The candidate is computed once and protected; the
result selects the recovery or equation branch, not a SAT solution.
-/
import PNP.Concrete.NormalizerSourceCheckState
namespace PNP.Concrete.NormalizerBlocks.SourceCheck
open BitRegister
attribute [local irreducible] CutDriver.State.store

def block : Block 36 := .seq SourceCandidate.block derive
def program : Program 36 := block.program 0 8
def result (input : BitString) : CutDriver.State := derived (SourceCandidate.result input)
def sourceSteps (input : BitString) : Nat :=
  SourceCandidate.sourceSteps input + deriveSteps (SourceCandidate.result input)
theorem block_exec (input : BitString) :
    Exec block (CutDriver.initial input).store (sourceSteps input) (result input).store :=
  Exec.seq (SourceCandidate.block_exec input) (derive_exec (SourceCandidate.result input))
theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0,(CutDriver.initial input).store⟩ := by
  simpa only [program, CutDriver.program, Block.program, BitRegister.initial] using
    CutDriver.initial_registers input
theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted,(result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 8


def deriveInputFuel : NatPolynomial := deriveBound.substitute SourceCandidate.resultSize
def sourceFuel : NatPolynomial :=
  .add (.add SourceCandidate.sourceFuel deriveInputFuel) (.constant 1)
def resultSize : NatPolynomial := .add (.linear 1 0) sourceFuel
theorem deriveInputFuel_eval (size : Nat) :
    deriveInputFuel.eval size = deriveBound.eval (SourceCandidate.resultSize.eval size) :=
  NatPolynomial.eval_substitute _ _ _
theorem sourceFuel_eval (size : Nat) :
    sourceFuel.eval size = SourceCandidate.sourceFuel.eval size + deriveInputFuel.eval size + 1 := rfl
theorem resultSize_eval (size : Nat) : resultSize.eval size = size + sourceFuel.eval size := by
  change (1 * size + 0) + sourceFuel.eval size = _
  rw [Nat.one_mul, Nat.add_zero]
theorem deriveSteps_input_bound (input : BitString) :
    deriveSteps (SourceCandidate.result input) ≤ deriveInputFuel.eval input.length := by
  rw [deriveInputFuel_eval]
  exact deriveSteps_bound (SourceCandidate.result input)
    (SourceCandidate.resultSize.eval input.length) (SourceCandidate.result_bounded input)
theorem sourceSteps_bound (input : BitString) :
    sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  rw [sourceFuel_eval]
  have prepared := SourceCandidate.sourceSteps_bound input
  have owners := deriveSteps_input_bound input
  unfold sourceSteps
  omega
theorem result_bounded (input : BitString) :
    (result input).store.Bounded (resultSize.eval input.length) := by
  have executed := (block_exec input).bounded input.length (CutDriver.initial_bounded input)
  apply Store.bounded_mono (store := (result input).store) executed
  rw [resultSize_eval]
  have bound := sourceSteps_bound input
  exact Nat.add_le_add_left (by omega : sourceSteps input ≤ sourceFuel.eval input.length) input.length
theorem padded_run (input : BitString) :
    BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input) =
      ⟨.accepted,(result input).store⟩ := by
  have bound := sourceSteps_bound input
  have split : sourceFuel.eval input.length =
      (sourceSteps input + 1) + (sourceFuel.eval input.length - (sourceSteps input + 1)) := by omega
  rw [split, BitRegister.run_add, closed_run, BitRegister.run_accepted]
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
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).store.get 8 = _
  rw [padded_run, CutDriver.State.get_output]
theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 36 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

theorem result_data (width : Nat) (formula : List (List CNFLiteral)) :
    CutDriver.Canonical width formula (result (MatchingDriver.encode width formula)) := by
  have data := SourceCandidate.result_data width formula
  have frame := derived_frame (SourceCandidate.result (MatchingDriver.encode width formula))
  exact ⟨frame.1.trans data.widthRead,frame.2.1.trans data.formulaRead,
    frame.2.2.1.trans data.matchingRead,frame.2.2.2.1.trans data.traceRead,
    frame.2.2.2.2.1.trans data.clausesRead,frame.2.2.2.2.2.trans data.variablesRead⟩

theorem result_cache (input : BitString) :
    SourceCacheDriver.columns (result input) = SourceCacheDriver.columns (SourceCandidate.result input) ∧
    SourceCacheDriver.rows (result input) = SourceCacheDriver.rows (SourceCandidate.result input) ∧
    SourceCacheDriver.slots (result input) = SourceCacheDriver.slots (SourceCandidate.result input) ∧
    SourceCacheDriver.modes (result input) = SourceCacheDriver.modes (SourceCandidate.result input) ∧
    SourceCacheDriver.owners (result input) = SourceCacheDriver.owners (SourceCandidate.result input) ∧
    SourceCacheDriver.literals (result input) = SourceCacheDriver.literals (SourceCandidate.result input) :=
  derived_cache (SourceCandidate.result input)
theorem result_candidate (input : BitString) :
    candidate (result input) = (SourceCandidate.result input).registers.output :=
  derived_candidate (SourceCandidate.result input)
private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 36 sourceFuel).eval input.length) input := rfl
theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 36 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm

end PNP.Concrete.NormalizerBlocks.SourceCheck
