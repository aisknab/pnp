/-
Copyright (c) 2026 PNP Labs.

One fixed finite candidate machine reads the count and both tables from its
input. Its all-bitstring polynomial bound includes parsing and every table
scan, and the verified compiler supplies an actual tape-machine runtime bound.
Canonical output is the first free seen index, not an externally supplied
answer. This primitive does not construct the reachability trace.
-/

import PNP.Concrete.NormalizerCandidatePacketLoader

namespace PNP.Concrete.NormalizerBlocks.CandidatePacket

open BitRegister

def block : Block 13 := .seq loader Candidate.loop
def program : Program 13 := block.program 0 12
def result (input : BitString) : Candidate.State := (Candidate.whole (loaded input)).state
def sourceSteps (input : BitString) : Nat := loaderFuel input + (Candidate.whole (loaded input)).fuel
def sourceFuel : NatPolynomial := .add (.linear 70 121) (.mul (.linear 24 52) (.linear 5 7))

theorem sourceFuel_eval (size : Nat) :
    sourceFuel.eval size = 70 * size + 121 + (24 * size + 52) * (5 * size + 7) := rfl

theorem block_exec (input : BitString) :
    Exec block (initial input).store (sourceSteps input) (result input).store :=
  Exec.seq (loader_exec input) (Candidate.whole_exec (loaded input))

theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (initial input).store⟩ := rfl

theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 12

theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have loader := loaderFuel_bound input
  have sizes := loaded_size input
  have loop := Candidate.whole_fuel_bound (loaded input)
  have perStep : 12 * (loaded input).matching.length + 12 * (loaded input).seen.length + 52 ≤
      24 * input.length + 52 := by omega
  have count : (loaded input).remaining.length + 1 ≤ 5 * input.length + 7 := by omega
  have product := Nat.mul_le_mul perStep count
  rw [sourceFuel_eval]
  simp only [sourceSteps]
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

theorem polynomial_output (input : BitString) : polynomial.output input = (result input).output := by
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).store.get 12 = _
  rw [padded_run]
  rfl

theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 13 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input

theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

theorem polynomial_canonical (count : Nat) (matching seen : MatchingTable.Entries) :
    polynomial.output (encode count matching seen) =
      TableOwner.answer (Candidate.selectFrom matching seen count 0) := by
  rw [polynomial_output]
  change (Candidate.whole (loaded (encode count matching seen))).state.output = _
  rw [loaded_canonical]
  exact Candidate.whole_canonical count matching seen

private theorem output_projection (input : BitString) :
    polynomial.output input =
      machineOutput (CompilerIO.rawMachine program)
        ((CompilerIO.runtimePolynomial 13 sourceFuel).eval input.length) input := rfl

theorem machine_canonical (count : Nat) (matching seen : MatchingTable.Entries) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 13 sourceFuel).eval (encode count matching seen).length)
      (encode count matching seen) = TableOwner.answer (Candidate.selectFrom matching seen count 0) :=
  (output_projection (encode count matching seen)).symm.trans (polynomial_canonical count matching seen)

end PNP.Concrete.NormalizerBlocks.CandidatePacket
