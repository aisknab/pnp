/-
Copyright (c) 2026 PNP Labs.

A closed polynomial-time table-update machine. One fixed finite program reads
its table and all updates from the encoded input, then runs the uniform loop.
The bound applies to every raw bitstring, including malformed packets; its
shared table-size invariant prevents repeated writes from hiding exponential
growth. The compiler supplies the actual tape-machine runtime theorem.
-/

import PNP.Concrete.NormalizerBatchPacketLoader

namespace PNP.Concrete.NormalizerBlocks.BatchPacket

open BitRegister

theorem tableBound_mono {pending pending' table table' : Nat}
    (hp : pending ≤ pending') (ht : table ≤ table') :
    TableBatch.tableBound pending table ≤ TableBatch.tableBound pending' table' := by
  have first : 18 * pending + 40 ≤ 18 * pending' + 40 := by omega
  have second : pending + 1 ≤ pending' + 1 := by omega
  have product := Nat.mul_le_mul first second
  simp only [TableBatch.tableBound]
  omega

theorem totalCostBound_mono {pending pending' table table' : Nat}
    (hp : pending ≤ pending') (ht : table ≤ table') :
    TableBatch.totalCostBound pending table ≤ TableBatch.totalCostBound pending' table' := by
  have cost := TableBatch.costBound_mono hp (tableBound_mono hp ht)
  have first :
      TableBatch.costBound pending (TableBatch.tableBound pending table) + 1 ≤
        TableBatch.costBound pending' (TableBatch.tableBound pending' table') + 1 := by omega
  have second : pending + 1 ≤ pending' + 1 := by omega
  have product := Nat.mul_le_mul first second
  simp only [TableBatch.totalCostBound]
  omega

def tableSizePolynomial : NatPolynomial :=
  .add .variable (.mul (.linear 18 40) (.add .variable (.constant 1)))

def iterationPolynomial : NatPolynomial :=
  .add
    (.add
      (.add (.mul (.linear 36 82) (.add tableSizePolynomial (.constant 1)))
        (.mul (.constant 80) .variable))
      (.mul (.constant 4) tableSizePolynomial))
    (.constant 191)

def wholePolynomial : NatPolynomial :=
  .add (.mul (.add iterationPolynomial (.constant 1)) (.add .variable (.constant 1))) (.constant 1)

def sourceFuel : NatPolynomial := .add (.linear 33 45) wholePolynomial

theorem sourceFuel_eval (size : Nat) :
    sourceFuel.eval size = 33 * size + 45 + TableBatch.totalCostBound size size := rfl

def block : Block 11 := .seq loader TableBatch.loop
def program : Program 11 := block.program 0 10
def result (input : BitString) : TableBatch.State := (TableBatch.whole (loaded input)).state
def sourceSteps (input : BitString) : Nat := loaderFuel input + (TableBatch.whole (loaded input)).fuel

theorem block_exec (input : BitString) :
    Exec block (seedState input).store (sourceSteps input) (result input).store :=
  Exec.seq (loader_exec input) (TableBatch.whole_exec (loaded input))

theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (seedState input).store⟩ := rfl

theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 10

theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have loader := loaderFuel_bound input
  have size := loaded_size input
  have loop := (TableBatch.whole_bounds (loaded input)).2
  have bound := totalCostBound_mono size.1 size.2
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
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 11 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin

private theorem polynomial_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl

theorem polynomial_output (input : BitString) : polynomial.output input = (result input).table := by
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).store.get 10 = _
  rw [padded_run]
  rfl

theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 11 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input

theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

end PNP.Concrete.NormalizerBlocks.BatchPacket
