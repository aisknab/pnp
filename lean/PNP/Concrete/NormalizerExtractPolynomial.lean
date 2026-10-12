/-
Copyright (c) 2026 PNP Labs.

Complete ordered extraction compiled to a deterministic finite tape machine.
All raw inputs halt within a polynomial in their encoded byte length.
Canonical inputs return exactly the first eligible unseen vertex and its
computed parent, preserving the order of every remaining vertex.
This is a search primitive, not a general SAT solver.
-/

import PNP.Concrete.NormalizerExtractLoader

namespace PNP.Concrete.NormalizerBlocks.Extraction
open BitRegister

def front : Block 27 := .seq loader loop
def frontResult (input : BitString) : State := (whole (loaded input)).state
def frontFuel (input : BitString) : Nat := loaderFuel input + (whole (loaded input)).fuel
def block : Block 27 := .seq front finish
def program : Program 27 := block.program 0 26
def result (input : BitString) : State := finished (frontResult input)
def sourceSteps (input : BitString) : Nat := frontFuel input + finishFuel (frontResult input)

def frontPolynomial : NatPolynomial :=
  .add (.linear 99 158) (.mul (.add (.linear 688 1376) (.mul (.linear 652 975) (.linear 1 1))) (.linear 1 1))
def sourceFuel : NatPolynomial := .add (.linear 10 26) (.mul (.linear 0 11) frontPolynomial)

theorem front_exec (input : BitString) : Exec front (initial input).store (frontFuel input) (frontResult input).store :=
  Exec.seq (loader_exec input) (whole_exec (loaded input))
theorem block_exec (input : BitString) : Exec block (initial input).store (sourceSteps input) (result input).store :=
  Exec.seq (front_exec input) (finish_exec (frontResult input))
theorem initial_registers (input : BitString) :
    BitRegister.initial program input = ⟨.running 0, (initial input).store⟩ := rfl

theorem closed_run (input : BitString) :
    BitRegister.run program (sourceSteps input + 1) (BitRegister.initial program input) =
      ⟨.accepted, (result input).store⟩ := by
  rw [initial_registers]
  exact (block_exec input).program_run 0 26

theorem frontPolynomial_eval (size : Nat) :
    frontPolynomial.eval size = 99 * size + 158 +
      (688 * size + 1376 + (652 * size + 975) * (size + 1)) * (size + 1) := by
  change 99 * size + 158 + (688 * size + 1376 + (652 * size + 975) * (1 * size + 1)) * (1 * size + 1) = _
  rw [Nat.one_mul]

theorem sourceFuel_eval (size : Nat) :
    sourceFuel.eval size = 10 * size + 26 + 11 * frontPolynomial.eval size := by
  change 10 * size + 26 + (0 * size + 11) * frontPolynomial.eval size = _
  rw [Nat.zero_mul, Nat.zero_add]

theorem loaded_step_bound (input : BitString) :
    stepBound (loaded input) ≤ 688 * input.length + 1375 + (652 * input.length + 975) * (input.length + 1) := by
  have sizes := loaded_size input
  have linear : 349 * (loaded input).pending.length +
      339 * (loaded input).parent.graph.core.matching.length + 1375 ≤ 688 * input.length + 1375 := by omega
  have coefficient :
      188 * (loaded input).parent.graph.core.formula.length +
        188 * (loaded input).parent.graph.core.matching.length + 236 * (loaded input).trace.length +
          40 * (loaded input).pending.length + 975 ≤ 652 * input.length + 975 := by omega
  have product := Nat.mul_le_mul coefficient (Nat.add_le_add_right sizes.2.2.1 1)
  exact Nat.add_le_add linear product

theorem frontFuel_bound (input : BitString) : frontFuel input ≤ frontPolynomial.eval input.length := by
  have load := loaderFuel_bound input
  have scanned := whole_fuel_bound (loaded input)
  have step := loaded_step_bound input
  have sizes := loaded_size input
  have coefficient : stepBound (loaded input) + 1 ≤ 688 * input.length + 1376 +
      (652 * input.length + 975) * (input.length + 1) := by omega
  have product := Nat.mul_le_mul coefficient (Nat.add_le_add_right sizes.2.2.2 1)
  rw [frontPolynomial_eval]
  unfold frontFuel
  omega

theorem front_bounded (input : BitString) :
    (frontResult input).store.Bounded (input.length + frontFuel input) := by
  have bounded := BitRegister.initial_bounded program input
  rw [initial_registers] at bounded
  exact (front_exec input).bounded input.length bounded

theorem finishFuel_of_bounded (r : State) (bound : Nat) (bounded : r.store.Bounded bound) :
    finishFuel r ≤ 10 * bound + 25 := by
  have skipped := Store.get_length_le r.store (23 : Fin 27) bounded
  have parent := Store.get_length_le r.store (19 : Fin 27) bounded
  have index := Store.get_length_le r.store (17 : Fin 27) bounded
  change r.skipped.length ≤ bound at skipped
  change r.parent.output.length ≤ bound at parent
  change r.parent.targetIndex.length ≤ bound at index
  have fuel := finishFuel_bound r
  omega

theorem finishing_bound (input : BitString) :
    finishFuel (frontResult input) ≤ 10 * (input.length + frontFuel input) + 25 :=
  finishFuel_of_bounded _ _ (front_bounded input)

theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have finish := finishing_bound input
  have product := Nat.mul_le_mul_left 11 (frontFuel_bound input)
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
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 27 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin

private theorem polynomial_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl

theorem polynomial_output (input : BitString) : polynomial.output input = (result input).output := by
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).store.get 26 = _
  rw [padded_run]
  rfl

theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 27 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input

theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

theorem polynomial_canonical (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (trace : List TraceData.Row) (unseen : List CNFLiteral) :
    polynomial.output (encode clauses entries trace unseen) = answer (value clauses entries trace unseen) := by
  rw [polynomial_output]
  exact phase_canonical _ clauses entries trace unseen (loaded_canonical clauses entries trace unseen)

private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 27 sourceFuel).eval input.length) input := rfl

theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 27 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm

theorem machine_canonical (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (trace : List TraceData.Row) (unseen : List CNFLiteral) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 27 sourceFuel).eval (encode clauses entries trace unseen).length)
      (encode clauses entries trace unseen) = answer (value clauses entries trace unseen) := by
  rw [machine_output, polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.Extraction
