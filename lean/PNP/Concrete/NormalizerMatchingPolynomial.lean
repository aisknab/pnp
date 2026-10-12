/-
Copyright (c) 2026 PNP Labs.

Complete matching compiled to a deterministic finite tape machine.
Every raw input has one uniform polynomial bound covering internal
initialization, all search/update rounds, and final encoded table output.
Canonical output agrees with the full internally initialized recurrence.
-/
import PNP.Concrete.NormalizerMatchingRoundBounds

namespace PNP.Concrete.NormalizerBlocks.MatchingDriver
open BitRegister

theorem scan_fuel_bound (fuel bound : Nat) (r : State) (data : Within bound r) :
    (scan fuel r).fuel ≤ (roundPolynomial.eval bound + 1) * fuel + 1 := by
  induction fuel generalizing r with
  | zero => simp only [scan, Nat.mul_zero, Nat.zero_add]; exact Nat.le_refl _
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil =>
          simp only [scan, remaining]
          omega
      | cons bit rest =>
          have nonempty : r.remaining ≠ [] := by rw [remaining]; intro h; cases h
          rw [scan_step fuel r nonempty, Nat.mul_succ]
          dsimp only
          have round := bodyFuel_bound bound r data
          have next := ih (bodyResult r) data.body
          omega

def limitPolynomial : NatPolynomial := .linear 6 6
def sourceFuel : NatPolynomial :=
  .add (.linear 122 230)
    (.mul (.add (roundPolynomial.substitute limitPolynomial) (.constant 1)) (.linear 6 8))
theorem sourceFuel_eval (size : Nat) :
    sourceFuel.eval size = 122 * size + 230 + (roundPolynomial.eval (6 * size + 6) + 1) * (6 * size + 8) := by
  change 122 * size + 230 + ((roundPolynomial.substitute limitPolynomial).eval size + 1) * (6 * size + 8) = _
  rw [NatPolynomial.eval_substitute]
  rfl
theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have start := initializeFuel_bound input
  have loop := scan_fuel_bound ((initialized input).remaining.length + 1) (6 * input.length + 6)
    (initialized input) (initialized_within input)
  have count := (initialized_fields input).2.2.2
  have counted := (Exploration.source_sizes input).2.2.2
  have size : (initialized input).remaining.length + 1 ≤ 6 * input.length + 8 := by omega
  have product := Nat.mul_le_mul_left (roundPolynomial.eval (6 * input.length + 6) + 1) size
  change (whole (initialized input)).fuel ≤ _ at loop
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
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 33 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin
private theorem polynomial_projection (input : BitString) :
    polynomial.output input = (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl
theorem polynomial_output (input : BitString) : polynomial.output input = (result input).registers.output := by
  rw [polynomial_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length) (BitRegister.initial program input)).store.get 8 = _
  rw [padded_run, State.get_output]
theorem polynomial_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 33 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input
theorem polynomial_table_bound (input : BitString) :
    (polynomial.output input).length ≤ MatchingLoop.tableBytes (6 * input.length + 6) (6 * input.length + 6) := by
  rw [polynomial_output]
  exact result_table_bound input
theorem polynomial_canonical (variables : Nat) (clauses : List (List CNFLiteral)) :
    polynomial.output (encode variables clauses) = MatchingTable.encode (MatchingLoop.fullTable variables clauses) := by
  rw [polynomial_output, result_canonical]
private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 33 sourceFuel).eval input.length) input := rfl
theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 33 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm
theorem machine_canonical (variables : Nat) (clauses : List (List CNFLiteral)) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 33 sourceFuel).eval (encode variables clauses).length)
      (encode variables clauses) = MatchingTable.encode (MatchingLoop.fullTable variables clauses) := by
  rw [machine_output, polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.MatchingDriver
