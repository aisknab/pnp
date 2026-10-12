/-
Copyright (c) 2026 PNP Labs.

Whole-search polynomial runtime and output bounds. Intermediate register
sizes are derived from actual execution, then substituted into the next
phase's budget. The compiled machine accepts every raw bitstring.
-/
import PNP.Concrete.NormalizerSearchBounds

namespace PNP.Concrete.NormalizerBlocks.Search
open BitRegister

def exploredBudget : NatPolynomial := .add (.linear 1 0) Exploration.sourceFuel
def derivedBudget : NatPolynomial := .add exploredBudget (seenBudget.substitute exploredBudget)
def selectedBudget : NatPolynomial := .add derivedBudget (selectBudget.substitute derivedBudget)
def sourceFuel : NatPolynomial :=
  .add (.constant 1) (.add Exploration.sourceFuel
    (.add (seenBudget.substitute exploredBudget)
      (.add (selectBudget.substitute derivedBudget) (decideBudget.substitute selectedBudget))))

theorem exploredBudget_eval (size : Nat) :
    exploredBudget.eval size = size + Exploration.sourceFuel.eval size := by
  change (1 * size + 0) + Exploration.sourceFuel.eval size = _
  rw [Nat.one_mul, Nat.add_zero]
theorem derivedBudget_eval (size : Nat) :
    derivedBudget.eval size = exploredBudget.eval size + seenBudget.eval (exploredBudget.eval size) := by
  change exploredBudget.eval size + (seenBudget.substitute exploredBudget).eval size = _
  rw [NatPolynomial.eval_substitute]
theorem selectedBudget_eval (size : Nat) :
    selectedBudget.eval size = derivedBudget.eval size + selectBudget.eval (derivedBudget.eval size) := by
  change derivedBudget.eval size + (selectBudget.substitute derivedBudget).eval size = _
  rw [NatPolynomial.eval_substitute]
theorem sourceFuel_eval (size : Nat) :
    sourceFuel.eval size = 1 + (Exploration.sourceFuel.eval size +
      (seenBudget.eval (exploredBudget.eval size) +
        (selectBudget.eval (derivedBudget.eval size) + decideBudget.eval (selectedBudget.eval size)))) := by
  change 1 + (Exploration.sourceFuel.eval size + ((seenBudget.substitute exploredBudget).eval size +
    ((selectBudget.substitute derivedBudget).eval size + (decideBudget.substitute selectedBudget).eval size))) = _
  rw [NatPolynomial.eval_substitute, NatPolynomial.eval_substitute, NatPolynomial.eval_substitute]

theorem explored_bounded (input : BitString) :
    (explored input).store.Bounded (exploredBudget.eval input.length) := by
  have start := BitRegister.initial_bounded program input
  rw [initial_registers] at start
  have checked := (explore_exec input).bounded input.length start
  apply Store.bounded_mono checked
  rw [exploredBudget_eval]
  exact Nat.add_le_add_left (exploreFuel_bound input) input.length

theorem seenDerived_bounded (input : BitString) :
    (seenDerived (explored input)).store.Bounded (derivedBudget.eval input.length) := by
  have before := explored_bounded input
  have fuel := deriveSeenFuel_bound (explored input) (exploredBudget.eval input.length) before
  have checked := (deriveSeen_exec (explored input)).bounded (exploredBudget.eval input.length) before
  apply Store.bounded_mono checked
  rw [derivedBudget_eval]
  exact Nat.add_le_add_left fuel _

theorem selected_bounded (input : BitString) :
    (selected (seenDerived (explored input))).store.Bounded (selectedBudget.eval input.length) := by
  have before := seenDerived_bounded input
  have fuel := selectFuel_bound (seenDerived (explored input)) (derivedBudget.eval input.length) before
  have checked := (select_exec (seenDerived (explored input))).bounded (derivedBudget.eval input.length) before
  apply Store.bounded_mono checked
  rw [selectedBudget_eval]
  exact Nat.add_le_add_left fuel _

theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ sourceFuel.eval input.length := by
  have exploration := exploreFuel_bound input
  have seen := deriveSeenFuel_bound (explored input) _ (explored_bounded input)
  have candidate := selectFuel_bound (seenDerived (explored input)) _ (seenDerived_bounded input)
  have decision := decideFuel_bound (selected (seenDerived (explored input))) _ (selected_bounded input)
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
    polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 29 sourceFuel) :=
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
      ((CompilerIO.runtimePolynomial 29 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input
theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  CompilerIO.compilePolynomial_output_length_le program sourceFuel acceptsWithin input

theorem polynomial_canonical (variables : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    polynomial.output (Exploration.encode variables clauses entries) = answer (value variables clauses entries) := by
  rw [polynomial_output, result_canonical]

private theorem machine_projection (input : BitString) :
    polynomial.output input = machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 29 sourceFuel).eval input.length) input := rfl
theorem machine_output (input : BitString) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 29 sourceFuel).eval input.length) input = polynomial.output input :=
  (machine_projection input).symm
theorem machine_canonical (variables : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    machineOutput (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 29 sourceFuel).eval (Exploration.encode variables clauses entries).length)
      (Exploration.encode variables clauses entries) = answer (value variables clauses entries) := by
  rw [machine_output, polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.Search
