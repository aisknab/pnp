import PNP.Concrete.NormalizerDenseLoop

namespace PNP.Concrete.NormalizerBlocks

example (r : DenseClauses.State) (remaining : r.remaining = []) :
    (DenseClauses.whole r).state = r := by
  change (DenseClauses.scan (r.remaining.length + 1) r).state = r
  rw [DenseClauses.scan_stopped _ r remaining]

example (r : DenseClauses.State) (remaining : r.remaining = [true,false]) :
    (DenseClauses.stepped r).core.buffer = r.core.buffer := by
  simp only [DenseClauses.stepped, remaining, DenseClauses.stopped]

example (r : DenseClauses.State) :
    (DenseClauses.whole r).state.formula = r.formula ∧
      (DenseClauses.whole r).state.core.variables = r.core.variables :=
  DenseClauses.whole_fields r

#print axioms DenseClauses.step_exec
#print axioms DenseClauses.step_progress
#print axioms DenseClauses.stepFuel_bound
#print axioms DenseClauses.scan_exec
#print axioms DenseClauses.scan_fields
#print axioms DenseClauses.scan_fuel_bound
#print axioms DenseClauses.whole_exec
#print axioms DenseClauses.whole_fuel_bound

end PNP.Concrete.NormalizerBlocks
