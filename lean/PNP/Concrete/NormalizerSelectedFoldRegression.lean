import PNP.Concrete.NormalizerSelectedFold

namespace PNP.Concrete.NormalizerBlocks

private def denseOperation : SelectedFold.Operation where
  body := DenseClauses.body
  after := DenseClauses.bodyResult
  cost := DenseClauses.bodyFuel
  execution := DenseClauses.body_exec
  remaining := fun r => (DenseClauses.body_fields r).2.1
  fields := fun r => ⟨(DenseClauses.body_fields r).1,(DenseClauses.body_fields r).2.2⟩
  bound := DenseClauses.bodyBound
  cost_bound := DenseClauses.bodyFuel_bound

example (r : DenseClauses.State) :
    Exec (SelectedFold.loop denseOperation) r.store
      (SelectedFold.whole denseOperation r).fuel (SelectedFold.whole denseOperation r).state.store :=
  SelectedFold.whole_exec denseOperation r

example (op : SelectedFold.Operation) (r : DenseClauses.State) (nonempty : r.remaining ≠ []) :
    (SelectedFold.stepped op r).remaining.length < r.remaining.length :=
  SelectedFold.step_progress op r nonempty

example (op : SelectedFold.Operation) (r : DenseClauses.State) (bound : Nat)
    (a : r.remaining.length ≤ bound) (b : r.formula.length ≤ bound)
    (c : r.core.variables.length ≤ bound) :
    (SelectedFold.whole op r).fuel ≤ (SelectedFold.loopBound op).eval bound :=
  SelectedFold.whole_fuel_bound op r bound a b c

#print axioms SelectedFold.step_exec
#print axioms SelectedFold.step_progress
#print axioms SelectedFold.scan_exec
#print axioms SelectedFold.scan_fields
#print axioms SelectedFold.scan_fuel_bound
#print axioms SelectedFold.whole_exec
#print axioms SelectedFold.whole_fuel_bound

end PNP.Concrete.NormalizerBlocks
