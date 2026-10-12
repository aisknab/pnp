import PNP.Concrete.NormalizerParentScan

namespace PNP.Concrete.NormalizerBlocks

example (r : ParentQuery.State) : (ParentQuery.whole r).state.pending = [] := ParentQuery.whole_stopped r
example (r : ParentQuery.State) :
    (ParentQuery.whole r).fuel ≤ (ParentQuery.stepBound r + 1) * (r.pending.length + 1) + 1 :=
  ParentQuery.whole_fuel_bound r
example (fuel : Nat) (r : ParentQuery.State) (h : r.pending = []) :
    ParentQuery.scan fuel r = ⟨1, r⟩ := ParentQuery.scan_empty fuel r h
example (fuel : Nat) (r : ParentQuery.State) :
    (ParentQuery.scan fuel r).state.targetTag = r.targetTag := (ParentQuery.scan_preserves fuel r).2.1

#print axioms ParentQuery.scan_empty
#print axioms ParentQuery.scan_step
#print axioms ParentQuery.scan_exec
#print axioms ParentQuery.scan_fuel_bound
#print axioms ParentQuery.scan_stopped
#print axioms ParentQuery.scan_preserves
#print axioms ParentQuery.whole_exec
#print axioms ParentQuery.whole_fuel_bound
#print axioms ParentQuery.whole_stopped

end PNP.Concrete.NormalizerBlocks
