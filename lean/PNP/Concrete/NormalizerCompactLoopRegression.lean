import PNP.Concrete.NormalizerCompactLoop

namespace PNP.Concrete.NormalizerBlocks

example (r : CompactClause.State) (pending : r.pending = []) :
    (CompactClause.whole r).state = r := by
  change (CompactClause.scan (r.pending.length + 1) r).state = r
  rw [CompactClause.scan_stopped _ r pending]

example (r : CompactClause.State) :
    (CompactClause.whole r).state.variables = r.variables :=
  CompactClause.whole_variables r

example (r : CompactClause.State) (bound : Nat) (bounded : r.store.Bounded bound) :
    (CompactClause.whole r).fuel ≤ (71 * bound + 119) * (bound + 1) + 1 := by
  rw [← CompactClause.callBound_eval]
  exact CompactClause.whole_fuel_bounded r bound bounded

#print axioms CompactClause.scan_exec
#print axioms CompactClause.scan_variables
#print axioms CompactClause.scan_fuel_bound
#print axioms CompactClause.whole_exec
#print axioms CompactClause.whole_variables
#print axioms CompactClause.whole_fuel_bound
#print axioms CompactClause.whole_fuel_bounded

end PNP.Concrete.NormalizerBlocks
