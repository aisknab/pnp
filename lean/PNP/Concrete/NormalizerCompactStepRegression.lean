import PNP.Concrete.NormalizerCompactStep

namespace PNP.Concrete.NormalizerBlocks

example (r : CompactClause.State) (pending : r.pending = [true,false]) :
    (CompactClause.stepped r).buffer = r.buffer := by
  simp only [CompactClause.stepped, pending, CompactClause.stopped,
    CompactClause.guarded, CompactClause.State.withCore]

example (r : CompactClause.State) (pending : r.pending = [false]) :
    (CompactClause.stepped r).pending = [] := by
  simp only [CompactClause.stepped, pending, CompactClause.stopped]

example (r : CompactClause.State) (nonempty : r.pending ≠ []) :
    (CompactClause.stepped r).pending.length < r.pending.length :=
  CompactClause.step_progress r nonempty

#print axioms CompactClause.step_exec
#print axioms CompactClause.stepped_variables
#print axioms CompactClause.step_progress
#print axioms CompactClause.stepFuel_bound
#print axioms CompactClause.step_canonical

end PNP.Concrete.NormalizerBlocks
